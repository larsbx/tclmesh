#!/usr/bin/env tclsh
# Per-party view and certificate conformance (docs/testing.md).
#
#   tclsh tools/views.tcl check CIRCUITS SPEC_VIEWS
#   tclsh tools/views.tcl certificates CIRCUITS > CERTS
#   tclsh tools/views.tcl check-certificates CERTS SPEC_CERTIFICATES
#
# For every circuit vector: the evaluator's view recorded by the oblivious
# backend, the view the Tcl harness declares, and the view the Lean model
# declares (`spec-eval --views`) must coincide; and every variant (other
# ciphertext inputs, same public inputs) must give the same recorded view.
# The calibration backends (`views-lazy`, `views-sized`) must be caught on
# every vector where they can leak.

package require Tcl 8.6
package require json
package require json::write
json::write indented 0
json::write aligned 0

set root [file dirname [file dirname [file normalize [info script]]]]
lappend ::auto_path $root
package require tclmesh 0.2.0

proc read_json {path} {
    set fh [open $path r]
    fconfigure $fh -encoding utf-8
    try { return [json::json2dict [read $fh]] } finally { close $fh }
}

proc circuit_of {c} {
    tclmesh private circuit [dict get $c name] [dict get $c inputs] [dict get $c outputs] \
        [dict get $c nodes] [dict create output_nodes [dict get $c output_nodes]]
}

# A view without the circuit digest (the Lean model does not hash), as a
# canonical dict: names sorted, sequences kept.
proc canonical_view {view} {
    set inputs {}
    foreach name [lsort [dict keys [dict get $view inputs]]] {
        lappend inputs $name [dict get $view inputs $name]
    }
    set outputs {}
    foreach name [lsort [dict keys [dict get $view outputs]]] {
        lappend outputs $name [dict get $view outputs $name]
    }
    list inputs $inputs trace [dict get $view trace] outputs $outputs
}

foreach mode {transparent lazy sized} {
    tclmesh private profile define views-$mode [dict create \
        backend views-$mode semantics exact-integer allow_decrypt true]
}

proc check {circuits_path spec_path} {
    set spec [dict get [read_json $spec_path] views]
    set failures 0
    foreach vector [dict get [read_json $circuits_path] vectors] {
        set id [dict get $vector id]
        set circuit [circuit_of [dict get $vector circuit]]
        set inputs [dict get $vector inputs]
        set variants [dict get $vector variants]

        set recorded [canonical_view [lindex [tclmesh views structure [dict get \
            [tclmesh views run views-transparent $circuit $inputs] evaluator]] 0]]
        set declared [canonical_view [lindex [dict get \
            [tclmesh views declared $circuit $inputs] evaluator] 0]]
        set lean [canonical_view [dict get $spec $id]]
        foreach {name view} [list declared $declared lean $lean] {
            if {$view ne $recorded} {
                puts "$id: recorded view differs from the $name view"
                puts "  recorded: $recorded"
                puts "  $name: $view"
                incr failures
            }
        }
        set findings [tclmesh views paired views-transparent $circuit $inputs $variants]
        if {[llength $findings]} {
            puts "$id: oblivious backend leaks: $findings"
            incr failures
        }
        if {![llength [tclmesh views paired views-sized $circuit $inputs $variants]]} {
            puts "$id: calibration: plaintext-dependent sizes went undetected"
            incr failures
        }
    }
    if {$failures} {
        puts "$failures view failure(s)"
        exit 1
    }
    puts "views: recorded = declared (Tcl) = declared (Lean); paired runs agree; calibration detected"
}

# Certificates: for every circuit, the emitted certificate and its
# mutations (each cipher node demoted, each oblivious select forgotten), with
# the Tcl checker's verdict.
proc js {s} { json::write string $s }
proc jlist {items} { json::write array {*}[lmap x $items {js $x}] }
proc jdict {d} {
    set out {}
    dict for {k v} $d { lappend out $k [js $v] }
    json::write object {*}$out
}

proc circuit_json {c} {
    set types {}
    foreach part {inputs outputs} {
        set m {}
        dict for {k v} [dict get $c $part] { lappend m $k [jlist $v] }
        dict set types $part [json::write object {*}$m]
    }
    set nodes {}
    dict for {k v} [dict get $c nodes] { lappend nodes $k [jlist $v] }
    json::write object name [js [dict get $c name]] \
        inputs [dict get $types inputs] outputs [dict get $types outputs] \
        nodes [json::write object {*}$nodes] \
        output_nodes [jdict [dict get $c output_nodes]]
}

proc certificates {circuits_path} {
    set out {}
    foreach vector [dict get [read_json $circuits_path] vectors] {
        set id [dict get $vector id]
        set raw [dict get $vector circuit]
        set circuit [circuit_of $raw]
        set cert [tclmesh certificate emit $circuit]
        set variants [list $id $cert]
        dict for {node label} [dict get $cert labels] {
            if {$label eq "cipher"} {
                set mutated $cert
                dict set mutated labels $node public
                lappend variants "$id/demote/$node" $mutated
            }
        }
        if {[llength [dict get $cert oblivious]]} {
            set mutated $cert
            dict set mutated oblivious {}
            lappend variants "$id/not-oblivious" $mutated
        }
        foreach {vid c} $variants {
            set accepted [expr {[llength [tclmesh certificate check $circuit $c]] == 0}]
            lappend out [json::write object \
                id [js $vid] \
                circuit [circuit_json $raw] \
                certificate [json::write object \
                    labels [jdict [dict get $c labels]] \
                    oblivious [jlist [dict get $c oblivious]]] \
                tcl_accepted [expr {$accepted ? "true" : "false"}]]
        }
    }
    puts [json::write object vectors [json::write array {*}$out]]
}

proc check_certificates {certs_path spec_path} {
    set spec [dict get [read_json $spec_path] certificates]
    set failures 0
    set count 0
    foreach vector [dict get [read_json $certs_path] vectors] {
        incr count
        set id [dict get $vector id]
        set lean [dict get $spec $id]
        set tcl_accepted [string is true [dict get $vector tcl_accepted]]
        if {$tcl_accepted != [string is true [dict get $lean accepted]]} {
            puts "$id: Tcl checker says $tcl_accepted, Lean checker says [dict get $lean accepted]"
            incr failures
        }
        set emitted [expr {[string first / $id] < 0}]
        if {$emitted != $tcl_accepted} {
            puts "$id: expected [expr {$emitted ? "acceptance" : "rejection"}]"
            incr failures
        }
        if {$emitted} {
            set cert [dict get $vector certificate]
            set least [dict get $lean least]
            set mine {}
            foreach k [lsort [dict keys [dict get $cert labels]]] { lappend mine $k [dict get $cert labels $k] }
            set theirs {}
            foreach k [lsort [dict keys [dict get $least labels]]] { lappend theirs $k [dict get $least labels $k] }
            if {$mine ne $theirs || [lsort [dict get $cert oblivious]] ne [lsort [dict get $least oblivious]]} {
                puts "$id: emitted certificate differs from Lean's least certificate"
                incr failures
            }
        }
    }
    if {$failures} {
        puts "$failures certificate failure(s)"
        exit 1
    }
    puts "certificates: $count checked; Tcl = Lean verdicts; emitted = least; every mutation rejected"
}

lassign $argv command a b
switch -- $command {
    check { check $a $b }
    certificates { certificates $a }
    check-certificates { check_certificates $a $b }
    default {
        puts stderr "usage: views.tcl check CIRCUITS SPEC_VIEWS | certificates CIRCUITS | check-certificates CERTS SPEC"
        exit 2
    }
}
