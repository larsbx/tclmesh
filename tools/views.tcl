#!/usr/bin/env tclsh
# Per-party view conformance (docs/testing.md).
#
#   tclsh tools/views.tcl check CIRCUITS SPEC_VIEWS
#
# For every circuit vector: the evaluator's view recorded by the oblivious
# backend, the view the Tcl harness declares, and the view the Lean model
# declares (`spec-eval --views`) must coincide; and every variant (other
# ciphertext inputs, same public inputs) must give the same recorded view.
# The calibration backends (`views-lazy`, `views-sized`) must be caught on
# every vector where they can leak.

package require Tcl 8.6
package require json

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

        set recorded [canonical_view [lindex [dict get \
            [tclmesh views run views-transparent $circuit $inputs] evaluator] 0]]
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

lassign $argv command a b
switch -- $command {
    check { check $a $b }
    default { puts stderr "usage: views.tcl check CIRCUITS SPEC_VIEWS"; exit 2 }
}
