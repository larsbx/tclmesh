# Tier A differential conformance: the Tcl reference evaluator as oracle.
#
#   tclsh tools/conformance.tcl run VECTORS          outcomes JSON on stdout
#   tclsh tools/conformance.tcl generate SEED COUNT ?NOISE?
#                                     random vectors on stdout; NOISE is the
#                                     percentage of malformed choices (default 3)
#   tclsh tools/conformance.tcl check                committed outcomes current?
#   tclsh tools/conformance.tcl update               rewrite committed outcomes

set here [file dirname [file normalize [info script]]]
set root [file dirname $here]
lappend auto_path $root
package require tclmesh
package require json
package require json::write

json::write indented 0
json::write aligned 0

namespace eval ::conformance {
    variable root $::root
    variable seed 0
    variable noise 3
}

# ------------------------------------------------------------------ outcomes

proc ::conformance::pairs {dict} {
    set out {}
    dict for {k v} $dict {
        lappend out [json::write array [json::write string $k] [json::write string $v]]
    }
    return [json::write array {*}$out]
}

proc ::conformance::outcome {vector} {
    set descriptor [dict get $vector descriptor]
    try {
        set e [::tclmesh::action::evaluate [dict get $vector action_id] \
            $descriptor [dict get $vector state] [dict get $vector request]]
    } trap {} {message options} {
        set code [lmap word [dict get $options -errorcode] {json::write string $word}]
        return [json::write object status [json::write string error] \
            code [json::write array {*}$code]]
    }

    set changes {}
    if {[dict exists $descriptor changes]} {
        foreach change [dict get $descriptor changes] {
            set field [lindex $change 1]
            if {![dict exists $changes $field]} {
                dict set changes $field [dict get $e state $field]
            }
        }
    }

    return [json::write object \
        status [json::write string ok] \
        verdict [json::write string [dict get $e deontic verdict]] \
        changes [pairs $changes] \
        effects [json::write array {*}[lmap effect [dict get $e effects] {pairs $effect}]]]
}

proc ::conformance::read_json {path} {
    set fh [open $path r]
    fconfigure $fh -encoding utf-8
    try { return [json::json2dict [read $fh]] } finally { close $fh }
}

# One outcome per line keeps recorded outcomes reviewable as diffs.
proc ::conformance::run {path} {
    set lines {}
    foreach vector [dict get [read_json $path] vectors] {
        lappend lines "    [json::write string [dict get $vector id]]: [outcome $vector]"
    }
    return "\{\n  \"tcl_patchlevel\": [json::write string [info patchlevel]],\n  \"outcomes\": \{\n[join $lines ",\n"]\n  \}\n\}\n"
}

# ----------------------------------------------------------------- generator

# 64-bit LCG (Knuth MMIX): reproducible independently of Tcl's rand().
proc ::conformance::next {n} {
    variable seed
    set seed [expr {($seed * 6364136223846793005 + 1442695040888963407) % 18446744073709551616}]
    return [expr {($seed >> 33) % $n}]
}

proc ::conformance::pick {items} { lindex $items [next [llength $items]] }
proc ::conformance::chance {percent} { expr {[next 100] < $percent} }
proc ::conformance::malformed {} { chance $::conformance::noise }

proc ::conformance::js {s} { json::write string $s }
proc ::conformance::ja {args} { json::write array {*}$args }

variable ::conformance::scalars {
    "" 0 -0 1 2 3 10 79 80 100 007 08 0x10 { 1} 1e3 1E3 1e400 -1e400 1e-400
    0.1 0.10000000000000000001 9007199254740993 9007199254740992.0 2.5 -2.5
    123456789012345678901234567890 Inf NaN abc north east {north east}
    {{a b} c} a\{b {"q"} {x y} ok {review ok} M type
    1e1001 1e-1000 1e0001000 0.10 1E-2 -0.0
    a\\b \u00e9 a\u00a0b a\u3000b {a\tb} {a\vb} \{a\} \{\} #x
}

proc ::conformance::scalar {} { js [pick $::conformance::scalars] }

proc ::conformance::list_value {} {
    ja {*}[lmap _ [lrepeat [expr {[next 3] + 1}] _] {scalar}]
}

proc ::conformance::path {kind} {
    set paths [expr {$kind eq "field"
        ? {a b n m s {nested x} {nested z w} {nested y} items missing {a x} {nested missing}}
        : {actor_id attempts region note {nested x} {nested z w} missing}}]
    ja [js $kind] {*}[lmap key [pick $paths] {js $key}]
}

proc ::conformance::value_expr {} {
    if {[malformed]} {
        return [pick [list [ja] [js "literal x"] [ja [js literal]] [ja [js field]] [ja [js bogus] [js x]]]]
    }
    switch [next 10] {
        0 { return [ja [js literal] [list_value]] }
        1 - 2 - 3 { return [ja [js literal] [scalar]] }
        4 - 5 - 6 { return [path field] }
        default { return [path request] }
    }
}

proc ::conformance::predicate {depth} {
    if {[malformed]} { return [pick [list [ja] [ja [js nope]] [ja [js eq] [value_expr]]]] }
    if {$depth > 0 && [chance 35]} {
        set op [pick {and or not}]
        set n [expr {$op eq "not" ? 1 : [next 3] + 1}]
        return [ja [js $op] {*}[lmap _ [lrepeat $n _] {predicate [expr {$depth - 1}]}]]
    }
    set op [pick {true false eq neq lt lte gt gte lt gte in in contains}]
    if {$op in {true false}} { return [ja [js $op]] }
    return [ja [js $op] [value_expr] [value_expr]]
}

proc ::conformance::state {} {
    set fields {}
    foreach key {a b n m s} {
        if {[chance 85]} { lappend fields $key [scalar] }
    }
    if {[chance 10]} { dict set fields a [json::write object x [scalar]] }
    lappend fields nested [json::write object x [scalar] y [list_value] z [json::write object w [scalar]]]
    lappend fields items [list_value]
    return [json::write object {*}$fields]
}

proc ::conformance::request {} {
    set fields [list actor_id [js user:1]]
    foreach key {attempts region note} {
        if {[chance 85]} { lappend fields $key [scalar] }
    }
    lappend fields nested [json::write object x [scalar] z [json::write object w [scalar]]]
    return [json::write object {*}$fields]
}

proc ::conformance::descriptor {} {
    set fields {}
    if {[malformed]} {
        lappend fields authorize [pick [list [ja] [ja [js permit] [js x]] [ja [js permit-if]]]]
    } else {
        switch [next 6] {
            0 {}
            1 { lappend fields authorize [ja [js permit]] }
            2 { lappend fields authorize [ja [js deny]] }
            default { lappend fields authorize [ja [js permit-if] [predicate 2]] }
        }
    }
    if {[chance 70]} {
        set verdicts [lmap _ [lrepeat [expr {[chance 85] ? 1 : 2}] _] {
            expr {[malformed] ? "X" : [pick {W N M M M K H}]}
        }]
        if {[malformed]} { set verdicts {} }
        lappend fields deontic [ja {*}[lmap v $verdicts {js $v}]]
    }
    set validations [lmap _ [lrepeat [next 3] _] {
        expr {[malformed] ? [ja [js check] [predicate 1]] : [ja [js assert] [predicate 2]]}
    }]
    if {[llength $validations]} { lappend fields validations [ja {*}$validations] }
    set changes [lmap _ [lrepeat [next 4] _] {
        ja [js set] [js [expr {[malformed] ? {} : [pick {a b new s s}]}]] [value_expr]
    }]
    if {[llength $changes]} { lappend fields changes [ja {*}$changes] }
    set effects [lmap _ [lrepeat [next 3] _] {
        set words [list [js emit] [js [expr {[malformed] ? {} : [pick {notify audit audit}]}]]]
        foreach _ [lrepeat [next 3] _] {
            lappend words [js [expr {[malformed] ? {} : [pick {k k2 type}]}]] [value_expr]
        }
        if {[malformed]} { lappend words [js dangling] }
        ja {*}$words
    }]
    if {[llength $effects]} { lappend fields effects [ja {*}$effects] }
    return [json::write object {*}$fields]
}

proc ::conformance::generate {seed count {noise 3}} {
    set ::conformance::seed $seed
    set ::conformance::noise $noise
    set vectors {}
    for {set i 1} {$i <= $count} {incr i} {
        lappend vectors [json::write object \
            id [js "gen-$seed-$i"] \
            action_id [js Generated::act] \
            descriptor [descriptor] \
            state [state] \
            request [request]]
    }
    return "\{\"vectors\": \[\n[join $vectors ",\n"]\n\]\}\n"
}

# ---------------------------------------------------------------------- main

proc ::conformance::committed {} {
    variable root
    return [list [file join $root conformance vectors.json] \
        [file join $root conformance expected.json]]
}

proc ::conformance::slurp {path} {
    set fh [open $path r]
    fconfigure $fh -encoding utf-8
    try { return [read $fh] } finally { close $fh }
}

fconfigure stdout -encoding utf-8
switch -- [lindex $argv 0] {
    run      { puts -nonewline [::conformance::run [lindex $argv 1]] }
    generate { puts -nonewline [::conformance::generate {*}[lrange $argv 1 3]] }
    check {
        lassign [::conformance::committed] vectors expected
        # The recording patchlevel is provenance, not part of the outcomes.
        set strip {regsub {\n  "tcl_patchlevel": [^\n]*} $text {}}
        set actual [apply [list text $strip] [::conformance::run $vectors]]
        set recorded [apply [list text $strip] [::conformance::slurp $expected]]
        if {$actual ne $recorded} {
            puts stderr "conformance/expected.json is stale: run 'tclsh tools/conformance.tcl update'"
            exit 1
        }
        puts "conformance outcomes current"
    }
    update {
        lassign [::conformance::committed] vectors expected
        set fh [open $expected w]
        fconfigure $fh -encoding utf-8
        puts -nonewline $fh [::conformance::run $vectors]
        close $fh
    }
    default {
        puts stderr "usage: tclsh tools/conformance.tcl run VECTORS | generate SEED COUNT ?NOISE? | check | update"
        exit 2
    }
}
