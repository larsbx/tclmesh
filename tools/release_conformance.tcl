#!/usr/bin/env tclsh
# Replays release traces through the governed Tcl release API and compares
# the observations with the proved Lean machine (TclMesh.Release.Machine).
#
#   tclsh tools/release_conformance.tcl run TRACES          print {"release": ...}
#   tclsh tools/release_conformance.tcl check TRACES SPEC   fail on any difference
#
# Every trace runs against a fresh file store in child processes. A `crash`
# event, and `combine I crash` (the backend exits after the attempt is
# committed), end the child; the next child reloads the durable store and
# resumes, so crashes are real process loss, not simulated rollbacks.
package require Tcl 8.6
package require json
package require json::write
json::write indented 0
json::write aligned 0
set root [file dirname [file dirname [file normalize [info script]]]]

proc read_json {path} {
    set fh [open $path r]
    try { return [json::json2dict [read $fh]] } finally { close $fh }
}

proc trace_of {path id} {
    foreach t [dict get [read_json $path] traces] {
        if {[dict get $t id] eq $id} {return $t}
    }
    error "unknown trace $id"
}

# Tcl error codes mapped to the Lean `Err.name` classes.
proc classify {code} {
    switch -glob -- $code {
        {TCLMESH RELEASE NOT_FOUND *} {return unknown}
        {TCLMESH RELEASE POLICY MANIFEST_CHANGED} {return stale}
        {TCLMESH RELEASE POLICY LANGUAGE_INACTIVE} {return revoked}
        {TCLMESH RELEASE POLICY ACTOR_NOT_ALLOWED} {return unauthorized}
        {TCLMESH RELEASE INVALID_STATE *} -
        {TCLMESH RELEASE RECOVERY INVALID_STATE *} {return state}
        {TCLMESH RELEASE DUPLICATE_CONTRIBUTION *} {return duplicate}
        {TCLMESH RELEASE RECOVERY IDEMPOTENCY_REQUIRED *} {return idempotency}
        {TCLMESH RELEASE COMBINE_FAILED *} {return backend-failed}
        default {return "unmapped:$code"}
    }
}

# ---- child: executes events [start, end) of one trace -----------------------

proc conformance_backend {op args} {
    if {$op eq "combine-authorization-quorum"} {
        switch -- $::outcome {
            fail {error "backend failure (conformance)"}
            crash {puts "crashed"; flush stdout; exit 0}
        }
    }
    return [::tclmesh::private::_plaintext_backend $op {*}$args]
}

proc manifest_for {trace version} {
    set circuit [tclmesh private circuit aggregate {} [dict create total {cipher int}] \
        [dict create total {constant 42}] \
        [dict create output_nodes [dict create total total] \
            profile conformance-profile release_policy report]]
    set manifest [tclmesh manifest new conformance $version]
    dict set manifest circuits aggregate $circuit
    dict set manifest ceremonies report [dict create kind authorization-quorum \
        circuit aggregate output total purpose conformance profile conformance-profile \
        quorum [dict get $trace quorum] holders [dict get $trace holders] \
        requesters {operator} combiners {operator} recoverers {operator} \
        request_capability release:request contribute_capability release:share \
        combine_capability release:combine recover_capability release:recover \
        context [dict create tenant conformance]]
    return $manifest
}

proc activate {trace version} {
    set installed [tclmesh manifest install [manifest_for $trace $version]]
    tclmesh manifest activate conformance $version [dict get $installed manifest_hash]
}

proc language_of {holder} {
    foreach id [tclmesh language list] {
        if {[dict get [tclmesh language describe $id] holder] eq $holder} {return $id}
    }
    error "no language for $holder"
}

proc release_id {index} {return "release:[expr {$index + 1}]"}

proc observe {index result} {
    if {$index eq "" || [catch {tclmesh release get [release_id $index]} r]} {
        return [list $result null 0]
    }
    return [list $result [dict get $r status] [dict get $r attempts]]
}

proc attempt {index script} {
    if {[catch {uplevel 1 $script} message options]} {
        return [observe $index [classify [dict get $options -errorcode]]]
    }
    return [observe $index ok]
}

proc child {traces id path start} {
    global outcome
    set outcome ok
    set trace [trace_of $traces $id]
    set caps {authorization-quorum persistent-handles}
    if {[dict get $trace idempotent]} {lappend caps idempotent-release}
    tclmesh private backend register conformance-backend conformance_backend $caps
    tclmesh private profile define conformance-profile [dict create \
        backend conformance-backend semantics exact-integer allow_decrypt false]
    set store [tclmesh store create file $path]
    tclmesh manifest use-store $store
    tclmesh language use-store $store
    tclmesh release use-store $store
    if {$start == 0} {
        activate $trace 1
        foreach holder [list operator {*}[dict get $trace holders] z] {
            set commands [expr {$holder eq "operator" ?
                {release:request release:combine release:recover} : {release:share}}]
            tclmesh language instantiate conformance-$holder $holder {release:report} \
                $commands [dict create tenant conformance]
        }
    }
    set op [language_of operator]
    set context [dict create tenant conformance]
    set events [dict get $trace events]
    if {[info exists ::resume]} {
        # The previous process was lost inside `combine K I`: report that step
        # from the reloaded durable state, then continue after it.
        lassign $::resume k i
        puts "step $k [observe $i ok]"
        set start [expr {$k + 1}]
    }
    for {set k $start} {$k < [llength $events]} {incr k} {
        set event [lassign [lindex $events $k] name]
        lassign $event i arg
        switch -- $name {
            create {
                set handle [dict get [tclmesh private evaluate-bound conformance-profile \
                    conformance aggregate {}] total]
                if {[catch {tclmesh release request-authorized $op $handle operator $context} r options]} {
                    set obs [list [classify [dict get $options -errorcode]] null 0]
                } else {
                    set obs [observe [expr {[string range [dict get $r id] 8 end] - 1}] ok]
                }
            }
            contribute {
                set obs [attempt $i {tclmesh release contribute-authorized \
                    [language_of $arg] [release_id $i] $arg share-$arg}]
            }
            revoke {tclmesh language revoke [language_of $i]; set obs [list ok null 0]}
            rotate {
                set version [expr {[dict get [tclmesh manifest active conformance] version] + 1}]
                activate $trace $version
                set obs [list ok null 0]
            }
            combine {
                set outcome $arg
                if {$arg eq "crash"} {puts "pending $k $i"; flush stdout}
                set obs [attempt $i {tclmesh release combine-authorized $op [release_id $i] operator}]
                set outcome ok
            }
            crash {puts "step $k [list ok null 0]"; puts "crashed"; flush stdout; exit 0}
            recover {
                set obs [attempt $i {tclmesh release recover-authorized $op [release_id $i] \
                    operator $arg recovered}]
            }
            reject - expire {
                set obs [attempt $i [list tclmesh release $name-authorized $op [release_id $i] operator]]
            }
            default {error "unknown event $name"}
        }
        puts "step $k $obs"
    }
    puts done
}

# ---- parent ------------------------------------------------------------------

proc run_trace {traces id} {
    set tmp [expr {[info exists ::env(TMPDIR)] ? $::env(TMPDIR) : "/tmp"}]
    set path [file join $tmp release-conformance-[pid]-$id.store]
    file delete -force $path
    set obs {}
    set start 0
    set pending {}
    try {
        while 1 {
            set out [exec [info nameofexecutable] [info script] child $traces $id $path $start \
                {*}$pending 2>@1]
            set pending {}
            set finished 0
            foreach line [split $out \n] {
                switch -- [lindex $line 0] {
                    step {
                        lappend obs [lrange $line 2 end]
                        set start [expr {[lindex $line 1] + 1}]
                        if {[lindex $pending 0] eq [lindex $line 1]} {set pending {}}
                    }
                    pending {set pending [lrange $line 1 2]}
                    done {set finished 1}
                    crashed {}
                    default {if {$line ne ""} {error "unexpected child output: $line"}}
                }
            }
            if {$finished} {break}
        }
    } finally {file delete -force $path}
    return $obs
}

proc obs_json {o} {
    lassign $o result status attempts
    json::write array [json::write string $result] \
        [expr {$status eq "null" ? "null" : [json::write string $status]}] $attempts
}

proc run_all {traces} {
    set out {}
    foreach t [dict get [read_json $traces] traces] {
        set id [dict get $t id]
        dict set out $id [run_trace $traces $id]
    }
    return $out
}

proc emit {results} {
    set fields {}
    dict for {id obs} $results {
        lappend fields $id [json::write array {*}[lmap o $obs {obs_json $o}]]
    }
    return [json::write object release [json::write object {*}$fields]]
}

proc check {traces specfile} {
    set spec [dict get [read_json $specfile] release]
    set mismatches 0
    dict for {id obs} [run_all $traces] {
        set want [dict get $spec $id]
        if {[llength $want] != [llength $obs]} {
            puts "$id: [llength $obs] Tcl steps, [llength $want] Lean steps"
            incr mismatches
            continue
        }
        set k 0
        foreach got $obs w $want {
            if {$got ne $w} {puts "$id step $k: Tcl {$got} Lean {$w}"; incr mismatches}
            incr k
        }
    }
    if {$mismatches} {puts "release conformance: $mismatches mismatches"; exit 1}
    puts "release conformance: [dict size $spec] traces, Tcl = Lean on every step"
}

set args [lassign $argv mode]
switch -- $mode {
    run {puts [emit [run_all {*}$args]]}
    check {check {*}$args}
    child {
        lappend auto_path $root
        package require tclmesh 0.2.0
        lassign $args traces id path start pk pi
        if {$pk ne ""} {set ::resume [list $pk $pi]}
        child $traces $id $path $start
    }
    default {puts stderr "usage: release_conformance.tcl run TRACES | check TRACES SPEC"; exit 2}
}
