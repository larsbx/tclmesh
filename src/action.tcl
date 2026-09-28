namespace eval ::tclmesh::action {
    namespace export run describe
    namespace ensemble create
}

proc ::tclmesh::action::_invoke {command args} {
    if {$command eq ""} {
        return {}
    }

    return [{*}$command {*}$args]
}

proc ::tclmesh::action::_require_decision {decision} {
    if {![dict exists $decision decision]} {
        return -code error             -errorcode {TCLMESH ACTION AUTHORIZATION INVALID_RESULT}             "authorization callback must return a decision descriptor"
    }

    if {[dict get $decision decision] ne "permit"} {
        return -code error             -errorcode {TCLMESH ACTION AUTHORIZATION DENIED}             "action authorization did not permit execution"
    }

    return $decision
}

proc ::tclmesh::action::_validate_result {result} {
    if {$result eq ""} {
        return
    }

    if {[string is boolean -strict $result]} {
        if {!$result} {
            return -code error                 -errorcode {TCLMESH ACTION VALIDATION FAILED}                 "action validation failed"
        }
        return
    }

    if {![catch {dict exists $result valid} is_dict] && $is_dict} {
        if {![dict get $result valid]} {
            return -code error                 -errorcode {TCLMESH ACTION VALIDATION FAILED}                 "action validation failed"
        }
        return
    }

    return -code error         -errorcode {TCLMESH ACTION VALIDATION INVALID_RESULT}         "validation callback returned an unsupported result"
}

proc ::tclmesh::action::_guarded_execute {
    action_id
    descriptor
    adapter
    request
    pin
} {
    set state [{*}$adapter load $request]

    set authorization [dict create decision permit]
    if {[dict exists $descriptor authorize]} {
        set authorization [_require_decision             [_invoke [dict get $descriptor authorize] $state $request]]
    }

    set verdicts {M}
    if {[dict exists $descriptor deontic]} {
        set verdicts [_invoke [dict get $descriptor deontic] $state $request]
    }
    set judgment [::tclmesh::deontic resolve $verdicts]

    if {[dict exists $descriptor validations]} {
        foreach validator [dict get $descriptor validations] {
            _validate_result [_invoke $validator $state $request]
        }
    }

    if {[dict exists $descriptor changes]} {
        foreach change [dict get $descriptor changes] {
            set state [_invoke $change $state $request]
        }
    }

    set effects {}
    if {[dict exists $descriptor effects]} {
        foreach producer [dict get $descriptor effects] {
            foreach effect [_invoke $producer $state $request] {
                lappend effects $effect
            }
        }
    }

    set persisted [{*}$adapter persist $request $state]

    return [dict create         status ok         action $action_id         application_id [dict get $pin application_id]         manifest_version [dict get $pin version]         manifest_hash [dict get $pin manifest_hash]         authorization $authorization         deontic $judgment         result $persisted         effects [dict create proposed $effects executed {}]]
}

proc ::tclmesh::action::describe {application_id action_id {version {}}} {
    set manifest [::tclmesh::manifest get $application_id $version]

    if {![dict exists $manifest actions $action_id]} {
        return -code error             -errorcode [::list TCLMESH ACTION NOT_FOUND $application_id $action_id]             "action '$action_id' is not defined by application '$application_id'"
    }

    return [dict get $manifest actions $action_id]
}

proc ::tclmesh::action::run {application_id action_id adapter request} {
    set pin [::tclmesh::manifest active $application_id]
    set version [dict get $pin version]
    set manifest [::tclmesh::manifest get $application_id $version]

    if {![dict exists $manifest actions $action_id]} {
        return -code error             -errorcode [::list TCLMESH ACTION NOT_FOUND $application_id $action_id]             "action '$action_id' is not defined by application '$application_id'"
    }

    if {[dict exists $request expected_manifest_hash] &&
        ![string equal -nocase             [dict get $request expected_manifest_hash]             [dict get $pin manifest_hash]]} {
        return -code error             -errorcode [::list TCLMESH ACTION MANIFEST_MISMATCH $application_id $action_id]             "request manifest hash does not match the active manifest"
    }

    set descriptor [dict get $manifest actions $action_id]
    set callback [::list         ::tclmesh::action::_guarded_execute         $action_id         $descriptor         $adapter         $request         $pin]

    return [{*}$adapter transact $callback]
}
