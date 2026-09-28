namespace eval ::tclmesh::action {
    namespace export run describe bind_manifest
    namespace ensemble create
}

proc ::tclmesh::action::_freeze_command {command} {
    if {$command eq ""} {
        return {}
    }

    set name [lindex $command 0]
    if {$name eq "apply"} {
        return $command
    }

    set resolved [uplevel #0 [::list namespace which -command $name]]
    if {$resolved eq "" || [llength [info procs $resolved]] == 0} {
        return -code error \
            -errorcode {TCLMESH ACTION CALLBACK NOT_FREEZABLE} \
            "action callback '$name' must be a Tcl procedure or an apply lambda"
    }

    set arguments {}
    foreach argument [info args $resolved] {
        if {[info default $resolved $argument default]} {
            lappend arguments [::list $argument $default]
        } else {
            lappend arguments $argument
        }
    }

    set lambda [::list $arguments [info body $resolved] [namespace qualifiers $resolved]]
    return [concat [::list apply $lambda] [lrange $command 1 end]]
}

proc ::tclmesh::action::bind_manifest {manifest} {
    dict for {action_id descriptor} [dict get $manifest actions] {
        foreach field {authorize deontic} {
            if {[dict exists $descriptor $field]} {
                dict set descriptor $field [_freeze_command [dict get $descriptor $field]]
            }
        }

        foreach field {validations changes effects} {
            if {![dict exists $descriptor $field]} {
                continue
            }

            set frozen {}
            foreach command [dict get $descriptor $field] {
                lappend frozen [_freeze_command $command]
            }
            dict set descriptor $field $frozen
        }

        dict set manifest actions $action_id $descriptor
    }

    return $manifest
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

proc ::tclmesh::action::_require_language {language_id action_id descriptor} {
    set language [::tclmesh::language describe $language_id]

    if {[dict get $language status] ne "active"} {
        return -code error \
            -errorcode {TCLMESH ACTION LANGUAGE INACTIVE} \
            "language '$language_id' is not active"
    }

    if {$action_id ni [dict get $language commands]} {
        return -code error \
            -errorcode [::list TCLMESH ACTION CAPABILITY COMMAND_NOT_GRANTED $action_id] \
            "language '$language_id' is not granted action '$action_id'"
    }

    set capability $action_id
    if {[dict exists $descriptor capability]} {
        set capability [dict get $descriptor capability]
    }

    if {$capability ni [dict get $language capabilities]} {
        return -code error \
            -errorcode [::list TCLMESH ACTION CAPABILITY NOT_GRANTED $capability] \
            "language '$language_id' lacks capability '$capability'"
    }

    return $language
}

proc ::tclmesh::action::_execution_decision {judgment} {
    if {[dict get $judgment status] eq "conflicted"} {
        return -code error \
            -errorcode {TCLMESH ACTION DEONTIC CONFLICT} \
            "conflicted deontic judgment does not permit execution"
    }

    if {[dict get $judgment status] ne "determinate" ||
        [dict get $judgment semantics admissibility] eq "omit-required"} {
        return -code error \
            -errorcode {TCLMESH ACTION DEONTIC FORBIDDEN} \
            "deontic judgment does not permit execution"
    }

    return [dict create decision execute]
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
    set execution [_execution_decision $judgment]

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

    return [dict create         status ok         action $action_id         application_id [dict get $pin application_id]         manifest_version [dict get $pin version]         manifest_hash [dict get $pin manifest_hash]         authorization $authorization         deontic $judgment         execution $execution         result $persisted         effects [dict create proposed $effects executed {}]]
}

proc ::tclmesh::action::describe {application_id action_id {version {}}} {
    set manifest [::tclmesh::manifest get $application_id $version]

    if {![dict exists $manifest actions $action_id]} {
        return -code error             -errorcode [::list TCLMESH ACTION NOT_FOUND $application_id $action_id]             "action '$action_id' is not defined by application '$application_id'"
    }

    return [dict get $manifest actions $action_id]
}

proc ::tclmesh::action::run {language_id application_id action_id adapter request} {
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
    _require_language $language_id $action_id $descriptor
    set callback [::list         ::tclmesh::action::_guarded_execute         $action_id         $descriptor         $adapter         $request         $pin]

    return [{*}$adapter transact $callback]
}
