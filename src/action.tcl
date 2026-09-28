namespace eval ::tclmesh::action {
    namespace export run describe bind_manifest
    namespace ensemble create
}

proc ::tclmesh::action::_eval_value {value state request} {
    if {[llength $value] == 0} {
        return {}
    }

    set op [lindex $value 0]
    switch -- $op {
        literal {
            if {[llength $value] != 2} {
                return -code error -errorcode {TCLMESH ACTION VALUE INVALID}                     "literal value expression requires exactly one argument"
            }
            return [lindex $value 1]
        }
        field {
            set path [lrange $value 1 end]
            if {[llength $path] == 0 || ![dict exists $state {*}$path]} {
                return -code error -errorcode {TCLMESH ACTION VALUE MISSING_FIELD}                     "state field path does not exist"
            }
            return [dict get $state {*}$path]
        }
        request {
            set path [lrange $value 1 end]
            if {[llength $path] == 0 || ![dict exists $request {*}$path]} {
                return -code error -errorcode {TCLMESH ACTION VALUE MISSING_REQUEST}                     "request field path does not exist"
            }
            return [dict get $request {*}$path]
        }
        default {
            return -code error                 -errorcode [::list TCLMESH ACTION VALUE UNKNOWN $op]                 "unknown canonical value operation '$op'"
        }
    }
}

proc ::tclmesh::action::_eval_predicate {expr state request} {
    if {[llength $expr] == 0} {
        return 0
    }

    set op [lindex $expr 0]
    switch -- $op {
        true { return 1 }
        false { return 0 }
        eq {
            if {[llength $expr] != 3} {
                return -code error -errorcode {TCLMESH ACTION PREDICATE INVALID}                     "eq predicate requires two value expressions"
            }
            return [expr {
                [_eval_value [lindex $expr 1] $state $request] eq
                [_eval_value [lindex $expr 2] $state $request]
            }]
        }
        neq {
            if {[llength $expr] != 3} {
                return -code error -errorcode {TCLMESH ACTION PREDICATE INVALID}                     "neq predicate requires two value expressions"
            }
            return [expr {
                [_eval_value [lindex $expr 1] $state $request] ne
                [_eval_value [lindex $expr 2] $state $request]
            }]
        }
        and {
            foreach child [lrange $expr 1 end] {
                if {![_eval_predicate $child $state $request]} {
                    return 0
                }
            }
            return 1
        }
        or {
            foreach child [lrange $expr 1 end] {
                if {[_eval_predicate $child $state $request]} {
                    return 1
                }
            }
            return 0
        }
        not {
            if {[llength $expr] != 2} {
                return -code error -errorcode {TCLMESH ACTION PREDICATE INVALID}                     "not predicate requires one child predicate"
            }
            return [expr {![_eval_predicate [lindex $expr 1] $state $request]}]
        }
        default {
            return -code error                 -errorcode [::list TCLMESH ACTION PREDICATE UNKNOWN $op]                 "unknown canonical predicate operation '$op'"
        }
    }
}

proc ::tclmesh::action::_authorization {spec state request} {
    if {$spec eq ""} {
        return [dict create decision permit]
    }

    set op [lindex $spec 0]
    switch -- $op {
        permit {
            if {[llength $spec] != 1} {
                return -code error -errorcode {TCLMESH ACTION AUTHORIZATION INVALID_SPEC}                     "permit authorization takes no arguments"
            }
            return [dict create decision permit]
        }
        deny {
            if {[llength $spec] != 1} {
                return -code error -errorcode {TCLMESH ACTION AUTHORIZATION INVALID_SPEC}                     "deny authorization takes no arguments"
            }
            return [dict create decision deny]
        }
        permit-if {
            if {[llength $spec] != 2} {
                return -code error -errorcode {TCLMESH ACTION AUTHORIZATION INVALID_SPEC}                     "permit-if authorization requires one predicate"
            }
            if {[_eval_predicate [lindex $spec 1] $state $request]} {
                return [dict create decision permit]
            }
            return [dict create decision deny]
        }
        default {
            return -code error                 -errorcode [::list TCLMESH ACTION AUTHORIZATION UNKNOWN $op]                 "unknown canonical authorization operation '$op'"
        }
    }
}

proc ::tclmesh::action::_validate_descriptor {action_id descriptor} {
    if {[dict exists $descriptor authorize]} {
        set op [lindex [dict get $descriptor authorize] 0]
        if {$op ni {permit deny permit-if}} {
            return -code error                 -errorcode [::list TCLMESH ACTION NON_CANONICAL $action_id authorize]                 "action '$action_id' authorize field must use canonical operations"
        }
    }

    if {[dict exists $descriptor deontic]} {
        foreach verdict [dict get $descriptor deontic] {
            ::tclmesh::deontic semantics $verdict
        }
    }

    foreach validation [expr {[dict exists $descriptor validations] ? [dict get $descriptor validations] : {}}] {
        if {[lindex $validation 0] ne "assert"} {
            return -code error                 -errorcode [::list TCLMESH ACTION NON_CANONICAL $action_id validations]                 "action '$action_id' validation must use canonical assert nodes"
        }
    }

    foreach change [expr {[dict exists $descriptor changes] ? [dict get $descriptor changes] : {}}] {
        if {[lindex $change 0] ne "set" || [llength $change] != 3} {
            return -code error                 -errorcode [::list TCLMESH ACTION NON_CANONICAL $action_id changes]                 "action '$action_id' change must use canonical set nodes"
        }
    }

    foreach effect [expr {[dict exists $descriptor effects] ? [dict get $descriptor effects] : {}}] {
        if {[lindex $effect 0] ne "emit" || [llength $effect] < 2} {
            return -code error                 -errorcode [::list TCLMESH ACTION NON_CANONICAL $action_id effects]                 "action '$action_id' effect must use canonical emit nodes"
        }
    }

    return $descriptor
}

proc ::tclmesh::action::bind_manifest {manifest} {
    dict for {action_id descriptor} [dict get $manifest actions] {
        _validate_descriptor $action_id $descriptor
    }
    return $manifest
}

proc ::tclmesh::action::_require_language {language_id actor_id action_id descriptor} {
    set language [::tclmesh::language describe $language_id]

    if {[dict get $language status] ne "active"} {
        return -code error             -errorcode {TCLMESH ACTION LANGUAGE INACTIVE}             "language '$language_id' is not active"
    }

    if {[dict get $language holder] ne $actor_id} {
        return -code error             -errorcode [::list TCLMESH ACTION LANGUAGE HOLDER_MISMATCH $language_id]             "language '$language_id' is not held by actor '$actor_id'"
    }

    if {$action_id ni [dict get $language commands]} {
        return -code error             -errorcode [::list TCLMESH ACTION CAPABILITY COMMAND_NOT_GRANTED $action_id]             "language '$language_id' is not granted action '$action_id'"
    }

    set capability $action_id
    if {[dict exists $descriptor capability]} {
        set capability [dict get $descriptor capability]
    }

    if {$capability ni [dict get $language capabilities]} {
        return -code error             -errorcode [::list TCLMESH ACTION CAPABILITY NOT_GRANTED $capability]             "language '$language_id' lacks capability '$capability'"
    }

    return $language
}

proc ::tclmesh::action::_execution_decision {judgment} {
    if {[dict get $judgment status] eq "conflicted"} {
        return -code error             -errorcode {TCLMESH ACTION DEONTIC CONFLICT}             "conflicted deontic judgment does not permit execution"
    }

    if {[dict get $judgment status] ne "determinate" ||
        [dict get $judgment semantics admissibility] eq "omit-required"} {
        return -code error             -errorcode {TCLMESH ACTION DEONTIC FORBIDDEN}             "deontic judgment does not permit execution"
    }

    return [dict create decision execute]
}

proc ::tclmesh::action::_apply_validation {validation state request} {
    if {[llength $validation] != 2 ||
        [lindex $validation 0] ne "assert"} {
        return -code error -errorcode {TCLMESH ACTION VALIDATION INVALID_SPEC}             "validation must be {assert predicate}"
    }

    if {![_eval_predicate [lindex $validation 1] $state $request]} {
        return -code error             -errorcode {TCLMESH ACTION VALIDATION FAILED}             "action validation failed"
    }
}

proc ::tclmesh::action::_apply_change {change state request} {
    lassign $change op field value
    if {$op ne "set" || $field eq ""} {
        return -code error -errorcode {TCLMESH ACTION CHANGE INVALID_SPEC}             "change must be {set field value-expression}"
    }

    dict set state $field [_eval_value $value $state $request]
    return $state
}

proc ::tclmesh::action::_build_effect {spec state request} {
    if {[lindex $spec 0] ne "emit" || [llength $spec] < 2} {
        return -code error -errorcode {TCLMESH ACTION EFFECT INVALID_SPEC}             "effect must begin with emit and an effect type"
    }

    set effect [dict create type [lindex $spec 1]]
    set rest [lrange $spec 2 end]

    if {[llength $rest] % 2 != 0} {
        return -code error -errorcode {TCLMESH ACTION EFFECT INVALID_SPEC}             "effect fields must be name/value-expression pairs"
    }

    foreach {field value} $rest {
        dict set effect $field [_eval_value $value $state $request]
    }

    return $effect
}

proc ::tclmesh::action::_guarded_execute {
    action_id
    descriptor
    adapter
    request
    pin
} {
    set state [{*}$adapter load $request]

    set authorization [_authorization         [expr {[dict exists $descriptor authorize] ? [dict get $descriptor authorize] : {permit}}]         $state         $request]

    if {[dict get $authorization decision] ne "permit"} {
        return -code error             -errorcode {TCLMESH ACTION AUTHORIZATION DENIED}             "action authorization did not permit execution"
    }

    set verdicts [expr {[dict exists $descriptor deontic] ? [dict get $descriptor deontic] : {M}}]
    set judgment [::tclmesh::deontic resolve $verdicts]
    set execution [_execution_decision $judgment]

    if {[dict exists $descriptor validations]} {
        foreach validation [dict get $descriptor validations] {
            _apply_validation $validation $state $request
        }
    }

    if {[dict exists $descriptor changes]} {
        foreach change [dict get $descriptor changes] {
            set state [_apply_change $change $state $request]
        }
    }

    set effects {}
    if {[dict exists $descriptor effects]} {
        foreach effect [dict get $descriptor effects] {
            lappend effects [_build_effect $effect $state $request]
        }
    }

    set persisted [{*}$adapter persist $request $state]

    return [dict create         status ok         action $action_id         actor_id [dict get $request actor_id]         application_id [dict get $pin application_id]         manifest_version [dict get $pin version]         manifest_hash [dict get $pin manifest_hash]         authorization $authorization         deontic $judgment         execution $execution         result $persisted         effects [dict create proposed $effects executed {}]]
}

proc ::tclmesh::action::describe {application_id action_id {version {}}} {
    set manifest [::tclmesh::manifest get $application_id $version]

    if {![dict exists $manifest actions $action_id]} {
        return -code error             -errorcode [::list TCLMESH ACTION NOT_FOUND $application_id $action_id]             "action '$action_id' is not defined by application '$application_id'"
    }

    return [dict get $manifest actions $action_id]
}

proc ::tclmesh::action::run {language_id application_id action_id adapter request} {
    if {![dict exists $request actor_id] || [dict get $request actor_id] eq ""} {
        return -code error             -errorcode {TCLMESH ACTION ACTOR_REQUIRED}             "authoritative action execution requires request actor_id"
    }

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
    _require_language         $language_id         [dict get $request actor_id]         $action_id         $descriptor

    set callback [::list         ::tclmesh::action::_guarded_execute         $action_id         $descriptor         $adapter         $request         $pin]

    return [{*}$adapter transact $callback]
}
