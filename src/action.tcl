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
        lt -
        lte -
        gt -
        gte {
            if {[llength $expr] != 3} {
                return -code error -errorcode {TCLMESH ACTION PREDICATE INVALID}                     "$op predicate requires two numeric value expressions"
            }

            set left [_eval_value [lindex $expr 1] $state $request]
            set right [_eval_value [lindex $expr 2] $state $request]

            # Tcl recognizes signed/payload NaN spellings as doubles, but
            # conversion rejects them. A false comparison must not let `not`
            # turn malformed numeric input into permission.
            if {![string is double -strict $left] ||
                ![string is double -strict $right] ||
                [catch {expr {double($left)}}] ||
                [catch {expr {double($right)}}]} {
                return -code error                     -errorcode [::list TCLMESH ACTION PREDICATE NON_NUMERIC $op]                     "predicate '$op' requires numeric operands other than NaN"
            }

            switch -- $op {
                lt  { return [expr {$left < $right}] }
                lte { return [expr {$left <= $right}] }
                gt  { return [expr {$left > $right}] }
                gte { return [expr {$left >= $right}] }
            }
        }
        in {
            if {[llength $expr] != 3} {
                return -code error -errorcode {TCLMESH ACTION PREDICATE INVALID}                     "in predicate requires a value and a list value"
            }

            set needle [_eval_value [lindex $expr 1] $state $request]
            set haystack [_eval_value [lindex $expr 2] $state $request]
            return [expr {$needle in $haystack}]
        }
        contains {
            if {[llength $expr] != 3} {
                return -code error -errorcode {TCLMESH ACTION PREDICATE INVALID}                     "contains predicate requires two string values"
            }

            set haystack [_eval_value [lindex $expr 1] $state $request]
            set needle [_eval_value [lindex $expr 2] $state $request]
            return [expr {[string first $needle $haystack] >= 0}]
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


proc ::tclmesh::action::_noncanonical {action_id field message} {
    return -code error         -errorcode [::list TCLMESH ACTION NON_CANONICAL $action_id $field]         "action '$action_id' $message"
}

proc ::tclmesh::action::_validate_value_spec {action_id field value} {
    if {[llength $value] == 0} {
        _noncanonical $action_id $field "contains an empty value expression"
    }

    set op [lindex $value 0]
    switch -- $op {
        literal {
            if {[llength $value] != 2} {
                _noncanonical $action_id $field                     "literal value expressions require exactly one argument"
            }
        }
        field -
        request {
            if {[llength $value] < 2} {
                _noncanonical $action_id $field                     "$op value expressions require a nonempty path"
            }
        }
        default {
            _noncanonical $action_id $field                 "contains unknown value operation '$op'"
        }
    }
}

proc ::tclmesh::action::_validate_predicate_spec {action_id field predicate} {
    if {[llength $predicate] == 0} {
        _noncanonical $action_id $field "contains an empty predicate"
    }

    set op [lindex $predicate 0]
    switch -- $op {
        true -
        false {
            if {[llength $predicate] != 1} {
                _noncanonical $action_id $field                     "predicate '$op' takes no arguments"
            }
        }
        eq -
        neq -
        lt -
        lte -
        gt -
        gte -
        in -
        contains {
            if {[llength $predicate] != 3} {
                _noncanonical $action_id $field                     "predicate '$op' requires two value expressions"
            }
            _validate_value_spec $action_id $field [lindex $predicate 1]
            _validate_value_spec $action_id $field [lindex $predicate 2]
        }
        and -
        or {
            if {[llength $predicate] < 2} {
                _noncanonical $action_id $field                     "predicate '$op' requires at least one child"
            }
            foreach child [lrange $predicate 1 end] {
                _validate_predicate_spec $action_id $field $child
            }
        }
        not {
            if {[llength $predicate] != 2} {
                _noncanonical $action_id $field                     "predicate 'not' requires one child"
            }
            _validate_predicate_spec $action_id $field [lindex $predicate 1]
        }
        default {
            _noncanonical $action_id $field                 "contains unknown predicate operation '$op'"
        }
    }
}

proc ::tclmesh::action::_validate_authorization_spec {action_id spec} {
    if {[llength $spec] == 0} {
        _noncanonical $action_id authorize             "authorize field contains an empty specification"
    }

    set op [lindex $spec 0]
    switch -- $op {
        permit -
        deny {
            if {[llength $spec] != 1} {
                _noncanonical $action_id authorize                     "authorization '$op' takes no arguments"
            }
        }
        permit-if {
            if {[llength $spec] != 2} {
                _noncanonical $action_id authorize                     "authorization 'permit-if' requires one predicate"
            }
            _validate_predicate_spec $action_id authorize [lindex $spec 1]
        }
        default {
            _noncanonical $action_id authorize                 "contains unknown authorization operation '$op'"
        }
    }
}

proc ::tclmesh::action::_validate_descriptor {action_id descriptor} {
    if {[dict exists $descriptor authorize]} {
        _validate_authorization_spec             $action_id [dict get $descriptor authorize]
    }

    if {[dict exists $descriptor deontic]} {
        set verdicts [dict get $descriptor deontic]
        if {[llength $verdicts] == 0} {
            _noncanonical $action_id deontic                 "deontic field must contain at least one verdict"
        }
        foreach verdict $verdicts {
            ::tclmesh::deontic semantics $verdict
        }
    }

    if {[dict exists $descriptor validations]} {
        foreach validation [dict get $descriptor validations] {
            if {[llength $validation] != 2 ||
                [lindex $validation 0] ne "assert"} {
                _noncanonical $action_id validations                     "validation must be {assert predicate}"
            }
            _validate_predicate_spec                 $action_id validations [lindex $validation 1]
        }
    }

    if {[dict exists $descriptor changes]} {
        foreach change [dict get $descriptor changes] {
            if {[llength $change] != 3 ||
                [lindex $change 0] ne "set" ||
                [lindex $change 1] eq ""} {
                _noncanonical $action_id changes                     "change must be {set field value-expression}"
            }
            _validate_value_spec                 $action_id changes [lindex $change 2]
        }
    }

    if {[dict exists $descriptor effects]} {
        foreach effect [dict get $descriptor effects] {
            if {[llength $effect] < 2 ||
                [lindex $effect 0] ne "emit" ||
                [lindex $effect 1] eq "" ||
                (([llength $effect] - 2) % 2) != 0} {
                _noncanonical $action_id effects                     "effect must be {emit type ?field value-expression ...?}"
            }

            foreach {name value} [lrange $effect 2 end] {
                if {$name eq ""} {
                    _noncanonical $action_id effects                         "effect field names must not be empty"
                }
                _validate_value_spec $action_id effects $value
            }
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
