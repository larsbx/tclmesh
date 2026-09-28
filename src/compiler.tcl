namespace eval ::tclmesh::compiler {
    variable states {}
    variable next_id 0

    namespace export compile
    namespace ensemble create
}

proc ::tclmesh::compiler::_state_get {token args} {
    variable states
    return [dict get $states $token {*}$args]
}

proc ::tclmesh::compiler::_state_set {token args} {
    variable states
    dict set states $token {*}$args
}

proc ::tclmesh::compiler::_require_action {token} {
    set action [_state_get $token current_action]
    if {$action eq ""} {
        return -code error             -errorcode {TCLMESH COMPILER ACTION_CONTEXT_REQUIRED}             "this declaration is only valid inside an action block"
    }
    return $action
}

proc ::tclmesh::compiler::_application {token id version} {
    if {$id eq "" || $version eq ""} {
        return -code error             -errorcode {TCLMESH COMPILER APPLICATION INVALID}             "application requires nonempty id and version"
    }

    set existing [_state_get $token manifest]
    if {$existing ne ""} {
        return -code error             -errorcode {TCLMESH COMPILER APPLICATION DUPLICATE}             "application may only be declared once"
    }

    _state_set $token manifest [::tclmesh::manifest new $id $version]
    return $id
}

proc ::tclmesh::compiler::_action {token name body} {
    if {[_state_get $token manifest] eq ""} {
        return -code error             -errorcode {TCLMESH COMPILER APPLICATION REQUIRED}             "application must be declared before actions"
    }

    if {[_state_get $token current_action] ne ""} {
        return -code error             -errorcode {TCLMESH COMPILER ACTION NESTED}             "actions may not be nested"
    }

    if {$name eq ""} {
        return -code error             -errorcode {TCLMESH COMPILER ACTION INVALID_NAME}             "action name must not be empty"
    }

    _state_set $token current_action $name
    _state_set $token action_descriptor [dict create kind update]

    set child [_state_get $token interpreter]
    try {
        interp eval $child $body
        set descriptor [_state_get $token action_descriptor]
        set manifest [_state_get $token manifest]
        dict set manifest actions $name $descriptor
        _state_set $token manifest $manifest
    } finally {
        _state_set $token current_action {}
        _state_set $token action_descriptor {}
    }

    return $name
}

proc ::tclmesh::compiler::_action_set {token field value} {
    _require_action $token
    set descriptor [_state_get $token action_descriptor]
    dict set descriptor $field $value
    _state_set $token action_descriptor $descriptor
    return $value
}

proc ::tclmesh::compiler::_action_append {token field value} {
    _require_action $token
    set descriptor [_state_get $token action_descriptor]
    set values {}
    if {[dict exists $descriptor $field]} {
        set values [dict get $descriptor $field]
    }
    lappend values $value
    dict set descriptor $field $values
    _state_set $token action_descriptor $descriptor
    return $value
}

proc ::tclmesh::compiler::_capability {token value} {
    if {$value eq ""} {
        return -code error             -errorcode {TCLMESH COMPILER CAPABILITY EMPTY}             "action capability must not be empty"
    }
    return [_action_set $token capability $value]
}

proc ::tclmesh::compiler::_authorize {token spec} {
    return [_action_set $token authorize $spec]
}

proc ::tclmesh::compiler::_deontic {token args} {
    if {[llength $args] == 0} {
        return -code error             -errorcode {TCLMESH COMPILER DEONTIC EMPTY}             "deontic requires at least one verdict"
    }
    return [_action_set $token deontic $args]
}

proc ::tclmesh::compiler::_validate {token spec} {
    return [_action_append $token validations $spec]
}

proc ::tclmesh::compiler::_change {token spec} {
    return [_action_append $token changes $spec]
}

proc ::tclmesh::compiler::_effect {token spec} {
    return [_action_append $token effects $spec]
}

proc ::tclmesh::compiler::_literal {value} {
    return [list literal $value]
}

proc ::tclmesh::compiler::_field {args} {
    if {[llength $args] == 0} {
        return -code error             -errorcode {TCLMESH COMPILER FIELD EMPTY}             "field requires a path"
    }
    return [linsert $args 0 field]
}

proc ::tclmesh::compiler::_request {args} {
    if {[llength $args] == 0} {
        return -code error             -errorcode {TCLMESH COMPILER REQUEST EMPTY}             "request requires a path"
    }
    return [linsert $args 0 request]
}

proc ::tclmesh::compiler::_binary {operator left right} {
    return [list $operator $left $right]
}

proc ::tclmesh::compiler::_variadic {operator args} {
    if {[llength $args] == 0} {
        return -code error             -errorcode [list TCLMESH COMPILER PREDICATE EMPTY $operator]             "predicate '$operator' requires at least one child"
    }
    return [linsert $args 0 $operator]
}

proc ::tclmesh::compiler::_not {child} {
    return [list not $child]
}

proc ::tclmesh::compiler::_assert {predicate} {
    return [list assert $predicate]
}

proc ::tclmesh::compiler::_set_field {field value} {
    if {$field eq ""} {
        return -code error             -errorcode {TCLMESH COMPILER CHANGE EMPTY_FIELD}             "set-field requires a field name"
    }
    return [list set $field $value]
}

proc ::tclmesh::compiler::_emit {type args} {
    if {$type eq ""} {
        return -code error             -errorcode {TCLMESH COMPILER EFFECT EMPTY_TYPE}             "emit requires a nonempty effect type"
    }

    if {[llength $args] % 2 != 0} {
        return -code error             -errorcode {TCLMESH COMPILER EFFECT INVALID_FIELDS}             "emit fields must be name/value-expression pairs"
    }

    return [linsert $args 0 emit $type]
}

proc ::tclmesh::compiler::_gensym {token base} {
    if {$base eq ""} {
        set base generated
    }

    set counter [_state_get $token gensym]
    incr counter
    _state_set $token gensym $counter
    return "${base}#g${counter}"
}

proc ::tclmesh::compiler::_install_aliases {child token} {
    foreach {name target} {
        application _application
        action _action
        capability _capability
        authorize _authorize
        deontic _deontic
        validate _validate
        change _change
        effect _effect
        literal _literal
        field _field
        request _request
        assert _assert
        set-field _set_field
        emit _emit
        gensym _gensym
    } {
        interp alias $child $name {} ::tclmesh::compiler::$target $token
    }

    interp alias $child eq {} ::tclmesh::compiler::_binary eq
    interp alias $child neq {} ::tclmesh::compiler::_binary neq
    interp alias $child all {} ::tclmesh::compiler::_variadic and
    interp alias $child any {} ::tclmesh::compiler::_variadic or
    interp alias $child not {} ::tclmesh::compiler::_not
}

proc ::tclmesh::compiler::compile {script {options {}}} {
    variable states
    variable next_id

    set max_commands 10000
    set max_seconds 2

    if {[dict exists $options max_commands]} {
        set max_commands [dict get $options max_commands]
    }
    if {[dict exists $options max_seconds]} {
        set max_seconds [dict get $options max_seconds]
    }

    if {![string is integer -strict $max_commands] || $max_commands <= 0} {
        return -code error             -errorcode {TCLMESH COMPILER INVALID_COMMAND_LIMIT}             "max_commands must be a positive integer"
    }
    if {![string is integer -strict $max_seconds] || $max_seconds <= 0} {
        return -code error             -errorcode {TCLMESH COMPILER INVALID_TIME_LIMIT}             "max_seconds must be a positive integer"
    }

    incr next_id
    set token "compile:$next_id"
    set child [interp create -safe]

    dict set states $token [dict create         interpreter $child         manifest {}         current_action {}         action_descriptor {}         gensym 0]

    _install_aliases $child $token

    interp limit $child command -value $max_commands
    interp limit $child time -seconds $max_seconds

    try {
        interp eval $child $script
        set manifest [_state_get $token manifest]
        if {$manifest eq ""} {
            return -code error                 -errorcode {TCLMESH COMPILER APPLICATION REQUIRED}                 "compiled script did not declare an application"
        }

        return [::tclmesh::manifest validate             [::tclmesh::action::bind_manifest $manifest]]
    } finally {
        catch {interp delete $child}
        dict unset states $token
    }
}
