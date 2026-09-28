namespace eval ::tclmesh::language {
    variable instances {}
    variable next_id 0

    namespace export instantiate describe commands revoke delegate why-not list
    namespace ensemble create
}

proc ::tclmesh::language::_require {id} {
    variable instances

    if {![dict exists $instances $id]} {
        return -code error             -errorcode {TCLMESH LANGUAGE NOT_FOUND}             "language '$id' does not exist"
    }

    return [dict get $instances $id]
}

proc ::tclmesh::language::_subset {child parent} {
    foreach item $child {
        if {$item ni $parent} {
            return 0
        }
    }
    return 1
}

proc ::tclmesh::language::_narrow_context {parent_context child_context} {
    set effective $parent_context

    dict for {key value} $child_context {
        if {[dict exists $parent_context $key] &&
            [dict get $parent_context $key] ne $value} {
            return -code error                 -errorcode [::list TCLMESH LANGUAGE CONTEXT_AMPLIFICATION $key]                 "delegated context cannot replace parent binding '$key'"
        }

        dict set effective $key $value
    }

    return $effective
}

proc ::tclmesh::language::instantiate {package holder commands capabilities {context {}} {parent {}}} {
    variable instances
    variable next_id

    incr next_id
    set id "language:$next_id"

    set descriptor [dict create         id $id         package $package         holder $holder         parent $parent         commands [lsort -unique $commands]         capabilities [lsort -unique $capabilities]         context $context         generation 1         status active]

    dict set instances $id $descriptor
    return $id
}

proc ::tclmesh::language::describe {id} {
    return [_require $id]
}

proc ::tclmesh::language::commands {id} {
    return [dict get [_require $id] commands]
}

proc ::tclmesh::language::list {} {
    variable instances
    return [lsort [dict keys $instances]]
}

proc ::tclmesh::language::revoke {id} {
    variable instances

    set descriptor [_require $id]
    dict set descriptor status revoked
    dict incr descriptor generation
    dict set instances $id $descriptor
    return $descriptor
}

proc ::tclmesh::language::delegate {parent holder commands capabilities {context {}}} {
    set source [_require $parent]

    if {[dict get $source status] ne "active"} {
        return -code error             -errorcode {TCLMESH LANGUAGE INACTIVE}             "cannot delegate from inactive language '$parent'"
    }

    if {![_subset $commands [dict get $source commands]]} {
        return -code error             -errorcode {TCLMESH LANGUAGE AUTHORITY_AMPLIFICATION COMMAND}             "delegated commands exceed parent authority"
    }

    if {![_subset $capabilities [dict get $source capabilities]]} {
        return -code error             -errorcode {TCLMESH LANGUAGE AUTHORITY_AMPLIFICATION CAPABILITY}             "delegated capabilities exceed parent authority"
    }

    set effective_context [_narrow_context         [dict get $source context]         $context]

    return [instantiate         [dict get $source package]         $holder         $commands         $capabilities         $effective_context         $parent]
}

proc ::tclmesh::language::why-not {id command} {
    set descriptor [_require $id]

    if {[dict get $descriptor status] ne "active"} {
        return [dict create             command $command             available false             blockers [::list [dict create                 kind language-state                 state [dict get $descriptor status]]]]
    }

    if {$command ni [dict get $descriptor commands]} {
        return [dict create             command $command             available false             blockers [::list [dict create kind command-not-granted]]]
    }

    return [dict create command $command available true blockers {}]
}
