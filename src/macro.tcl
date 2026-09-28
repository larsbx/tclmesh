namespace eval ::tclmesh::macro {
    variable registry {}

    namespace export define describe expand list
    namespace ensemble create
}

proc ::tclmesh::macro::define {name kind phase command {contract {}}} {
    variable registry

    if {$name eq ""} {
        return -code error -errorcode {TCLMESH MACRO INVALID_NAME}             "macro name must not be empty"
    }

    if {$kind ni {declaration expression semantic resource workflow language private}} {
        return -code error -errorcode {TCLMESH MACRO INVALID_KIND}             "unsupported macro kind '$kind'"
    }

    dict set registry $name [dict create         name $name         kind $kind         phase $phase         command $command         contract $contract]

    return $name
}

proc ::tclmesh::macro::describe {name} {
    variable registry

    if {![dict exists $registry $name]} {
        return -code error -errorcode {TCLMESH MACRO NOT_FOUND}             "macro '$name' is not registered"
    }

    return [dict get $registry $name]
}

proc ::tclmesh::macro::expand {name args} {
    set descriptor [describe $name]
    set command [dict get $descriptor command]
    return [{*}$command {*}$args]
}

proc ::tclmesh::macro::list {} {
    variable registry
    return [lsort [dict keys $registry]]
}
