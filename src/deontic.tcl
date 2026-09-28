namespace eval ::tclmesh::deontic {
    variable semantics [dict create         W [dict create admissibility perform-required preference perform]         N [dict create admissibility both-allowed preference perform]         M [dict create admissibility both-allowed preference neutral]         K [dict create admissibility both-allowed preference omit]         H [dict create admissibility omit-required preference omit]]

    namespace export semantics resolve
    namespace ensemble create
}

proc ::tclmesh::deontic::semantics {verdict} {
    variable semantics

    if {![dict exists $semantics $verdict]} {
        return -code error -errorcode {TCLMESH DEONTIC INVALID_VERDICT}             "unknown deontic verdict '$verdict'"
    }

    return [dict get $semantics $verdict]
}

proc ::tclmesh::deontic::_conflict_class {verdicts} {
    if {"W" in $verdicts && "H" in $verdicts} {
        return hard-admissibility
    }
    if {"N" in $verdicts && "K" in $verdicts} {
        return preference
    }
    return unresolved
}

proc ::tclmesh::deontic::resolve {verdicts} {
    if {[llength $verdicts] == 0} {
        return [dict create status inapplicable verdict {} conflicts {}]
    }

    set normalized {}
    foreach verdict $verdicts {
        semantics $verdict
        if {$verdict ni $normalized} {
            lappend normalized $verdict
        }
    }
    set normalized [lsort $normalized]

    if {[llength $normalized] == 1} {
        set verdict [lindex $normalized 0]
        return [dict create             status determinate             verdict $verdict             semantics [semantics $verdict]             conflicts {}]
    }

    return [dict create         status conflicted         verdict {}         support $normalized         conflicts [list [_conflict_class $normalized]]]
}
