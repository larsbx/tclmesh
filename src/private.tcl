namespace eval ::tclmesh::private {
    variable allowed_ops {
        constant input
        add subtract multiply negate
        equal less-than less-or-equal greater-than greater-or-equal
        and or not select
        rotate reduce-sum lookup polynomial
    }

    namespace export node circuit validate
    namespace ensemble create
}

proc ::tclmesh::private::node {op args} {
    variable allowed_ops

    if {$op ni $allowed_ops} {
        return -code error -errorcode {TCLMESH PRIVATE UNKNOWN_NODE}             "unsupported private-circuit operation '$op'"
    }

    return [linsert $args 0 $op]
}

proc ::tclmesh::private::circuit {name inputs outputs nodes {metadata {}}} {
    return [dict create         name $name         inputs $inputs         outputs $outputs         nodes $nodes         metadata $metadata]
}

proc ::tclmesh::private::validate {circuit} {
    variable allowed_ops

    foreach key {name inputs outputs nodes metadata} {
        if {![dict exists $circuit $key]} {
            return -code error -errorcode [list TCLMESH PRIVATE CIRCUIT MISSING $key]                 "private circuit is missing required field '$key'"
        }
    }

    dict for {id node} [dict get $circuit nodes] {
        set op [lindex $node 0]
        if {$op ni $allowed_ops} {
            return -code error -errorcode [list TCLMESH PRIVATE UNKNOWN_NODE $id]                 "node '$id' uses unsupported operation '$op'"
        }
    }

    return $circuit
}
