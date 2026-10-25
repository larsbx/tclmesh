# Circuit certificates (spec/TclMesh/Certificate.lean).
#
# `emit` computes the least certificate for a circuit: every node labelled
# public or cipher, and every select on a cipher condition named oblivious.
# `check` validates any certificate against a circuit and returns the list of
# violations (empty when it is accepted). The Lean checker, proved sound, is
# authoritative; this one must agree with it (tools/views.tcl).

namespace eval ::tclmesh::certificate {
    namespace export emit check
    namespace ensemble create
}

proc ::tclmesh::certificate::_vis_label {descriptor} {
    expr {[lindex $descriptor 0] eq "public" ? "public" : "cipher"}
}

proc ::tclmesh::certificate::_le {a b} {
    expr {$a eq "public" || $b eq "cipher"}
}

proc ::tclmesh::certificate::_least {circuit id memoVar} {
    upvar 1 $memoVar memo
    if {[dict exists $memo $id]} {
        return [dict get $memo $id]
    }
    set node [dict get $circuit nodes $id]
    if {[lindex $node 0] eq "input"} {
        set label [_vis_label [dict get $circuit inputs [lindex $node 1]]]
    } else {
        set label public
        foreach ref [::tclmesh::private::_node_refs $node] {
            if {[_least $circuit $ref memo] eq "cipher"} {
                set label cipher
            }
        }
    }
    dict set memo $id $label
    return $label
}

proc ::tclmesh::certificate::emit {circuit} {
    set circuit [::tclmesh::private::validate $circuit]
    set memo {}
    set labels {}
    set oblivious {}
    foreach id [dict keys [dict get $circuit nodes]] {
        dict set labels $id [_least $circuit $id memo]
        set node [dict get $circuit nodes $id]
        if {[lindex $node 0] eq "select" &&
            [_least $circuit [lindex $node 1] memo] eq "cipher"} {
            lappend oblivious $id
        }
    }
    return [dict create labels $labels oblivious $oblivious]
}

proc ::tclmesh::certificate::_label {cert id} {
    if {[dict exists $cert labels $id]} {
        return [dict get $cert labels $id]
    }
    return cipher
}

proc ::tclmesh::certificate::check {circuit cert} {
    set violations {}
    dict for {id node} [dict get $circuit nodes] {
        if {![dict exists $cert labels $id]} {
            lappend violations [list unlabelled $id]
            continue
        }
        set label [dict get $cert labels $id]
        if {[lindex $node 0] eq "input"} {
            set declared {}
            if {[dict exists $circuit inputs [lindex $node 1]]} {
                set declared [dict get $circuit inputs [lindex $node 1]]
            }
            if {![_le [_vis_label $declared] $label]} {
                lappend violations [list input-demoted $id]
            }
        } else {
            foreach ref [::tclmesh::private::_node_refs $node] {
                if {![_le [_label $cert $ref] $label]} {
                    lappend violations [list under-labelled $id $ref]
                }
            }
        }
        if {[lindex $node 0] eq "select" && [llength $node] == 4 &&
            [_label $cert [lindex $node 1]] eq "cipher" &&
            $id ni [dict get $cert oblivious]} {
            lappend violations [list not-oblivious $id]
        }
    }
    dict for {name descriptor} [dict get $circuit outputs] {
        set node {}
        if {[dict exists $circuit metadata output_nodes $name]} {
            set node [dict get $circuit metadata output_nodes $name]
        }
        if {[lindex $descriptor 0] eq "public" && [_label $cert $node] ne "public"} {
            lappend violations [list public-output-of-cipher $name]
        }
    }
    return $violations
}
