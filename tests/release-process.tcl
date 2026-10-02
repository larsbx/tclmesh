# Child-process fixture for release recovery; no parent interpreter state is used.
lappend auto_path [file dirname [file dirname [file normalize [info script]]]]
package require tclmesh 0.2.0
lassign $argv mode path
proc durable_reference {op args} {
    if {$op eq "restore-handle" && $::mode eq "deny-restore"} {
        error "backend denied restoration"
    }
    if {$op eq "combine-release" && $::mode eq "interrupt"} {
        # Simulate loss of the process after the combining state was committed.
        exit 0
    }
    return [::tclmesh::private::_plaintext_backend $op {*}$args]
}
tclmesh private backend register durable-reference durable_reference {
    threshold-release idempotent-release persistent-handles destroy
}
tclmesh private profile define durable-profile [dict create \
    backend durable-reference semantics [expr {$mode eq "changed-profile" ? "changed" : "exact-integer"}] allow_decrypt false]
set store [tclmesh store create file $path]
tclmesh release use-store $store
if {$mode in {quorum interrupt destroy}} {
    set handle [tclmesh private encrypt durable-profile int 73]
    set request [tclmesh release request $handle report 2 {a b}]
    set id [dict get $request id]
    tclmesh release contribute $id a share-a
    tclmesh release contribute $id b share-b
    if {$mode eq "interrupt"} {tclmesh release combine $id}
    if {$mode eq "destroy"} {tclmesh private handle destroy $handle}
    puts ready
} else {
    set id [lindex [tclmesh release list] 0]
    set before [tclmesh release get $id]
    set handle [dict get $before handle]
    # Allocating another handle must not collide with the restored bound ID.
    set other [tclmesh private encrypt durable-profile int 999]
    if {$other eq $handle} {error "restored handle ID reused"}
    if {$mode eq "revoked"} {
        catch {tclmesh release combine $id} message options
        puts [dict get $options -errorcode]
    } else {
        if {[dict get $before status] eq "combining"} {
            tclmesh release recover $id retry
        }
        catch {tclmesh private decrypt $handle} message options
        set released [tclmesh release combine $id]
        puts [list [dict get $before status] [dict get $released status] \
            [dict get $released result] [dict get $released attempts] \
            [dict get $released recoveries] \
            [dict get $options -errorcode] \
            [dict exists [tclmesh private handle describe $handle] token]]
    }
}
