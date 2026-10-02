lappend auto_path [file dirname [file dirname [file normalize [info script]]]]
package require tclmesh 0.2.0
source [file join [file dirname [info script]] release-policy-support.tcl]
lassign $argv mode path
proc policy_process_backend {op args} {
    if {$op eq "combine-release"} {
        set context [lindex $args 4]
        if {[dict get $context authorization policy_id] ne "report" ||
            [dict get $context contribution_authority a actor_id] ne "a"} {
            error "missing backend authorization receipts"
        }
        if {$::mode eq "interrupt"} {exit 0}
    }
    return [::tclmesh::private::_plaintext_backend $op {*}$args]
}
tclmesh private backend register policy-backend policy_process_backend {
    threshold-release idempotent-release persistent-handles
}
tclmesh private profile define policy-profile [dict create \
    backend policy-backend semantics exact-integer allow_decrypt false]
set store [tclmesh store create file $path]
tclmesh manifest use-store $store
tclmesh language use-store $store
if {$mode eq "extra-context"} {
    set state [tclmesh store get $store release.registry]
    set id [lindex [dict keys [dict get $state requests]] 0]
    dict set state requests $id context recipient unapproved
    tclmesh store put $store release.registry $state
}
tclmesh release use-store $store
if {$mode in {produce interrupt}} {
    set setup [policytest_setup policy-process]
    set id [dict get [policytest_request $setup] id]
    policytest_quorum $setup $id
    if {$mode eq "interrupt"} {
        tclmesh release combine-authorized [dict get $setup operator] $id operator
    }
    puts ready
} else {
    set id [lindex [tclmesh release list] 0]
    set request [tclmesh release get $id]
    set op [dict get $request authorization requester language_id]
    if {$mode eq "extra-context"} {
        catch {tclmesh release combine-authorized $op $id operator} message options
        set after [tclmesh release get $id]
        puts [list [dict get $options -errorcode] [dict get $after status] [dict get $after attempts]]
    } elseif {$mode eq "revoked"} {
        tclmesh language revoke [dict get $request contribution_authority a language_id]
        catch {tclmesh release combine-authorized $op $id operator} message options
        puts [dict get $options -errorcode]
    } else {
        if {[dict get $request status] eq "combining"} {
            tclmesh release recover-authorized $op $id operator retry
        }
        set released [tclmesh release combine-authorized $op $id operator]
        puts [list [dict get $released status] [dict get $released attempts] \
            [dict get $released recoveries] [dict get $released result]]
    }
}
