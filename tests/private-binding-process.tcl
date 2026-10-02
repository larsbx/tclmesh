# Independent-process conformance fixture for persisted circuit/output provenance.
lappend auto_path [file dirname [file dirname [file normalize [info script]]]]
package require tclmesh 0.2.0
lassign $argv mode path
proc binding_backend {op args} {
    if {$op eq "combine-release"} {
        set context [lindex $args 4]
        set binding [dict get $context binding]
        if {[dict get $binding output_name] ne "total" ||
            [dict get $binding circuit_id] ne "aggregate" ||
            [dict get $binding manifest_hash] ne $::expected_manifest_hash} {
            error "backend rejected release binding"
        }
    }
    return [::tclmesh::private::_plaintext_backend $op {*}$args]
}
tclmesh private backend register binding-backend binding_backend {
    threshold-release idempotent-release persistent-handles
}
tclmesh private profile define binding-profile [dict create \
    backend binding-backend semantics exact-integer allow_decrypt false]
set store [tclmesh store create file $path]
tclmesh manifest use-store $store
tclmesh release use-store $store
if {$mode eq "produce"} {
    set circuit [tclmesh private circuit aggregate {} [dict create total {cipher int}] \
        [dict create total {constant 42}] [dict create output_nodes [dict create total total]]]
    set manifest [tclmesh manifest new binding-process 1]
    dict set manifest circuits aggregate $circuit
    set installed [tclmesh manifest install $manifest]
    tclmesh manifest activate binding-process 1 [dict get $installed manifest_hash]
    set handle [dict get [tclmesh private evaluate-bound binding-profile binding-process aggregate {}] total]
    set request [tclmesh release request $handle report 2 {a b}]
    set id [dict get $request id]
    tclmesh release contribute $id a share-a
    tclmesh release contribute $id b share-b
    puts ready
} else {
    set manifest [tclmesh manifest get binding-process 1]
    set ::expected_manifest_hash [tclmesh manifest digest $manifest]
    set id [lindex [tclmesh release list] 0]
    set request [tclmesh release get $id]
    set binding [dict get $request binding]
    set released [tclmesh release combine $id]
    puts [list [expr {[dict get $binding circuit_hash] eq \
        [tclmesh private digest [dict get $manifest circuits aggregate]]}] \
        [dict get $binding manifest_version] [dict get $binding output_spec] \
        [dict get $released result]]
}
