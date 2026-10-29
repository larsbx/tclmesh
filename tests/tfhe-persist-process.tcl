# Child-process fixture for persistent TFHE deployments (tests/tfhe.test
# T-029). Each phase is a fresh process, so a fresh backend: keys come from
# KEYS ($TCLMESH_TFHE_KEYS) and handles from the file store at STORE.
#
#   first:   encrypt 41, import a proof under ctx/1 and destroy its handle.
#   second:  41 decrypts after the restart; a fresh proof under ctx/1 is
#            refused, since destroyed records keep their context; ctx/2 is
#            accepted, since the public key and CRS persisted.
#   foreign: other keys refuse the store's recovery material.
lassign $argv root keys path zk phase
set ::env(TCLMESH_TFHE_KEYS) $keys
lappend auto_path $root
package require tclmesh 0.2.0
tclmesh private profile define p [dict create backend tfhe semantics int32-checked allow_decrypt true]
set store [tclmesh store create file $path]

proc proven {zk context x} {
    set out [file join $zk proof-[file tail $context]-[pid].bin]
    exec [::tclmesh::tfhe::prover] $zk $context 0 8 $x $out
    return $out
}

switch -- $phase {
    first {
        tclmesh release use-store $store
        tclmesh private publish p $zk
        set a [tclmesh private encrypt p int 41 {0 100}]
        set b [tclmesh private import p [proven $zk ctx/1 7] ctx/1 0 8]
        tclmesh private handle destroy $b
        puts [list $a $b]
    }
    second {
        tclmesh release use-store $store
        set a [lindex [tclmesh private handle list] 0]
        catch {tclmesh private import p [proven $zk ctx/1 9] ctx/1 0 8} - options
        set c [tclmesh private import p [proven $zk ctx/2 42] ctx/2 0 8]
        puts [list [tclmesh private decrypt $a] [dict get $options -errorcode] \
            [tclmesh private decrypt $c]]
    }
    foreign {
        puts [expr {[catch {tclmesh release use-store $store} msg] &&
            [string match "*another keyset*" $msg] ? "refused" : "restored: $msg"}]
    }
}
