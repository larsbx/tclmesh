# Child-process fixture for CRS adoption (tests/tfhe.test T-020): a fresh
# backend adopts a CRS that a third party generated, proves and imports under
# it, refuses a proof made under another CRS, and refuses to change a fixed CRS.
lassign $argv root dir foreign_crs
lappend auto_path $root
package require tclmesh 0.2.0
tclmesh private profile define p [dict create backend tfhe semantics int32-checked allow_decrypt true]
tclmesh private publish p $dir [file join $dir third-party-crs.bin]
set out {}

set proof [file join $dir proof.bin]
exec [::tclmesh::tfhe::prover] $dir ctx/1 0 8 42 $proof
lappend out adopted [tclmesh private decrypt [tclmesh private import p $proof ctx/1 0 8]]

# A proof built with the CRS this process did not adopt.
set foreign [file join $dir foreign]
file mkdir $foreign
file copy -force [file join $dir public-key.bin] $foreign
file copy -force $foreign_crs [file join $foreign crs.bin]
exec [::tclmesh::tfhe::prover] $foreign ctx/2 0 8 42 [file join $foreign proof.bin]
lappend out [expr {[catch {tclmesh private import p [file join $foreign proof.bin] ctx/2 0 8} msg] &&
    [string match "*proof rejected*" $msg] ? "foreign-refused" : "foreign-accepted: $msg"}]

lappend out [expr {[catch {tclmesh private publish p $dir $foreign_crs} msg] &&
    [string match "*already fixed*" $msg] ? "fixed-refused" : "fixed-changed: $msg"}]
puts $out
