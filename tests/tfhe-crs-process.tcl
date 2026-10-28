# Child-process fixture for CRS adoption (tests/tfhe.test T-020, T-021): a
# fresh backend refuses each CRS source in BAD, adopts CRS (a file a third
# party generated, or a ceremony directory), proves and imports under it,
# refuses a proof made under another CRS, and refuses to change a fixed CRS.
lassign $argv root dir crs foreign_crs bad
lappend auto_path $root
package require tclmesh 0.2.0
tclmesh private profile define p [dict create backend tfhe semantics int32-checked allow_decrypt true]
set out {}
foreach source $bad {
    lappend out [expr {[catch {tclmesh private publish p $dir $source} msg] ?
        "refused" : "adopted-bad: $source"}]
}
tclmesh private publish p $dir $crs

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
