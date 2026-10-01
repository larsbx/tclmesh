set here [file dirname [file normalize [info script]]]
set root [file dirname $here]

lappend auto_path $root
package require tclmesh 0.3.0

set fh [open [file join $root VERSION] r]
try {
    set declared [string trim [read $fh]]
} finally {
    close $fh
}

set loaded [package present tclmesh]

if {$declared ne $loaded} {
    error "VERSION '$declared' does not match package version '$loaded'"
}

set shipment [string trim [exec tclsh [file join $root examples shipment.tcl]]]
if {$shipment ne "accepted|N|succeeded|private-ir-ok"} {
    error "shipment quickstart output mismatch: '$shipment'"
}

set private [string trim [exec tclsh [file join $root examples private_release.tcl]]]
if {$private ne "differential:true|released:42"} {
    error "private release quickstart output mismatch: '$private'"
}

puts "tclmesh $loaded release-check ok"
