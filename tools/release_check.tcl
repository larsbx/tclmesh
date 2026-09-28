set here [file dirname [file normalize [info script]]]
set root [file dirname $here]

lappend auto_path $root
package require tclmesh 0.1.0

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

set output [string trim [exec tclsh [file join $root examples shipment.tcl]]]
if {$output ne "accepted|N|succeeded|private-ir-ok"} {
    error "quickstart output mismatch: '$output'"
}

puts "tclmesh $loaded release-check ok"
