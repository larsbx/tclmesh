package require Tcl 8.6
package require tcltest 2

namespace import ::tcltest::*

set here [file dirname [file normalize [info script]]]
set root [file dirname $here]

if {$root ni $::auto_path} {
    lappend ::auto_path $root
}

configure -testdir $here -singleproc 1
runAllTests
