if {![package vsatisfies [package provide Tcl] 8.6]} {
    return
}

package ifneeded tclmesh 0.3.0 [list source [file join $dir src tclmesh.tcl]]
