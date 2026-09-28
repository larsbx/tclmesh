namespace eval ::tclmesh {
    variable version 0.1
}

set ::tclmesh::here [file dirname [info script]]
foreach file {
    manifest.tcl
    macro.tcl
    deontic.tcl
    language.tcl
    private.tcl
} {
    source [file join $::tclmesh::here $file]
}
unset ::tclmesh::here

namespace eval ::tclmesh {
    namespace ensemble create -command ::tclmesh -map {
        manifest ::tclmesh::manifest
        macro    ::tclmesh::macro
        deontic  ::tclmesh::deontic
        language ::tclmesh::language
        private  ::tclmesh::private
    }
}

package provide tclmesh 0.1
