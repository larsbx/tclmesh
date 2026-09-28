namespace eval ::tclmesh {
    variable version 0.1.0
}

set ::tclmesh::here [file dirname [info script]]
foreach file {
    manifest.tcl
    compiler.tcl
    action.tcl
    effect.tcl
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
        compiler ::tclmesh::compiler
        action   ::tclmesh::action
        effect   ::tclmesh::effect
        macro    ::tclmesh::macro
        deontic  ::tclmesh::deontic
        language ::tclmesh::language
        private  ::tclmesh::private
    }
}

package provide tclmesh 0.1.0
