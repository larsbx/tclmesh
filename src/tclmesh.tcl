namespace eval ::tclmesh {
    variable version 0.3.0
}

set ::tclmesh::here [file dirname [info script]]
foreach file {
    store.tcl
    audit.tcl
    manifest.tcl
    compiler.tcl
    action.tcl
    effect.tcl
    macro.tcl
    deontic.tcl
    language.tcl
    workflow.tcl
    private.tcl
    release.tcl
} {
    source [file join $::tclmesh::here $file]
}
unset ::tclmesh::here

namespace eval ::tclmesh {
    namespace ensemble create -command ::tclmesh -map {
        store    ::tclmesh::store
        audit    ::tclmesh::audit
        manifest ::tclmesh::manifest
        compiler ::tclmesh::compiler
        action   ::tclmesh::action
        effect   ::tclmesh::effect
        macro    ::tclmesh::macro
        deontic  ::tclmesh::deontic
        language ::tclmesh::language
        workflow ::tclmesh::workflow
        private  ::tclmesh::private
        release  ::tclmesh::release
    }
}

package provide tclmesh 0.3.0
