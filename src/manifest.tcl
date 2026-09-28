namespace eval ::tclmesh::manifest {
    variable registry {}

    namespace export new validate install get list
    namespace ensemble create
}

proc ::tclmesh::manifest::new {application_id version} {
    return [dict create         manifest_version 1         application [dict create id $application_id version $version]         types {}         resources {}         actions {}         policies {}         rules {}         circuits {}         workflows {}         ceremonies {}         languages {}         capabilities {}         provenance {}]
}

proc ::tclmesh::manifest::validate {manifest} {
    foreach key {
        manifest_version
        application
        types
        resources
        actions
        policies
        rules
        circuits
        workflows
        ceremonies
        languages
        capabilities
        provenance
    } {
        if {![dict exists $manifest $key]} {
            return -code error -errorcode [list TCLMESH MANIFEST MISSING $key]                 "manifest is missing required field '$key'"
        }
    }

    foreach key {id version} {
        if {![dict exists $manifest application $key]} {
            return -code error -errorcode [list TCLMESH MANIFEST APPLICATION MISSING $key]                 "manifest application is missing required field '$key'"
        }
    }

    if {[dict get $manifest manifest_version] != 1} {
        return -code error -errorcode {TCLMESH MANIFEST VERSION UNSUPPORTED}             "unsupported manifest version"
    }

    return $manifest
}

proc ::tclmesh::manifest::install {manifest} {
    variable registry

    set manifest [validate $manifest]
    set id [dict get $manifest application id]
    dict set registry $id $manifest
    return $id
}

proc ::tclmesh::manifest::get {application_id} {
    variable registry

    if {![dict exists $registry $application_id]} {
        return -code error -errorcode {TCLMESH MANIFEST NOT_FOUND}             "manifest '$application_id' is not installed"
    }

    return [dict get $registry $application_id]
}

proc ::tclmesh::manifest::list {} {
    variable registry
    return [lsort [dict keys $registry]]
}
