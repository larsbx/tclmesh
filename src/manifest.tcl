namespace eval ::tclmesh::manifest {
    variable registry {}

    namespace export         new validate canonical digest install get describe versions         activate active list
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
            return -code error                 -errorcode [::list TCLMESH MANIFEST MISSING $key]                 "manifest is missing required field '$key'"
        }
    }

    foreach key {id version} {
        if {![dict exists $manifest application $key]} {
            return -code error                 -errorcode [::list TCLMESH MANIFEST APPLICATION MISSING $key]                 "manifest application is missing required field '$key'"
        }
    }

    if {[dict get $manifest manifest_version] != 1} {
        return -code error             -errorcode {TCLMESH MANIFEST VERSION UNSUPPORTED}             "unsupported manifest version"
    }

    return $manifest
}

proc ::tclmesh::manifest::_canonical_map {value} {
    set output {}

    foreach key [lsort -dictionary [dict keys $value]] {
        lappend output $key [dict get $value $key]
    }

    return $output
}

proc ::tclmesh::manifest::canonical {manifest} {
    set manifest [validate $manifest]

    set output [::list         manifest_version [dict get $manifest manifest_version]         application [_canonical_map [dict get $manifest application]]]

    foreach section {
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
        lappend output $section [_canonical_map [dict get $manifest $section]]
    }

    return $output
}

proc ::tclmesh::manifest::digest {manifest} {
    package require sha256

    set bytes [encoding convertto utf-8 [canonical $manifest]]
    return [string tolower [::sha2::sha256 -hex -- $bytes]]
}

proc ::tclmesh::manifest::_descriptor {application_id version} {
    variable registry

    if {![dict exists $registry $application_id versions $version]} {
        return -code error             -errorcode [::list TCLMESH MANIFEST VERSION_NOT_FOUND $application_id $version]             "manifest '$application_id' version '$version' is not installed"
    }

    return [dict get $registry $application_id versions $version]
}

proc ::tclmesh::manifest::install {manifest} {
    variable registry

    set manifest [validate $manifest]
    set id [dict get $manifest application id]
    set version [dict get $manifest application version]

    if {[dict exists $registry $id versions $version]} {
        return -code error             -errorcode [::list TCLMESH MANIFEST ALREADY_INSTALLED $id $version]             "manifest '$id' version '$version' is already installed"
    }

    set hash [digest $manifest]
    set descriptor [dict create         application_id $id         version $version         manifest_hash $hash         manifest $manifest]

    dict set registry $id versions $version $descriptor

    if {![dict exists $registry $id active]} {
        dict set registry $id active {}
    }

    return [dict create         application_id $id         version $version         manifest_hash $hash]
}

proc ::tclmesh::manifest::get {application_id {version {}}} {
    variable registry

    if {$version eq ""} {
        if {![dict exists $registry $application_id active] ||
            [dict get $registry $application_id active] eq ""} {
            return -code error                 -errorcode [::list TCLMESH MANIFEST NOT_ACTIVE $application_id]                 "manifest '$application_id' has no active version"
        }

        set version [dict get $registry $application_id active]
    }

    return [dict get [_descriptor $application_id $version] manifest]
}

proc ::tclmesh::manifest::describe {application_id version} {
    return [_descriptor $application_id $version]
}

proc ::tclmesh::manifest::versions {application_id} {
    variable registry

    if {![dict exists $registry $application_id versions]} {
        return -code error             -errorcode [::list TCLMESH MANIFEST NOT_FOUND $application_id]             "manifest '$application_id' is not installed"
    }

    return [lsort -dictionary [dict keys [dict get $registry $application_id versions]]]
}

proc ::tclmesh::manifest::activate {application_id version expected_hash} {
    variable registry

    set descriptor [_descriptor $application_id $version]
    set actual [dict get $descriptor manifest_hash]

    if {![string equal -nocase $actual $expected_hash]} {
        return -code error             -errorcode [::list TCLMESH MANIFEST HASH_MISMATCH $application_id $version]             "manifest '$application_id' version '$version' hash does not match activation request"
    }

    dict set registry $application_id active $version

    return [dict create         application_id $application_id         version $version         manifest_hash $actual]
}

proc ::tclmesh::manifest::active {application_id} {
    variable registry

    if {![dict exists $registry $application_id active] ||
        [dict get $registry $application_id active] eq ""} {
        return -code error             -errorcode [::list TCLMESH MANIFEST NOT_ACTIVE $application_id]             "manifest '$application_id' has no active version"
    }

    set version [dict get $registry $application_id active]
    set descriptor [_descriptor $application_id $version]

    return [dict create         application_id $application_id         version $version         manifest_hash [dict get $descriptor manifest_hash]]
}

proc ::tclmesh::manifest::list {} {
    variable registry
    return [lsort -dictionary [dict keys $registry]]
}
