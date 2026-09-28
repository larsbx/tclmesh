namespace eval ::tclmesh::manifest {
    variable registry {}
    variable store {}

    # Fields whose values are maps from names to canonical node descriptors.
    variable node_map_fields {
        types resources actions policies rules circuits workflows ceremonies
        languages capabilities attributes relationships identities calculations
        aggregates inputs outputs steps phases
    }

    # Fields whose values are maps from names to ordered semantic sequences.
    variable sequence_map_fields {
        nodes
    }

    # Fields whose values are ordinary maps. Their keys are canonicalized, while
    # values remain scalar unless their enclosing node schema says otherwise.
    variable scalar_map_fields {
        application constraints metadata context packing threshold
        provenance compiler runtime
    }

    # Ordered semantic sequences. Order is preserved exactly.
    variable sequence_fields {
        values accepts validations changes preparations effects commands
        defeats defeated_by participants requested_outputs completed ready
        failed compensations
    }

    namespace export         new validate canonical digest install get describe versions         activate active list use-store
    namespace ensemble create
}

proc ::tclmesh::manifest::_commit {candidate} {
    variable registry
    variable store

    if {$store ne ""} {
        ::tclmesh::store put $store manifest.registry             [dict create registry $candidate]
    }

    set registry $candidate
}

proc ::tclmesh::manifest::use-store {store_id} {
    variable registry
    variable store

    if {$store_id eq ""} {
        set store {}
        return {}
    }

    ::tclmesh::store describe $store_id

    if {[::tclmesh::store exists $store_id manifest.registry]} {
        set state [::tclmesh::store get $store_id manifest.registry]
        if {![dict exists $state registry]} {
            return -code error                 -errorcode {TCLMESH MANIFEST STORE INVALID_STATE}                 "manifest registry store is missing registry state"
        }
        set candidate [dict get $state registry]
    } else {
        set candidate $registry
        ::tclmesh::store put $store_id manifest.registry             [dict create registry $candidate]
    }

    set registry $candidate
    set store $store_id
    return $store
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

    if {[dict get $manifest application version] eq ""} {
        return -code error             -errorcode {TCLMESH MANIFEST APPLICATION EMPTY version}             "manifest application version must not be empty"
    }

    if {[dict get $manifest manifest_version] != 1} {
        return -code error             -errorcode {TCLMESH MANIFEST VERSION UNSUPPORTED}             "unsupported manifest version"
    }

    return $manifest
}

proc ::tclmesh::manifest::_canonical_scalar_map {value} {
    set output {}

    foreach key [lsort -dictionary [dict keys $value]] {
        lappend output $key [dict get $value $key]
    }

    return $output
}

proc ::tclmesh::manifest::_canonical_node_map {value} {
    set output {}

    foreach key [lsort -dictionary [dict keys $value]] {
        lappend output $key [_canonical_node [dict get $value $key]]
    }

    return $output
}

proc ::tclmesh::manifest::_canonical_sequence {value} {
    # Sequence order is semantic. Rebuild the list only to ensure a single Tcl
    # list representation without sorting or treating even-length lists as maps.
    set output {}
    foreach item $value {
        lappend output $item
    }
    return $output
}

proc ::tclmesh::manifest::_canonical_sequence_map {value} {
    set output {}

    foreach key [lsort -dictionary [dict keys $value]] {
        lappend output $key [_canonical_sequence [dict get $value $key]]
    }

    return $output
}

proc ::tclmesh::manifest::_canonical_node {node} {
    variable node_map_fields
    variable sequence_map_fields
    variable scalar_map_fields
    variable sequence_fields

    set output {}

    foreach key [lsort -dictionary [dict keys $node]] {
        set value [dict get $node $key]

        if {$key in $node_map_fields} {
            set value [_canonical_node_map $value]
        } elseif {$key in $sequence_map_fields} {
            set value [_canonical_sequence_map $value]
        } elseif {$key in $scalar_map_fields} {
            set value [_canonical_scalar_map $value]
        } elseif {$key in $sequence_fields} {
            set value [_canonical_sequence $value]
        }

        lappend output $key $value
    }

    return $output
}

proc ::tclmesh::manifest::canonical {manifest} {
    variable node_map_fields

    set manifest [validate $manifest]

    set output [::list         manifest_version [dict get $manifest manifest_version]         application [_canonical_scalar_map [dict get $manifest application]]]

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
    } {
        lappend output $section [_canonical_node_map [dict get $manifest $section]]
    }

    lappend output provenance         [_canonical_node [dict get $manifest provenance]]

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
    if {[llength [info commands ::tclmesh::action::bind_manifest]]} {
        set manifest [::tclmesh::action::bind_manifest $manifest]
    }
    set id [dict get $manifest application id]
    set version [dict get $manifest application version]

    set candidate $registry

    if {[dict exists $candidate $id versions $version]} {
        return -code error             -errorcode [::list TCLMESH MANIFEST ALREADY_INSTALLED $id $version]             "manifest '$id' version '$version' is already installed"
    }

    set hash [digest $manifest]
    set descriptor [dict create         application_id $id         version $version         manifest_hash $hash         manifest $manifest]

    dict set candidate $id versions $version $descriptor

    if {![dict exists $candidate $id active]} {
        dict set candidate $id active {}
    }

    _commit $candidate

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

    if {$version eq ""} {
        return -code error             -errorcode {TCLMESH MANIFEST APPLICATION EMPTY version}             "manifest application version must not be empty"
    }

    set descriptor [_descriptor $application_id $version]
    set actual [dict get $descriptor manifest_hash]

    if {![string equal -nocase $actual $expected_hash]} {
        return -code error             -errorcode [::list TCLMESH MANIFEST HASH_MISMATCH $application_id $version]             "manifest '$application_id' version '$version' hash does not match activation request"
    }

    set candidate $registry
    dict set candidate $application_id active $version
    _commit $candidate

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
