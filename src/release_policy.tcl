# Manifest-owned threshold release authorization. Caller identities must be
# authenticated by the trusted adapter, as for the action/workflow APIs.
namespace eval ::tclmesh::release {
    namespace export request-authorized contribute-authorized combine-authorized \
        recover-authorized reject-authorized expire-authorized
}

proc ::tclmesh::release::_policy_error {code} {
    return -code error -errorcode [::list TCLMESH RELEASE POLICY $code] \
        "release policy check failed: $code"
}

proc ::tclmesh::release::_validate_policy {manifest id policy} {
    set fields {kind circuit output purpose profile quorum holders requesters combiners recoverers
        request_capability contribute_capability combine_capability recover_capability context}
    foreach key [dict keys $policy] {
        if {$key ni $fields} {_policy_error UNKNOWN_FIELD}
    }
    foreach key $fields {
        if {![dict exists $policy $key] || ($key ne "context" && [dict get $policy $key] eq "")} {
            _policy_error MISSING_FIELD
        }
    }
    if {[dict get $policy kind] ne "threshold-release"} {_policy_error INVALID_KIND}
    foreach key {holders requesters combiners recoverers} {
        set members [dict get $policy $key]
        if {[llength $members] != [llength [lsort -unique $members]] || "" in $members} {
            _policy_error INVALID_MEMBERS
        }
        dict set policy $key [lsort -unique $members]
    }
    set threshold [dict get $policy quorum]
    if {![string is integer -strict $threshold] || $threshold <= 0 ||
        $threshold > [llength [dict get $policy holders]]} {_policy_error INVALID_THRESHOLD}
    dict size [dict get $policy context]
    set circuit_id [dict get $policy circuit]
    if {![dict exists $manifest circuits $circuit_id]} {_policy_error UNKNOWN_CIRCUIT}
    set circuit [dict get $manifest circuits $circuit_id]
    ::tclmesh::private::validate $circuit
    if {![dict exists $circuit outputs [dict get $policy output]] ||
        [::tclmesh::private::_visibility [dict get $circuit outputs [dict get $policy output]]] ne "cipher"} {
        _policy_error UNKNOWN_OUTPUT
    }
    if {![dict exists $circuit metadata release_policy] ||
        [dict get $circuit metadata release_policy] ne $id ||
        ![dict exists $circuit metadata profile] ||
        [dict get $circuit metadata profile] ne [dict get $policy profile]} {
        _policy_error CIRCUIT_BINDING
    }
    return $policy
}

proc ::tclmesh::release::bind_manifest {manifest} {
    dict for {id policy} [dict get $manifest ceremonies] {
        if {[dict exists $policy kind] && [dict get $policy kind] eq "threshold-release"} {
            _validate_policy $manifest $id $policy
        }
    }
    dict for {id circuit} [dict get $manifest circuits] {
        if {[dict exists $circuit metadata release_policy]} {
            set policy_id [dict get $circuit metadata release_policy]
            if {![dict exists $manifest ceremonies $policy_id]} {_policy_error NOT_FOUND}
            _validate_policy $manifest $policy_id [dict get $manifest ceremonies $policy_id]
            if {[dict get $manifest ceremonies $policy_id circuit] ne $id} {_policy_error CIRCUIT_BINDING}
        }
    }
    return $manifest
}

proc ::tclmesh::release::_handle_policy {handle} {
    set binding [_binding $handle]
    if {![dict exists $binding manifest_hash]} {return {}}
    set manifest [::tclmesh::manifest get [dict get $binding application_id] [dict get $binding manifest_version]]
    if {[::tclmesh::manifest digest $manifest] ne [dict get $binding manifest_hash]} {_policy_error MANIFEST_MISMATCH}
    set circuit [dict get $manifest circuits [dict get $binding circuit_id]]
    if {![dict exists $circuit metadata release_policy]} {return {}}
    return [dict get $circuit metadata release_policy]
}

proc ::tclmesh::release::_authorize {language_id actor policy_id policy role context} {
    if {$actor eq ""} {_policy_error ACTOR_REQUIRED}
    set language [::tclmesh::language describe $language_id]
    set seen {}
    set current $language
    while {1} {
        set id [dict get $current id]
        if {$id in $seen} {_policy_error LANGUAGE_LINEAGE}
        lappend seen $id
        if {[dict get $current status] ne "active"} {_policy_error LANGUAGE_INACTIVE}
        set parent [dict get $current parent]
        if {$parent eq ""} {break}
        set current [::tclmesh::language describe $parent]
    }
    if {[dict get $language holder] ne $actor} {_policy_error HOLDER_MISMATCH}
    if {"release:$policy_id" ni [dict get $language commands]} {_policy_error COMMAND_NOT_GRANTED}
    if {[dict get $policy ${role}_capability] ni [dict get $language capabilities]} {_policy_error CAPABILITY_NOT_GRANTED}
    switch $role {
        request {set members [dict get $policy requesters]}
        contribute {set members [dict get $policy holders]}
        combine {set members [dict get $policy combiners]}
        recover {set members [dict get $policy recoverers]}
    }
    if {$actor ni $members} {_policy_error ACTOR_NOT_ALLOWED}
    set approved {}
    foreach required [::list [dict get $policy context] [dict get $language context]] {
        dict for {key value} $required {
            if {[dict exists $approved $key] && [dict get $approved $key] ne $value} {
                _policy_error CONTEXT_MISMATCH
            }
            dict set approved $key $value
        }
    }
    # Dictionary equality is independent of insertion order. Reject all fields
    # outside the policy/language union before persisting or invoking a backend.
    if {[dict size $context] != [dict size $approved]} {_policy_error CONTEXT_MISMATCH}
    dict for {key value} $approved {
        if {![dict exists $context $key] || [dict get $context $key] ne $value} {
            _policy_error CONTEXT_MISMATCH
        }
    }
    return [dict create language_id $language_id actor_id $actor generation [dict get $language generation]]
}

proc ::tclmesh::release::_request_policy {descriptor} {
    if {![dict exists $descriptor authorization] || [dict get $descriptor authorization] eq ""} {
        _policy_error AUTHORIZATION_REQUIRED
    }
    set authorization [dict get $descriptor authorization]
    set binding [_binding $descriptor]
    set app [dict get $binding application_id]
    set pin [::tclmesh::manifest active $app]
    if {[dict get $pin manifest_hash] ne [dict get $binding manifest_hash] ||
        [dict get $pin version] ne [dict get $binding manifest_version]} {_policy_error MANIFEST_CHANGED}
    set manifest [::tclmesh::manifest get $app [dict get $pin version]]
    if {[::tclmesh::manifest digest $manifest] ne [dict get $pin manifest_hash]} {_policy_error MANIFEST_MISMATCH}
    set policy_id [dict get $authorization policy_id]
    set policy [_validate_policy $manifest $policy_id [dict get $manifest ceremonies $policy_id]]
    foreach key {purpose holders profile} {
        if {[dict get $descriptor $key] ne [dict get $policy $key]} {_policy_error REQUEST_BINDING}
    }
    if {[dict get $descriptor threshold] != [dict get $policy quorum]} {_policy_error REQUEST_BINDING}
    set origin [dict get $authorization requester]
    _authorize [dict get $origin language_id] [dict get $origin actor_id] $policy_id $policy request [dict get $descriptor context]
    if {[dict exists $descriptor contribution_authority]} {
        dict for {holder receipt} [dict get $descriptor contribution_authority] {
            _authorize [dict get $receipt language_id] $holder $policy_id $policy contribute [dict get $descriptor context]
        }
    }
    return [::list $policy_id $policy]
}

proc ::tclmesh::release::_managed_guard {descriptor} {
    if {[dict exists $descriptor authorization] && [dict get $descriptor authorization] ne ""} {
        _policy_error AUTHORIZATION_REQUIRED
    }
}

proc ::tclmesh::release::request-authorized {language_id handle_id actor context} {
    set handle [::tclmesh::private::_require_handle $handle_id]
    set policy_id [_handle_policy $handle]
    if {$policy_id eq ""} {_policy_error AUTHORIZATION_REQUIRED}
    set binding [_binding $handle]
    set app [dict get $binding application_id]
    set pin [::tclmesh::manifest active $app]
    if {[dict get $pin manifest_hash] ne [dict get $binding manifest_hash] ||
        [dict get $pin version] ne [dict get $binding manifest_version]} {_policy_error MANIFEST_CHANGED}
    set manifest [::tclmesh::manifest get $app [dict get $pin version]]
    set policy [_validate_policy $manifest $policy_id [dict get $manifest ceremonies $policy_id]]
    if {[dict get $binding circuit_id] ne [dict get $policy circuit] ||
        [dict get $binding output_name] ne [dict get $policy output] ||
        [dict get $handle profile] ne [dict get $policy profile]} {_policy_error OUTPUT_BINDING}
    set requester [_authorize $language_id $actor $policy_id $policy request $context]
    return [_request $handle_id [dict get $policy purpose] [dict get $policy quorum] \
        [dict get $policy holders] $context [dict create policy_id $policy_id requester $requester]]
}

proc ::tclmesh::release::_transition_authority {language_id id actor role} {
    set descriptor [_require $id]
    lassign [_request_policy $descriptor] policy_id policy
    return [_authorize $language_id $actor $policy_id $policy $role [dict get $descriptor context]]
}
proc ::tclmesh::release::contribute-authorized {language_id id actor share} {
    set authority [_transition_authority $language_id $id $actor contribute]
    return [_contribute $id $actor $share $authority]
}
proc ::tclmesh::release::combine-authorized {language_id id actor} {
    _transition_authority $language_id $id $actor combine
    return [_combine $id]
}
proc ::tclmesh::release::recover-authorized {language_id id actor disposition {result {}}} {
    _transition_authority $language_id $id $actor recover
    return [_recover $id $disposition $result]
}
proc ::tclmesh::release::reject-authorized {language_id id actor {reason {}}} {
    _transition_authority $language_id $id $actor recover
    return [_terminal_transition $id {collecting quorum-reached} rejected [dict create reason $reason]]
}
proc ::tclmesh::release::expire-authorized {language_id id actor {reason {}}} {
    _transition_authority $language_id $id $actor recover
    return [_terminal_transition $id {collecting quorum-reached} expired [dict create reason $reason]]
}
