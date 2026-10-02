namespace eval ::tclmesh::release {
    variable requests {}
    variable next_id 0
    variable store {}

    namespace export         use-store request contribute reject expire combine recover get list
    namespace ensemble create
}

proc ::tclmesh::release::_commit {candidate_requests candidate_next_id} {
    variable requests
    variable next_id
    variable store

    if {$store ne ""} {
        ::tclmesh::store put $store release.registry [dict create             requests $candidate_requests             next_id $candidate_next_id]
    }

    set requests $candidate_requests
    set next_id $candidate_next_id
}

proc ::tclmesh::release::use-store {store_id} {
    variable requests
    variable next_id
    variable store

    if {$store_id eq ""} {
        ::tclmesh::private::_use_handle_store {}
        set store {}
        return {}
    }

    ::tclmesh::store describe $store_id

    if {[::tclmesh::store exists $store_id release.registry]} {
        set state [::tclmesh::store get $store_id release.registry]
        foreach key {requests next_id} {
            if {![dict exists $state $key]} {
                return -code error                     -errorcode [::list TCLMESH RELEASE STORE INVALID_STATE $key]                     "release registry store is missing '$key'"
            }
        }

        set candidate_requests [dict get $state requests]
        set candidate_next_id [dict get $state next_id]
        if {[dict size $candidate_requests] > 0 &&
            ![::tclmesh::store exists $store_id private.handles]} {
            return -code error -errorcode {TCLMESH RELEASE STORE HANDLE_STATE_REQUIRED}                 "persisted releases require a durable private handle registry"
        }
    } else {
        set candidate_requests $requests
        set candidate_next_id $next_id
        ::tclmesh::store put $store_id release.registry [dict create             requests $candidate_requests             next_id $candidate_next_id]
    }

    ::tclmesh::private::_use_handle_store $store_id
    set requests $candidate_requests
    set next_id $candidate_next_id
    set store $store_id
    return $store
}

proc ::tclmesh::release::_require {id} {
    variable requests

    if {![dict exists $requests $id]} {
        return -code error             -errorcode [::list TCLMESH RELEASE NOT_FOUND $id]             "release request '$id' does not exist"
    }

    return [dict get $requests $id]
}

proc ::tclmesh::release::_unique {values} {
    return [lsort -unique $values]
}

proc ::tclmesh::release::_binding {descriptor} {
    if {[dict exists $descriptor binding]} {
        return [dict get $descriptor binding]
    }
    return {}
}

proc ::tclmesh::release::_assert_bound_handle {descriptor} {
    set handle_id [dict get $descriptor handle]
    set handle [::tclmesh::private::_require_handle $handle_id]

    foreach key {profile backend type} {
        if {[dict get $handle $key] ne [dict get $descriptor $key]} {
            return -code error                 -errorcode [::list TCLMESH RELEASE HANDLE_BINDING_MISMATCH                     [dict get $descriptor id] $key]                 "release request handle binding changed for '$key'"
        }
    }

    if {[_binding $handle] ne [_binding $descriptor]} {
        return -code error \
            -errorcode [::list TCLMESH RELEASE HANDLE_BINDING_MISMATCH \
                [dict get $descriptor id] binding] \
            "release circuit/output binding changed"
    }
    return $handle
}

proc ::tclmesh::release::request {handle_id purpose threshold holders {context {}}} {
    set handle [::tclmesh::private::_require_handle $handle_id]
    if {[_handle_policy $handle] ne ""} {_policy_error AUTHORIZATION_REQUIRED}
    return [_request $handle_id $purpose $threshold $holders $context {}]
}

proc ::tclmesh::release::_request {handle_id purpose threshold holders context authorization} {
    variable requests
    variable next_id

    if {$purpose eq ""} {
        return -code error             -errorcode {TCLMESH RELEASE EMPTY_PURPOSE}             "release purpose must not be empty"
    }

    if {![string is integer -strict $threshold] || $threshold <= 0} {
        return -code error             -errorcode {TCLMESH RELEASE INVALID_THRESHOLD}             "release threshold must be a positive integer"
    }

    set unique_holders [_unique $holders]
    if {[llength $unique_holders] == 0} {
        return -code error             -errorcode {TCLMESH RELEASE EMPTY_HOLDERS}             "release holder set must not be empty"
    }
    if {[llength $unique_holders] != [llength $holders]} {
        return -code error             -errorcode {TCLMESH RELEASE DUPLICATE_HOLDER}             "release holder set must not contain duplicates"
    }
    if {$threshold > [llength $unique_holders]} {
        return -code error             -errorcode {TCLMESH RELEASE THRESHOLD_EXCEEDS_HOLDERS}             "release threshold exceeds holder count"
    }

    set handle [::tclmesh::private::_require_handle $handle_id]
    set profile [dict get $handle profile]
    set backend [dict get $handle backend]
    set type [dict get $handle type]

    set backend_descriptor [::tclmesh::private::backend::describe $backend]
    if {"threshold-release" ni [dict get $backend_descriptor capabilities]} {
        return -code error             -errorcode [::list TCLMESH RELEASE BACKEND_UNSUPPORTED $backend]             "backend '$backend' does not support threshold release"
    }

    set candidate_next_id [expr {$next_id + 1}]
    set id "release:$candidate_next_id"

    set descriptor [dict create         id $id         status collecting         handle $handle_id         profile $profile         backend $backend         type $type         purpose $purpose         threshold $threshold         holders $unique_holders         contributions {}         context $context         binding [_binding $handle]         attempts 0         recoveries 0         result {}]

    dict set descriptor authorization $authorization
    dict set descriptor contribution_authority {}
    set candidate_requests $requests
    dict set candidate_requests $id $descriptor
    _commit $candidate_requests $candidate_next_id
    return $descriptor
}

proc ::tclmesh::release::contribute {id holder share} {
    _managed_guard [_require $id]
    return [_contribute $id $holder $share {}]
}

proc ::tclmesh::release::_contribute {id holder share authority} {
    variable requests
    variable next_id

    set descriptor [_require $id]
    if {[dict get $descriptor status] ne "collecting"} {
        return -code error             -errorcode [::list TCLMESH RELEASE INVALID_STATE $id]             "release request '$id' is not collecting contributions"
    }

    if {$holder ni [dict get $descriptor holders]} {
        return -code error             -errorcode [::list TCLMESH RELEASE HOLDER_NOT_AUTHORIZED $id $holder]             "holder '$holder' is not authorized for release request '$id'"
    }

    if {[dict exists $descriptor contributions $holder]} {
        return -code error             -errorcode [::list TCLMESH RELEASE DUPLICATE_CONTRIBUTION $id $holder]             "holder '$holder' has already contributed"
    }

    if {$share eq ""} {
        return -code error             -errorcode [::list TCLMESH RELEASE EMPTY_CONTRIBUTION $id $holder]             "release contribution must not be empty"
    }

    dict set descriptor contributions $holder $share
    dict set descriptor contribution_authority $holder $authority

    if {[dict size [dict get $descriptor contributions]] >=
        [dict get $descriptor threshold]} {
        dict set descriptor status quorum-reached
    }

    set candidate_requests $requests
    dict set candidate_requests $id $descriptor
    _commit $candidate_requests $next_id
    return $descriptor
}

proc ::tclmesh::release::_terminal_transition {id expected target {result {}}} {
    variable requests
    variable next_id

    set descriptor [_require $id]
    if {[dict get $descriptor status] ni $expected} {
        return -code error             -errorcode [::list TCLMESH RELEASE INVALID_STATE $id]             "release request '$id' cannot transition to '$target'"
    }

    dict set descriptor status $target
    if {$result ne ""} {
        dict set descriptor result $result
    }

    set candidate_requests $requests
    dict set candidate_requests $id $descriptor
    _commit $candidate_requests $next_id
    return $descriptor
}

proc ::tclmesh::release::reject {id {reason {}}} {
    _managed_guard [_require $id]
    return [_terminal_transition         $id         {collecting quorum-reached}         rejected         [dict create reason $reason]]
}

proc ::tclmesh::release::expire {id {reason {}}} {
    _managed_guard [_require $id]
    return [_terminal_transition         $id         {collecting quorum-reached}         expired         [dict create reason $reason]]
}

proc ::tclmesh::release::combine {id} {
    _managed_guard [_require $id]
    return [_combine $id]
}

proc ::tclmesh::release::_combine {id} {
    variable requests
    variable next_id

    set descriptor [_require $id]
    if {[dict get $descriptor status] ne "quorum-reached"} {
        return -code error             -errorcode [::list TCLMESH RELEASE INVALID_STATE $id]             "release request '$id' has not reached quorum"
    }

    set handle [_assert_bound_handle $descriptor]
    foreach key {authorization contribution_authority} {
        if {![dict exists $descriptor $key]} {dict set descriptor $key {}}
    }
    set backend_descriptor [::tclmesh::private::backend::describe         [dict get $descriptor backend]]
    set command [dict get $backend_descriptor command]
    set profile [::tclmesh::private::profile::describe         [dict get $descriptor profile]]

    dict set descriptor status combining
    dict incr descriptor attempts

    set candidate_requests $requests
    dict set candidate_requests $id $descriptor
    _commit $candidate_requests $next_id

    set code [catch {
        {*}$command combine-release             $profile             [dict get $descriptor type]             [dict get $handle token]             [dict get $descriptor contributions]             [dict create                 purpose [dict get $descriptor purpose]                 context [dict get $descriptor context]                 release_id $id binding [_binding $descriptor] authorization [dict get $descriptor authorization] contribution_authority [dict get $descriptor contribution_authority]]
    } result options]

    if {$code} {
        set descriptor [_require $id]
        dict set descriptor status failed
        dict set descriptor result [dict create             class combination             message $result]

        set candidate_requests $requests
        dict set candidate_requests $id $descriptor
        _commit $candidate_requests $next_id

        return -options $options             -errorcode [::list TCLMESH RELEASE COMBINE_FAILED $id]             $result
    }

    set descriptor [_require $id]
    dict set descriptor status released
    dict set descriptor result $result

    set candidate_requests $requests
    dict set candidate_requests $id $descriptor
    _commit $candidate_requests $next_id
    return $descriptor
}

proc ::tclmesh::release::recover {id disposition {result {}}} {
    _managed_guard [_require $id]
    return [_recover $id $disposition $result]
}

proc ::tclmesh::release::_recover {id disposition {result {}}} {
    variable requests
    variable next_id

    set descriptor [_require $id]
    if {[dict get $descriptor status] ni {combining failed}} {
        return -code error             -errorcode [::list TCLMESH RELEASE RECOVERY INVALID_STATE $id]             "release request '$id' is not in a recoverable state"
    }

    set backend_descriptor [::tclmesh::private::backend::describe         [dict get $descriptor backend]]

    switch -- $disposition {
        retry {
            if {"idempotent-release" ni
                [dict get $backend_descriptor capabilities]} {
                return -code error                     -errorcode [::list TCLMESH RELEASE RECOVERY IDEMPOTENCY_REQUIRED $id]                     "release retry requires an idempotent-release backend"
            }
            _assert_bound_handle $descriptor
            dict set descriptor status quorum-reached
            dict set descriptor result {}
            dict incr descriptor recoveries
        }
        released {
            dict set descriptor status released
            dict set descriptor result $result
            dict incr descriptor recoveries
        }
        failed {
            dict set descriptor status failed
            dict set descriptor result $result
            dict incr descriptor recoveries
        }
        default {
            return -code error                 -errorcode [::list TCLMESH RELEASE RECOVERY INVALID_DISPOSITION                     $disposition]                 "release recovery disposition must be retry, released, or failed"
        }
    }

    set candidate_requests $requests
    dict set candidate_requests $id $descriptor
    _commit $candidate_requests $next_id
    return $descriptor
}

proc ::tclmesh::release::get {id} {
    return [_require $id]
}

proc ::tclmesh::release::list {} {
    variable requests
    return [lsort -dictionary [dict keys $requests]]
}
