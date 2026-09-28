namespace eval ::tclmesh::effect {
    variable ledger {}
    variable idempotency {}
    variable next_id 0
    variable store {}

    namespace export propose authorize execute recover get list reset use-store
    namespace ensemble create
}

proc ::tclmesh::effect::_commit {
    candidate_ledger
    candidate_idempotency
    candidate_next_id
} {
    variable ledger
    variable idempotency
    variable next_id
    variable store

    if {$store ne ""} {
        ::tclmesh::store put $store effect.registry [dict create             ledger $candidate_ledger             idempotency $candidate_idempotency             next_id $candidate_next_id]
    }

    set ledger $candidate_ledger
    set idempotency $candidate_idempotency
    set next_id $candidate_next_id
}

proc ::tclmesh::effect::use-store {store_id} {
    variable ledger
    variable idempotency
    variable next_id
    variable store

    if {$store_id eq ""} {
        set store {}
        return {}
    }

    ::tclmesh::store describe $store_id

    if {[::tclmesh::store exists $store_id effect.registry]} {
        set state [::tclmesh::store get $store_id effect.registry]
        foreach key {ledger idempotency next_id} {
            if {![dict exists $state $key]} {
                return -code error                     -errorcode [::list TCLMESH EFFECT STORE INVALID_STATE $key]                     "effect registry store is missing '$key'"
            }
        }
        set candidate_ledger [dict get $state ledger]
        set candidate_idempotency [dict get $state idempotency]
        set candidate_next_id [dict get $state next_id]
    } else {
        set candidate_ledger $ledger
        set candidate_idempotency $idempotency
        set candidate_next_id $next_id
        ::tclmesh::store put $store_id effect.registry [dict create             ledger $candidate_ledger             idempotency $candidate_idempotency             next_id $candidate_next_id]
    }

    set ledger $candidate_ledger
    set idempotency $candidate_idempotency
    set next_id $candidate_next_id
    set store $store_id
    return $store
}

proc ::tclmesh::effect::_require {effect_id} {
    variable ledger

    if {![dict exists $ledger $effect_id]} {
        return -code error             -errorcode [::list TCLMESH EFFECT NOT_FOUND $effect_id]             "effect '$effect_id' does not exist"
    }

    return [dict get $ledger $effect_id]
}

proc ::tclmesh::effect::_fingerprint {effect context} {
    package require sha256

    set canonical [::list         effect [::tclmesh::manifest::_canonical_node $effect]         context [::tclmesh::manifest::_canonical_node $context]]

    set bytes [encoding convertto utf-8 $canonical]
    return [string tolower [::sha2::sha256 -hex -- $bytes]]
}

proc ::tclmesh::effect::reset {} {
    _commit {} {} 0
}

proc ::tclmesh::effect::propose {effect context} {
    variable ledger
    variable idempotency
    variable next_id

    if {![dict exists $effect type] || [dict get $effect type] eq ""} {
        return -code error             -errorcode {TCLMESH EFFECT INVALID_TYPE}             "effect proposal requires a nonempty type"
    }

    foreach key {manifest_hash action actor_id} {
        if {![dict exists $context $key] || [dict get $context $key] eq ""} {
            return -code error                 -errorcode [::list TCLMESH EFFECT MISSING_CONTEXT $key]                 "effect proposal requires context '$key'"
        }
    }

    set fingerprint [_fingerprint $effect $context]
    set key {}
    if {[dict exists $context idempotency_key]} {
        set key [dict get $context idempotency_key]
    }

    if {$key ne "" && [dict exists $idempotency $key]} {
        set existing_id [dict get $idempotency $key]
        set existing [_require $existing_id]

        if {[dict get $existing fingerprint] ne $fingerprint} {
            return -code error                 -errorcode [::list TCLMESH EFFECT IDEMPOTENCY_CONFLICT $key]                 "idempotency key '$key' is already bound to a different effect"
        }

        return $existing
    }

    set candidate_next_id [expr {$next_id + 1}]
    set id "effect:$candidate_next_id"
    set descriptor [dict create         id $id         status proposed         effect $effect         context $context         fingerprint $fingerprint         attempts 0         recoveries 0         result {}]

    set candidate_ledger $ledger
    set candidate_idempotency $idempotency
    dict set candidate_ledger $id $descriptor
    if {$key ne ""} {
        dict set candidate_idempotency $key $id
    }

    _commit $candidate_ledger $candidate_idempotency $candidate_next_id
    return $descriptor
}

proc ::tclmesh::effect::authorize {effect_id decision} {
    variable ledger
    variable idempotency
    variable next_id

    set descriptor [_require $effect_id]
    if {[dict get $descriptor status] ne "proposed"} {
        return -code error             -errorcode [::list TCLMESH EFFECT INVALID_STATE $effect_id]             "effect '$effect_id' is not awaiting authorization"
    }

    switch -- $decision {
        permit {
            dict set descriptor status authorized
        }
        deny {
            dict set descriptor status denied
        }
        default {
            return -code error                 -errorcode {TCLMESH EFFECT INVALID_DECISION}                 "effect authorization decision must be permit or deny"
        }
    }

    set candidate_ledger $ledger
    dict set candidate_ledger $effect_id $descriptor
    _commit $candidate_ledger $idempotency $next_id
    return $descriptor
}

proc ::tclmesh::effect::execute {effect_id adapter} {
    variable ledger
    variable idempotency
    variable next_id

    set descriptor [_require $effect_id]
    if {[dict get $descriptor status] eq "succeeded"} {
        return $descriptor
    }

    if {[dict get $descriptor status] ne "authorized"} {
        return -code error             -errorcode [::list TCLMESH EFFECT INVALID_STATE $effect_id]             "effect '$effect_id' is not authorized for execution"
    }

    dict set descriptor status executing
    dict incr descriptor attempts
    set candidate_ledger $ledger
    dict set candidate_ledger $effect_id $descriptor
    _commit $candidate_ledger $idempotency $next_id

    set code [catch {
        {*}$adapter execute             [dict get $descriptor effect]             [dict get $descriptor context]
    } result options]

    if {$code} {
        set descriptor [_require $effect_id]
        dict set descriptor status failed
        dict set descriptor result [dict create             class execution             message $result]

        set candidate_ledger $ledger
        dict set candidate_ledger $effect_id $descriptor
        _commit $candidate_ledger $idempotency $next_id

        return -options $options             -errorcode [::list TCLMESH EFFECT EXECUTION FAILED $effect_id]             $result
    }

    set descriptor [_require $effect_id]
    dict set descriptor status succeeded
    dict set descriptor result $result

    set candidate_ledger $ledger
    dict set candidate_ledger $effect_id $descriptor
    _commit $candidate_ledger $idempotency $next_id
    return $descriptor
}

proc ::tclmesh::effect::recover {effect_id disposition {result {}}} {
    variable ledger
    variable idempotency
    variable next_id

    set descriptor [_require $effect_id]
    set status [dict get $descriptor status]

    if {$status ni {executing failed}} {
        return -code error             -errorcode [::list TCLMESH EFFECT RECOVERY INVALID_STATE $effect_id]             "effect '$effect_id' is not in a recoverable state"
    }

    switch -- $disposition {
        retry {
            set context [dict get $descriptor context]
            if {![dict exists $context idempotency_key] ||
                [dict get $context idempotency_key] eq ""} {
                return -code error                     -errorcode [::list TCLMESH EFFECT RECOVERY IDEMPOTENCY_REQUIRED $effect_id]                     "retry recovery requires an idempotency key"
            }
            dict set descriptor status authorized
            dict set descriptor result {}
            dict incr descriptor recoveries
        }
        succeeded {
            dict set descriptor status succeeded
            dict set descriptor result $result
            dict incr descriptor recoveries
        }
        failed {
            dict set descriptor status failed
            dict set descriptor result $result
            dict incr descriptor recoveries
        }
        default {
            return -code error                 -errorcode [::list TCLMESH EFFECT RECOVERY INVALID_DISPOSITION $disposition]                 "recovery disposition must be retry, succeeded, or failed"
        }
    }

    set candidate_ledger $ledger
    dict set candidate_ledger $effect_id $descriptor
    _commit $candidate_ledger $idempotency $next_id
    return $descriptor
}

proc ::tclmesh::effect::get {effect_id} {
    return [_require $effect_id]
}

proc ::tclmesh::effect::list {} {
    variable ledger
    return [lsort -dictionary [dict keys $ledger]]
}
