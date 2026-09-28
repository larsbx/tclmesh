namespace eval ::tclmesh::effect {
    variable ledger {}
    variable idempotency {}
    variable next_id 0

    namespace export propose authorize execute get list reset
    namespace ensemble create
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
    variable ledger
    variable idempotency
    variable next_id

    set ledger {}
    set idempotency {}
    set next_id 0
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

    incr next_id
    set id "effect:$next_id"
    set descriptor [dict create         id $id         status proposed         effect $effect         context $context         fingerprint $fingerprint         result {}]

    dict set ledger $id $descriptor
    if {$key ne ""} {
        dict set idempotency $key $id
    }

    return $descriptor
}

proc ::tclmesh::effect::authorize {effect_id decision} {
    variable ledger

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

    dict set ledger $effect_id $descriptor
    return $descriptor
}

proc ::tclmesh::effect::execute {effect_id adapter} {
    variable ledger

    set descriptor [_require $effect_id]
    if {[dict get $descriptor status] eq "succeeded"} {
        return $descriptor
    }

    if {[dict get $descriptor status] ne "authorized"} {
        return -code error             -errorcode [::list TCLMESH EFFECT INVALID_STATE $effect_id]             "effect '$effect_id' is not authorized for execution"
    }

    dict set descriptor status executing
    dict set ledger $effect_id $descriptor

    set code [catch {
        {*}$adapter execute             [dict get $descriptor effect]             [dict get $descriptor context]
    } result options]

    if {$code} {
        dict set descriptor status failed
        dict set descriptor result [dict create             class execution             message $result]
        dict set ledger $effect_id $descriptor

        return -options $options             -errorcode [::list TCLMESH EFFECT EXECUTION FAILED $effect_id]             $result
    }

    dict set descriptor status succeeded
    dict set descriptor result $result
    dict set ledger $effect_id $descriptor
    return $descriptor
}

proc ::tclmesh::effect::get {effect_id} {
    return [_require $effect_id]
}

proc ::tclmesh::effect::list {} {
    variable ledger
    return [lsort -dictionary [dict keys $ledger]]
}
