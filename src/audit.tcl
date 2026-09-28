namespace eval ::tclmesh::audit {
    variable events {}
    variable next_id 0
    variable store {}

    namespace export use-store append get list reset
    namespace ensemble create
}

proc ::tclmesh::audit::_commit {candidate_events candidate_next_id} {
    variable events
    variable next_id
    variable store

    if {$store ne ""} {
        ::tclmesh::store put $store audit.stream [dict create             events $candidate_events             next_id $candidate_next_id]
    }

    set events $candidate_events
    set next_id $candidate_next_id
}

proc ::tclmesh::audit::use-store {store_id} {
    variable events
    variable next_id
    variable store

    if {$store_id eq ""} {
        set store {}
        return {}
    }

    ::tclmesh::store describe $store_id

    if {[::tclmesh::store exists $store_id audit.stream]} {
        set state [::tclmesh::store get $store_id audit.stream]
        foreach key {events next_id} {
            if {![dict exists $state $key]} {
                return -code error                     -errorcode [::list TCLMESH AUDIT STORE INVALID_STATE $key]                     "audit store is missing '$key'"
            }
        }
        set candidate_events [dict get $state events]
        set candidate_next_id [dict get $state next_id]
    } else {
        set candidate_events $events
        set candidate_next_id $next_id
        ::tclmesh::store put $store_id audit.stream [dict create             events $candidate_events             next_id $candidate_next_id]
    }

    set events $candidate_events
    set next_id $candidate_next_id
    set store $store_id
    return $store
}

proc ::tclmesh::audit::reset {} {
    _commit {} 0
}

proc ::tclmesh::audit::append {type data {context {}}} {
    variable events
    variable next_id

    if {$type eq ""} {
        return -code error             -errorcode {TCLMESH AUDIT EMPTY_TYPE}             "audit event type must not be empty"
    }

    set candidate_next_id [expr {$next_id + 1}]
    set id "audit:$candidate_next_id"

    set event [dict create         id $id         sequence $candidate_next_id         type $type         data $data         context $context]

    set candidate_events $events
    dict set candidate_events $id $event
    _commit $candidate_events $candidate_next_id
    return $event
}

proc ::tclmesh::audit::get {id} {
    variable events

    if {![dict exists $events $id]} {
        return -code error             -errorcode [::list TCLMESH AUDIT NOT_FOUND $id]             "audit event '$id' does not exist"
    }

    return [dict get $events $id]
}

proc ::tclmesh::audit::list {} {
    variable events
    return [lsort -dictionary [dict keys $events]]
}
