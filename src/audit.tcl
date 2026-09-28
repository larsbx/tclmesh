namespace eval ::tclmesh::audit {
    variable events {}
    variable next_id 0
    variable store {}

    namespace export use-store append get list reset
    namespace ensemble create
}

proc ::tclmesh::audit::_persist {} {
    variable events
    variable next_id
    variable store

    if {$store ne ""} {
        ::tclmesh::store put $store audit.stream [dict create             events $events             next_id $next_id]
    }
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
    set store $store_id

    if {[::tclmesh::store exists $store audit.stream]} {
        set state [::tclmesh::store get $store audit.stream]
        foreach key {events next_id} {
            if {![dict exists $state $key]} {
                return -code error                     -errorcode [::list TCLMESH AUDIT STORE INVALID_STATE $key]                     "audit store is missing '$key'"
            }
        }
        set events [dict get $state events]
        set next_id [dict get $state next_id]
    } else {
        _persist
    }

    return $store
}

proc ::tclmesh::audit::reset {} {
    variable events
    variable next_id

    set events {}
    set next_id 0
    _persist
}

proc ::tclmesh::audit::append {type data {context {}}} {
    variable events
    variable next_id

    if {$type eq ""} {
        return -code error             -errorcode {TCLMESH AUDIT EMPTY_TYPE}             "audit event type must not be empty"
    }

    incr next_id
    set id "audit:$next_id"

    set event [dict create         id $id         sequence $next_id         type $type         data $data         context $context]

    dict set events $id $event
    _persist
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
