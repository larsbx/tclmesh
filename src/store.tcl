namespace eval ::tclmesh::store {
    variable stores {}
    variable next_id 0

    namespace export create get put exists keys delete describe
    namespace ensemble create
}

proc ::tclmesh::store::_require {id} {
    variable stores
    if {![dict exists $stores $id]} {
        return -code error             -errorcode [::list TCLMESH STORE NOT_FOUND $id]             "store '$id' does not exist"
    }
    return [dict get $stores $id]
}

proc ::tclmesh::store::_persist {id descriptor} {
    variable stores

    if {[dict get $descriptor type] eq "file"} {
        set path [dict get $descriptor path]
        set dir [file dirname $path]
        if {![file isdirectory $dir]} {
            file mkdir $dir
        }

        set tmp [file join $dir ".[file tail $path].[pid].tmp"]
        set channel [open $tmp {WRONLY CREAT TRUNC}]
        try {
            chan configure $channel -encoding utf-8 -translation lf
            puts -nonewline $channel [dict get $descriptor data]
            flush $channel
        } finally {
            close $channel
        }

        file rename -force $tmp $path
    }

    dict set stores $id $descriptor
}

proc ::tclmesh::store::create {type args} {
    variable stores
    variable next_id

    if {$type ni {memory file}} {
        return -code error             -errorcode [::list TCLMESH STORE INVALID_TYPE $type]             "store type must be memory or file"
    }

    incr next_id
    set id "store:$next_id"
    set descriptor [dict create type $type data {}]

    if {$type eq "file"} {
        if {[llength $args] != 1 || [lindex $args 0] eq ""} {
            return -code error                 -errorcode {TCLMESH STORE FILE PATH_REQUIRED}                 "file store requires exactly one nonempty path"
        }

        set path [file normalize [lindex $args 0]]
        dict set descriptor path $path

        if {[file exists $path]} {
            set channel [open $path RDONLY]
            try {
                chan configure $channel -encoding utf-8 -translation lf
                set data [read $channel]
            } finally {
                close $channel
            }

            if {$data ne ""} {
                if {[catch {dict size $data}]} {
                    return -code error                         -errorcode [::list TCLMESH STORE CORRUPT $path]                         "file store '$path' does not contain a valid Tcl dictionary"
                }
                dict set descriptor data $data
            }
        }
    } elseif {[llength $args] != 0} {
        return -code error             -errorcode {TCLMESH STORE MEMORY UNEXPECTED_ARGUMENTS}             "memory store takes no additional arguments"
    }

    dict set stores $id $descriptor
    return $id
}

proc ::tclmesh::store::get {id key {default __TCLMESH_NO_DEFAULT__}} {
    set descriptor [_require $id]
    set data [dict get $descriptor data]

    if {[dict exists $data $key]} {
        return [dict get $data $key]
    }

    if {$default ne "__TCLMESH_NO_DEFAULT__"} {
        return $default
    }

    return -code error         -errorcode [::list TCLMESH STORE KEY_NOT_FOUND $id $key]         "store '$id' does not contain key '$key'"
}

proc ::tclmesh::store::put {id key value} {
    set descriptor [_require $id]
    set data [dict get $descriptor data]
    dict set data $key $value
    dict set descriptor data $data
    _persist $id $descriptor
    return $value
}

proc ::tclmesh::store::exists {id key} {
    set descriptor [_require $id]
    return [dict exists [dict get $descriptor data] $key]
}

proc ::tclmesh::store::keys {id} {
    set descriptor [_require $id]
    return [lsort -dictionary [dict keys [dict get $descriptor data]]]
}

proc ::tclmesh::store::delete {id key} {
    set descriptor [_require $id]
    set data [dict get $descriptor data]

    if {[dict exists $data $key]} {
        dict unset data $key
        dict set descriptor data $data
        _persist $id $descriptor
    }

    return
}

proc ::tclmesh::store::describe {id} {
    set descriptor [_require $id]
    dict unset descriptor data
    return $descriptor
}
