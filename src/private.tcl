namespace eval ::tclmesh::private {
    variable allowed_ops {
        constant input
        add subtract multiply negate
        equal less-than less-or-equal greater-than greater-or-equal
        and or not select
        rotate reduce-sum lookup polynomial clamp
    }

    variable profiles {}
    variable backends {}
    variable handles {}
    variable next_handle 0
    variable handle_store {}

    namespace export         node circuit validate canonical digest encrypt publish import range-check admit evaluate evaluate-bound decrypt differential         profile backend handle
}

namespace eval ::tclmesh::private::profile {
    namespace export define describe list
    namespace ensemble create
}

namespace eval ::tclmesh::private::backend {
    namespace export register describe list
    namespace ensemble create
}

namespace eval ::tclmesh::private::handle {
    namespace export describe destroy list
    namespace ensemble create
}

proc ::tclmesh::private::node {op args} {
    variable allowed_ops

    if {$op ni $allowed_ops} {
        return -code error             -errorcode [::list TCLMESH PRIVATE UNKNOWN_NODE $op]             "unsupported private-circuit operation '$op'"
    }

    return [linsert $args 0 $op]
}

proc ::tclmesh::private::circuit {name inputs outputs nodes {metadata {}}} {
    return [dict create         name $name         inputs $inputs         outputs $outputs         nodes $nodes         metadata $metadata]
}

proc ::tclmesh::private::_node_refs {node} {
    set op [lindex $node 0]
    switch -- $op {
        input -
        constant {
            return {}
        }
        negate -
        not -
        rotate -
        reduce-sum -
        polynomial -
        clamp {
            return [::list [lindex $node 1]]
        }
        add -
        subtract -
        multiply -
        equal -
        less-than -
        less-or-equal -
        greater-than -
        greater-or-equal -
        and -
        or -
        lookup {
            return [::list [lindex $node 1] [lindex $node 2]]
        }
        select {
            return [::list                 [lindex $node 1]                 [lindex $node 2]                 [lindex $node 3]]
        }
        default {
            return {}
        }
    }
}

proc ::tclmesh::private::_validate_node {circuit id visiting visitedVar} {
    upvar 1 $visitedVar visited

    if {[dict exists $visited $id]} {
        return
    }
    if {[dict exists $visiting $id]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE CIRCUIT CYCLE $id]             "private circuit contains a dependency cycle at '$id'"
    }

    set nodes [dict get $circuit nodes]
    if {![dict exists $nodes $id]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE CIRCUIT UNKNOWN_REFERENCE $id]             "private circuit references unknown node '$id'"
    }

    dict set visiting $id 1
    set node [dict get $nodes $id]
    set op [lindex $node 0]

    switch -- $op {
        input {
            if {[llength $node] != 2 ||
                ![dict exists $circuit inputs [lindex $node 1]]} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT INVALID_INPUT_NODE $id]                     "input node '$id' must reference one declared input"
            }
        }
        constant {
            if {[llength $node] != 2} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT INVALID_CONSTANT $id]                     "constant node '$id' requires exactly one value"
            }
        }
        negate -
        not -
        reduce-sum {
            if {[llength $node] != 2} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT INVALID_ARITY $id]                     "node '$id' has invalid arity"
            }
        }
        rotate {
            if {[llength $node] != 3} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT INVALID_ARITY $id]                     "rotate node '$id' requires an input and offset"
            }
        }
        clamp {
            lassign $node - - lo hi
            if {[llength $node] != 4 || ![::tclmesh::range::_int $lo] ||
                ![::tclmesh::range::_int $hi] || $lo > $hi} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT INVALID_CLAMP $id]                     "clamp node '$id' requires an input and canonical bounds lo <= hi"
            }
        }
        polynomial {
            if {[llength $node] != 3} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT INVALID_ARITY $id]                     "polynomial node '$id' requires an input and coefficients"
            }
        }
        add -
        subtract -
        multiply -
        equal -
        less-than -
        less-or-equal -
        greater-than -
        greater-or-equal -
        and -
        or -
        lookup {
            if {[llength $node] != 3} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT INVALID_ARITY $id]                     "node '$id' requires two operands"
            }
        }
        select {
            if {[llength $node] != 4} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT INVALID_ARITY $id]                     "select node '$id' requires condition, true, and false operands"
            }
        }
        default {
            return -code error                 -errorcode [::list TCLMESH PRIVATE UNKNOWN_NODE $id]                 "node '$id' uses unsupported operation '$op'"
        }
    }

    foreach ref [_node_refs $node] {
        _validate_node $circuit $ref $visiting visited
    }

    dict unset visiting $id
    dict set visited $id 1
}

proc ::tclmesh::private::validate {circuit} {
    variable allowed_ops

    foreach key {name inputs outputs nodes metadata} {
        if {![dict exists $circuit $key]} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE CIRCUIT MISSING $key]                 "private circuit is missing required field '$key'"
        }
    }

    if {[dict get $circuit name] eq ""} {
        return -code error             -errorcode {TCLMESH PRIVATE CIRCUIT EMPTY_NAME}             "private circuit name must not be empty"
    }

    set visiting {}
    set visited {}
    dict for {id node} [dict get $circuit nodes] {
        if {[llength $node] == 0 ||
            [lindex $node 0] ni $allowed_ops} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE UNKNOWN_NODE $id]                 "node '$id' uses unsupported operation '[lindex $node 0]'"
        }
        _validate_node $circuit $id $visiting visited
    }

    if {[dict exists $circuit metadata output_nodes]} {
        set output_nodes [dict get $circuit metadata output_nodes]
        dict for {name descriptor} [dict get $circuit outputs] {
            if {![dict exists $output_nodes $name]} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT MISSING_OUTPUT_NODE $name]                     "output '$name' has no output-node mapping"
            }
            set node_id [dict get $output_nodes $name]
            if {![dict exists [dict get $circuit nodes] $node_id]} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE CIRCUIT UNKNOWN_OUTPUT_NODE $name $node_id]                     "output '$name' references unknown node '$node_id'"
            }
        }
    }

    return $circuit
}

# Canonical identity is schema-directed: named maps are sorted, while each
# type descriptor and circuit operation remains an ordered sequence.
proc ::tclmesh::private::canonical {circuit} {
    set circuit [validate $circuit]
    set result {}
    foreach key [lsort -dictionary [dict keys $circuit]] {
        set value [dict get $circuit $key]
        switch -- $key {
            inputs - outputs - nodes {
                set value [::tclmesh::manifest::_canonical_sequence_map $value]
            }
            metadata {
                set metadata {}
                foreach name [lsort -dictionary [dict keys $value]] {
                    set item [dict get $value $name]
                    if {$name in {output_nodes packing}} {
                        set item [::tclmesh::manifest::_canonical_scalar_map $item]
                    }
                    lappend metadata $name $item
                }
                set value $metadata
            }
        }
        lappend result $key $value
    }
    return $result
}

proc ::tclmesh::private::digest {circuit} {
    package require sha256
    set bytes [encoding convertto utf-8 [::list tclmesh-private-circuit-v1 [canonical $circuit]]]
    return [string tolower [::sha2::sha256 -hex -- $bytes]]
}

proc ::tclmesh::private::backend::register {name command {capabilities {}}} {
    variable ::tclmesh::private::backends

    if {$name eq ""} {
        return -code error             -errorcode {TCLMESH PRIVATE BACKEND EMPTY_NAME}             "backend name must not be empty"
    }
    if {[dict exists $backends $name]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE BACKEND ALREADY_REGISTERED $name]             "backend '$name' is already registered"
    }

    set prefix [lindex $command 0]
    if {$prefix eq "" ||
        [uplevel #0 [::list namespace which -command $prefix]] eq ""} {
        return -code error             -errorcode [::list TCLMESH PRIVATE BACKEND INVALID_COMMAND $name]             "backend '$name' command does not resolve"
    }

    dict set backends $name [dict create         name $name         command $command         capabilities [lsort -unique $capabilities]]

    return $name
}

proc ::tclmesh::private::backend::describe {name} {
    variable ::tclmesh::private::backends
    if {![dict exists $backends $name]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE BACKEND NOT_FOUND $name]             "backend '$name' is not registered"
    }
    return [dict get $backends $name]
}

proc ::tclmesh::private::backend::list {} {
    variable ::tclmesh::private::backends
    return [lsort -dictionary [dict keys $backends]]
}

proc ::tclmesh::private::profile::define {name descriptor} {
    variable ::tclmesh::private::profiles

    if {$name eq ""} {
        return -code error             -errorcode {TCLMESH PRIVATE PROFILE EMPTY_NAME}             "profile name must not be empty"
    }
    if {[dict exists $profiles $name]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE PROFILE ALREADY_DEFINED $name]             "profile '$name' is already defined"
    }

    foreach key {backend semantics} {
        if {![dict exists $descriptor $key] ||
            [dict get $descriptor $key] eq ""} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE PROFILE MISSING $key]                 "profile '$name' is missing '$key'"
        }
    }

    set backend [dict get $descriptor backend]
    set backend_descriptor [::tclmesh::private::backend::describe $backend]
    set width [::tclmesh::private::_checked_width $descriptor]
    if {$width ne ""} {
        ::tclmesh::range::word $width
    }

    if {![dict exists $descriptor parameters]} {
        dict set descriptor parameters {}
    }
    if {![dict exists $descriptor allow_decrypt]} {
        dict set descriptor allow_decrypt false
    }
    if {![string is boolean -strict [dict get $descriptor allow_decrypt]]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE PROFILE INVALID_ALLOW_DECRYPT $name]             "profile '$name' allow_decrypt must be boolean"
    }

    set command [dict get $backend_descriptor command]
    set accepted [{*}$command validate-profile $descriptor]
    if {![string is boolean -strict $accepted] || !$accepted} {
        return -code error             -errorcode [::list TCLMESH PRIVATE PROFILE BACKEND_REJECTED $name]             "backend '$backend' rejected profile '$name'"
    }

    dict set descriptor name $name
    dict set profiles $name $descriptor
    return $name
}

proc ::tclmesh::private::profile::describe {name} {
    variable ::tclmesh::private::profiles
    if {![dict exists $profiles $name]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE PROFILE NOT_FOUND $name]             "profile '$name' is not defined"
    }
    return [dict get $profiles $name]
}

proc ::tclmesh::private::profile::list {} {
    variable ::tclmesh::private::profiles
    return [lsort -dictionary [dict keys $profiles]]
}

proc ::tclmesh::private::_logical_type {descriptor} {
    if {[llength $descriptor] < 2} {
        return -code error             -errorcode {TCLMESH PRIVATE TYPE INVALID_DESCRIPTOR}             "private type descriptor must include visibility and logical type"
    }
    return [lindex $descriptor 1]
}

proc ::tclmesh::private::_visibility {descriptor} {
    if {[llength $descriptor] < 2} {
        return -code error             -errorcode {TCLMESH PRIVATE TYPE INVALID_DESCRIPTOR}             "private type descriptor must include visibility and logical type"
    }

    set visibility [lindex $descriptor 0]
    if {$visibility ni {cipher public}} {
        return -code error             -errorcode [::list TCLMESH PRIVATE TYPE INVALID_VISIBILITY $visibility]             "private input/output visibility must be cipher or public"
    }
    return $visibility
}

# Internal persistence boundary: only registered backends serialize and restore
# their tokens. Public handle descriptors never expose this recovery material.
proc ::tclmesh::private::_commit_handles {candidate next} {
    variable handles
    variable next_handle
    variable handle_store
    if {$handle_store ne ""} {
        set saved {}
        dict for {id descriptor} $candidate {
            set record $descriptor
            dict unset record token
            if {[dict get $descriptor status] eq "active"} {
                set backend [backend::describe [dict get $descriptor backend]]
                if {"persistent-handles" ni [dict get $backend capabilities]} {
                    return -code error -errorcode {TCLMESH PRIVATE HANDLE PERSISTENCE_UNSUPPORTED} "backend does not support persistent handles"
                }
                set profile [profile::describe [dict get $descriptor profile]]
                dict set record profile_spec $profile
                dict set record recovery [{*}[dict get $backend command] export-handle $profile [dict get $descriptor type] [dict get $descriptor token]]
            }
            dict set saved $id $record
        }
        ::tclmesh::store put $handle_store private.handles [dict create handles $saved next_handle $next]
    }
    set handles $candidate
    set next_handle $next
}

proc ::tclmesh::private::_use_handle_store {store_id} {
    variable handles
    variable next_handle
    variable handle_store
    if {$store_id eq ""} {
        set handle_store {}
        return
    }
    set candidate $handles
    set next $next_handle
    if {[::tclmesh::store exists $store_id private.handles]} {
        set state [::tclmesh::store get $store_id private.handles]
        set candidate {}
        set next [dict get $state next_handle]
        dict for {id record} [dict get $state handles] {
            set token {}
            if {[dict get $record status] eq "active"} {
                set profile [profile::describe [dict get $record profile]]
                if {$profile ne [dict get $record profile_spec] ||
                    [dict get $profile backend] ne [dict get $record backend]} {
                    return -code error -errorcode {TCLMESH PRIVATE HANDLE BACKEND_MISMATCH} "persisted handle backend differs from profile"
                }
                set backend [backend::describe [dict get $record backend]]
                if {"persistent-handles" ni [dict get $backend capabilities]} {
                    return -code error -errorcode {TCLMESH PRIVATE HANDLE PERSISTENCE_UNSUPPORTED} "backend does not support persistent handles"
                }
                set token [{*}[dict get $backend command] restore-handle $profile [dict get $record type] [dict get $record recovery]]
                dict unset record recovery
                dict unset record profile_spec
            }
            dict set record token $token
            dict set candidate $id $record
        }
    }
    set previous $handle_store
    set handle_store $store_id
    try {
        _commit_handles $candidate $next
    } on error {message options} {
        set handle_store $previous
        return -options $options $message
    }
}

proc ::tclmesh::private::_new_handle {profile type backend token origin {binding {}} {range {}}} {
    variable handles
    variable next_handle

    set next [expr {$next_handle + 1}]
    set id "ct:$next"
    set candidate $handles
    dict set candidate $id [dict create         id $id         status active         profile $profile         type $type         backend $backend         origin $origin         binding $binding         token $token]
    if {$range ne ""} {
        dict set candidate $id range $range
    }
    _commit_handles $candidate $next
    return $id
}

proc ::tclmesh::private::_require_handle {id} {
    variable handles
    if {![dict exists $handles $id]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE HANDLE NOT_FOUND $id]             "ciphertext handle '$id' does not exist"
    }

    set descriptor [dict get $handles $id]
    if {[dict get $descriptor status] ne "active"} {
        return -code error             -errorcode [::list TCLMESH PRIVATE HANDLE INACTIVE $id]             "ciphertext handle '$id' is not active"
    }

    return $descriptor
}

proc ::tclmesh::private::handle::describe {id} {
    set descriptor [::tclmesh::private::_require_handle $id]
    dict unset descriptor token
    return $descriptor
}

proc ::tclmesh::private::handle::destroy {id} {
    variable ::tclmesh::private::handles

    set descriptor [::tclmesh::private::_require_handle $id]
    set backend_descriptor [::tclmesh::private::backend::describe         [dict get $descriptor backend]]
    set command [dict get $backend_descriptor command]

    if {"destroy" in [dict get $backend_descriptor capabilities]} {
        {*}$command destroy [dict get $descriptor token]
    }

    dict set descriptor status destroyed
    dict set descriptor token {}
    set candidate $handles
    dict set candidate $id $descriptor
    ::tclmesh::private::_commit_handles $candidate $::tclmesh::private::next_handle

    dict unset descriptor token
    return $descriptor
}

proc ::tclmesh::private::handle::list {} {
    variable ::tclmesh::private::handles
    return [lsort -dictionary [dict keys $handles]]
}

# The word width W of an `int<W>-checked` profile, or {} for any other.
proc ::tclmesh::private::_checked_width {profile} {
    if {[regexp {^int([0-9]+)-checked$} [dict get $profile semantics] -> width]} {
        return $width
    }
    return {}
}

# Under an `int<W>-checked` profile the plaintext is checked here, once, and
# only its declared range (by default the whole word) is kept with the
# handle: the encrypting party's range claim, which a deployment that keeps
# the plaintext away from the runtime must replace by a range proof.
proc ::tclmesh::private::encrypt {profile_name type value {range {}}} {
    set profile [::tclmesh::private::profile::describe $profile_name]
    set backend [dict get $profile backend]
    set backend_descriptor [::tclmesh::private::backend::describe $backend]
    set command [dict get $backend_descriptor command]

    set width [_checked_width $profile]
    if {$width ne ""} {
        set range [_checked_value $width $type $value $range encrypt]
    } elseif {$range ne ""} {
        return -code error -errorcode {TCLMESH PRIVATE RANGE UNCHECKED_PROFILE} \
            "only int<W>-checked profiles carry ranges"
    }
    set token [{*}$command encrypt $profile $type $value]
    return [_new_handle $profile_name $type $backend $token encrypt {} $range]
}

# The backend command of a profile whose backend has CAPABILITY.
proc ::tclmesh::private::_capable {profile capability} {
    set backend [::tclmesh::private::backend::describe [dict get $profile backend]]
    if {$capability ni [dict get $backend capabilities]} {
        return -code error -errorcode [::list TCLMESH PRIVATE BACKEND UNSUPPORTED $capability] \
            "backend '[dict get $profile backend]' does not support $capability"
    }
    return [dict get $backend command]
}

# Write to DIR what an encrypting party needs to prove inputs for PROFILE
# without its secret key: the public key and the proof system's CRS. With
# CRS, the backend adopts a CRS that no single party's trapdoor controls: a
# ceremony directory (`tclmesh-tfhe-crs init|contribute`), which it verifies
# first, or a file generated by a third party; without it, the backend
# generates one itself. TRUSTED lists the public key files of contributors
# the caller trusts (`tclmesh-tfhe-crs keygen`): the ceremony is adopted only
# if one of them signed a contribution, so one honest party suffices.
proc ::tclmesh::private::publish {profile_name dir {crs {}} {trusted {}}} {
    set profile [profile::describe $profile_name]
    if {[llength $trusted] > 0 && $crs eq ""} {
        return -code error -errorcode {TCLMESH PRIVATE RANGE TRUST_WITHOUT_CEREMONY} \
            "trusted contributors need a ceremony"
    }
    {*}[_capable $profile proven-inputs] publish $profile $dir $crs $trusted
    return $dir
}

# Accept a proven ciphertext input: an offset a < 2^BITS encrypted with a
# zero-knowledge proof bound to CONTEXT, LO, BITS and, if given, HI
# (`tclmesh-tfhe-prove`). The backend verifies it and holds LO + a, or
# min(LO + a, HI): the handle's range, [LO, LO + 2^BITS - 1] or exactly
# [LO, HI], is proved, not claimed, and the runtime never sees the value
# (spec/TclMesh/Range.lean, `inputs_of_proofs`, `bounded_import`). With HI an
# honest input is unchanged and a dishonest one is clamped to HI; to reject
# instead, follow with `range-check` and `admit`.
proc ::tclmesh::private::import {profile_name proof context lo bits {hi {}}} {
    set profile [profile::describe $profile_name]
    set width [_checked_width $profile]
    if {$width eq ""} {
        return -code error -errorcode {TCLMESH PRIVATE RANGE UNCHECKED_PROFILE} \
            "proven inputs need an int<W>-checked profile"
    }
    if {$bits ni {2 4 6 8 10 12 14 16 32} || ![::tclmesh::range::_int $lo]} {
        return -code error -errorcode {TCLMESH PRIVATE RANGE INVALID_PROOF_STATEMENT} \
            "a proven input needs a canonical lo and bits in 2, 4, ..., 16 or 32"
    }
    set top [expr {$lo + (1 << $bits) - 1}]
    if {$hi ne "" && !([::tclmesh::range::_int $hi] && $lo <= $hi && $hi <= $top)} {
        return -code error -errorcode {TCLMESH PRIVATE RANGE INVALID_PROOF_STATEMENT} \
            "hi must be a canonical integer in \[lo, lo + 2^bits - 1\]"
    }
    set range [::list $lo [expr {$hi eq "" ? $top : $hi}]]
    if {![::tclmesh::range::_within [::list $lo $top] [::tclmesh::range::word $width]]} {
        return -code error -errorcode {TCLMESH PRIVATE RANGE INVALID_PROOF_STATEMENT} \
            "proven range [::list $lo $top] leaves the $width-bit word"
    }
    # A context names one use: a proof accepted under it once is not accepted
    # again while its handle record exists (destroyed handles keep theirs).
    # The record outlives the process only on backends with persistent
    # handles; the TFHE backend has none, so there it lasts one process, but
    # its keys do too, and a proof does not verify under another key.
    variable handles
    dict for {id record} $handles {
        if {[dict get $record profile] eq $profile_name && [dict exists $record proof_context] &&
            [dict get $record proof_context] eq $context} {
            return -code error -errorcode [::list TCLMESH PRIVATE RANGE CONTEXT_REUSED $id] \
                "proof context '$context' was already used by $id"
        }
    }
    set token [{*}[_capable $profile proven-inputs] import $profile $proof $context $lo $bits $hi]
    set id [_new_handle $profile_name int [dict get $profile backend] $token proved {} $range]
    set candidate $handles
    dict set candidate $id proof_context $context
    _commit_handles $candidate $::tclmesh::private::next_handle
    return $id
}

# The admission circuit for [LO, HI]: one encrypted bit, LO <= x <= HI.
# Comparisons are exact on words, so the bit is exact whatever x holds.
proc ::tclmesh::private::_admission_circuit {lo hi} {
    circuit admission [dict create x {cipher int}] [dict create ok {cipher bool}] \
        [dict create nx {input x} lo [::list constant $lo] hi [::list constant $hi] \
            ge {greater-or-equal nx lo} le {less-or-equal nx hi} ok {and ge le}] \
        [dict create output_nodes [dict create ok ok]]
}

# Rejecting admission, step 1: evaluate whether SUBJECT lies in [LO, HI],
# as an encrypted bit bound to SUBJECT and the range. Release that bit, and
# only that bit, through `tclmesh release` (a t-of-n quorum), then `admit`.
# What is revealed is exactly whether the input is admissible.
proc ::tclmesh::private::range-check {profile_name subject lo hi} {
    set profile [profile::describe $profile_name]
    set width [_checked_width $profile]
    if {$width eq ""} {
        return -code error -errorcode {TCLMESH PRIVATE RANGE UNCHECKED_PROFILE} \
            "admission needs an int<W>-checked profile"
    }
    if {![::tclmesh::range::_bounds $lo $hi] ||
        ![::tclmesh::range::_within [::list $lo $hi] [::tclmesh::range::word $width]]} {
        return -code error -errorcode {TCLMESH PRIVATE RANGE INVALID_ADMISSION} \
            "admission needs canonical bounds lo <= hi inside the $width-bit word"
    }
    set handle [_require_handle $subject]
    if {[dict get $handle type] ne "int"} {
        return -code error -errorcode [::list TCLMESH PRIVATE RANGE INVALID_ADMISSION $subject] \
            "only int handles are admitted to a range"
    }
    set outputs [_evaluate $profile_name [_admission_circuit $lo $hi] [dict create x $subject] \
        [dict create admission_subject $subject admission_range [::list $lo $hi]]]
    return [dict get $outputs ok]
}

# Rejecting admission, step 2: given a released admission bit, narrow its
# subject's range to [LO, HI] if the bit is 1, and refuse otherwise. The
# release must be of the admission circuit for that range on that subject
# (its binding records both), so no other released bit is accepted
# (spec/TclMesh/Range.lean, `admission_sound`).
proc ::tclmesh::private::admit {release_id} {
    variable handles
    variable next_handle
    set release [::tclmesh::release::get $release_id]
    set binding [::tclmesh::release::_binding $release]
    if {[dict get $release status] ne "released" ||
        ![dict exists $binding admission_subject] || ![dict exists $binding admission_range] ||
        [dict get $binding output_name] ne "ok"} {
        return -code error -errorcode [::list TCLMESH PRIVATE RANGE NOT_AN_ADMISSION $release_id] \
            "release '$release_id' is not a released admission check"
    }
    set subject [dict get $binding admission_subject]
    set range [dict get $binding admission_range]
    if {[dict get $binding circuit_hash] ne [digest [_admission_circuit {*}$range]]} {
        return -code error -errorcode [::list TCLMESH PRIVATE RANGE NOT_AN_ADMISSION $release_id] \
            "release '$release_id' is not of the admission circuit for $range"
    }
    if {[dict get $release result] ne "1"} {
        return -code error -errorcode [::list TCLMESH PRIVATE RANGE ADMISSION_REFUSED $subject] \
            "input '$subject' lies outside $range"
    }
    set handle [_require_handle $subject]
    if {[dict get $handle profile] ne [dict get $release profile]} {
        return -code error -errorcode [::list TCLMESH PRIVATE RANGE NOT_AN_ADMISSION $release_id] \
            "release '$release_id' belongs to another profile"
    }
    set candidate $handles
    dict set candidate $subject range $range
    dict set candidate $subject admission $release_id
    _commit_handles $candidate $next_handle
    return $subject
}

# The range a checked value of TYPE carries: RANGE (int; the word when empty)
# or {0 1} (bool), after checking that VALUE lies in it.
proc ::tclmesh::private::_checked_value {width type value range what} {
    set word [::tclmesh::range::word $width]
    switch -- $type {
        int { set allowed [expr {$range eq "" ? $word : $range}] }
        bool { set allowed {0 1} }
        default {
            return -code error -errorcode [::list TCLMESH PRIVATE RANGE UNSUPPORTED_TYPE $type] \
                "int$width-checked supports int and bool, not '$type'"
        }
    }
    if {![::tclmesh::range::_valid $allowed] || ![::tclmesh::range::_within $allowed $word] ||
        ![::tclmesh::range::_int $value] ||
        ![::tclmesh::range::_within [::list $value $value] $allowed]} {
        return -code error -errorcode [::list TCLMESH PRIVATE RANGE OUT_OF_RANGE $what] \
            "$what: value outside its declared range"
    }
    return $allowed
}

proc ::tclmesh::private::_prepare_inputs {profile_name circuit inputs} {
    set prepared {}
    set width [_checked_width [::tclmesh::private::profile::describe $profile_name]]

    dict for {name type_descriptor} [dict get $circuit inputs] {
        if {![dict exists $inputs $name]} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE EVALUATE MISSING_INPUT $name]                 "private evaluation is missing input '$name'"
        }

        set visibility [_visibility $type_descriptor]
        set type [_logical_type $type_descriptor]
        set value [dict get $inputs $name]

        if {$width ne ""} {
            set declared [::tclmesh::range::_input $type_descriptor $width]
            if {$declared eq ""} {
                return -code error -errorcode [::list TCLMESH PRIVATE RANGE UNSUPPORTED_INPUT $name] \
                    "input '$name' has no range under int$width-checked"
            }
        }

        if {$visibility eq "public"} {
            if {$width ne ""} {
                _checked_value $width $type $value $declared $name
            }
            dict set prepared $name [::list public $value]
            continue
        }

        set handle [_require_handle $value]
        if {[dict get $handle profile] ne $profile_name} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE HANDLE PROFILE_MISMATCH $name]                 "input '$name' handle belongs to a different profile"
        }
        if {[dict get $handle type] ne $type} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE HANDLE TYPE_MISMATCH $name]                 "input '$name' handle has the wrong logical type"
        }
        if {$width ne "" && $declared ne [::tclmesh::range::word $width] && !([dict exists $handle range] &&
                [::tclmesh::range::_valid [dict get $handle range]] &&
                [lindex [dict get $handle range] 0] <= [lindex [dict get $handle range] 1] &&
                [::tclmesh::range::_within [dict get $handle range] $declared])} {
            return -code error -errorcode [::list TCLMESH PRIVATE RANGE OUT_OF_RANGE $name] \
                "input '$name' handle is not known to lie in its declared range"
        }

        dict set prepared $name [::list cipher [dict get $handle token]]
    }

    return $prepared
}

proc ::tclmesh::private::evaluate {profile_name circuit inputs} {
    return [_evaluate $profile_name $circuit $inputs {}]
}

# Resolve authoritative circuit semantics from the active immutable manifest.
# This is a provenance boundary; caller authorization remains an adapter concern.
proc ::tclmesh::private::evaluate-bound {profile_name application_id circuit_id inputs} {
    set pin [::tclmesh::manifest active $application_id]
    set manifest [::tclmesh::manifest get $application_id [dict get $pin version]]
    if {[::tclmesh::manifest digest $manifest] ne [dict get $pin manifest_hash]} {
        return -code error -errorcode {TCLMESH PRIVATE MANIFEST_MISMATCH} "active manifest does not match its hash"
    }
    if {![dict exists $manifest circuits $circuit_id]} {
        return -code error -errorcode [::list TCLMESH PRIVATE CIRCUIT NOT_FOUND $circuit_id] "circuit is not declared by the active manifest"
    }
    set circuit [dict get $manifest circuits $circuit_id]
    if {[dict exists $circuit metadata profile] &&
        [dict get $circuit metadata profile] ne $profile_name} {
        return -code error -errorcode {TCLMESH PRIVATE CIRCUIT PROFILE_MISMATCH} "circuit requires a different parameter profile"
    }
    set binding [dict create \
        application_id $application_id \
        manifest_version [dict get $pin version] \
        manifest_hash [dict get $pin manifest_hash] \
        circuit_id $circuit_id]
    return [_evaluate $profile_name $circuit $inputs $binding]
}

proc ::tclmesh::private::_evaluate {profile_name circuit inputs manifest_binding} {
    set circuit [validate $circuit]
    if {![dict exists $circuit metadata output_nodes]} {
        return -code error             -errorcode {TCLMESH PRIVATE EVALUATE OUTPUT_NODES_REQUIRED}             "private evaluation requires metadata output_nodes"
    }

    set profile [::tclmesh::private::profile::describe $profile_name]
    set backend [dict get $profile backend]
    set backend_descriptor [::tclmesh::private::backend::describe $backend]
    set command [dict get $backend_descriptor command]
    set width [_checked_width $profile]
    set ranges {}
    if {$width ne ""} {
        set ranges [::tclmesh::range::require $circuit $width]
        # A descriptor alone cannot turn an integer node into a bit. Prove
        # the output invariant before invoking the backend or issuing handles.
        dict for {name descriptor} [dict get $circuit outputs] {
            if {[_logical_type $descriptor] eq "bool" &&
                ![::tclmesh::range::_within \
                    [dict get $ranges [dict get $circuit metadata output_nodes $name]] {0 1}]} {
                return -code error -errorcode [::list TCLMESH PRIVATE RANGE BOOLEAN_OUTPUT $name] \
                    "output '$name' is not certified to be boolean"
            }
        }
    }
    set prepared [_prepare_inputs $profile_name $circuit $inputs]

    set circuit_hash [digest $circuit]
    set output_tokens [{*}$command evaluate $profile $circuit $prepared]
    set outputs {}

    dict for {name type_descriptor} [dict get $circuit outputs] {
        if {[_visibility $type_descriptor] ne "cipher"} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE EVALUATE PUBLIC_OUTPUT_UNSUPPORTED $name]                 "v0.3 backend evaluation requires cipher outputs"
        }
        if {![dict exists $output_tokens $name]} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE EVALUATE MISSING_OUTPUT $name]                 "backend did not return output '$name'"
        }

        set type [_logical_type $type_descriptor]
        set binding [dict merge $manifest_binding [dict create \
            circuit_hash $circuit_hash \
            output_name $name \
            output_spec [::tclmesh::manifest::_canonical_sequence $type_descriptor]]]
        set range {}
        if {$width ne ""} {
            set range [dict get $ranges [dict get $circuit metadata output_nodes $name]]
        }
        dict set outputs $name [_new_handle \
            $profile_name $type $backend [dict get $output_tokens $name] evaluate $binding $range]
    }

    return $outputs
}

proc ::tclmesh::private::decrypt {handle_id} {
    set handle [_require_handle $handle_id]
    if {[::tclmesh::release::_handle_policy $handle] ne ""} {
        return -code error -errorcode {TCLMESH PRIVATE DECRYPT RELEASE_REQUIRED}             "governed output requires authorized threshold release"
    }
    set profile [::tclmesh::private::profile::describe         [dict get $handle profile]]

    if {![dict get $profile allow_decrypt]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE DECRYPT FORBIDDEN                 [dict get $handle profile]]             "profile does not permit direct decryption"
    }

    set backend_descriptor [::tclmesh::private::backend::describe         [dict get $handle backend]]
    set command [dict get $backend_descriptor command]

    return [{*}$command decrypt         $profile         [dict get $handle type]         [dict get $handle token]]
}

proc ::tclmesh::private::_reference_node {circuit id inputs cacheVar activeVar} {
    upvar 1 $cacheVar cache $activeVar active

    if {[dict exists $cache $id]} {
        return [dict get $cache $id]
    }
    if {[dict exists $active $id]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE REFERENCE CYCLE $id]             "reference evaluation encountered a cycle"
    }

    dict set active $id 1
    set node [dict get $circuit nodes $id]
    set op [lindex $node 0]

    switch -- $op {
        input {
            set name [lindex $node 1]
            set value [dict get $inputs $name]
        }
        constant {
            set value [lindex $node 1]
        }
        add -
        subtract -
        multiply -
        equal -
        less-than -
        less-or-equal -
        greater-than -
        greater-or-equal -
        and -
        or {
            set left [_reference_node                 $circuit [lindex $node 1] $inputs cache active]
            set right [_reference_node                 $circuit [lindex $node 2] $inputs cache active]

            switch -- $op {
                add { set value [expr {$left + $right}] }
                subtract { set value [expr {$left - $right}] }
                multiply { set value [expr {$left * $right}] }
                equal { set value [expr {$left eq $right}] }
                less-than { set value [expr {$left < $right}] }
                less-or-equal { set value [expr {$left <= $right}] }
                greater-than { set value [expr {$left > $right}] }
                greater-or-equal { set value [expr {$left >= $right}] }
                and { set value [expr {bool($left) && bool($right)}] }
                or { set value [expr {bool($left) || bool($right)}] }
            }
        }
        negate {
            set input [_reference_node                 $circuit [lindex $node 1] $inputs cache active]
            set value [expr {-$input}]
        }
        not {
            set input [_reference_node                 $circuit [lindex $node 1] $inputs cache active]
            set value [expr {!bool($input)}]
        }
        clamp {
            set input [_reference_node                 $circuit [lindex $node 1] $inputs cache active]
            lassign $node - - lo hi
            set value [expr {max($lo, min($input, $hi))}]
        }
        select {
            set condition [_reference_node                 $circuit [lindex $node 1] $inputs cache active]
            if {$condition} {
                set value [_reference_node                     $circuit [lindex $node 2] $inputs cache active]
            } else {
                set value [_reference_node                     $circuit [lindex $node 3] $inputs cache active]
            }
        }
        reduce-sum {
            set input [_reference_node                 $circuit [lindex $node 1] $inputs cache active]
            set value 0
            foreach item $input {
                set value [expr {$value + $item}]
            }
        }
        rotate {
            set input [_reference_node                 $circuit [lindex $node 1] $inputs cache active]
            set n [llength $input]
            if {$n == 0} {
                set value {}
            } else {
                set offset [expr {[lindex $node 2] % $n}]
                if {$offset < 0} {
                    set offset [expr {$offset + $n}]
                }
                set value [concat                     [lrange $input $offset end]                     [lrange $input 0 [expr {$offset - 1}]]]
            }
        }
        polynomial {
            set input [_reference_node                 $circuit [lindex $node 1] $inputs cache active]
            set coefficients [lindex $node 2]
            set value 0
            foreach coefficient [lreverse $coefficients] {
                set value [expr {$value * $input + $coefficient}]
            }
        }
        lookup {
            set input [_reference_node                 $circuit [lindex $node 1] $inputs cache active]
            set table [_reference_node                 $circuit [lindex $node 2] $inputs cache active]
            if {![dict exists $table $input]} {
                return -code error                     -errorcode [::list TCLMESH PRIVATE REFERENCE LOOKUP_MISSING $input]                     "lookup table has no value for '$input'"
            }
            set value [dict get $table $input]
        }
        default {
            return -code error                 -errorcode [::list TCLMESH PRIVATE REFERENCE UNSUPPORTED $op]                 "reference backend does not support '$op'"
        }
    }

    dict unset active $id
    dict set cache $id $value
    return $value
}

proc ::tclmesh::private::_reference_evaluate {circuit inputs} {
    set circuit [validate $circuit]
    if {![dict exists $circuit metadata output_nodes]} {
        return -code error             -errorcode {TCLMESH PRIVATE REFERENCE OUTPUT_NODES_REQUIRED}             "reference evaluation requires metadata output_nodes"
    }

    set cache {}
    set active {}
    set results {}

    dict for {name node_id} [dict get $circuit metadata output_nodes] {
        dict set results $name [_reference_node             $circuit $node_id $inputs cache active]
    }

    return $results
}

proc ::tclmesh::private::_plaintext_backend {operation args} {
    switch -- $operation {
        validate-profile {
            return true
        }
        encrypt {
            lassign $args profile type value
            return [dict create value $value]
        }
        evaluate {
            lassign $args profile circuit prepared
            set values {}

            dict for {name tagged} $prepared {
                lassign $tagged visibility payload
                if {$visibility eq "cipher"} {
                    dict set values $name [dict get $payload value]
                } else {
                    dict set values $name $payload
                }
            }

            set plain [_reference_evaluate $circuit $values]
            set tokens {}
            dict for {name value} $plain {
                dict set tokens $name [dict create value $value]
            }
            return $tokens
        }
        export-handle -
        restore-handle {
            lassign $args profile type token
            # Reference backend only: this material contains plaintext.
            dict get $token value
            return $token
        }
        decrypt {
            lassign $args profile type token
            return [dict get $token value]
        }
        combine-release {
            lassign $args profile type token contributions context
            if {[dict size $contributions] == 0} {
                return -code error                     -errorcode {TCLMESH PRIVATE PLAINTEXT RELEASE EMPTY_CONTRIBUTIONS}                     "reference threshold release requires contributions"
            }
            return [dict get $token value]
        }
        destroy {
            return
        }
        default {
            return -code error                 -errorcode [::list TCLMESH PRIVATE BACKEND INVALID_OPERATION $operation]                 "plaintext backend does not support '$operation'"
        }
    }
}

proc ::tclmesh::private::differential {
    profile_name
    circuit
    plaintext_inputs
} {
    set profile [::tclmesh::private::profile::describe $profile_name]
    if {![dict get $profile allow_decrypt]} {
        return -code error             -errorcode [::list TCLMESH PRIVATE DIFFERENTIAL DECRYPT_REQUIRED $profile_name]             "differential execution requires a decrypt-enabled profile"
    }

    set reference [_reference_evaluate $circuit $plaintext_inputs]
    set runtime_inputs {}

    dict for {name descriptor} [dict get $circuit inputs] {
        if {![dict exists $plaintext_inputs $name]} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE DIFFERENTIAL MISSING_INPUT $name]                 "differential input '$name' is missing"
        }

        set value [dict get $plaintext_inputs $name]
        if {[_visibility $descriptor] eq "cipher"} {
            dict set runtime_inputs $name [encrypt                 $profile_name                 [_logical_type $descriptor]                 $value]
        } else {
            dict set runtime_inputs $name $value
        }
    }

    set encrypted_outputs [evaluate         $profile_name $circuit $runtime_inputs]
    set actual {}
    dict for {name handle_id} $encrypted_outputs {
        dict set actual $name [decrypt $handle_id]
    }

    set tolerance 0
    if {[dict exists $profile tolerance]} {
        set tolerance [dict get $profile tolerance]
    }

    set match true
    dict for {name expected} $reference {
        if {![dict exists $actual $name]} {
            set match false
            continue
        }

        set observed [dict get $actual $name]
        if {$tolerance > 0 &&
            [string is double -strict $expected] &&
            [string is double -strict $observed]} {
            if {[expr {abs(double($expected) - double($observed))}] > $tolerance} {
                set match false
            }
        } elseif {$expected ne $observed} {
            set match false
        }
    }

    return [dict create         match $match         reference $reference         backend $actual         outputs $encrypted_outputs]
}

namespace eval ::tclmesh::private {
    namespace ensemble create -command ::tclmesh::private -map {
        node ::tclmesh::private::node
        circuit ::tclmesh::private::circuit
        validate ::tclmesh::private::validate
        canonical ::tclmesh::private::canonical
        digest ::tclmesh::private::digest
        profile ::tclmesh::private::profile
        backend ::tclmesh::private::backend
        handle ::tclmesh::private::handle
        encrypt ::tclmesh::private::encrypt
        publish ::tclmesh::private::publish
        import ::tclmesh::private::import
        range-check ::tclmesh::private::range-check
        admit ::tclmesh::private::admit
        evaluate ::tclmesh::private::evaluate
        evaluate-bound ::tclmesh::private::evaluate-bound
        decrypt ::tclmesh::private::decrypt
        differential ::tclmesh::private::differential
    }
}

::tclmesh::private::backend::register     plaintext     ::tclmesh::private::_plaintext_backend     {decrypt destroy reference threshold-release idempotent-release persistent-handles}
