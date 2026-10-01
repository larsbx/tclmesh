namespace eval ::tclmesh::private {
    variable allowed_ops {
        constant input
        add subtract multiply negate
        equal less-than less-or-equal greater-than greater-or-equal
        and or not select
        rotate reduce-sum lookup polynomial
    }

    variable profiles {}
    variable backends {}
    variable handles {}
    variable next_handle 0

    namespace export         node circuit validate encrypt evaluate decrypt differential         profile backend handle
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
        polynomial {
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

proc ::tclmesh::private::_new_handle {profile type backend token origin} {
    variable handles
    variable next_handle

    incr next_handle
    set id "ct:$next_handle"
    dict set handles $id [dict create         id $id         status active         profile $profile         type $type         backend $backend         origin $origin         token $token]
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
    dict set handles $id $descriptor

    dict unset descriptor token
    return $descriptor
}

proc ::tclmesh::private::handle::list {} {
    variable ::tclmesh::private::handles
    return [lsort -dictionary [dict keys $handles]]
}

proc ::tclmesh::private::encrypt {profile_name type value} {
    set profile [::tclmesh::private::profile::describe $profile_name]
    set backend [dict get $profile backend]
    set backend_descriptor [::tclmesh::private::backend::describe $backend]
    set command [dict get $backend_descriptor command]

    set token [{*}$command encrypt $profile $type $value]
    return [_new_handle $profile_name $type $backend $token encrypt]
}

proc ::tclmesh::private::_prepare_inputs {profile_name circuit inputs} {
    set prepared {}

    dict for {name type_descriptor} [dict get $circuit inputs] {
        if {![dict exists $inputs $name]} {
            return -code error                 -errorcode [::list TCLMESH PRIVATE EVALUATE MISSING_INPUT $name]                 "private evaluation is missing input '$name'"
        }

        set visibility [_visibility $type_descriptor]
        set type [_logical_type $type_descriptor]
        set value [dict get $inputs $name]

        if {$visibility eq "public"} {
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

        dict set prepared $name [::list cipher [dict get $handle token]]
    }

    return $prepared
}

proc ::tclmesh::private::evaluate {profile_name circuit inputs} {
    set circuit [validate $circuit]
    if {![dict exists $circuit metadata output_nodes]} {
        return -code error             -errorcode {TCLMESH PRIVATE EVALUATE OUTPUT_NODES_REQUIRED}             "private evaluation requires metadata output_nodes"
    }

    set profile [::tclmesh::private::profile::describe $profile_name]
    set backend [dict get $profile backend]
    set backend_descriptor [::tclmesh::private::backend::describe $backend]
    set command [dict get $backend_descriptor command]
    set prepared [_prepare_inputs $profile_name $circuit $inputs]

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
        dict set outputs $name [_new_handle             $profile_name             $type             $backend             [dict get $output_tokens $name]             evaluate]
    }

    return $outputs
}

proc ::tclmesh::private::decrypt {handle_id} {
    set handle [_require_handle $handle_id]
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
        profile ::tclmesh::private::profile
        backend ::tclmesh::private::backend
        handle ::tclmesh::private::handle
        encrypt ::tclmesh::private::encrypt
        evaluate ::tclmesh::private::evaluate
        decrypt ::tclmesh::private::decrypt
        differential ::tclmesh::private::differential
    }
}

::tclmesh::private::backend::register     plaintext     ::tclmesh::private::_plaintext_backend     {decrypt destroy reference threshold-release idempotent-release}
