# Per-party views of private evaluation (docs/testing.md).
#
# A view is everything one party observes in a run. `run` evaluates a circuit
# through a recording backend and returns the views; `declared` computes what
# each party may observe from the circuit and its public inputs alone (the
# Lean model, TclMesh.Circuit, computes the same); `paired` checks the
# hyperproperty that runs agreeing on what a party may learn give that party
# equal views.
#
# Parties:
#   evaluator  runs the circuit: sees the circuit digest, public inputs, the
#              types of ciphertext inputs and outputs, the operation trace, and
#              each token's observable metadata (its size, when a backend
#              exposes one);
#   recipient  decrypts the outputs: sees their plaintext values.

namespace eval ::tclmesh::views {
    variable log {}
    namespace export run declared paired schedule structure
    namespace ensemble create
}

# Syntactic evaluation order: depth-first post-order from the outputs, taken
# in sorted name order, visiting operands in node order. It depends on the
# circuit alone.
proc ::tclmesh::views::schedule {circuit} {
    set circuit [::tclmesh::private::validate $circuit]
    set order {}
    set seen {}
    set output_nodes [dict get $circuit metadata output_nodes]
    foreach name [lsort [dict keys $output_nodes]] {
        _visit $circuit [dict get $output_nodes $name] seen order
    }
    return $order
}

proc ::tclmesh::views::_visit {circuit id seenVar orderVar} {
    upvar 1 $seenVar seen $orderVar order
    if {[dict exists $seen $id]} {
        return
    }
    dict set seen $id 1
    foreach ref [::tclmesh::private::_node_refs [dict get $circuit nodes $id]] {
        _visit $circuit $ref seen order
    }
    lappend order $id
}

proc ::tclmesh::views::_trace {circuit ids} {
    lmap id $ids {
        ::list $id [lindex [dict get $circuit nodes $id] 0]
    }
}

# What the evaluator observes about one prepared input.
proc ::tclmesh::views::_input_view {circuit prepared} {
    set result {}
    foreach name [lsort [dict keys [dict get $circuit inputs]]] {
        lassign [dict get $prepared $name] visibility payload
        set type [::tclmesh::private::_logical_type [dict get $circuit inputs $name]]
        if {$visibility eq "public"} {
            lappend result $name [::list public $type $payload]
        } else {
            lappend result $name [_cipher_view $type $payload]
        }
    }
    return $result
}

# A ciphertext is observed through its type and, if the token exposes one
# (`size`, or `bytes` for serialized ciphertexts), its size; never through its
# contents.
proc ::tclmesh::views::_cipher_view {type token} {
    foreach key {size bytes} {
        if {[dict exists $token $key]} {
            return [::list cipher $type size [dict get $token $key]]
        }
    }
    return [::list cipher $type]
}

# A view without ciphertext sizes: the declared view fixes the structure, but
# not the sizes a backend's ciphertexts happen to have. Sizes are compared
# across paired runs instead, where they must not change.
proc ::tclmesh::views::structure {view} {
    lmap event $view {
        foreach part {inputs outputs} {
            set stripped {}
            dict for {name seen} [dict get $event $part] {
                if {[lindex $seen 0] eq "cipher"} {
                    set seen [lrange $seen 0 1]
                }
                lappend stripped $name $seen
            }
            dict set event $part $stripped
        }
        set event
    }
}

proc ::tclmesh::views::_output_view {circuit tokens} {
    set result {}
    foreach name [lsort [dict keys [dict get $circuit outputs]]] {
        set type [::tclmesh::private::_logical_type [dict get $circuit outputs $name]]
        lappend result $name [_cipher_view $type [dict get $tokens $name]]
    }
    return $result
}

proc ::tclmesh::views::_record {circuit prepared trace tokens} {
    variable log
    lappend log [dict create \
        operation evaluate \
        circuit [::tclmesh::private::digest $circuit] \
        inputs [_input_view $circuit $prepared] \
        trace [_trace $circuit $trace] \
        outputs [_output_view $circuit $tokens]]
}

proc ::tclmesh::views::_plain {prepared} {
    set values {}
    dict for {name tagged} $prepared {
        lassign $tagged visibility payload
        if {$visibility eq "cipher"} {
            dict set values $name [dict get $payload value]
        } else {
            dict set values $name $payload
        }
    }
    return $values
}

# Strict evaluation in schedule order: every node is computed, whatever the
# data, as a homomorphic evaluator must.
proc ::tclmesh::views::_strict {circuit values} {
    set cache {}
    set active {}
    set ids [schedule $circuit]
    foreach id $ids {
        ::tclmesh::private::_reference_node $circuit $id $values cache active
    }
    set results {}
    dict for {name id} [dict get $circuit metadata output_nodes] {
        dict set results $name [dict get $cache $id]
    }
    return [::list $results $ids]
}

# Lazy evaluation, as the plaintext reference does it: `select` computes only
# the taken branch. The order in which nodes complete is the trace.
proc ::tclmesh::views::_lazy {circuit values} {
    set cache {}
    set active {}
    set results {}
    set output_nodes [dict get $circuit metadata output_nodes]
    foreach name [lsort [dict keys $output_nodes]] {
        set id [dict get $output_nodes $name]
        dict set results $name [::tclmesh::private::_reference_node \
            $circuit $id $values cache active]
    }
    return [::list $results [dict keys $cache]]
}

# Recording backends. `transparent` is oblivious; `lazy` and `sized` are
# calibration breaks the harness must detect: a data-dependent trace, and a
# ciphertext size that depends on the plaintext.
proc ::tclmesh::views::_backend {mode operation args} {
    switch -- $operation {
        validate-profile {
            return true
        }
        encrypt {
            lassign $args profile type value
            return [_token $mode $value]
        }
        evaluate {
            lassign $args profile circuit prepared
            set values [_plain $prepared]
            if {$mode eq "lazy"} {
                lassign [_lazy $circuit $values] plain trace
            } else {
                lassign [_strict $circuit $values] plain trace
            }
            set tokens {}
            dict for {name value} $plain {
                dict set tokens $name [_token $mode $value]
            }
            _record $circuit $prepared $trace $tokens
            return $tokens
        }
        decrypt {
            lassign $args profile type token
            return [dict get $token value]
        }
        export-handle -
        restore-handle {
            # test backend: tokens hold plaintext, like the reference backend
            lassign $args profile type token
            return $token
        }
        combine-authorization-quorum {
            lassign $args profile type token contributions context
            if {[dict size $contributions] == 0} {
                return -code error \
                    -errorcode {TCLMESH VIEWS RELEASE EMPTY_CONTRIBUTIONS} \
                    "release requires contributions"
            }
            return [dict get $token value]
        }
        destroy {
            return
        }
        default {
            return -code error \
                -errorcode [::list TCLMESH VIEWS BACKEND INVALID_OPERATION $operation] \
                "recording backend does not support '$operation'"
        }
    }
}

proc ::tclmesh::views::_token {mode value} {
    if {$mode eq "sized"} {
        return [dict create value $value size [string length $value]]
    }
    return [dict create value $value]
}

foreach mode {transparent lazy sized} {
    ::tclmesh::private::backend::register views-$mode \
        [::list ::tclmesh::views::_backend $mode] {decrypt destroy reference reference-release authorization-quorum persistent-handles}
}
unset mode

# Runs a circuit on plaintext inputs: ciphertext inputs are encrypted under
# the profile, the circuit is evaluated, the outputs are decrypted. Returns the
# views of every party.
proc ::tclmesh::views::run {profile circuit inputs} {
    variable log
    set log {}
    set runtime {}
    dict for {name descriptor} [dict get $circuit inputs] {
        set value [dict get $inputs $name]
        if {[::tclmesh::private::_visibility $descriptor] eq "cipher"} {
            set value [::tclmesh::private::encrypt $profile \
                [::tclmesh::private::_logical_type $descriptor] $value]
        }
        dict set runtime $name $value
    }
    set handles [::tclmesh::private::evaluate $profile $circuit $runtime]
    set recipient {}
    foreach name [lsort [dict keys $handles]] {
        lappend recipient $name [::tclmesh::private::decrypt [dict get $handles $name]]
    }
    return [dict create evaluator $log recipient $recipient]
}

# What each party may observe: the evaluator learns only the circuit, the
# public inputs, the declared types and the syntactic trace; the recipient
# learns the outputs, as the reference semantics computes them.
proc ::tclmesh::views::declared {circuit inputs} {
    set circuit [::tclmesh::private::validate $circuit]
    set view {}
    foreach name [lsort [dict keys [dict get $circuit inputs]]] {
        set descriptor [dict get $circuit inputs $name]
        set type [::tclmesh::private::_logical_type $descriptor]
        if {[::tclmesh::private::_visibility $descriptor] eq "public"} {
            lappend view $name [::list public $type [dict get $inputs $name]]
        } else {
            lappend view $name [::list cipher $type]
        }
    }
    set outputs {}
    foreach name [lsort [dict keys [dict get $circuit outputs]]] {
        lappend outputs $name [::list cipher \
            [::tclmesh::private::_logical_type [dict get $circuit outputs $name]]]
    }
    set evaluator [::list [dict create \
        operation evaluate \
        circuit [::tclmesh::private::digest $circuit] \
        inputs $view \
        trace [_trace $circuit [schedule $circuit]] \
        outputs $outputs]]
    set reference [::tclmesh::private::_reference_evaluate $circuit $inputs]
    set recipient {}
    foreach name [lsort [dict keys $reference]] {
        lappend recipient $name [dict get $reference $name]
    }
    return [dict create evaluator $evaluator recipient $recipient]
}

# The views of `run` against `declared` on the given inputs, and the
# evaluator's views on pairs of inputs that agree on everything public:
# `variants` lists alternative values for the ciphertext inputs. The declared
# view is compared on structure; paired runs on everything, sizes included.
# Returns the mismatches found; an empty list means none.
proc ::tclmesh::views::paired {profile circuit inputs variants} {
    set findings {}
    set base [run $profile $circuit $inputs]
    set expected [declared $circuit $inputs]
    if {[structure [dict get $base evaluator]] ne [dict get $expected evaluator]} {
        lappend findings [::list declared evaluator $inputs]
    }
    if {[dict get $base recipient] ne [dict get $expected recipient]} {
        lappend findings [::list declared recipient $inputs]
    }
    foreach variant $variants {
        set other [dict merge $inputs $variant]
        set view [run $profile $circuit $other]
        if {[dict get $view evaluator] ne [dict get $base evaluator]} {
            lappend findings [::list paired evaluator $inputs $other]
        }
    }
    return $findings
}
