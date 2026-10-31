# TFHE backend (backends/tfhe): circuits evaluated under real homomorphic
# encryption by the `tclmesh-tfhe` process. Registered as backend `tfhe` when
# the binary exists: $TCLMESH_TFHE, or backends/tfhe/target/release.
#
# Integers are `W`-bit words, `FheInt32` or `FheInt64`: arithmetic wraps
# modulo 2^W, as profiles must declare. Under `semantics int<W>-wrapping`
# results equal the exact reference only while every intermediate value fits;
# under `int<W>-checked` the runtime evaluates only circuits whose range
# certificate proves that they all do (src/range.tcl, spec/TclMesh/Range.lean).
# A profile claiming exact integers unconditionally is rejected, since an
# overflow under encryption cannot be detected.
#
# Proven inputs (`private publish`, `private import`): an encrypting party
# proves its ciphertext's range in zero knowledge with `tclmesh-tfhe-prove`,
# using only the published public key and CRS (backends/tfhe/src/lib.rs).
#
# Tokens are `{tfhe ID bytes N}`: an opaque number for a ciphertext held by
# the process, and its serialized size. Evaluation is recorded through the
# view harness (`tclmesh views`), so paired runs check the trace of real
# homomorphic evaluation; sizes are checked separately (tests/tfhe.test).

namespace eval ::tclmesh::tfhe {
    variable channel {}
    variable binary {}
}

proc ::tclmesh::tfhe::_locate {root} {
    if {[info exists ::env(TCLMESH_TFHE)] && [file executable $::env(TCLMESH_TFHE)]} {
        return $::env(TCLMESH_TFHE)
    }
    set candidate [file join $root backends tfhe target release tclmesh-tfhe]
    if {[file executable $candidate]} {
        return $candidate
    }
    return {}
}

proc ::tclmesh::tfhe::_call {request} {
    variable channel
    variable binary
    package require json
    if {$channel eq ""} {
        set channel [open |[list $binary] r+]
        fconfigure $channel -buffering line -translation lf -encoding utf-8
    }
    puts $channel $request
    flush $channel
    if {[gets $channel line] < 0} {
        return -code error -errorcode {TCLMESH TFHE PROCESS_EXITED} "tclmesh-tfhe exited"
    }
    set response [json::json2dict $line]
    if {[dict exists $response error]} {
        return -code error -errorcode [list TCLMESH TFHE [dict get $response error]] \
            "tfhe backend: [dict get $response error]"
    }
    return $response
}

proc ::tclmesh::tfhe::_s {value} { json::write string $value }

# The word width W of a profile's `int<W>-…` semantics.
proc ::tclmesh::tfhe::_width {profile} {
    regexp {^int(32|64)-(?:wrapping|checked)$} [dict get $profile semantics] -> width
    return $width
}

proc ::tclmesh::tfhe::_token {response} {
    list tfhe [dict get $response token] bytes [dict get $response bytes]
}

proc ::tclmesh::tfhe::_backend {operation args} {
    package require json::write
    json::write indented 0
    json::write aligned 0
    switch -- $operation {
        validate-profile {
            lassign $args profile
            return [regexp {^int(32|64)-(wrapping|checked)$} [dict get $profile semantics]]
        }
        encrypt {
            lassign $args profile type value
            return [_token [_call [json::write object \
                op [_s encrypt] type [_s $type] value [_s $value] width [_width $profile]]]]
        }
        evaluate {
            lassign $args profile circuit prepared
            set types {}
            set inputs {}
            dict for {name descriptor} [dict get $circuit inputs] {
                lappend types $name [_s [::tclmesh::private::_logical_type $descriptor]]
                lassign [dict get $prepared $name] visibility payload
                if {$visibility eq "cipher"} {
                    lappend inputs $name [json::write object cipher [lindex $payload 1]]
                } else {
                    lappend inputs $name [json::write object public [_s $payload]]
                }
            }
            set nodes {}
            dict for {id node} [dict get $circuit nodes] {
                lappend nodes $id [json::write array {*}[lmap word $node {_s $word}]]
            }
            set outputs {}
            dict for {name id} [dict get $circuit metadata output_nodes] {
                lappend outputs $name [_s $id]
            }
            set response [_call [json::write object \
                op [_s evaluate] \
                input_types [json::write object {*}$types] \
                inputs [json::write object {*}$inputs] \
                nodes [json::write object {*}$nodes] \
                output_nodes [json::write object {*}$outputs] \
                width [_width $profile]]]
            set tokens {}
            dict for {name result} [dict get $response outputs] {
                dict set tokens $name [_token $result]
            }
            ::tclmesh::views::_record $circuit $prepared [dict get $response trace] $tokens
            return $tokens
        }
        decrypt {
            lassign $args profile type token
            return [dict get [_call [json::write object \
                op [_s decrypt] token [lindex $token 1]]] value]
        }
        combine-release -
        verify-contribution -
        combine-verified-release {
            return -code error -errorcode {TCLMESH TFHE RELEASE CRYPTOGRAPHIC_THRESHOLD_UNAVAILABLE} \
                "single-key TFHE does not implement cryptographic threshold decryption"
        }
        combine-authorization-quorum {
            lassign $args profile type token contributions context
            if {[dict size $contributions] == 0} {
                return -code error -errorcode {TCLMESH TFHE RELEASE EMPTY_CONTRIBUTIONS} \
                    "authorization-only release requires approvals"
            }
            return [dict get [_call [json::write object \
                op [_s decrypt] token [lindex $token 1]]] value]
        }
        publish {
            lassign $args profile dir crs trusted
            set adopt [expr {$crs eq "" ? {} : [::list crs [_s [file normalize $crs]]]}]
            if {[llength $trusted] > 0} {
                lappend adopt trusted [json::write array \
                    {*}[lmap key $trusted {_s [file normalize $key]}]]
            }
            _call [json::write object op [_s publish] dir [_s [file normalize $dir]] {*}$adopt]
            return
        }
        import {
            lassign $args profile proof context lo bits hi
            set bound [expr {$hi eq "" ? {} : [::list hi [_s $hi]]}]
            return [_token [_call [json::write object op [_s import] \
                proof [_s [file normalize $proof]] context [_s $context] lo [_s $lo] bits $bits \
                width [_width $profile] {*}$bound]]]
        }
        export-handle {
            lassign $args profile type token
            return [_call [json::write object op [_s export] token [lindex $token 1]]]
        }
        restore-handle {
            lassign $args profile type recovery
            return [_token [_call [json::write object op [_s restore] \
                keyset [_s [dict get $recovery keyset]] kind [_s [dict get $recovery kind]] \
                ciphertext [_s [dict get $recovery ciphertext]]]]]
        }
        destroy {
            set token [lindex $args end]
            _call [json::write object op [_s destroy] token [lindex $token 1]]
            return
        }
        default {
            return -code error \
                -errorcode [list TCLMESH TFHE INVALID_OPERATION $operation] \
                "tfhe backend does not support '$operation'"
        }
    }
}

set ::tclmesh::tfhe::binary [::tclmesh::tfhe::_locate [file dirname $::tclmesh::here]]
# Handles persist only with persistent keys: $TCLMESH_TFHE_KEYS names the
# directory that holds them (and an adopted CRS). Recovery material is a
# ciphertext bound to its keyset, refused under any other.
proc ::tclmesh::tfhe::capabilities {} {
    return [concat {decrypt destroy authorization-quorum homomorphic proven-inputs} \
        [expr {[info exists ::env(TCLMESH_TFHE_KEYS)] ? "persistent-handles" : ""}]]
}
if {$::tclmesh::tfhe::binary ne ""} {
    ::tclmesh::private::backend::register tfhe ::tclmesh::tfhe::_backend [::tclmesh::tfhe::capabilities]
}

# The encrypting party's tool (`tclmesh-tfhe-prove`), built beside the
# backend: it needs only what `private publish` writes, never the secret key.
proc ::tclmesh::tfhe::prover {} {
    variable binary
    file join [file dirname $binary] tclmesh-tfhe-prove
}

# The CRS tool (`tclmesh-tfhe-crs`): a multi-party ceremony
# (`keygen`, `init|contribute|verify DIR`) or a one-party CRS file, either
# adopted with `private publish PROFILE DIR CRS ?TRUSTED?`.
proc ::tclmesh::tfhe::crs-generator {} {
    variable binary
    file join [file dirname $binary] tclmesh-tfhe-crs
}

