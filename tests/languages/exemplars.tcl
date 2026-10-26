# Exemplar encrypted languages (docs/testing.md): one per decision pattern.
# Each is a dict: name, decision, circuit, inputs (plaintext), variants
# (other ciphertext inputs with the same public inputs), and optionally a
# threshold release of one output.

namespace eval ::exemplars {}

proc ::exemplars::node {args} { tclmesh private node {*}$args }

# Oblivious: a sealed-bid auction. The auctioneer learns the winning bid and
# whether it clears the reserve; the evaluator learns nothing about the bids.
proc ::exemplars::sealed_bid {} {
    dict create name sealed-bid decision oblivious \
        circuit [tclmesh private circuit sealed-bid \
            [dict create a {cipher int} b {cipher int} reserve {public int}] \
            [dict create winner {cipher int} clears {cipher bool} margin {cipher int}] \
            [dict create \
                na [node input a] nb [node input b] nr [node input reserve] \
                gt [node greater-than na nb] \
                winner [node select gt na nb] \
                clears [node greater-or-equal winner nr] \
                ab [node subtract na nb] ba [node subtract nb na] \
                margin [node select gt ab ba]] \
            [dict create output_nodes [dict create winner winner clears clears margin margin]]] \
        inputs [dict create a 120 b 95 reserve 100] \
        variants {{a 10 b 300} {a 7 b 7} {a 0 b -1}}
}

# Released: a second-price auction. The clearing price (the lower bid) is
# released by two of three holders; nothing else is ever decrypted.
proc ::exemplars::second_price {} {
    dict create name second-price decision released \
        circuit [tclmesh private circuit second-price \
            [dict create a {cipher int} b {cipher int}] \
            [dict create price {cipher int}] \
            [dict create \
                na [node input a] nb [node input b] \
                gt [node greater-than na nb] \
                price [node select gt nb na]] \
            [dict create output_nodes [dict create price price]]] \
        inputs [dict create a 120 b 95] \
        variants {{a 1 b 2} {a 50 b 50}} \
        release [dict create output price threshold 2 holders {holder:a holder:b holder:c}]
}

# Oblivious policy check: a member, or an adult under a public age limit.
proc ::exemplars::policy_boolean {} {
    dict create name policy-boolean decision oblivious \
        circuit [tclmesh private circuit policy-boolean \
            [dict create member {cipher bool} age {cipher int} limit {public int}] \
            [dict create ok {cipher bool}] \
            [dict create \
                nm [node input member] na [node input age] nl [node input limit] \
                adult [node greater-or-equal na nl] \
                ok [node or nm adult]] \
            [dict create output_nodes [dict create ok ok]]] \
        inputs [dict create member 0 age 30 limit 18] \
        variants {{member 1 age 3} {member 0 age 12} {member 1 age 70}}
}

# The same policy in an arithmetic encoding: ok = 1 − (1 − member)(1 − adult).
# A metamorphic twin of `policy_boolean`: equal results on every input.
proc ::exemplars::policy_arithmetic {} {
    dict create name policy-arithmetic decision oblivious \
        circuit [tclmesh private circuit policy-arithmetic \
            [dict create member {cipher bool} age {cipher int} limit {public int}] \
            [dict create ok {cipher int}] \
            [dict create \
                nm [node input member] na [node input age] nl [node input limit] \
                one [node constant 1] \
                adult [node greater-or-equal na nl] \
                notm [node subtract one nm] nota [node subtract one adult] \
                both [node multiply notm nota] \
                ok [node subtract one both]] \
            [dict create output_nodes [dict create ok ok]]] \
        inputs [dict create member 0 age 30 limit 18] \
        variants {{member 1 age 3} {member 0 age 12} {member 1 age 70}}
}

# Oblivious set membership: is the secret code one of three public codes?
proc ::exemplars::set_membership {} {
    dict create name set-membership decision oblivious \
        circuit [tclmesh private circuit set-membership \
            [dict create x {cipher int} s1 {public int} s2 {public int} s3 {public int}] \
            [dict create member {cipher bool}] \
            [dict create \
                nx [node input x] n1 [node input s1] n2 [node input s2] n3 [node input s3] \
                e1 [node equal nx n1] e2 [node equal nx n2] e3 [node equal nx n3] \
                e12 [node or e1 e2] member [node or e12 e3]] \
            [dict create output_nodes [dict create member member]]] \
        inputs [dict create x 404 s1 200 s2 404 s3 500] \
        variants {{x 0} {x 200} {x 501}}
}

# Not yet expressible in the runtime, listed so the gap stays visible:
#   proved     an encrypted range check (age ≥ 18) proved in zero knowledge by
#              the key holder (security/src/zk.rs tests the Σ-protocol layer);
#   typed-leak deterministic encryption, declared and charged as leakage.
proc ::exemplars::pending {} {
    list proved typed-leak
}

proc ::exemplars::all {} {
    list [sealed_bid] [second_price] [policy_boolean] [policy_arithmetic] [set_membership]
}
