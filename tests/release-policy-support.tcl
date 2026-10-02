# Helpers shared by ordinary conformance tests and independent child processes.
proc policytest_manifest {app version} {
    set circuit [tclmesh private circuit aggregate {} [dict create total {cipher int} other {cipher int}] \
        [dict create total {constant 42} other {constant 99}] \
        [dict create output_nodes [dict create total total other other] \
            profile policy-profile release_policy report]]
    set manifest [tclmesh manifest new $app $version]
    dict set manifest circuits aggregate $circuit
    dict set manifest ceremonies report [dict create kind threshold-release \
        circuit aggregate output total purpose quarterly-report profile policy-profile \
        quorum 2 holders {b a} requesters {operator} combiners {operator} recoverers {operator} \
        request_capability release:request contribute_capability release:share \
        combine_capability release:combine recover_capability release:recover \
        context [dict create tenant example]]
    return $manifest
}
proc policytest_profile {} {
    if {[catch {tclmesh private profile describe policy-profile}]} {
        # Even a backend profile permitting direct decrypt must not bypass policy.
        tclmesh private profile define policy-profile [dict create \
            backend plaintext semantics exact-integer allow_decrypt true]
    }
}
proc policytest_setup {app} {
    policytest_profile
    set installed [tclmesh manifest install [policytest_manifest $app 1]]
    tclmesh manifest activate $app 1 [dict get $installed manifest_hash]
    set language [tclmesh language instantiate release-operator operator {release:report} \
        {release:request release:combine release:recover} [dict create tenant example]]
    set a [tclmesh language instantiate release-holder a {release:report} \
        {release:share} [dict create tenant example]]
    set b [tclmesh language instantiate release-holder b {release:report} \
        {release:share} [dict create tenant example]]
    set outputs [tclmesh private evaluate-bound policy-profile $app aggregate {}]
    return [dict create operator $language a $a b $b outputs $outputs]
}
proc policytest_request {setup} {
    return [tclmesh release request-authorized [dict get $setup operator] \
        [dict get $setup outputs total] operator [dict create tenant example]]
}
proc policytest_quorum {setup id} {
    tclmesh release contribute-authorized [dict get $setup a] $id a share-a
    tclmesh release contribute-authorized [dict get $setup b] $id b share-b
}
