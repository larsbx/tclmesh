set here [file dirname [file normalize [info script]]]
set root [file dirname $here]
lappend auto_path $root

package require tclmesh 0.1.0

namespace eval ::demo {
    variable state [dict create id shipment-1 status proposed]
    variable in_transaction 0
}

proc ::demo::storage {operation args} {
    variable state
    variable in_transaction

    switch -- $operation {
        transact {
            if {$in_transaction} {
                error "nested transaction"
            }
            set in_transaction 1
            try {
                set result [uplevel #0 [lindex $args 0]]
            } finally {
                set in_transaction 0
            }
            return $result
        }
        load {
            if {!$in_transaction} {
                error "load outside transaction"
            }
            return $state
        }
        persist {
            if {!$in_transaction} {
                error "persist outside transaction"
            }
            set state [lindex $args 1]
            return $state
        }
        default {
            error "unknown storage operation '$operation'"
        }
    }
}

proc ::demo::effect_driver {operation effect context} {
    if {$operation ne "execute"} {
        error "unknown effect operation '$operation'"
    }
    return [dict create recorded true type [dict get $effect type]]
}

set manifest [tclmesh manifest new shipping-demo 1]
dict set manifest actions Shipment::accept [dict create     kind update     capability shipment:accept     authorize {permit}     deontic {N}     validations [list         [list assert [list eq [list field status] [list literal proposed]]]]     changes [list         [list set status [list literal accepted]]]     effects [list         [list emit audit status [list field status]]]]

set installed [tclmesh manifest install $manifest]
tclmesh manifest activate     shipping-demo     1     [dict get $installed manifest_hash]

set language [tclmesh language instantiate     Operator     user:alice     {Shipment::accept}     {shipment:accept}]

set result [tclmesh action run     $language     shipping-demo     Shipment::accept     ::demo::storage     [dict create         object_id shipment-1         actor_id user:alice         expected_manifest_hash [dict get $installed manifest_hash]]]

set effect_spec [lindex [dict get $result effects proposed] 0]
set effect [tclmesh effect propose     $effect_spec     [dict create         manifest_hash [dict get $result manifest_hash]         action [dict get $result action]         actor_id [dict get $result actor_id]         idempotency_key shipment-1:accept:audit]]

tclmesh effect authorize [dict get $effect id] permit
set completed [tclmesh effect execute [dict get $effect id] ::demo::effect_driver]

set circuit [tclmesh private circuit score     {x {cipher uint32}}     {total {cipher uint32}}     [dict create         n1 [tclmesh private node input x]         n2 [tclmesh private node constant 1]         n3 [tclmesh private node add n1 n2]]]
tclmesh private validate $circuit

puts [join [list     [dict get $result result status]     [dict get $result deontic verdict]     [dict get $completed status]     private-ir-ok] |]
