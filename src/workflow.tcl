namespace eval ::tclmesh::workflow {
    variable instances {}
    variable next_id 0
    variable store {}

    namespace export         use-store bind_manifest start describe list run-next retry recover
    namespace ensemble create
}

proc ::tclmesh::workflow::_commit {candidate_instances candidate_next_id} {
    variable instances
    variable next_id
    variable store

    if {$store ne ""} {
        ::tclmesh::store put $store workflow.registry [dict create             instances $candidate_instances             next_id $candidate_next_id]
    }

    set instances $candidate_instances
    set next_id $candidate_next_id
}

proc ::tclmesh::workflow::use-store {store_id} {
    variable instances
    variable next_id
    variable store

    if {$store_id eq ""} {
        set store {}
        return {}
    }

    ::tclmesh::store describe $store_id

    if {[::tclmesh::store exists $store_id workflow.registry]} {
        set state [::tclmesh::store get $store_id workflow.registry]
        foreach key {instances next_id} {
            if {![dict exists $state $key]} {
                return -code error                     -errorcode [::list TCLMESH WORKFLOW STORE INVALID_STATE $key]                     "workflow registry store is missing '$key'"
            }
        }
        set candidate_instances [dict get $state instances]
        set candidate_next_id [dict get $state next_id]
    } else {
        set candidate_instances $instances
        set candidate_next_id $next_id
        ::tclmesh::store put $store_id workflow.registry [dict create             instances $candidate_instances             next_id $candidate_next_id]
    }

    set instances $candidate_instances
    set next_id $candidate_next_id
    set store $store_id
    return $store
}

proc ::tclmesh::workflow::_dependencies {step} {
    if {[dict exists $step dependencies]} {
        return [dict get $step dependencies]
    }
    return {}
}

proc ::tclmesh::workflow::_validate_descriptor {workflow_id descriptor} {
    if {![dict exists $descriptor steps]} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW MISSING_STEPS $workflow_id]             "workflow '$workflow_id' must define steps"
    }

    set steps [dict get $descriptor steps]
    if {[dict size $steps] == 0} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW EMPTY_STEPS $workflow_id]             "workflow '$workflow_id' must define at least one step"
    }

    dict for {step_id step} $steps {
        if {![dict exists $step operation] || [dict get $step operation] eq ""} {
            return -code error                 -errorcode [::list TCLMESH WORKFLOW STEP MISSING_OPERATION $workflow_id $step_id]                 "workflow step '$step_id' requires an operation"
        }

        foreach dependency [_dependencies $step] {
            if {$dependency eq $step_id} {
                return -code error                     -errorcode [::list TCLMESH WORKFLOW STEP SELF_DEPENDENCY $workflow_id $step_id]                     "workflow step '$step_id' cannot depend on itself"
            }
            if {![dict exists $steps $dependency]} {
                return -code error                     -errorcode [::list TCLMESH WORKFLOW STEP UNKNOWN_DEPENDENCY                         $workflow_id $step_id $dependency]                     "workflow step '$step_id' depends on unknown step '$dependency'"
            }
        }

        if {[dict exists $step idempotent] &&
            ![string is boolean -strict [dict get $step idempotent]]} {
            return -code error                 -errorcode [::list TCLMESH WORKFLOW STEP INVALID_IDEMPOTENT                     $workflow_id $step_id]                 "workflow step '$step_id' idempotent must be boolean"
        }
    }

    # Reject dependency cycles with deterministic topological elimination.
    set remaining [lsort -dictionary [dict keys $steps]]
    set completed {}

    while {[llength $remaining] > 0} {
        set progressed 0
        set next {}

        foreach step_id $remaining {
            set ready 1
            foreach dependency [_dependencies [dict get $steps $step_id]] {
                if {$dependency ni $completed} {
                    set ready 0
                    break
                }
            }

            if {$ready} {
                lappend completed $step_id
                set progressed 1
            } else {
                lappend next $step_id
            }
        }

        if {!$progressed} {
            return -code error                 -errorcode [::list TCLMESH WORKFLOW CYCLE $workflow_id]                 "workflow '$workflow_id' contains a dependency cycle"
        }

        set remaining $next
    }

    return $descriptor
}

proc ::tclmesh::workflow::bind_manifest {manifest} {
    dict for {workflow_id descriptor} [dict get $manifest workflows] {
        _validate_descriptor $workflow_id $descriptor
    }
    return $manifest
}

proc ::tclmesh::workflow::_require {id} {
    variable instances

    if {![dict exists $instances $id]} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW NOT_FOUND $id]             "workflow instance '$id' does not exist"
    }

    return [dict get $instances $id]
}

proc ::tclmesh::workflow::_require_language {
    language_id actor_id workflow_id descriptor
} {
    set language [::tclmesh::language describe $language_id]

    if {[dict get $language status] ne "active"} {
        return -code error             -errorcode {TCLMESH WORKFLOW LANGUAGE INACTIVE}             "language '$language_id' is not active"
    }

    if {[dict get $language holder] ne $actor_id} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW LANGUAGE HOLDER_MISMATCH $language_id]             "language '$language_id' is not held by actor '$actor_id'"
    }

    if {$workflow_id ni [dict get $language commands]} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW COMMAND_NOT_GRANTED $workflow_id]             "language '$language_id' is not granted workflow '$workflow_id'"
    }

    set capability "workflow:$workflow_id"
    if {[dict exists $descriptor capability]} {
        set capability [dict get $descriptor capability]
    }

    if {$capability ni [dict get $language capabilities]} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW CAPABILITY_NOT_GRANTED $capability]             "language '$language_id' lacks workflow capability '$capability'"
    }

    return $language
}

proc ::tclmesh::workflow::_step_states {steps} {
    set states {}

    dict for {step_id step} $steps {
        set dependencies [_dependencies $step]
        set status [expr {
            [llength $dependencies] == 0 ? "ready" : "pending"
        }]

        dict set states $step_id [dict create             status $status             attempts 0             result {}             error {}]
    }

    return $states
}

proc ::tclmesh::workflow::_descriptor_for_instance {instance} {
    set manifest [::tclmesh::manifest get         [dict get $instance application_id]         [dict get $instance manifest_version]]

    if {[::tclmesh::manifest digest $manifest] ne
        [dict get $instance manifest_hash]} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW MANIFEST_MISMATCH                 [dict get $instance id]]             "workflow pinned manifest no longer matches its hash"
    }

    set workflow_id [dict get $instance workflow_id]
    if {![dict exists $manifest workflows $workflow_id]} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW DEFINITION_NOT_FOUND                 [dict get $instance application_id] $workflow_id]             "workflow '$workflow_id' is not defined"
    }

    return [dict get $manifest workflows $workflow_id]
}

proc ::tclmesh::workflow::_require_instance_language {instance descriptor} {
    return [_require_language         [dict get $instance language_id]         [dict get $instance actor_id]         [dict get $instance workflow_id]         $descriptor]
}

proc ::tclmesh::workflow::start {
    language_id application_id workflow_id request
} {
    variable instances
    variable next_id

    if {![dict exists $request actor_id] ||
        [dict get $request actor_id] eq ""} {
        return -code error             -errorcode {TCLMESH WORKFLOW ACTOR_REQUIRED}             "workflow start requires request actor_id"
    }

    set pin [::tclmesh::manifest active $application_id]
    set manifest [::tclmesh::manifest get         $application_id [dict get $pin version]]

    if {![dict exists $manifest workflows $workflow_id]} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW DEFINITION_NOT_FOUND                 $application_id $workflow_id]             "workflow '$workflow_id' is not defined"
    }

    set descriptor [dict get $manifest workflows $workflow_id]
    _require_language         $language_id         [dict get $request actor_id]         $workflow_id         $descriptor

    set candidate_next_id [expr {$next_id + 1}]
    set id "workflow:$candidate_next_id"

    set instance [dict create         id $id         status running         application_id $application_id         workflow_id $workflow_id         manifest_version [dict get $pin version]         manifest_hash [dict get $pin manifest_hash]         language_id $language_id         actor_id [dict get $request actor_id]         request $request         steps [_step_states [dict get $descriptor steps]]]

    set candidate_instances $instances
    dict set candidate_instances $id $instance
    _commit $candidate_instances $candidate_next_id

    ::tclmesh::audit append workflow.started         [dict create workflow_instance $id workflow $workflow_id]         [dict create             manifest_hash [dict get $pin manifest_hash]             actor_id [dict get $request actor_id]             language_id $language_id]

    return $instance
}

proc ::tclmesh::workflow::_ready_after_success {instance descriptor} {
    set states [dict get $instance steps]
    set steps [dict get $descriptor steps]

    dict for {step_id state} $states {
        if {[dict get $state status] ne "pending"} {
            continue
        }

        set ready 1
        foreach dependency [_dependencies [dict get $steps $step_id]] {
            if {[dict get $states $dependency status] ne "succeeded"} {
                set ready 0
                break
            }
        }

        if {$ready} {
            dict set states $step_id status ready
        }
    }

    dict set instance steps $states
    return $instance
}

proc ::tclmesh::workflow::_all_succeeded {states} {
    dict for {step_id state} $states {
        if {[dict get $state status] ne "succeeded"} {
            return 0
        }
    }
    return 1
}

proc ::tclmesh::workflow::_save_instance {instance} {
    variable instances
    variable next_id

    set candidate_instances $instances
    dict set candidate_instances [dict get $instance id] $instance
    _commit $candidate_instances $next_id
    return $instance
}

proc ::tclmesh::workflow::_audit {type instance step_id} {
    ::tclmesh::audit append $type         [dict create             workflow_instance [dict get $instance id]             step $step_id]         [dict create             manifest_hash [dict get $instance manifest_hash]             actor_id [dict get $instance actor_id]             language_id [dict get $instance language_id]]
}

proc ::tclmesh::workflow::run-next {id executor} {
    set instance [_require $id]
    if {[dict get $instance status] ne "running"} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW INVALID_STATE $id]             "workflow '$id' is not running"
    }

    set descriptor [_descriptor_for_instance $instance]
    _require_instance_language $instance $descriptor
    set states [dict get $instance steps]

    set ready {}
    dict for {step_id state} $states {
        if {[dict get $state status] eq "ready"} {
            lappend ready $step_id
        }
    }

    if {[llength $ready] == 0} {
        if {[_all_succeeded $states]} {
            dict set instance status succeeded
            return [_save_instance $instance]
        }

        return -code error             -errorcode [::list TCLMESH WORKFLOW NO_READY_STEP $id]             "workflow '$id' has no ready step"
    }

    set step_id [lindex [lsort -dictionary $ready] 0]
    set step_descriptor [dict get $descriptor steps $step_id]

    dict set instance steps $step_id status running
    set attempts [dict get $instance steps $step_id attempts]
    dict set instance steps $step_id attempts [expr {$attempts + 1}]
    set instance [_save_instance $instance]
    _audit workflow.step.started $instance $step_id

    set execution_context [dict create         workflow_instance $id         workflow_id [dict get $instance workflow_id]         step $step_id         request [dict get $instance request]         manifest_hash [dict get $instance manifest_hash]         actor_id [dict get $instance actor_id]         language_id [dict get $instance language_id]]

    set code [catch {
        {*}$executor execute             $step_id             $step_descriptor             $execution_context
    } result options]

    if {$code} {
        set errorcode {}
        if {[dict exists $options -errorcode]} {
            set errorcode [dict get $options -errorcode]
        }

        set instance [_require $id]
        dict set instance status failed
        dict set instance steps $step_id status failed
        dict set instance steps $step_id error [dict create             message $result             errorcode $errorcode]
        set instance [_save_instance $instance]
        _audit workflow.step.failed $instance $step_id
        return $instance
    }

    set instance [_require $id]
    dict set instance steps $step_id status succeeded
    dict set instance steps $step_id result $result
    set instance [_ready_after_success $instance $descriptor]

    if {[_all_succeeded [dict get $instance steps]]} {
        dict set instance status succeeded
    }

    set instance [_save_instance $instance]
    _audit workflow.step.succeeded $instance $step_id
    return $instance
}

proc ::tclmesh::workflow::retry {id step_id} {
    set instance [_require $id]
    if {[dict get $instance status] ne "failed"} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW RETRY INVALID_STATE $id]             "workflow '$id' is not failed"
    }

    if {![dict exists $instance steps $step_id] ||
        [dict get $instance steps $step_id status] ne "failed"} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW RETRY INVALID_STEP $id $step_id]             "workflow step '$step_id' is not failed"
    }

    set descriptor [_descriptor_for_instance $instance]
    _require_instance_language $instance $descriptor

    set step_descriptor [dict get $descriptor steps $step_id]
    if {![dict exists $step_descriptor idempotent] ||
        ![dict get $step_descriptor idempotent]} {
        return -code error \
            -errorcode [::list TCLMESH WORKFLOW RETRY IDEMPOTENCY_REQUIRED $id $step_id] \
            "retry requires an idempotent workflow step; reconcile its external outcome instead"
    }

    dict set instance status running
    dict set instance steps $step_id status ready
    dict set instance steps $step_id error {}
    set instance [_save_instance $instance]
    _audit workflow.step.retry $instance $step_id
    return $instance
}

proc ::tclmesh::workflow::recover {id step_id disposition {result {}}} {
    set instance [_require $id]

    if {![dict exists $instance steps $step_id] ||
        [dict get $instance steps $step_id status] ni {running failed}} {
        return -code error             -errorcode [::list TCLMESH WORKFLOW RECOVERY INVALID_STEP $id $step_id]             "workflow step '$step_id' is not running or failed"
    }

    set descriptor [_descriptor_for_instance $instance]
    _require_instance_language $instance $descriptor
    set step_descriptor [dict get $descriptor steps $step_id]

    switch -- $disposition {
        retry {
            if {![dict exists $step_descriptor idempotent] ||
                ![dict get $step_descriptor idempotent]} {
                return -code error                     -errorcode [::list TCLMESH WORKFLOW RECOVERY IDEMPOTENCY_REQUIRED                         $id $step_id]                     "retry recovery requires an idempotent workflow step"
            }
            dict set instance status running
            dict set instance steps $step_id status ready
            dict set instance steps $step_id error {}
        }
        succeeded {
            dict set instance steps $step_id status succeeded
            dict set instance steps $step_id result $result
            set instance [_ready_after_success $instance $descriptor]
            if {[_all_succeeded [dict get $instance steps]]} {
                dict set instance status succeeded
            } else {
                dict set instance status running
            }
        }
        failed {
            dict set instance status failed
            dict set instance steps $step_id status failed
            dict set instance steps $step_id error $result
        }
        default {
            return -code error                 -errorcode [::list TCLMESH WORKFLOW RECOVERY INVALID_DISPOSITION                     $disposition]                 "workflow recovery disposition must be retry, succeeded, or failed"
        }
    }

    set instance [_save_instance $instance]
    _audit "workflow.step.recovered.$disposition" $instance $step_id
    return $instance
}

proc ::tclmesh::workflow::describe {id} {
    return [_require $id]
}

proc ::tclmesh::workflow::list {} {
    variable instances
    return [lsort -dictionary [dict keys $instances]]
}
