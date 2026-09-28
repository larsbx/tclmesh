# TclMesh v0.1.0 Quickstart

## Requirements

- TCL 8.6 or newer
- Tcllib `sha256`

Add the repository root to `auto_path` and load the package:

```tcl
lappend auto_path /path/to/tclmesh
package require tclmesh 0.1.0
```

## Define and install a manifest

```tcl
set manifest [tclmesh manifest new shipping 1]

dict set manifest actions Shipment::accept [dict create \
    kind update \
    capability shipment:accept \
    authorize {permit} \
    deontic {N} \
    validations [list \
        [list assert [list eq [list field status] [list literal proposed]]]] \
    changes [list \
        [list set status [list literal accepted]]] \
    effects [list \
        [list emit audit status [list field status]]]]

set installed [tclmesh manifest install $manifest]

tclmesh manifest activate \
    shipping \
    1 \
    [dict get $installed manifest_hash]
```

Installation is immutable and versioned. Activation is a separate hash-bound operation.

## Create a holder-bound language

```tcl
set language [tclmesh language instantiate \
    Operator \
    user:alice \
    {Shipment::accept} \
    {shipment:accept}]
```

A language instance carries vocabulary and capabilities. Delegated children can only narrow the parent's commands, capabilities, and context.

## Run an authoritative action

The application supplies a storage adapter with three operations:

```text
transact callback
load request
persist request state
```

Then:

```tcl
set result [tclmesh action run \
    $language \
    shipping \
    Shipment::accept \
    ::myapp::storage \
    [dict create \
        object_id shipment-1 \
        actor_id user:alice \
        expected_manifest_hash [dict get $installed manifest_hash]]]
```

The runtime verifies the active manifest, actor/language holder binding, action command, capability, authorization, deontic verdict, validations, changes, and persistence guard.

## Execute proposed effects

State mutation and external effects are intentionally separate.

```tcl
set effect_spec [lindex [dict get $result effects proposed] 0]

set proposed [tclmesh effect propose \
    $effect_spec \
    [dict create \
        manifest_hash [dict get $result manifest_hash] \
        action [dict get $result action] \
        actor_id [dict get $result actor_id] \
        idempotency_key shipment-1:accept:audit]]

tclmesh effect authorize [dict get $proposed id] permit
tclmesh effect execute [dict get $proposed id] ::myapp::effect_driver
```

The reference effect ledger enforces lifecycle and idempotency. It is memory-backed in v0.1.0; production deployments should persist the ledger behind their application boundary.

## Private-computation IR

v0.1.0 validates private-computation circuit IR but does not include a cryptographic execution backend.

```tcl
set circuit [tclmesh private circuit score \
    {x {cipher uint32}} \
    {total {cipher uint32}} \
    [dict create \
        n1 [tclmesh private node input x] \
        n2 [tclmesh private node constant 1] \
        n3 [tclmesh private node add n1 n2]]]

tclmesh private validate $circuit
```

Run the full executable example:

```text
tclsh examples/shipment.tcl
```

Expected output:

```text
accepted|N|succeeded|private-ir-ok
```
