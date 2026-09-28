# TclMesh

TclMesh is a TCL reference kernel for building hash-bound application semantics with capability-scoped languages, canonical actions, fivefold deontic judgments, idempotent effects, and private-computation circuit IR.

**Current release target:** v0.1.0 reference kernel.

TCL may be highly dynamic while defining meaning; authoritative execution is reduced to typed, canonical, versioned, hash-bound, capability-bounded manifest data.

## What v0.1.0 ships

- immutable, versioned manifest installation;
- schema-aware canonical manifest hashing;
- explicit hash-bound activation;
- canonical action operations rather than mutable runtime callbacks;
- transaction-guarded state transitions;
- active-language and holder-bound capability enforcement;
- attenuating user/agent language delegation;
- W/N/M/K/H deontic resolution with explicit conflicts;
- idempotent effect proposal, authorization, and execution lifecycle;
- private-computation circuit IR construction and validation;
- macro registry/expansion primitives;
- executable end-to-end example and acceptance tests.

v0.1.0 does **not** claim FULL v1 conformance. Durable workflow/ceremony execution, process supervision, persistent registries, and cryptographic private-computation execution remain on the roadmap.

## Install

Requirements:

- TCL 8.6 or newer;
- Tcllib `sha256`.

Add the repository root to `auto_path`:

```tcl
lappend auto_path /path/to/tclmesh
package require tclmesh 0.1.0
```

## Run the example

```text
tclsh examples/shipment.tcl
```

Expected output:

```text
accepted|N|succeeded|private-ir-ok
```

The example demonstrates:

1. canonical manifest definition;
2. immutable installation and hash-bound activation;
3. a holder-bound language instance;
4. guarded action execution;
5. fivefold deontic resolution;
6. effect proposal and idempotent execution;
7. private-circuit IR validation.

## Test

```text
tclsh tests/all.tcl
```

The top-level test runner propagates failures to the process exit status. CI also injects an intentional failing test to verify that invariant.

## Core boundaries

TclMesh preserves six boundaries:

1. TCL syntax vs. canonical semantics.
2. Decision vs. external effect.
3. Deontic judgment vs. authorization/execution.
4. Language vocabulary vs. underlying authority.
5. Private-computation IR vs. plaintext release.
6. Extensible declaration logic vs. a small authoritative runtime.

## Documentation

- [Quickstart](docs/quickstart.md)
- [Architecture](docs/architecture.md)
- [Normative v1 target](docs/spec-v1.md)
- [Roadmap and v0.1 scope](docs/roadmap.md)
- [Security](SECURITY.md)
- [Changelog](CHANGELOG.md)

## Release status

v0.1.0 is suitable as a **reference-kernel/source release** and for controlled integrations that provide appropriate durable storage and trusted adapters.

The in-memory registries are intentionally reference implementations. Applications requiring crash durability, multi-process authority, or distributed consistency must supply durable deployment boundaries before treating those registries as production authorities.

The repository currently does not declare an open-source license; publication of a tag or source archive does not by itself grant additional reuse rights.
