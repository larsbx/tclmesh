# TclMesh

TclMesh is a TCL reference kernel for building hash-bound application semantics with capability-scoped languages, canonical actions, fivefold deontic judgments, durable workflows, private-computation backends, opaque ciphertext handles, and threshold-governed release.

**Current release target:** v0.3.0 reference kernel.

TCL may be highly dynamic while defining meaning; authoritative execution is reduced to typed, canonical, versioned, hash-bound, capability-bounded manifest data.

## What v0.3.0 ships

- immutable, versioned manifest installation and hash-bound activation;
- deterministic safe compiler interpreter with compilation-local gensym;
- canonical action/value/predicate validation;
- transaction-guarded state transitions;
- active-language and holder-bound capability enforcement;
- attenuating user/agent language delegation;
- W/N/M/K/H deontic resolution with explicit conflicts;
- idempotent effect lifecycle and uncertain-execution reconciliation;
- pluggable persistent registries and atomic single-process file storage;
- durable manifest-pinned workflows with retry/reconciliation;
- append-only structured audit stream;
- private-computation backend protocol;
- immutable private parameter profiles;
- opaque ct:* ciphertext handles bound to backend/profile/type;
- stronger private-circuit graph validation;
- plaintext reference backend for deterministic testing only;
- plaintext/backend differential execution;
- profile-gated direct decryption;
- threshold-release requests with fixed holders, quorum, purpose binding, persistence, and uncertain-combine recovery;
- executable shipping and private-release examples.

v0.3.0 does **not** claim FULL v1 conformance and does **not** ship a confidential homomorphic-encryption backend. The built-in plaintext backend is a reference backend whose values are not secret from the host process.

## Install

Requirements:

- TCL 8.6 or newer;
- Tcllib sha256.

Add the repository root to auto_path:

    lappend auto_path /path/to/tclmesh
    package require tclmesh 0.3.0

## Run the examples

Application/action/effect path:

    tclsh examples/shipment.tcl

Expected:

    accepted|N|succeeded|private-ir-ok

Private backend + threshold release path:

    tclsh examples/private_release.tcl

Expected:

    differential:true|released:42

The private example demonstrates:

1. defining an immutable backend profile;
2. constructing and validating a private circuit;
3. differential execution against the reference backend;
4. encrypting into an opaque ct:* handle;
5. forbidding direct decryption through profile policy;
6. creating a 2-of-3 release request;
7. collecting unique holder contributions;
8. releasing only after quorum.

## Test

    tclsh tests/all.tcl

The top-level test runner propagates failures to the process exit status. CI injects an intentional failing test to verify that property, then runs the normal suite and release self-check.

## Core boundaries

TclMesh preserves these boundaries:

1. TCL syntax vs. canonical semantics.
2. Decision vs. external effect.
3. Deontic judgment vs. authorization/execution.
4. Language vocabulary vs. underlying authority.
5. Private circuit semantics vs. backend implementation.
6. Opaque ciphertext handles vs. backend tokens.
7. Direct decryption vs. threshold-governed release.
8. Extensible declaration logic vs. a small authoritative runtime.

## Documentation

- [Quickstart](docs/quickstart.md)
- [Architecture](docs/architecture.md)
- [Normative v1 target](docs/spec-v1.md)
- [Roadmap and release scope](docs/roadmap.md)
- [Security](SECURITY.md)
- [Changelog](CHANGELOG.md)

## Release status

v0.3.0 is suitable as a **reference-kernel/source release** and for controlled integrations that provide appropriate durable storage, trusted adapters, and—if confidentiality is required—a real private-computation backend.

The built-in file store is a single-process reference persistence adapter. It does not provide multi-process locking or distributed consistency.

The repository currently does not declare an open-source license; publication of a tag or source archive does not by itself grant additional reuse rights.
