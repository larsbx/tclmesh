# TclMesh

TclMesh is a TCL application fabric for building resource-oriented, macro-extensible, capability-scoped applications with fivefold deontic rules, task/user/agent-specific languages, supervised workflows, and privacy-preserving computation.

## Core thesis

TCL may be highly dynamic while defining meaning; authoritative execution must depend on typed, canonical, versioned, hash-bound, capability-bounded, inspectable manifest data.

The project is organized around six hard boundaries:

1. TCL syntax vs. canonical semantics.
2. Decision vs. effect.
3. Deontic judgment vs. authorization.
4. Language vocabulary vs. underlying authority.
5. Encrypted computation vs. plaintext release.
6. Extensible declaration layer vs. a small trusted runtime.

## Architecture

```text
TCL declarations and macros
        |
        v
compiler and verifier
        |
        v
canonical manifest
        |
        +--> resource/action runtime
        +--> policy and deontic resolver
        +--> language-instance runtime
        +--> workflow and ceremony runtime
        +--> private-computation runtime
        +--> effect ledger and supervision
```

## Conformance profiles

- CORE — resources, types, actions, queries, manifests.
- MACRO — declaration, expression, and semantic macros.
- POLICY — capabilities and authorization.
- DEONTIC — W/N/M/K/H judgments, conflicts, defeat, certificates.
- LANGUAGE — language packages, instances, delegation, lifecycle.
- WORKFLOW — durable workflows, retry, compensation.
- PRIVATE — encrypted types, circuit IR, release policy and threshold release.
- SUPERVISION — supervised runtime units and recovery.
- FULL — all profiles.

See [docs/architecture.md](docs/architecture.md) and [docs/spec-v1.md](docs/spec-v1.md).
