# Changelog

## 0.3.0

- private-computation backend registration and capability protocol;
- immutable backend parameter profiles;
- opaque ciphertext handles with explicit destruction and profile/type checks;
- recursive private-circuit arity/reference/cycle/output validation;
- plaintext reference backend for deterministic development and tests;
- exact/tolerance-aware differential execution against backend results;
- profile-gated direct decryption;
- threshold-release requests bound to one handle/profile, purpose, holder set, and quorum;
- persistent release request state, terminal rejection/expiry, and uncertain-combine reconciliation;
- reference threshold-release backend path with idempotent retry support.

Security note: the built-in plaintext backend provides no confidentiality and its threshold contributions are not cryptographic shares. Confidentiality requires a separate backend with appropriate cryptographic guarantees.

## 0.2.0

- safe compiler interpreters, resource limits, and hygienic `gensym`;
- richer canonical comparisons, membership, and containment;
- persistent manifest, language, effect, workflow, and audit registries;
- single-process atomic file storage and uncertain-effect reconciliation;
- durable manifest-pinned workflows and append-only audit events;
- reject NaN ordered operands even under negation;
- require declared idempotency for failed-step retry; permit explicit external
  success/failure reconciliation without replay.

Reference-kernel release only: no distributed consistency, cryptographic private
execution, ceremony engine, or process supervision conformance claim.

## 0.1.0

Initial TclMesh reference-kernel release.

### Added

- versioned immutable manifest registry;
- schema-aware canonical manifest hashing;
- explicit hash-bound manifest activation;
- canonical action runtime;
- transaction-guarded state transitions;
- holder-bound language capability enforcement;
- attenuating language delegation;
- fivefold deontic verdict resolution;
- explicit deontic execution blocking;
- idempotent effect ledger and effect-driver boundary;
- private-computation circuit IR validation;
- macro registry primitives;
- executable quickstart and end-to-end acceptance test;
- truthful test-process exit status.

### Security boundaries

- authoritative manifests reject mutable Tcl action callbacks;
- parent language lineage can only be created through delegation;
- state mutation and external effects remain separate;
- private circuit support in this release is IR-only and does not claim encrypted execution.
