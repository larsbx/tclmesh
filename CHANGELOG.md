# Changelog

## Unreleased — v0.3 reference runtime

- backend protocol, immutable parameter profiles, opaque ciphertext handles, and
  plaintext/backend differential evaluation;
- threshold release, backend-controlled handle persistence, and independent-process
  recovery for quorum and interrupted combination;
- canonical circuit SHA-256 identity and installed-manifest-bound evaluation;
- circuit/output provenance preserved in handles, release requests, and backend
  combination context, including after process restart.

- manifest-owned release policies with role-specific holder/language authorization,
  active-ancestor/context checks, current-manifest revalidation, governed direct
  decryption/raw-API rejection, and persisted authority receipts.

No PRIVATE/FULL conformance, identity authentication, cryptographic
share verification, or confidentiality claim. Package version remains 0.2.0.

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
