# TclMesh Roadmap

## v0.1.0 — reference kernel ship scope

v0.1.0 is viable to ship when all of the following are true:

- immutable versioned manifests have deterministic SHA-256 identities;
- activation is explicit and hash-bound;
- authoritative actions contain canonical operations rather than mutable callbacks;
- mutable state is loaded, checked, transformed, and persisted inside one transaction/atomic guard;
- action execution is bound to an active language and its holder;
- delegated languages cannot amplify commands, capabilities, parent context, or lineage;
- fivefold deontic judgments block forbidden and conflicted mutation;
- external effects are separated from state transactions and use an idempotent lifecycle ledger;
- private-computation IR is typed and validated, with no claim of encrypted execution;
- test failures propagate to CI;
- an executable end-to-end acceptance scenario passes;
- package version, quickstart, security notes, and changelog are present.

## v0.1.0 conformance claim

The release is a **reference kernel**, not FULL v1 conformance.

Stable in v0.1.0:

- canonical/versioned manifest registry;
- manifest hash activation;
- canonical action subset;
- transaction-guarded state mutation;
- language instances and attenuating delegation;
- holder-bound action capability checks;
- W/N/M/K/H verdict resolution;
- effect proposal/authorization/execution lifecycle;
- private-computation circuit IR construction and validation;
- macro registry/expansion primitives;
- executable tests and example.

Experimental or partial:

- macro hygiene and safe compiler interpreters;
- broad policy expression language;
- private-computation planning beyond AST validation;
- durable effect storage adapters.

Deferred beyond v0.1.0:

- homomorphic-encryption execution backend;
- keyset and threshold-release implementation;
- durable workflow/ceremony engine;
- process supervision runtime;
- persistent manifest registry;
- distributed language-instance registry;
- automatic migrations;
- generated user interfaces and external API surfaces.

## v0.2

Status after all v0.2 slices:

- [x] safe compiler interpreter with deterministic command surface and resource limits;
- [x] compilation-local hygienic `gensym`;
- [x] recursive canonical action/value/predicate validation;
- [x] pluggable persistent registries for manifests, languages, effects, workflows, and audit;
- [x] single-process atomic file-store reference adapter with stale-handle merge protection;
- [x] crash reconciliation for uncertain effect execution;
- [x] durable workflow state machine with pinned manifests, step dependencies, idempotency-gated retry, and explicit reconciliation of interrupted or failed steps;
- [x] append-only structured audit event stream with persistent monotonic sequence numbers and no public reset operation;
- [x] richer canonical expression operators: numeric comparison, membership, and containment in addition to equality/boolean composition, rejecting NaN numeric operands.

## v0.3 — private reference runtime (unreleased)

Implemented on main through PR #15:

- [x] private-computation backend protocol;
- [x] immutable parameter-profile registry;
- [x] opaque ciphertext-handle lifecycle;
- [x] plaintext/private differential execution;
- [x] backend-driven threshold-release state machine;
- [x] backend-controlled durable handles and fresh-process quorum/combination recovery.

Circuit/output provenance (merged PR #15):

- [x] schema-directed canonical circuit SHA-256 identity;
- [x] evaluation of installed circuits pinned to the active manifest version/hash;
- [x] output-handle and release binding to circuit hash, output name/specification,
  and, for bound evaluation, manifest identity;
- [x] process-boundary conformance checking of that binding at the backend.

Release-policy milestone (this branch):

- [x] canonical manifest-owned threshold-release policy validation;
- [x] role-separated request/contribution/combination/recovery capabilities;
- [x] actor-holder, policy membership, context, and active ancestor checks;
- [x] governed output/API bypass rejection and current-authority revalidation;
- [x] independent-process authorized quorum/retry recovery and revocation checks.

These are reference authorization checks, not normative PRIVATE conformance.
Before a v0.3 release or a stronger claim, continue in this order:
1. Bind keyset and cryptographic context metadata; require backend-verified
   contribution scope/consumption across requests. Current reference shares are
   nonempty opaque values, not verified cryptographic shares.
2. Add circuit type/range checks, checked overflow semantics, and approved profile
   compatibility. Packing metadata is hashed but not yet semantically validated.
3. Extend integrated acceptance and provenance reconstruction through private
   evaluation/release; audit private operations without exposing protected data.
4. Review release/security/quickstart consistency, run all conformance and release
   checks, and only then decide on the v0.3 reference-kernel version/tag.

Real cryptographic execution and FULL/PRIVATE conformance remain open. The
plaintext backend provides neither confidentiality nor cryptographic quorum.

## Encrypted languages

Goal: TclMesh as a meta-language that writes encrypted languages, whose
programs move homomorphic ciphertext that no TclMesh component, the kernel
included, can decrypt.

Tier A kernel (this branch):

- [x] pure canonical action evaluation (`action evaluate`) in the Tcl reference;
- [x] Rust kernel (`kernel/`) refining it under a typed JSON data model;
- [x] canonical comparison domain shared by both: decimal-only numbers, quote-
  and backslash-free lists;
- [x] curated and seeded random differential conformance in CI.

Next, in order:

1. **Canonical IR.** Serialize manifests, including circuits and release policies,
   as typed canonical data (deterministic CBOR or JSON) with a schema. Kernel
   manifest hashing must agree with the Tcl reference.
2. **Ciphertext as a kernel type.** Handles carry profile, logical type, circuit
   provenance, and keyset context. The type system forbids ciphertext in
   plaintext predicates, comparisons, changes, and effect fields, so no control
   flow depends on encrypted values. The kernel has no `decrypt` operation.
3. **Backend trait in Rust.** A plaintext reference backend for differential
   testing, then a real FHE backend (e.g. TFHE for boolean/integer circuits,
   CKKS for approximate arithmetic) behind the same trait. Evaluation keys are
   held by the kernel; secret keys never are.
4. **Kernel-side release.** Threshold release where the kernel collects and
   verifies partial decryptions from holders and checks them against
   manifest-declared policy. It cannot combine shares it is not authorized to
   see. Verifiable decryption shares replace the current opaque reference shares.
5. **Language generation.** `language define` in the meta-language declares an
   encrypted language: its types, operators lowered to circuits, the parameter
   profile, and the release policy. Generated languages compile to kernel IR,
   and each one becomes a delegable language instance.
6. **Orchestration tier.** An optional restricted Tcl profile for non-
   authoritative workflow and routing that emits only inert proposals. It needs
   real budgets: an operator block for `**`/`<<` (a single `expr` can otherwise
   run without bound), per-command size caps, and replay transcripts.

## v1.0

v1.0 targets all normative profiles in `docs/spec-v1.md`, including durable workflows, ceremonies, private release, supervision, and the full integrated acceptance scenario.
