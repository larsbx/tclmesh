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
2. Add circuit type checks and approved profile compatibility. Range checks and
   checked overflow semantics are in (`int<W>-checked`, `spec/TclMesh/Range.lean`);
   a ciphertext input's range is proved by its encrypting party in zero
   knowledge (`private import`, TFHE-rs `zk-pok`, `inputs_of_proofs`), enforced
   inside the circuit by `range guard` (`clamp`, `guarded_sound`), or claimed
   and checked at `encrypt`. Proven ranges are `[lo, lo + 2^k − 1]` for even
   `k ≤ 16` or `k = 32` (in a 64-bit word, or as the whole 32-bit word); an exact `[lo, hi]` is clamped by `import … hi` by default, or
   rejected through a released admission bit (`range-check`, `admit`), since
   the proof system cannot relate two proven offsets. The CRS comes from a
   multi-party ceremony (`tclmesh-tfhe-crs init|contribute|verify`) that
   `publish` verifies before adopting, so its trapdoor is unknown unless every
   contributor colludes; contributors sign their receipts with long-term keys,
   and `publish … TRUSTED` requires a contribution signed by a trusted party,
   so one honest party suffices. Distributing and revoking those public keys
   is the deployment's. Proof contexts are
   single-use while their handle records exist, and a proof is bound to the
   public key it was made under. With persistent TFHE keys
   (`TCLMESH_TFHE_KEYS`) handles persist as keyset-bound ciphertexts, so
   consumed contexts survive restarts with their records; recovery material
   from another keyset is refused. This is a single-authoritative-store
   persistence guarantee, not a distributed uniqueness proof: separate handle
   stores sharing a keyset can reuse the same proof context. Until a durable
   atomic keyset-scoped context claim is implemented and refined, deploy
   persistent TFHE with only one authoritative handle store and do not claim
   cross-process at-most-once admission.
   Packing metadata is hashed but not yet semantically validated.
3. Extend integrated acceptance and provenance reconstruction through private
   evaluation/release; audit private operations without exposing protected data.
4. Review release/security/quickstart consistency, run all conformance and release
   checks, and only then decide on the v0.3 reference-kernel version/tag.

Real cryptographic execution and FULL/PRIVATE conformance remain open. The
plaintext backend provides neither confidentiality nor cryptographic quorum.

## Encrypted languages

Goal: TclMesh as a meta-language that writes encrypted languages. Their
programs compute and decide on homomorphic ciphertext that no TclMesh component,
the kernel included, can decrypt.

Decisions over ciphertext are the point, not something to forbid. What is
required is that every dependence of an observable on ciphertext is designed,
declared, and accounted for. There are three kinds of decision:

| Decision | Who learns it | Mechanisms | Leakage |
|---|---|---|---|
| oblivious | nobody; the result stays encrypted | homomorphic select (CMUX), programmable bootstrapping / encrypted lookup tables, loops unrolled to a declared bound | none; the trace depends only on public inputs |
| released | named parties, under policy | threshold decryption of the decision (not the data); functional-encryption keys that reveal only `f(x)` | exactly `f(x)`, charged to a budget |
| proved | the kernel, without decrypting | zero-knowledge proofs by the key holder (range, membership, correct computation); verifiable decryption shares | only that the statement holds, attested by that holder |

Leaky encodings (deterministic or order-revealing encryption, MPC with public
output, attested enclaves) are admissible only with their leakage typed
explicitly.

The manifest declares, for each requirement, what may be learned, by whom, at
what cost, and under which trust assumptions. The compiler chooses a mechanism
that satisfies the declaration, or rejects it.

### Formal methods first

The Lean 4 specification in `spec/` is the root of trust. New semantics start
as a Lean definition and its theorems. Implementations follow:

- the Rust kernel is refined against the spec: `kernel/core` by Aeneas proofs,
  the rest by exact conformance with the executable spec;
- the Tcl reference is checked against it by conformance testing;
- the Tcl meta-language acts as a certifying compiler, whose certificates a
  checker proved in Lean validates before activation.

CI rejects `sorry` and any axiom outside Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`). Cryptographic assumptions enter
only as named hypotheses of the theorems that use them.

Proof obligations:

- [x] label lattice; declassification-indexed non-interference for typed
  expressions with oblivious `select`, `release`, and `verify` (`spec/TclMesh/Flow.lean`);
- [x] actions: public guards, labelled fields and effect fields; non-interference
  of every public observable modulo agreed releases;
- [x] obliviousness: the operation trace is determined by public inputs alone;
- [x] mechanism selection in miniature: a source `if` on secret data compiles
  to `select`, with semantic preservation, well-typedness, and obliviousness;
- [x] verified label checker (`infer`), sound and complete for the typing relation;
- [x] static leakage budget: an accepted action leaks at most its budget;
- [x] threshold release: an accepted release has a quorum of distinct authorized
  holders bound to the request;
- [x] deontic resolution laws, and fail-closed evaluation of the canonical
  predicate language;
- [x] canonical numbers as exact decimals: a total preorder, exponent-independent
  scaling, and parser cases (`Decimal.lean`), with Tcl and Rust migrated;
- [x] executable spec as the conformance oracle (`Kernel.lean`, `lake exe spec-eval`).
  The Rust kernel must equal it on every vector, and its own fail-closed
  `not` and exact-comparison theorems are proved;
- [x] `kernel/core` in the subset Aeneas can translate. Its deontic resolution,
  exact decimal parsing and comparison, and predicate decisions (canonical
  lists, membership, containment, fail-closed `not`, short-circuit `and`/`or`)
  are proved equal to the spec through Aeneas (`proof/`), with no axioms;
- [ ] Aeneas refinement of the rest of evaluation (lowering, validation,
  changes, effects), as it moves into `kernel/core`;
- [ ] ciphertext values and the IFC type system in the kernel IR, with the Tcl
  compiler emitting label certificates;
- [ ] mechanism lemmas: CMUX select, threshold release, functional encryption,
  each "correct and leaks exactly L" under named assumptions (zero-knowledge
  range proofs: the range consequence is proved in `Range.inputs_of_proofs`,
  with proof-system soundness a named hypothesis);
- [x] noise-budget soundness for bootstrapped circuits (`Noise.bootstrapped_sound`:
  any depth, under the per-bootstrap contract and a union bound);
- [ ] noise-budget soundness for leveled circuits, and the refinement of
  TFHE-rs integer operations to block gate programs;
- [ ] leakage budgets in bits and in differential-privacy epsilon across runs.

Engineering sequence, after the proofs above:

1. Canonical typed IR for whole manifests, so circuits and release policies hash
   identically in Tcl and Rust.
2. The IFC type system with oblivious, released, and proved decisions in the
   kernel IR. `select` is the first oblivious construct, and the existing release
   policies become the released path.
3. A Rust backend trait: a plaintext reference backend, then real FHE (TFHE for
   integer and boolean circuits, CKKS for approximate arithmetic). The kernel
   holds evaluation keys and never secret keys.
4. Threshold release with verifiable decryption shares, checked against manifest
   policy by the kernel.
5. `language define`: declares an encrypted language's types, operators lowered
   to circuits, parameter profile, leakage declarations, and mechanism
   preferences. Generated languages compile to kernel IR and become delegable
   language instances.
6. An optional orchestration tier: a restricted Tcl profile with real budgets
   that emits only inert proposals.

## v1.0

v1.0 targets all normative profiles in `docs/spec-v1.md`, including durable workflows, ceremonies, private release, supervision, and the full integrated acceptance scenario.
