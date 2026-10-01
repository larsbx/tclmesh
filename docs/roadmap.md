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

## v0.3

Status after all v0.3 reference slices:

- [x] private-computation backend protocol;
- [x] immutable parameter-profile registry;
- [x] opaque ciphertext-handle lifecycle with backend/profile/type binding;
- [x] stronger executable private-circuit graph validation;
- [x] plaintext reference backend for deterministic development only;
- [x] plaintext/backend differential execution;
- [x] profile-gated direct decryption;
- [x] threshold-release state machine with fixed holder sets, quorum, purpose binding, persistence, and uncertain-combine reconciliation.

The v0.3 built-in plaintext backend is explicitly non-confidential. A homomorphic or otherwise confidential backend is an integration target, not a property of the reference backend.

## v0.4

- process-supervision runtime and restart policies;
- ceremony engine built on durable workflow primitives;
- first-class keyset lifecycle and holder rotation;
- backend conformance suite for real confidential/private-computation plugins;
- persistent or externally resolvable ciphertext-handle strategy across process restart;
- multi-process/distributed registry adapter contract;
- compensation/deadline policy completion for workflows.

## v1.0

v1.0 targets all normative profiles in `docs/spec-v1.md`, including durable workflows, ceremonies, private release, supervision, and the full integrated acceptance scenario.
