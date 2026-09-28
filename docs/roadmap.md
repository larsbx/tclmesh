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

- safe compiler interpreter;
- hygienic generated symbols;
- richer canonical expression AST;
- pluggable persistent registries for manifests, languages, and effects;
- first durable workflow state machine;
- structured audit event stream.

## v0.3

- private-computation backend protocol;
- parameter-profile registry;
- ciphertext-handle lifecycle;
- plaintext/private differential execution;
- threshold-release state machine.

## v1.0

v1.0 targets all normative profiles in `docs/spec-v1.md`, including durable workflows, ceremonies, private release, supervision, and the full integrated acceptance scenario.
