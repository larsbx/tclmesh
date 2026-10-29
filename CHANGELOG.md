# Changelog

## Unreleased — v0.3 reference runtime

- 64-bit words: `int64-checked` and `int64-wrapping` under TFHE
  (`FheInt64`), alongside 32-bit; the backend carries each value's width and
  refuses to mix widths, and proven inputs import into either word. Range
  certificates accept `W ≤ 64`, following finite-math-kernels' widened
  `word_range` contract (corpus re-pinned with its `w = 64` rows, finite-math-kernels#89); the Tcl/Lean
  range differential runs at width 64;
- CRS ceremony: `tclmesh-tfhe-crs init|contribute|verify DIR` runs a
  multi-party powers-of-tau setup from the public trapdoor `1`; each
  contribution carries a Schnorr proof of knowledge chained to its
  predecessor, and `verify` checks the chain and the CRS's power structure
  by pairings. `tclmesh private publish PROFILE DIR CEREMONY` verifies and
  adopts it, refusing a ceremony without contributions. SECURITY.md now
  states that a proven range does not depend on the CRS; its trapdoor
  threatens knowledge soundness (input independence);
- proof hygiene: `tclmesh-tfhe-crs` generates the CRS for a party other than
  the key holder, and `tclmesh private publish PROFILE DIR CRS` adopts it
  (fixed once adopted); proof contexts are single-use (`CONTEXT_REUSED`);
- exact proven ranges: `tclmesh private import … hi` (the proof binds `hi`)
  holds `min(lo + a, hi)`, so `[lo, hi]` is exact for honest inputs and
  dishonest ones are clamped; `tclmesh private range-check` and `admit`
  instead release one encrypted admission bit to a quorum and narrow the
  handle only if it is `1`; `Range.bounded_import` and `Range.admission_sound`;
- proven inputs: `tclmesh private publish` writes the public key and CRS, the
  encrypting party proves a `k`-bit offset with `tclmesh-tfhe-prove` (TFHE-rs
  `zk-pok`, no secret key), and `tclmesh private import` verifies the proof
  bound to its context, offset and width, yielding a handle whose range
  `[lo, lo + 2^k − 1]` is proved and whose value the runtime never sees;
  `Range.inputs_of_proofs` proves the range consequence;
- fix checked Boolean handle composition: validate consumed bit ranges and
  reject Boolean output labels whose certified ranges exceed `[0,1]`, before
  backend execution; `Range.bit_output_sound` proves the resulting invariant;
- require clamp bounds to fit the signed word in both the Tcl and Lean
  checkers; regressions cover redundant out-of-word bounds and real TFHE
  boundary execution; run TFHE checks on relevant PRs;
- pin the accepted finite-math-kernels #83 merge, including the regenerated
  provenance manifest, preserving the byte-identical 1,720-row range corpus;

- range certificates for private circuits (`tclmesh range emit|check|require`,
  `spec/TclMesh/Range.lean`): least ranges by interval arithmetic from declared
  input ranges (`{cipher int range LO HI}`), with a Lean checker proved sound —
  if it accepts, `w`-bit wrapped evaluation equals exact evaluation and no
  intermediate leaves the word (`check_sound`). Profile semantics
  `int<W>-checked` (TFHE: `int32-checked`) evaluates only accepted circuits on
  inputs inside their declared ranges; handles carry their ranges. The
  arithmetic is the contract of `finite_exact/word_range.mojo` in
  larsbx/finite-math-kernels, whose corpus is vendored, pinned in
  `UPSTREAM.toml` and replayed by Tcl and Lean;
- `clamp x lo hi` circuit operation (TFHE: homomorphic `max`/`min`) and
  `tclmesh range guard`, which enforces declared ciphertext ranges inside the
  circuit; `guarded_sound` proves guarded circuits exact on any ciphertext,
  with no trusted range claim;
- pure Tier A evaluation, `action evaluate action_id descriptor state request`,
  which `action run` now wraps;
- **breaking:** ordered comparisons accept only canonical decimal numbers
  (hex, octal, padded, signed, and `Inf`/`NaN` spellings raise `NON_NUMERIC`).
  `in` accepts only quote- and backslash-free lists (`NON_CANONICAL_LIST`);
- **breaking:** ordered comparisons use exact decimals (no floating-point
  rounding), with written exponents capped at 1000;
- `kernel/core`: a dependency-free crate (predicate decisions, decimal parsing
  and comparison, canonical lists, deontic resolution) that the kernel calls.
  Aeneas translates it to Lean, and `proof/` proves the translated
  `deontic::resolve`, `deontic::admits`, `decimal::parse`, `decimal::compare`
  and `predicate::eval` equal to the specification, with no axioms (CI job
  `proof`);
- the specification evaluates predicates as lowering then a byte-level decision
  (`TclMesh.Predicate`); canonical lists and `contains` work on UTF-8 bytes;
- executable Lean specification of the Tier A kernel (`lake exe spec-eval`). The
  Rust kernel must equal it on every conformance vector;
- Rust Tier A kernel (`kernel/`) refining the Tcl evaluator, with curated and
  seeded random differential conformance (`tools/conformance.tcl`,
  `conformance/`) run in CI;
- Lean 4 specification (`spec/`, `docs/proofs.md`) proving declassification-
  indexed non-interference with oblivious `select`, typed `release` and `verify`,
  action-level non-interference, obliviousness of `if`→`select` compilation,
  sound and complete label checkers, leakage-budget soundness, threshold-release
  quorum safety, deontic admission laws, and fail-closed canonical predicates.
  An axiom audit in CI rejects `sorry`;

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

- licensed under Apache-2.0.

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
