# Testing the meta-language and the encrypted languages

TclMesh has two kinds of artifact under test:

- **M, the meta-language**: declarations → compiler → a generated language,
  together with a certificate naming the mechanism that serves each decision
  and what it costs.
- **L, each generated language**: programs → circuits over three kinds of
  decision (see [roadmap](roadmap.md#encrypted-languages)): *oblivious*
  (homomorphic select, encrypted lookup), *released* (threshold or functional
  decryption of a declared `f(x)`), *proved* (zero-knowledge statements checked
  without decryption).

Testing M means testing that every language it generates meets its
declarations. Testing L means testing that each mechanism behaves as declared.
Homomorphic correctness is one cell of a larger matrix.

## One question for every program

> Does each party see exactly what the manifest says it may see, and is the
> decrypted answer right?

Every channel a party can observe is instrumented: outputs, released values,
decryption shares, proofs, operation traces, ciphertext sizes, timing buckets,
logs. A run produces a **view** `View_P` per party `P`. The manifest, read
through the Lean leakage model, declares what each party may learn, `f_P(x)`.

| Check | Statement | Oracle |
|---|---|---|
| correctness | `Dec(⟦C(p)⟧(Enc x)) = ⟦p⟧(x)` | plaintext reference semantics |
| leakage exactness | `f_P(x) = f_P(x')` ⇒ `View_P(x) ≈ View_P(x')`, and `View_P(x)` contains `f_P(x)` | Lean leakage model |

Leakage exactness is a **hyperproperty**: it relates pairs of runs, so it is
tested on pairs. Generate `x, x'` that agree on everything `P` may learn, run
both, compare views. A difference is a leak; a missing `f_P(x)` is a broken
mechanism. The same harness covers all three decision kinds:

- oblivious: `f_P` is the public input only, so traces must coincide;
- released: exactly `f(x)` appears, charged to the budget;
- proved: the verifier's view holds the statement and the proof, never the
  witness.

`≈` is equality for structural views (traces, sizes, released values) and
computational indistinguishability for ciphertext contents. The second cannot
be checked by running code; it is where semantic security comes in (below).

## Layers

| Layer | Establishes | Tools |
|---|---|---|
| L0 proof | spec theorems: non-interference, obliviousness, budgets, quorum safety, fail-closed predicates | Lean (`spec/`), axiom audit |
| L1 refinement | Rust kernel core = spec | Aeneas (`proof/`) |
| L2 conformance | spec oracle = Rust kernel; Rust refines Tcl | `tools/conformance.tcl`, `conform --exact` |
| L3 mechanism differential | backend result = plaintext reference, on the same circuits | `private differential`, plaintext / real backends |
| L4 views | per-party views equal the declared leakage; paired runs agree | view recorder, pair generator |
| L5 security | games, simulators, parameter estimates, side channels | security harness (below) |
| L6 acceptance | exemplar languages end to end | `tests/languages/` |

## Property matrix

| Property | Proved | Refined | Differential | Paired views | Adversarial |
|---|---|---|---|---|---|
| kernel decisions, predicates | spec theorems | `kernel/core` | spec / Rust / Tcl | — | mutated descriptors |
| non-interference, obliviousness | `Flow`, `Oblivious` | IR checker (planned) | — | trace equality | timing and size probes |
| homomorphic correctness | named assumption | — | plaintext vs real backend | — | wrong-result backend |
| noise, parameters | noise budget (planned) | — | measured vs predicted noise | — | parameters under the security estimate |
| released decisions | budget soundness | — | `f(x)` against the reference | views equal for `x ≈ x'` | budget exhaustion, unauthorized release |
| threshold release | quorum safety | — | — | — | forged, replayed, duplicated shares |
| proved decisions | statement semantics | verifier in core | honest proofs accepted | no witness in any view | forged and mutated proofs rejected |
| no decryption authority | spec invariant | kernel API has no decrypt | — | — | kernel attempts decryption |
| compiler (M) | certificate checker sound | checker in core | — | — | mutated certificates rejected |

## Testing the meta-language

- **Certificates, not compiler proofs.** M emits, for every compiled program, a
  certificate: labels, mechanism per decision, budget charges, trust
  assumptions. A checker proved in Lean validates it before activation. Tests
  assert both directions: every certificate M emits is accepted, and every
  mutated certificate (a weakened label, a cheaper mechanism, a dropped budget
  charge) is rejected. The second is mutation testing of the checker.
- **Metamorphic tests.** The same semantic program written in two generated
  languages gives the same decrypted results. Changing the mechanism for one
  decision (oblivious ↔ released) under the same declaration keeps the result
  and changes only the declared views.
- **Canonical forms.** `canonical ∘ canonical = canonical`, digests are stable,
  parse ∘ print = id: these are already tested for manifests and circuits.

## Backends as instruments

1. **transparent**: plaintext inside, records what each party would learn; fast
   enough for property tests and paired runs on every build;
2. **real**: TFHE-rs or OpenFHE behind the same interface, seeded; correctness
   and noise, nightly;
3. **adversarial**: returns wrong ciphertexts, forges shares or proofs, or plays
   a kernel trying to decrypt. Each must be detected or impossible, wherever
   the manifest claims verification.

## Testing semantic security

Semantic security (IND-CPA) says: for every efficient adversary, the advantage
in telling `Enc(m₀)` from `Enc(m₁)` is negligible. It quantifies over all
adversaries and is asymptotic, so **no finite test establishes it**. It is
established by proof, relative to a hardness assumption; testing supports the
proof in five ways.

1. **Reduction proofs (L0).** We do not prove LWE hard. We prove that TclMesh's
   use of the scheme is secure *if* the scheme is: structural non-interference
   plus IND-CPA implies that the views of leakage-equivalent inputs are
   indistinguishable, with advantage at most `q · Adv_IND-CPA` for `q`
   ciphertexts (a hybrid argument). The assumption is a named hypothesis of the
   theorem, never an axiom.
2. **Exhaustive small models.** With toy parameters every distribution is
   finite, so advantages can be *computed exactly* rather than estimated: the
   exact distinguishing advantage of a toy scheme, perfect secrecy of a
   one-time pad, perfect simulation for a toy proof system. These bridge the
   proofs and the sampled tests below.
3. **Falsification games.** The game runner plays IND-CPA against a battery of
   concrete adversaries: byte-frequency and chi-square tests, ciphertext
   equality (determinism), length and size leakage, timing, mutual-information
   estimates, trained classifiers. Each reports an advantage with a confidence
   interval, corrected for multiple comparisons. **Passing proves nothing;
   failing proves a break.** That asymmetry is the point: the tests are a net
   for implementation and integration mistakes, not a security argument.
4. **Calibration (mutation testing of the security tests).** The game runner is
   itself tested on deliberately broken schemes: deterministic encryption,
   reused randomness, too little noise, plaintext in the token (the reference
   backend is exactly this). A battery that does not catch a known break has no
   value, so CI requires every calibration break to be detected.
5. **Instantiation checks.** The assumption has to hold for the parameters
   actually used:
   - parameter sets meet a target security level under a lattice estimator;
   - noise and key distributions pass statistical tests (chi-square,
     Kolmogorov–Smirnov) against their specification;
   - the random source passes health tests;
   - known-answer tests against reference implementations;
   - constant-time checks (dudect-style timing t-tests) on secret-dependent
     code.

## Testing zero knowledge

A proof system has three properties, and two of them are directly testable.

| Property | Definition | How it is tested |
|---|---|---|
| completeness | an honest prover with a valid witness is accepted | property tests over the relation |
| (knowledge) soundness | an accepting prover "knows" a witness | adversarial provers; **extractor tests** |
| zero knowledge | a simulator produces transcripts indistinguishable from real ones without the witness | **simulator tests**, exact on small models |

- **Extractor tests make soundness constructive.** For a Σ-protocol, special
  soundness gives an extractor: from two accepting transcripts with the same
  commitment and different challenges, it computes a witness. The test rewinds
  the prover, runs the extractor and checks that the output satisfies the
  relation. Calibration: a prover that reuses a nonce across two sessions *is*
  such a transcript pair, so the same extractor recovers its secret, and the
  test must report that leak.
- **Simulator tests make zero knowledge observable.** The simulator is part of
  the proof, so it is implemented and tested. On small parameters, the
  distributions of real and simulated transcripts are computed exactly and
  compared: equal for perfect zero knowledge, total variation distance for
  statistical. On real parameters they are sampled and fed to the same
  distinguisher battery as the IND-CPA games. Calibration: a prover whose
  response leaks a witness bit must be told apart from its simulator.
- **Fiat–Shamir binding.** Non-interactive proofs must hash the whole statement
  and every commitment. A mutation that drops a statement field from the
  challenge (the class of bug behind "frozen heart" forgeries) must let the
  harness forge a proof, and the unmutated system must not.
- **What remains a proof obligation.** Malicious-verifier zero knowledge, and
  security under composition, are stated in Lean against the simulator, with
  the hardness assumptions as named hypotheses.

## Exemplar languages

`tests/languages/` holds one small language per decision pattern, each with a
manifest, programs, expected views and expected results:

- private set membership: oblivious;
- sealed-bid auction: oblivious comparison, winner released by threshold;
- encrypted policy check released to one party;
- an encrypted range check (age over 18), proved;
- a typed leak (deterministic encryption), declared and accounted.

Each exemplar runs through every layer, and the corpus documents what M can
generate.

## Status

| Piece | Where | State |
|---|---|---|
| per-party views, paired runs | `src/views.tcl`, `tests/views.test` | evaluator and recipient views; transparent backend; `lazy` and `sized` calibration breaks detected |
| declared views from the spec | `spec/TclMesh/Circuit.lean`, `spec-eval --views` | `declared` with `declared_publics` (the view depends on public inputs only) and `schedule_nodup` proved |
| view conformance | `tools/views.tcl check`, `conformance/circuits.json` | recorded = declared (Tcl) = declared (Lean) on every vector, in CI |
| certificates | `src/certificate.tcl`, `spec/TclMesh/Certificate.lean`, `tests/certificates.test` | the compiler emits least labels and oblivious selects; the Lean checker is proved sound for every operation semantics (`check_sound`, `public_outputs`); `tools/views.tcl` checks Tcl verdicts = Lean verdicts and emitted = least on every circuit, and that every mutation (each cipher node demoted, each oblivious select forgotten) is rejected |
| range certificates | `src/range.tcl`, `spec/TclMesh/Range.lean`, `tests/range.test` | the compiler emits least ranges by interval arithmetic from declared input ranges (`{cipher int range LO HI}`); the Lean checker is proved sound (`check_sound`: accepted ⇒ wrapped = exact, no intermediate leaves the word); `tools/views.tcl ranges`/`check-ranges` check Tcl verdicts = Lean verdicts and emitted = least on every circuit with declared, bounded and skewed input ranges at widths 32 and 8, and that every mutation (each range narrowed past its least range, each node dropped) is rejected. `int<W>-checked` profiles evaluate only accepted circuits, on values, handles and public inputs inside their declared ranges. `range guard` replaces declared ciphertext ranges by `clamp` nodes (homomorphic `max`/`min`, never wrapped), so no range claim is trusted (`guarded_sound`; under TFHE, T-009 on ±2³¹) |
| proven inputs | `backends/tfhe` (`publish`, `import`, `tclmesh-tfhe-prove`, `tests/proven.rs`), `tests/tfhe.test` T-012..T-016, `tests/range.test` R-022 | the encrypting party proves an offset `a < 2^k` with TFHE-rs `zk-pok`, using only the published public key and CRS; the runtime verifies the proof against its context, offset and width and holds `lo + a`. Proven bids evaluate exactly with no clamp; another context, offset or width, or one flipped bit, is refused; a proven range wider than the declared one is refused at evaluation; a dishonest prover calling TFHE-rs directly cannot leave the proven width (Rust test); skipping verification is caught (mutation). Exact `[lo, hi]`: by default `import … hi` clamps (T-017; the Rust test drives a dishonest offset past `hi` to `hi`, and the proof is bound to `hi`); for rejection, a released admission bit admits in-range inputs and refuses the rest (T-018 under TFHE; R-023..R-025, R-027 on the reference backend, including another circuit's released bit, an unreleased check and a widened record; mutations of the bit and binding checks are caught). A proof context is accepted once (T-019); a CRS generated by a third party with `tclmesh-tfhe-crs` is adopted by a fresh backend, which then refuses proofs made under another CRS and refuses to change its fixed CRS (T-020, `tests/tfhe-crs-process.tcl`) |
| upstream word-range kernel | `UPSTREAM.toml`, `conformance/word_range_v1.txt`, CI job `upstream` | the corpus of `finite_exact/word_range.mojo` (larsbx/finite-math-kernels), vendored byte-for-byte and pinned by SHA-256, is replayed by the Tcl interval arithmetic (`tests/range.test`) and the Lean model (`spec-eval --word-range`); CI checks it equals the file at the pinned commit, which the pinned upstream reference regenerates and the canonical Mojo kernel replays |
| exemplar corpus | `tests/languages/exemplars.tcl`, `tests/languages.test` | sealed-bid and set membership (oblivious), second-price auction (released by 2 of 3 holders, direct decryption forbidden, no early combine), a policy check in two encodings (metamorphic agreement on every input); each through certificates, views, paired runs and correctness. `proved` and `typed-leak` are listed as not yet expressible |
| real HE backend | `backends/tfhe`, `src/tfhe.tcl`, `tests/tfhe.test`, nightly `tfhe.yml` | TFHE-rs 1.8 (`FheInt32`, `FheBool`); every exemplar decrypts to the reference result; the traces of real homomorphic evaluation equal the declared view on all pairs; ciphertext size is independent of the plaintext, for fresh and evaluated ciphertexts (paired runs compare sizes); quorum release of the clearing price; integers declared `int32-wrapping`, or `int32-checked`, under which a range-certified circuit decrypts to the exact reference and one that may overflow is refused before evaluation (profiles claiming exact integers unconditionally are rejected). Skipped where the binary is not built |
| IND-CPA games | `security/src/ind_cpa.rs` | battery of five adversaries with Bonferroni-corrected Wilson intervals; toy Regev sound and with five flaws |
| calibration | `security/tests/games.rs` | every flaw detected, sound scheme passes. The first run caught a blind spot: an unstandardized centroid missed an appended plaintext bit |
| exact small models | `security/src/exact.rs` | one-time pad advantage exactly 0; toy Regev single-ciphertext advantage exactly `q^{-n}` (the `a = 0` leak) |
| computational bridge | `proof/TclMeshProof/Security.lean` | `view_hybrid`: any distinguisher of two views of `n` ciphertexts yields explicit non-adaptive IND-CPA adversaries (`reduction D i`: `n − 1` oracle queries, one call to `D`) with `Adv_view(D) ≤ Σ Adv_cpa`; `view_bound` and `leakage_bound`: leakage-equivalent inputs give `n·ε`-close views under the named IND-CPA hypothesis |
| zero knowledge, proved | `proof/TclMeshProof/Security.lean` | Schnorr in the exponent model: `completeness`, `special_soundness`, `simulate_verifies`, `hvzk` and `hvzk_prob` (perfect honest-verifier zero knowledge) |
| zero knowledge | `security/src/zk.rs` | Schnorr: completeness and extractor on every witness, nonce and challenge pair of a small group; perfect HVZK (TV = 0) against the simulator; nonce reuse and biased nonces detected; weak Fiat–Shamir forged, strong not |
