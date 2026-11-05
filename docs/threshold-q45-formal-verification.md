# P2b acceptance boundary: Lean and Quint

This extends [PR #56](https://github.com/larsbx/tclmesh/pull/56) with checked
mathematics, finite-state model checking and a concrete model-to-actor replay.
It does not change the cryptographic protocol, ceremony transition code or
governed-release gate. The [adversarial acceptance report](threshold-q45-p2b-adversarial-acceptance.md)
remains the account of the actual toy implementation's failures.

## Reproduce

Requirements: the exact version in `spec/lean-toolchain` (Lean 4.35.0),
Node/npm, Java 21 and Erlang/OTP with Crypto. Quint 0.33.1 and its npm
dependencies are locked; the runner explicitly pins Apalache 0.62.4 for
translation and uses its bundled TLC for exhaustive finite-state checking.

```sh
npm ci --ignore-scripts --no-audit --no-fund --prefix formal/quint
python3 -B tools/check_q45_formal.py --receipt /tmp/q45-formal-receipt.json --evidence-dir /tmp/q45-formal-evidence
```

The runner requires every proof, axiom audit, typecheck, scenario, positive
TLC check, expected TLC counterexample and concrete actor projection to
succeed as specified. It accepts an expected failure only when TLC reports
an invariant violation and a counterexample. A parse error, timeout or failed
download cannot satisfy a negative check. Positive TLC runs must report a
completed graph search and an empty queue. There is no silent simulation-only
fallback. The path-scoped [CI workflow](../.github/workflows/q45-formal.yml)
uploads logs, the generated ITF trace and a source-hashed receipt.

Local evidence is retained under
[`formal/quint/evidence/local-2026-11-05`](../formal/quint/evidence/local-2026-11-05).
The receipt separates source hashes from evidence hashes. Hosted results are
separate from this local replay; earlier PR #55/#56 workflows predate these
formal additions.

## Lean: what is proved

[`TclMesh.Q45Adversarial`](../spec/TclMesh/Q45Adversarial.lean) is imported by
the existing executable specification and included in its axiom audit. It
contains 20 kernel-checked theorems, with no `sorry` or `native_decide`.

| Theorems | Exact scope |
| --- | --- |
| `submit_preserves_wellBound`, `submissions_preserve_wellBound` | At the frozen-partials phase, admission preserves distinct sender labels, exact session/ciphertext/quorum binding and frozen-quorum membership, across an arbitrary finite list of submissions. |
| `duplicate_rejected`, `foreign_binding_rejected` | A duplicate label or foreign binding leaves that abstract state unchanged. |
| `envelope_ignores_ghost_correctness`, `envelope_ignores_encoding` | The modeled opaque P1 envelope cannot distinguish messages differing only in correctness or canonical encoding. Encoding checks belong to the callback, not this envelope. |
| `verified_submission_preserves_correctness`, `verified_submissions_preserve_correctness` | A proposed verification interface preserves correctness **assuming** `∀ c, verify c = true → c.correct = true`. This is the unimplemented cryptographic soundness obligation, not a theorem about a concrete verifier. |
| `canonical_bad_partial_is_admitted`, `envelope_admission_does_not_imply_correctness`, `signatures_alone_are_not_a_sound_verifier` | Explicit countermodels: a canonical, abstractly authenticated but incorrect contribution is admitted; authentication alone does not logically imply arithmetic correctness. `authenticated` is a Boolean abstraction, not an implemented signature system. |
| `offset_is_canonical`, `phase_offset` | Any offset modulo a positive modulus remains canonical. Changing one scalar partial translates the scalar unverified combination phase by that offset modulo `q`. These statements hold for arbitrary natural-number inputs. |
| `exact_zero_phase_bit_flip`, `exact_one_phase_bit_flip` | At the actual toy modulus `2^127−1`, the two zero-noise plaintext phases decode to opposite bits after adding `DELTA`. The decoder here matches the unsigned canonical-phase decoder in the Erlang replay. This is not a proof of all noisy BFV decodings. |
| `sum_of_bounded` | A list of residual magnitudes individually bounded by `B` has sum at most `length * B`. Individual bounds are hypotheses. |
| `decoding_budget_does_not_enforce_masks` | A total four-mask budget can contain an individual magnitude `B+1`; total headroom cannot verify every holder's bound. |
| `honest_80_bit_headroom`, `measured_width_has_80_bit_margin`, `width_33_misses_72_bit_margin` | Exact numerical implications under the measured `E < 2^34`/width hypotheses. No proof establishes those hypotheses for malicious setup, evaluation or holder contributions. |

The local library audit reports 2,027 declarations and 723 theorems depending
only on the standard allowed Lean axioms. That count includes the existing
specification; it is not a count of new cryptographic proofs.

## Quint: what is checked

[`q45_ceremony.qnt`](../formal/quint/q45_ceremony.qnt) models all five inputs,
all five seals, first-four quorum freezing, one partial per frozen label,
opaque malformed/incorrect payload classes, callback decoding, terminal
recording, and a bounded per-phase clock. Binding token `0` denotes the exact
expected session/ciphertext/quorum context; token `1` denotes a mismatch.
The plaintext truth is normalized to zero. An incorrect symbolic partial
represents a one-bit phase-offset class, not an arbitrary RLWE polynomial.

| Check | Meaning |
| --- | --- |
| `safety`, current `init` | Exhaustive local envelope/state safety: membership, phase prerequisites, no malformed successful callback, and at most one recorded result. All 15,412 reachable model states are checked. |
| `safety and outputIntegrity`, `initStrict` | Exhaustive check of a **proposed ideal verifier contract** that admits only canonical, correct partials. All 682 reachable model states are checked. This uses ghost correctness as a perfect filter; no verifier is implemented. |
| `outputIntegrity`, current `init` | Required counterexample: a canonical incorrect completion exists. The checker must report an invariant violation. |
| Seven deterministic scenarios | Canonical corruption, malformed callback abort, duplicate partial, foreign binding, empty partial, outside-quorum partial and frozen-holder withholding. |

[`q45_setup_views.qnt`](../formal/quint/q45_setup_views.qnt) models two
receivers, five labeled public/first/second-round messages at each receiver,
local aggregation and finalization. Only participant 5 supplies differing
symbolic contribution classes; other participants use the honest class.
The receiver checks the **declared** first-round aggregate, while the
contribution's **computed** aggregate is ghost information recording the
context from which it was actually derived.

| Check | Meaning |
| --- | --- |
| `localSafety` | Exhaustive finite check of local sender membership and complete-round prerequisites across all 114,244 reachable setup-model states. |
| `agreement` | Required counterexample: both local views finalize while their aggregate public keys or first-round aggregates differ. |
| `noRelabeling` | Required counterexample: a contribution derived from another aggregate is admitted after its declared aggregate is relabeled. |
| Five deterministic scenarios | Public-key equivocation, first-round equivocation, relabeling, rejection of an explicitly conflicting declared aggregate, and local duplicate rejection. |

State counts and complete counterexamples for these checks are in the receipt
and logs. These checks enumerate the **specified finite abstractions**, not
the full space of FHE polynomials, cryptographic secrets, network behaviors or
arbitrary message encodings. The setup's two classes are symbolic; its parity
aggregation is not claimed to be a homomorphic quotient of the odd toy ring.

## Connection to the implementation

[`check_q45_quint_projection.py`](../tools/check_q45_quint_projection.py)
asks Quint to generate an ITF trace with seed `0x45`, using `attackStep`.
The generator chooses input, seal, commitment and partial ordering. It corrupts
the first partial and then reaches a successful wrong-bit completion.

The bridge replaces those symbolic values with actual P2b ciphertexts and
80-bit holder-local partials from an all-zero input fixture. It adds `DELTA`
to the selected partial's constant coefficient and submits the generated
events to the unchanged P1 BEAM actor. An independent Erlang decoder combines
the admitted bytes. All 20 snapshots must match the model's phase, input,
seal, commitment, frozen-quorum and partial label sets, and result.
A deliberately wrong final-result projection must fail specifically with
`projection_mismatch`.

This checks a selected generated trace and its projection; it is not a
universal refinement theorem. The original 640-case honest and 640-case
targeted-corruption replays remain separate evidence. The bridge introduces
no production cryptographic or release interface.

## Trust and remaining obligations

Lean checks mathematical proof terms. Quint scenario tests execute specified
runs; TLC separately explores complete finite graphs using its ordinary
fingerprinting-based state storage. Neither tool verifies a real signature,
share proof, DKG or relinearization protocol here.

The Lean admission abstraction covers only the frozen-partials phase. The
Quint clock has two finite ticks per phase; it does not establish wall-clock
refinement. The generated actor trace exercises timely events. The withholding
scenario schedules expiry explicitly: no fairness assumption or eventual
termination theorem has been established. Setup agreement, authentication,
private-fragment consistency, sound partial/relinearization proofs, privacy,
secure parameters and active-corruption fault bounds remain obligations.

The local host needed a temporary adapter translating its inconsistent
`/proc/<pid>/exe` lookup to `/proc/self/exe` for the unmodified Lean binaries.
This changes executable-path discovery only, not Lean's checker or axioms;
the CI workflow uses the normal pinned distribution without that adapter.

The next proof boundary is a concrete contribution-verification relation and
an implementation refinement argument for that relation. Treating
`correct` or `authenticated` as trusted Booleans does not discharge it.
Protocol implementation changes and merging remain subject to approval.
Governed cryptographic release stays disabled.
