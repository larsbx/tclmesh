# Proofs

`spec/` is a Lean 4 project with no dependencies beyond Lean core; the Lean
version is pinned in `spec/lean-toolchain`. It is the root of trust for
TclMesh semantics: definitions and theorems come first, implementations
follow. CI runs the following:

```sh
cd spec
lake build                 # check every proof
lake env lean Audit.lean   # fail on sorry or any non-standard axiom
```

The audit walks every `TclMesh` declaration and allows only `propext`,
`Classical.choice`, and `Quot.sound`. A planted `sorry` fails it with `sorryAx`.

## Model

Ciphertext is modelled by its plaintext, as an ideal functionality. The
theorems are about who may learn what. They do not yet cover cryptographic
security, which will enter later as named hypotheses (for example "FHE
evaluation is correct within its noise budget" or "the range proof is sound")
of the mechanism lemmas that need them.

Secret data may drive decisions. Each kind of decision is a construct with a
typing rule:

| Construct | Decision | Typing |
|---|---|---|
| `select c a b` | oblivious: both branches run, the result stays secret | label `c ⊔ a ⊔ b` |
| `release to w e` | released: `e` reduced to `w` bits, revealed at `to` | policy must authorize `label(e) → to` |
| `verify to e` | proved: a key holder attests `e ≠ 0`, one bit at `to` | policy must authorize `label(e) → to` |

## Theorems

| File | Theorem | Statement |
|---|---|---|
| `Label` | `join_le_iff` | `a ⊔ b ⊑ c ↔ a ⊑ c ∧ b ⊑ c` |
| `Flow` | `infer_iff` | the label checker decides the typing relation exactly (sound and complete) |
| | `HasType.unique` | labels are unique |
| | `noninterference` | **declassification-indexed non-interference**: if `e : ℓ` and `ℓ ⊑ obs`, then `e`'s value is determined by the inputs `obs` may read plus the releases and proofs `obs` was shown |
| | `noninterference_strict` | with nothing visibly released, classical non-interference |
| | `observe_bounded`, `observed_bits_le` | every shown value fits its declared width, and the bits shown never exceed the static leakage `bits e` |
| | `releases_authorized` | every release and proof inside a well-typed expression is authorized for its operand's label |
| `Action` | `checkAction_iff` | the action checker decides well-typedness (public guard, no write-down to fields or effect fields) |
| | `action_noninterference` | an observer's view of an action (whether it ran, visible changed fields, visible effect fields) depends only on readable inputs and the releases and proofs shown |
| | `budget_sound` | if the budget check accepts, every run shows each observer at most the budget in bits |
| `Oblivious` | `exec_oblivious` | the operation trace of any target expression is the same under every input |
| | `source_leaks` | an ordinary `if` leaks its condition through the trace (a concrete witness) |
| | `compile_correct`, `compile_typed`, `compile_oblivious`, `compile_strict` | compiling `if` to `select` preserves values, is well typed at the label of what it reads, is oblivious, and leaks nothing |
| `Release` | `accepts_quorum` | an accepted threshold release has at least `t` distinct authorized holders, each with a valid share bound to this request |
| | `accepts_ignores_other_requests`, `accepts_duplicate` | shares for other requests and repeated shares have no effect |
| `Deontic` | `admits_iff` | execution is admitted iff all verdicts are one verdict other than `H` |
| | `admits_congr`, `H_blocks`, `conflict_blocks` | admission ignores order and repetition; `H` and any conflict block execution |
| `Decimal` | `le_refl`, `le_trans`, `le_total` | exact decimal order is a total preorder |
| | `scaled_le_iff`, `le_iff_at` | comparing at any exponent at or below both operands gives the same result |
| | `neg_zero`, and 20 cases checked by `decide` | signed zero is zero; `1e3 = 1000`, `0.1 < 0.10000000000000000001`, `1e1001`, `007`, `0x10`, `Inf` and similar are rejected |
| `Kernel` | `not_permits` | in the executable kernel, `not c` permits iff `c` evaluated to `false` |
| | `cmp_ok` | in the executable kernel, a successful comparison had two canonical decimals and reports their exact order |
| `Canonical` | `cmp_ok_canonical` | in the canonical domain, comparison success implies exact decimal order |
| `Range` | `wrap_id` | reduction modulo `2^w` into the signed word is the identity on the word |
| | `mul_mem` | a product lies in any range holding the four products of its operands' bounds |
| | `check_sound` | **if the range checker accepts a circuit and every input lies in its declared range, then wherever exact evaluation over `ℤ` is defined, `w`-bit wrapped evaluation (TFHE `FheInt32` at `w = 32`, `FheInt64` at `w = 64`) is defined and equal to it, and every node's value lies in its certified range: no intermediate wraps** |
| | `inputs_of_type`, `guarded_sound` | **for a circuit whose inputs declare no narrower range than their type (the form `range guard` produces, enforcing declared ranges with `clamp`), acceptance alone gives `wrapped = exact` on every input a ciphertext can hold — a word, or a bit — whoever encrypted it** |
| | `blocks_lt`, `offset_lt`, `proven_in_range`, `inputs_of_proofs` | **a proven input discharges the input hypothesis of `check_sound`: `k/2` sanitized base-4 blocks give an offset below `2^k`, so `lo + a` lies in `[lo, lo + 2^k − 1]` and in any declared range holding it; the soundness of TFHE-rs `zk-pok` and its sanitizing expansion are named hypotheses** |
| | `bounded_import`, `admission_sound` | **an exact `[lo, hi]`: `min (lo + a) hi` lies in `[lo, hi]` and equals `lo + a` for an honest input; the released admission bit is `1` exactly when `x ∈ [lo, hi]`, under any arithmetic reduction (comparisons never wrap), so releasing it reveals only the admission verdict** |
| | 12 cases checked by `decide` | canonical integer spellings; `maxBid` over whole words is rejected (`a − b` can leave the word), accepted with bids in `[0, 10⁶]`, rejected when a range is narrowed, and accepted guarded with `clamp`; the upstream word-range contract (`fit`, `wordOp`) at the word edge |
| `Noise` | `decode_correct` | decryption (rounding the phase `Δ·m + e`) returns `m` while `2\|e\| < Δ` |
| | `lin_bounds`, `lin_noise` | a linear combination `Σ w·cᵢ + k` lies in the interval extension of its operands, with noise at most `Σ \|w\|·levelᵢ · fresh` (the model's conservative absolute-noise accounting) |
| | `bootstrapped_sound`, `bootstrapped_representable` | **conditional abstract block soundness at any depth: every checked wire has a representable interval; under fresh bounded input noise, `2·maxLevel·fresh < Δ`, and success of the actual PBS calls, outputs decode to cleartext evaluation. Native PBS/noise correspondence remains an assumption.** |
| | `torus_decode_tfhe22` | exact modular rounding at Δ = 2^59 and q = 2^64 agrees with the integer lift for cleartexts 0..15 under the explicit absolute-noise bound |
| `NoiseProbability` | `failureMass_eq`, `conditional_union_bound`, `output_failure_bound` | **finite weighted adaptive execution theorem: `den * outputErrorMass ≤ pbsCount * num * totalMass`, assuming a conditional bound `num/den` on the full actual-call failure event after each successful prefix; no independence or unconditional native 2^-128 claim** |
| `Noise` | `chain_check`, `leveled_rejected` | under `tfhe22` (`max_degree 15`, `max_noise_level 5`), bootstrapped doubling chains are accepted at every depth; without bootstraps three doublings are rejected |
| | `permits_not` | `not p` permits only when `p` evaluated to `false`, never from a fault |
| | `cmp_ok`, `mem_ok` | a successful comparison had both operands in the canonical numeric domain; a successful membership test had a canonical list |
| | `and_fault_left`, `and_false_left`, `or_true_left` | fault propagation and short-circuiting, as in the Tcl and Rust evaluators |

`Range` takes TFHE's correctness as a named hypothesis outside the model: each
homomorphic operation decrypts to the wrapped result of its plaintext
operation (`wrapped w`), within its noise budget. `Noise` proves an abstract
block noise-budget theorem under explicit
absolute-noise and actual-call hypotheses. Identifying these hypotheses with
native TFHE-rs behavior and refining its integer algorithms to block programs
computing `wrapped w` remain unverified obligations. See
[the versioned correspondence audit](noise-correspondence.md). `Range` proves
that word wrapping never happens on an accepted circuit. Its arithmetic is the contract
of `finite_exact/word_range.mojo` in `larsbx/finite-math-kernels`, pinned in
`UPSTREAM.toml`; `spec-eval --word-range` replays the vendored upstream corpus
against `fit`, `wordOp` and `wrap`, and CI checks the vendored file against
the pinned upstream file, which the upstream Mojo kernel replays.

## Executable specification

`TclMesh/Kernel.lean` is a total model of the Tier A kernel over the typed data
model: descriptor validation with the same fault codes, authorization,
deontic resolution through `Deontic.resolve`, validations, sequential changes,
and effects. Predicates are evaluated in two stages: `Kernel.lower` resolves
every operand against the state and request (to UTF-8 bytes, list elements,
or the fault resolution raised) and makes `and`/`or` binary; then
`TclMesh/Predicate.lean`'s `Pred.eval` decides the result. Resolution is pure, so
resolving operands that short-circuiting never inspects changes nothing. `lake exe spec-eval VECTORS` runs it, and CI requires the Rust
kernel to reproduce every outcome exactly, on the curated vectors and on
seeded random ones.

## Rust refinement (Aeneas)

`kernel/core` is the dependency-free part of the Rust kernel that the running
kernel calls for predicate decisions (with decimal parsing and comparison,
canonical lists, and byte-level containment) and for deontic resolution. The
kernel lowers each JSON predicate to `predicate::Pred` exactly as
`Kernel.lower` does, and `predicate::eval` decides it. It is written in
the subset Aeneas translates: loops without early return, slices, `Vec`, enums,
no `?` on `Option`, no traits beyond derives.

`proof/extract.sh` runs Charon and Aeneas, both pinned, and regenerates
`proof/TclMeshProof/Core/Core.lean`, a pure Lean model of that Rust code.
`proof/CORE_SOURCE.sha256` records the sources it was generated from, and CI
fails if they change without regeneration. The model contains no axioms.

| File | Theorem | Statement |
|---|---|---|
| `Deontic` | `resolve_spec` | Rust `deontic::resolve` returns exactly `TclMesh.Deontic.resolve` of the abstracted verdicts |
| | `admits_spec` | Rust `deontic::admits` returns exactly `TclMesh.Deontic.admits` |
| `Decimal` | `compare_magnitude_loop_spec` | the digit loop computes the lexicographic order of the zero-padded digit strings |
| | `compare_magnitude_spec` | for nonzero canonical digit strings, `compare_magnitude a pa b pb` is the order of `a·10^pa` and `b·10^pb` |
| | `magnitude_spec` | exponent alignment to the smaller effective exponent is exact |
| | `compare_spec` | **on well-formed decimals, Rust `decimal::compare` returns exactly `TclMesh.Decimal.Dec.cmp`** |
| `Parse` | `digits_end_loop_spec`, `sign_end_spec`, `integer_ok_spec`, `fraction_end_spec`, `exponent_spec` | each scanner returns the split of the input bytes that the corresponding part of `TclMesh.Decimal.parseBytes` computes (`takeDigits`, `signPart`, `intOk`, `fracPart`, `expPart`) |
| | `bounded_exp_spec` | the saturating exponent accumulator returns exactly `boundedExp`: the value if at most 1000, else `none` |
| | `push_digits_loop_spec`, `mantissa_spec` | dropping leading zeros preserves the value `digitsVal (int ++ frac)` and yields digits without a leading zero |
| | `parse_spec` | **Rust `decimal::parse` returns exactly `TclMesh.Decimal.parseBytes` of the input bytes (under `absDec`), refusing only inputs longer than `u32::MAX` bytes, and every decimal it returns is well formed** |
| | `parse_compare_spec` | **end to end: parsing two operands and comparing them in Rust is the specification's comparison of their bytes** |
| `Predicate` | `range_eq_spec`, `bytes_eq_spec`, `is_infix_spec` | byte equality, and containment exactly as `isInfix` |
| | `plain_element_spec`, `has_quote_loop_spec` | the plain-element scan is `plainElement`; the quote scan is `List.any` |
| | `group_end_loop_spec`, `list_item_spec`, `list_member_loop_spec`, `list_member_spec` | brace groups scan as `braced`; one element as `listElems` takes it; **membership in a text list is `parseList` then `contains`** |
| | `items_member_loop_spec`, `member_spec` | membership in a list value validates every element as `elements` does, then tests containment |
| | `compare_spec`, `holds_spec` | ordered comparisons parse both operands with `parseBytes` and test the order |
| | `eval_spec` | **Rust `predicate::eval` decides every resolved predicate exactly as `TclMesh.Kernel.Pred.eval`, faults included, for comparison operands of at most `u32::MAX` bytes** |
| `Digits` | `lex_eq_compare`, `val_lt`, `val_ge`, `val_append_zeros` | lexicographic order of equal-length digit strings is numeric order; length bounds; zero padding multiplies by `10^p` |

### Computational security

`proof/TclMeshProof/Security.lean` connects the structural theorems to
computational security by a concrete-security hybrid argument. A
distinguisher `D` of two views of `n` ciphertexts under one key yields
explicit non-adaptive IND-CPA adversaries: `reduction D i` queries the
encryption oracle on the other `n − 1` hybrid messages and runs `D` once.

| Theorem | Statement |
|---|---|
| `game_reduction` | the IND-CPA game against `reduction D i` is exactly a view with the challenge at position `i` |
| `view_hybrid` | `Adv_view(D) ≤ Σ i, Adv_cpa(reduction D i)` |
| `view_bound` | if every non-adaptive IND-CPA adversary has advantage at most `ε` (a named hypothesis), views are `n·ε`-close |
| `leakage_bound` | views that agree on their public part (as the structural theorems guarantee for leakage-equivalent inputs) are `n·ε`-close |
| `completeness`, `special_soundness`, `hvzk`, `hvzk_prob` | Schnorr's Σ-protocol, in the exponent model `ZMod q`: honest proofs verify; two transcripts with one commitment determine the witness; real and simulated transcripts have equal distributions |

`security/` tests the same properties empirically on implementations
(`docs/testing.md`).

The proofs use Aeneas's Lean library and Mathlib, both at pinned versions
(`proof/lakefile.toml`). The audit (`lake env lean Audit.lean`) checks every
generated definition and every refinement theorem against the standard
axioms.

## Not yet proved

These are listed in the [roadmap](roadmap.md#formal-methods-first):

- full refinement of the executable kernel against the `Canonical` and `Flow`
  models (beyond the two lemmas above);
- lowering (operand resolution along paths), validation, changes and effects,
  which the Rust kernel implements outside `kernel/core` and which are covered
  by exact conformance with the executable specification only;
- ciphertext and labels in the kernel IR;
- per-mechanism lemmas under cryptographic assumptions;
- noise-budget soundness for leveled (bootstrap-free) evaluation beyond the
  block discipline, and the refinement of TFHE-rs integer operations to
  block gate programs;
- differential-privacy budgets.

## Checked handle and clamp admission

`int<W>-checked` requires the input hypotheses of `Range.check_sound` at
handle consumption, including `[0,1]` for Boolean handles. A Boolean label
alone is insufficient: legacy, persisted or imported handles must carry a
valid ordered subrange of `[0,1]`. Whole-word integer inputs still need no
narrow-range claim, as required by `Range.guarded_sound`.

Before backend evaluation, a Boolean output's certified node range must lie
inside `[0,1]`. `Range.bit_output_sound` derives the bit invariant and exact
wrapped result from `check_sound` and precisely this extra obligation. The
arithmetic certificate alone makes no claim about an output descriptor's type.
The runtime refuses a constant `2147483647` labelled `bool`; constants `0`
and `1` may compose through Boolean handles without decryption.

Both the Tcl and Lean range checkers require ordered clamp bounds inside the
signed word. A mathematically redundant lower bound `-2147483649` is refused
at width 32 even when clamping `0` would yield `0`. This deliberately restricts
admission to constants representable by TFHE's `FheInt32`; exact reference
evaluation remains available for arbitrary integer bounds. Word endpoints are
accepted. `conformance/range_admission.json` exercises both sides of this
boundary through the Tcl/Lean differential gate; `tests/tfhe.test` exercises
real encrypted endpoints, Boolean handle composition and counterexample
refusals. Relevant PRs now run the TFHE workflow before merge.

`UPSTREAM.toml` pins finite-math-kernels merge `7e921aa72c3bc59e7d1671f1a163f8bf34efd3a8`
(PR #89), which extends the canonical word-range contract through 64 bits.
The vendored 2,060-row corpus is byte-identical to that commit and has SHA-256
`7e0a5905383a80b3ec2a39a556de45249238a1dc39b932928e58077bda439dc1`.
The previous 1,720 rows are retained unchanged; 340 rows cover width 64.
CI verifies the pin, regenerates and replays the corpus with the upstream
Mojo kernel, and independently replays it through the Lean model.
