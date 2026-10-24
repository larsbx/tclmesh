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
| | `permits_not` | `not p` permits only when `p` evaluated to `false`, never from a fault |
| | `cmp_ok`, `mem_ok` | a successful comparison had both operands in the canonical numeric domain; a successful membership test had a canonical list |
| | `and_fault_left`, `and_false_left`, `or_true_left` | fault propagation and short-circuiting, as in the Tcl and Rust evaluators |

## Executable specification

`TclMesh/Kernel.lean` is a total model of the Tier A kernel over the typed data
model: descriptor validation with the same fault codes, authorization,
deontic resolution through `Deontic.resolve`, validations, sequential changes,
and effects. `lake exe spec-eval VECTORS` runs it, and CI requires the Rust
kernel to reproduce every outcome exactly, on the curated vectors and on
seeded random ones.

## Not yet proved

These are listed in the [roadmap](roadmap.md#formal-methods-first):

- full refinement of the executable kernel against the `Canonical` and `Flow`
  models (beyond the two lemmas above);
- an Aeneas refinement proof for the Rust kernel;
- ciphertext and labels in the kernel IR;
- per-mechanism lemmas under cryptographic assumptions;
- noise-budget soundness;
- differential-privacy budgets.
