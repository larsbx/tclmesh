# SPEC_4of5 — encrypted 4-of-5 quorum kernel

A kernel that reveals exactly one bit, `T = [x₁+…+x₅ ≥ 4]`, decryptable by any
4 of 5 key holders. The P0 oracle `tools/q45_oracle.py` discharges 10/10
obligations on 4 seeds (`tests/test_threshold_q45_oracle.py`).

**Status: P0 toy arithmetic reference and P1 inert ceremony experiment.**
The P0 parameters are insecure. P1 checks message order and binding using
simulated payloads. The [governed threshold release boundary](threshold-release-boundary.md)
still refuses cryptographic threshold release.

## 1. Reference semantics

```math
P = \{P_1,\dots,P_5\},\quad x_i \in \mathbb{F}_2,\quad w = \textstyle\sum_i x_i \in [0,5],\quad T(x) = [\,w \ge 4\,] \in \mathbb{F}_2
```

| Property | Requirement |
|---|---|
| Output | `T(x)`, released to the decrypting quorum (or a designated receiver) |
| Leakage | `T` only; `w` and every `xᵢ` stay hidden |
| Access structure | `𝒜 = {S ⊆ P : |S| ≥ 4}`; maximal unqualified sets `C(5,3)` = 10 |
| Adversary | static; semi-honest at P0–P2, malicious from P3; corrupts ≤ 3 parties |
| Availability | any one party may be offline after all five have input and sealed |

Two limits are inherent, not defects. Four colluders form a quorum and can
decrypt any `Enc(xᵢ)`. The last partial decryptor sees `T` first (no
fairness). Fixing that needs commit-then-reveal of partials, which is out of
scope.

## 2. Kernel circuit

Over 𝔽₂ the threshold is one symmetric polynomial, `T ≡ e₄(x)`, the high bit
of the 3-bit popcount:

```math
[\,w \ge k\,] = \sum_{j=k}^{n} (-1)^{j-k}\binom{j-1}{k-1} e_j(x)
\;\Longrightarrow\; T = e_4 - 4e_5 \equiv e_4 \equiv \mathrm{bit}_2(w) \pmod 2
```

The identity is checked for all `n ≤ 11`. The mod-2 collapse is Lucas:
`C(w,4) mod 2 = bit₂(w)` because `w ≤ 5 < 8`.

```math
p_{12}=x_1x_2,\; p_{45}=x_4x_5,\; \pi = x_3x_4 + x_3x_5 + p_{45},\; \rho = (x_1{+}x_2)x_3,\qquad T = p_{12}\pi + p_{45}\rho
```

Level 1 holds 5 multiplications and level 2 holds 2: **7 multiplications,
depth 2**. A cost semantics in the tests counts the distinct multiplication
nodes, so the shared `p₄₅` is counted once. The kernel is written once as
`e4(add, mul, x)` and evaluated under 𝔽₂ and toy-BFV semantics. The oracle
therefore compares one term, not two transcriptions of it.

| Backend | Evaluation | Cost | Input validity |
|---|---|---|---|
| BFV/BGV, `t = 2` — **P0 default** | `e₄` circuit above | 7 mult + 7 relin, depth 2 | free: every plaintext is in 𝔽₂ |
| TFHE | `w = Σ cᵢ`, one PBS with LUT `s ↦ [s ≥ 4]`; message space ≥ 6 | 4 adds + 1 PBS | clamp each input `x ↦ [x ≠ 0]` (+5 PBS), or a ZK bit proof |
| BFV, prime `t ≥ 7` | `f(w) = C(w,4)·(21 − 4w)/5` | depth 3 | ZK proof `xᵢ ∈ {0,1}` required |
| Additive HE only | `Enc(rₐ(w − a))`, `a ∈ {0..3}`, shuffle, threshold-decrypt; any zero ⇒ `T = 0` | 4 decryptions + 1 shuffle | ZK proof `xᵢ ∈ {0,1}` required |

## 3. Key sharing

Replicated sharing over the 10 maximal unqualified sets. Every recombination
coefficient is 1, so partial-decryption noise is never amplified.

```math
\mathcal{U} = \tbinom{P}{3},\quad s = \sum_{A\in\mathcal{U}} r_A,\quad r_A \text{ held by } H(A) = P\setminus A,\qquad \delta_S(A) = \min\big(H(A)\cap S\big)
```

- **Load.** Each share has 2 holders. Each party holds `C(4,3) = 4` shares.
- **Designation is total iff `S ∈ 𝒜`.** If `|S| ≤ 3` then `S ⊆ A` for some
  `A`, so `r_A` is unreachable. If `|S| ≥ 4` then every `H(A)` meets `S`.
- **Partial.** `dᵢ = c₁·σᵢ + Eᵢ`, where `σᵢ = Σ r_A` over `δ_S(A) = i` and
  `Eᵢ ← U[−2^ς, 2^ς]^N`.
- **Combine.** `c₀ + Σ_{i∈S} dᵢ = Δ·T + e + Σ Eᵢ`, decoded by rounding `(t/q)·(·)`.

```math
\varsigma \ge \log_2\lVert e\rVert_\infty + \kappa, \qquad \lVert e\rVert_\infty + |S|\cdot 2^{\varsigma} < \Delta/2
```

**Shamir alternative.** Shares are `sⱼ = f(j)` with `deg f = 3` and
`f(0) = s`. Party `j` must apply its own Lagrange coefficient:
`dⱼ = λⱼˢ·c₁·sⱼ + Eⱼ`. If the combiner applies `λ` after smudging, the noise
is `Σ λⱼEⱼ`, and `λⱼ mod q` is q-sized whenever `λⱼ ∉ ℤ`. The oracle measures
this: only `{1,2,3,4}` (λ = 4, −6, 4, −1) and `{2,3,4,5}` (λ = 10, −20, 15,
−4) survive. Shoup's `n!` scaling makes every `λ` integral, but
`5! ≡ 0 (mod 2)` erases a `t = 2` plaintext. It needs `gcd(n!, t) = 1`, so it
is excluded.

**Choice.** Replicated sharing at `n = 5`. Shamir with local `λ` only if `n`
grows: the replicated share count `C(n, k−1)` explodes (`n = 10, k = 7` gives
210).

## 4. Ceremony

Privacy against ≤ 3 corrupt parties rests on one rule. Every quorum contains
an honest party, and an honest party decrypts only the `c_T` it recomputed
itself.

1. **Setup.** Produce `pk`, `rlk` and the holdings `{r_A}`. A trusted dealer
   does this at P0; DKG replaces it at P2.
2. **Input.** `Pᵢ` publishes `cᵢ = Enc_pk(xᵢ)`, bound to `(sid, i)`. From P3
   on, it also attaches a proof of plaintext knowledge, which stops copying or
   tweaking another party's input.
3. **Seal.** With all 5 inputs present, every party recomputes
   `c_T = e4(add, mul_rlk, c)` deterministically and posts `H(c_T)`. Sealing
   requires all posted hashes to agree.
4. **Quorum.** The first 4 parties to commit form `S`. `S` and `δ_S` are
   frozen in the ledger before any partial is released.
5. **Partial.** Each `i ∈ S` releases `dᵢ` over `c_T` only, bound to
   `(sid, H(c_T), S)`, with fresh smudging `Eᵢ`.
6. **Combine.** Anyone computes `T` from the 4 partials and appends it to
   the ledger.

### P1 transition contract

The [standalone Erlang experiment](../experiments/threshold_q45/q45_ceremony.erl)
serializes one session in a `gen_statem`. Its deterministic reducer takes a
trusted logical time. The process adapter supplies local monotonic time and
fires an idle timeout. Each phase has a fresh deadline, fixed until the next
phase. A message processed at the deadline or later causes a terminal abort.

| Phase | Accepted transition |
|---|---|
| Inputs | One nonempty ciphertext per party in the session. After all five, a trusted simulated evaluator receives them in party order and fixes the exact output bytes and SHA-256 digest. |
| Sealing | All five distinct parties attest to the locally computed digest. A conflicting digest is rejected and does not count. |
| Quorum | The first four distinct commitments to that digest freeze the sorted quorum and the share designation. |
| Partials | A single nonempty simulated payload per frozen member, bound to the session, exact output bytes, digest, and canonical quorum. |
| Result | After all four contributions, a matching one-bit result is checked by the trusted simulated combiner and recorded once. |
| Complete or aborted | Terminal. Later submissions cannot change the session. |

P1 aborts on missing inputs, attestations, commitments, partials, or a result
at the respective deadline. A missing partial requires a fresh session ID
and a fresh transcript. In-session quorum re-formation is deferred. The
caller is responsible for unique session IDs, authenticated attribution in
any future integration, and trusted, deterministic evaluation and
combination callbacks. P1 records state in memory. Its simulated messages
carry no signatures or proofs of input knowledge or partial correctness.

## 5. Invariants

| ID | Statement | Discharged by | Rung |
|---|---|---|---|
| INV-Q1 | Circuit fidelity: `e4` over 𝔽₂ equals `T` on all of 𝔽₂⁵ | O1; M1, M2 rejected | P0 |
| INV-Q2 | Correctness: `∀x ∀S ∈ C(P,4)`, `Combine_S ∘ Partial_S ∘ Eval ∘ Enc(x) = (T(x), 0, …, 0)` | O2, O3 | P0 |
| INV-Q3 | Access: `δ_S` total ⇔ `|S| ≥ 4`, over all 32 subsets | O4 | P0 |
| INV-Q4 | Unit recombination: no coefficient other than 1 touches a smudged term | structural; M3 shows the failure | P0 |
| INV-Q5 | Noise margin: `log₂‖e‖ + κ ≤ ς` and `‖e‖ + 5·2^ς < Δ/2` | O5 | P0 |
| INV-Q6 | Smudging present: `‖dᵢ − c₁σᵢ‖∞ ≥ 2^(ς−4)` | O7 | P0 |
| INV-Q7 | Sub-quorum blind: 3 parties pooling every share they hold decode `T` at chance | O6 (empirical) | P0 |
| INV-Q8 | Decrypt-only-`c_T`: admit simulated partials only for the exact locally recomputed `c_T` | Exact-byte and digest checks, foreign ciphertext mutant | P1 |
| INV-Q9 | Model order: `S`, `δ_S` frozen before the first partial; `T` recorded once in the session process | Prefix model, deadline tests, transition mutants | P1 |
| INV-Q10 | Input binding: `cᵢ` bound to `(sid, i)` with a proof of plaintext knowledge | proof verifier + replay mutant | P3 |

## 6. Dec∘Eval differential oracle

`tools/q45_oracle.py` is a pure-Python toy BFV with exact integer arithmetic:
`N = 32`, `t = 2`, `q = 2¹²⁷ − 1` (a Mersenne prime, so Shamir `λ` exist),
relin base `2¹⁶` with 8 digits, CBD(η = 3) errors, ternary `s` and `u`,
`κ = 40`, `ς = 72`. A run takes about 1.5 s.

```text
python3 -I tools/q45_oracle.py [seed]
```

It exits 0 iff every obligation passes. An obligation that raises counts as a
failure (`discharge`). Results for seed `0x45`:

| Obligation | Checks | Result |
|---|---|---|
| O1 | `e4` over 𝔽₂ ≡ `T` | 32/32 inputs |
| O2 | `Dec_s ∘ Eval ≡ T`, full key, all 32 coefficients | 32/32 |
| O3 | `Combine_S ∘ Partial_S ∘ Eval ≡ T`, `∀S ∈ C(5,4)` | 160/160 (input, quorum) cases |
| O4 | `δ_S` total ⇔ `|S| ≥ 4`; load 4 shares per party | 32 subsets; load {4} |
| O5 | noise margins | `log₂‖e‖ = 26`; 26 + 40 ≤ 72; `Δ/2 ≈ 2¹²⁵` |
| O6 | 3 parties pooling all held shares decode ≈ coin | hit rate 0.500 over 128 trials (band 0.3–0.7) |
| O7 | partial residual carries smudge | 72, 72, 72, 72 bits |
| M1 | mutant `e4` missing `x₂x₃x₄x₅` rejected | witnesses (0,1,1,1,1), (1,1,1,1,1) |
| M2 | mutant threshold `k = 3` rejected | 10 witnesses |
| M3 | Shamir λ-local passes `∀S`; λ-after-smudge fails `∃S` | 5/5 vs. only {1,2,3,4}, {2,3,4,5} |

Across seeds `0x45, 0x1234, 0x7, 0x63`, `log₂‖e‖ ∈ {26, 27}` and the O6 hit
rate falls between 0.477 and 0.586.

M1–M3 are the discriminating witnesses. Each one is a plausible wrong
implementation the oracle must reject, so a green run cannot be vacuous. The
tests add a fourth: with smudging removed, O7 fails. O6 is a statistical band,
not a proof. The P1 sampling check uses 10⁴ trials across the same four
seeds, drawing a fresh replicated sharing and a random three-party coalition
each trial from a balanced target-bit distribution over the existing toy
ciphertext corpus.

## 7. Rung ladder and open questions

Each later rung reuses the same oracle with one component swapped, so every
rung is gated by the same O/M obligations plus its own.

1. **P0 — toy reference (done).** Python BFV, trusted dealer, replicated
   sharing. Gate: 10/10 on 4 seeds.
2. **P1 — inert ceremony state machine.** Check INV-Q8 and Q9 using
   every commitment permutation, adversarial submissions at each modeled
   prefix, exact deadlines, and deliberately broken transitions. Replay the
   P0 toy ciphertexts and partials through the P1 process for all four seeds.
   The wider O6 check remains an empirical toy measurement.
3. **P2 — DKG.** Each party deals its own `sⱼ` in replicated form, and
   `s = Σ sⱼ`. `pk` aggregates over a common reference string; `rlk` needs a
   multiparty relinearization-key round. Gate: O2–O7 pass with DKG keys, and
   the dealer is gone from the code path. P2a below exercises the public-key
   and holder-local setup before the relinearization round.
4. **P3 — malicious inputs.** Proof of plaintext knowledge bound to
   `(sid, i)`, or the TFHE clamp path. Gate: INV-Q10, plus a replay or copy
   mutant that must be rejected.
5. **P4 — production backend.** A native BFV (`t = 2`) or TFHE worker. Gate:
   differential Dec∘Eval of the backend against the P0 reference on all 160
   (input, quorum) cases, with secure parameters and `q` sized for `ς + κ`
   headroom.

Open questions:

- [ ] Should a later rung support retrying with a different quorum within one session?
- [ ] Output receiver: does `T` go to all 5 parties, or only to the quorum?
- [ ] Is fairness (commit-then-reveal of partials) required?
- [ ] Does the chosen library's threshold API support k-of-n with local `λ`,
  or only n-of-n with share recovery? Unverified; check before P4.
- [ ] Many concurrent sessions in SIMD slots: `t = 2` batching is restricted,
  so does P4 need `t ≥ 7` or TFHE instead?

## 8. Reproduce P1

From the repository root with Python 3 and Erlang/OTP (compiler, Crypto and EUnit):

```sh
python3 tools/check_q45_ceremony_mutants.py
python3 -B tools/check_q45_toy_replay.py
python3 -B -m unittest discover -s tests -p 'test_threshold_q45*.py'
```

The EUnit model visits the prefixes of 120 complete commitment orders,
including all five possible frozen quorums. The mutant runner compiles each
changed transition separately and requires its named acceptance test to fail.
The Python suite exercises the original arithmetic and the wider toy O6
sampling check.

The P0/P1 replay generates all 640 seed, input, and quorum combinations using
the Python toy oracle. Its evaluator callback returns the precomputed
ciphertext only for the exact five input ciphertexts in party order. The
Erlang combiner independently decodes all 32 coefficients from the admitted
partial bytes and checks the 31 trailing zeros. Each transcript rejects
changed ciphertext bytes, the opposite result bit, and repeated result
submission. Four extra probes demonstrate that a malformed partial can
enter the opaque simulation envelope but aborts before a result is
recorded. This replay uses trusted toy vectors and the original trusted
dealer. Share authentication and cryptographic proof verification belong
to later rungs.

## 9. P2a toy collective public key and holder setup

The [P2a experiment](../tools/q45_collective_setup.py) gives each of five
participants a separate deterministic random stream in the test harness.
They agree on one public polynomial `a` and each samples a private additive
contribution `s_i` and error `e_i`. Each publishes `b_i = -a s_i + e_i`.
The evaluator receives only `(Σ b_i, a)`. In the toy ring, adding the public
shares gives `Σ b_i = -a Σ s_i + Σ e_i`.

Each participant also splits its own `s_i` using the P0 replicated sharing.
For each excluded triple, it sends one copy of the corresponding fragment to
each of the two remaining holders. A holder adds the five fragments for each
triple assigned to it. Each designated holder then computes its partial from
its own inbox-derived pieces. No API in this setup returns the aggregate
secret polynomial. The single-process test harness simulates all five inboxes
and can inspect their contents.

The tests encrypt all 32 input patterns, add the five ciphertexts, and
reconstruct the resulting parity through each of the five possible quorums
on each of four seeds. They also check exact fragment routing and rejection
of incomplete, duplicate, foreign, malformed, and misrouted contributions.
Run from the repository root:

```sh
python3 -B -m unittest discover -s tests -p 'test_threshold_q45_collective_setup.py'
```

This experiment assumes honest participants, a consistent public setup and
private fragment delivery by the harness. Its parameters and randomness are
for reproducible tests. The remaining P2 gate requires collective
relinearization-key generation and replay of the nonlinear `e4` circuit
under that key. Authenticated delivery and verifiable share correctness are
outside the P2a model.

## 10. P2b toy collective relinearization

The [P2b experiment](../tools/q45_collective_relin.py) adds two rounds of
contributions followed by public aggregation. It adapts the algebra of
[Lattigo's relinearization-key protocol](https://pkg.go.dev/github.com/tuneinsight/lattigo/v6@v6.2.0/multiparty#RelinearizationKeyGenProtocol)
to the P0 base-2¹⁶ gadget. The test harness supplies a fresh common polynomial
`a_j` per digit and simulates delivery. For each digit `g_j = 2^(16j)`,
participant `i` uses its local contribution `s_i` and samples an ephemeral
`u_i`. All operations below are in the toy ring.

```text
A_j = sum_i(-u_i a_j + g_j s_i + e0_i)
B_j = sum_i( s_i a_j             + e1_i)
C_j = sum_i( s_i A_j + (u_i - s_i) B_j + e2_i)
R_j = (C_j, B_j)
```

With `s = sum_i(s_i)`, `u = sum_i(u_i)` and `E_k = sum_i(ek_i)`,
the decrypting phase is `C_j + s B_j = g_j s² + s E0 + u E1 + E2`.
The evaluator receives the aggregated public and relinearization keys.
Only the test oracle assembles the summed secret to check the gadget
residuals, full-key decoding, and noise. Actual threshold reconstruction uses
holder-local partials. All five parties are required for setup.

The unchanged `e4` circuit is tested on all 128 seed/input combinations
and all 640 seed/input/quorum combinations. Tests also cover incomplete or
mixed transcripts, actual smudging in holder-local partials, and an empirical
O6 check using the ten three-party views of each fixed toy setup.

Collective relinearization raised the measured ciphertext noise width to
33, 33, 33, and 34 bits across the four seeds. The P0 72-bit smudging setting
missed the 40-bit margin in 61 of 128 ciphertexts. P2b uses an 80-bit setting
and checks both the smudging margin and the four-partial decoding bound on
every sampled ciphertext. These are reproducible toy measurements.

```sh
python3 -B -m unittest discover -s tests -p 'test_threshold_q45_collective_relin.py'
```

The experiment assumes honest contributors and a consistent first-round
aggregate delivered to each participant. The Python objects do not implement
authenticated broadcast, share proofs, or production key custody.

## 11. P2b dishonest-participant characterization

The [adversarial acceptance model](threshold-q45-p2b-adversarial-acceptance.md)
preserves the 640 honest cases and exposes canonical dishonest contributions
that the current interfaces accept. In particular, adding `DELTA` to one
partial flips the bit in all 640 cases, including through the inert P1 actor.
The 80-bit smudging checks establish correctness bounds only under the honest
noise and bounded-mask assumptions; they do not enforce contribution integrity.

```sh
python3 -B tools/check_q45_adversarial.py
```

The failure matrix distinguishes local validation, authenticated agreement,
verifiable sharing/partial proofs and construction-level obligations. These
tests document limitations and add no malicious-security or release capability.
