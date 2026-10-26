import Mathlib

/-!
# Computational security: from structural non-interference to IND-CPA

Structural theorems (`TclMesh.Flow`, `TclMesh.Circuit.declared_publics`) show
that a party's view depends on secret inputs *only* through ciphertexts. This
file closes the gap to computational security with a concrete-security hybrid
argument: any distinguisher of two such views yields explicit IND-CPA
adversaries whose advantages sum to at least its own.

* `view_hybrid`: `Adv_view(D) ≤ Σ i, Adv_cpa(reduction D i)`;
* `view_bound`: if every (non-adaptive) IND-CPA adversary has advantage at
  most `ε`, views of `n` ciphertexts are `n·ε`-indistinguishable.

The reduction is explicit: `reduction D i` queries the encryption oracle on
the other `n − 1` messages and runs `D` once, so its cost is evident from its
definition. Non-adaptive adversaries are the weaker assumption.

The second half proves Schnorr's Σ-protocol complete, special-sound and
perfectly honest-verifier zero knowledge, in the exponent model `ZMod q`.
-/

open Finset

namespace TclMeshProof.Security

/-! ## Finite probability -/

/-- The probability of an event under uniform randomness. -/
noncomputable def prob {Ω : Type} [Fintype Ω] (E : Ω → Bool) : ℝ :=
  ((univ.filter fun ω => E ω = true).card : ℝ) / Fintype.card Ω

/-- An event that ignores one independent uniform coordinate. -/
theorem prob_prod_fst {Ω R : Type} [Fintype Ω] [Fintype R] [Nonempty R] (E : Ω → Bool) :
    prob (fun p : Ω × R => E p.1) = prob E := by
  unfold prob
  have hR : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hc : (univ.filter fun p : Ω × R => E p.1 = true) =
      (univ.filter fun ω => E ω = true) ×ˢ (univ : Finset R) := by
    ext ⟨ω, r⟩; simp
  rw [hc, card_product, card_univ, Fintype.card_prod]
  push_cast
  rw [mul_div_mul_right _ _ hR]

/-- Probability is invariant under a bijection of the randomness. -/
theorem prob_equiv {Ω Ω' : Type} [Fintype Ω] [Fintype Ω'] (e : Ω ≃ Ω') (E : Ω' → Bool) :
    prob (fun ω => E (e ω)) = prob E := by
  unfold prob
  rw [Fintype.card_congr e]
  congr 2
  exact_mod_cast card_equiv e (fun ω => by simp)

/-! ## Encryption schemes and the IND-CPA game -/

/-- An encryption scheme with uniform keys `K` and per-ciphertext randomness `R`. -/
structure Scheme (K R M C : Type) where
  enc : K → M → R → C

variable {K R M C : Type} [Fintype K] [Fintype R] [Nonempty R]

/-- A non-adaptive chosen-plaintext adversary: it fixes `n` oracle queries,
then sees their answers and the challenge. -/
structure Adversary (M C : Type) (n : ℕ) where
  queries : Fin n → M
  decide : (Fin n → C) → C → Bool

/-- The IND-CPA game for challenge message `m`: a key, the challenge's
randomness, and fresh randomness for every query. -/
noncomputable def game {n : ℕ} (S : Scheme K R M C) (B : Adversary M C n) (m : M) : ℝ :=
  prob fun ω : K × R × (Fin n → R) =>
    B.decide (fun j => S.enc ω.1 (B.queries j) (ω.2.2 j)) (S.enc ω.1 m ω.2.1)

noncomputable def cpaAdv {n : ℕ} (S : Scheme K R M C) (B : Adversary M C n) (m₀ m₁ : M) : ℝ :=
  |game S B m₀ - game S B m₁|

/-! ## Views of ciphertexts and the hybrid argument -/

/-- The distribution of a view: `n` ciphertexts under one key, read by `D`. -/
noncomputable def view {n : ℕ} (S : Scheme K R M C) (ms : Fin n → M) (D : (Fin n → C) → Bool) : ℝ :=
  prob fun ω : K × (Fin n → R) => D fun j => S.enc ω.1 (ms j) (ω.2 j)

noncomputable def viewAdv {n : ℕ} (S : Scheme K R M C) (D : (Fin n → C) → Bool)
    (ms ms' : Fin n → M) : ℝ :=
  |view S ms D - view S ms' D|

/-- Hybrid `i`: the first `i` messages from `ms'`, the rest from `ms`. -/
def hybrid {n : ℕ} (ms ms' : Fin n → M) (i : ℕ) : Fin n → M :=
  fun j => if j.val < i then ms' j else ms j

/-- The reduction for position `i`: query every other position's hybrid
message, place the challenge at `i`, run `D` once. -/
def reduction {n : ℕ} (D : (Fin n → C) → Bool) (ms ms' : Fin n → M) (i : Fin n) :
    Adversary M C n where
  queries := hybrid ms ms' i.val
  decide := fun answers c => D fun j => if j = i then c else answers j

/-- The game against `reduction D i` *is* a view: the challenge randomness
fills position `i`, and the unused query randomness there is independent. -/
theorem game_reduction {n : ℕ} (S : Scheme K R M C) (D : (Fin n → C) → Bool) (ms ms' : Fin n → M)
    (i : Fin n) (m : M) :
    game S (reduction D ms ms' i) m = view S (Function.update (hybrid ms ms' i.val) i m) D := by
  unfold game view
  -- (k, r, rs) ↦ ((k, rs[i := r]), rs i) is a bijection
  let e : K × R × (Fin n → R) ≃ (K × (Fin n → R)) × R :=
    { toFun := fun ω => ((ω.1, Function.update ω.2.2 i ω.2.1), ω.2.2 i)
      invFun := fun p => (p.1.1, p.1.2 i, Function.update p.1.2 i p.2)
      left_inv := fun ω => by
        obtain ⟨k, r, rs⟩ := ω
        simp
      right_inv := fun p => by
        obtain ⟨⟨k, rs⟩, r⟩ := p
        simp }
  let F : K × (Fin n → R) → Bool := fun ω =>
    D fun j => S.enc ω.1 (Function.update (hybrid ms ms' i.val) i m j) (ω.2 j)
  change _ = prob F
  rw [← prob_prod_fst (R := R) F, ← prob_equiv e (fun p => F p.1)]
  congr 1
  funext ω
  obtain ⟨k, r, rs⟩ := ω
  simp only [reduction, e, F, Equiv.coe_fn_mk]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem update_hybrid {n : ℕ} (ms ms' : Fin n → M) (i : Fin n) :
    Function.update (hybrid ms ms' i.val) i (ms i) = hybrid ms ms' i.val ∧
    Function.update (hybrid ms ms' i.val) i (ms' i) = hybrid ms ms' (i.val + 1) := by
  constructor <;> funext j <;> by_cases h : j = i
  · subst h; simp [hybrid]
  · simp [Function.update_of_ne h, hybrid]
  · subst h; simp [hybrid]
  · have : j.val ≠ i.val := fun hv => h (Fin.ext hv)
    simp only [Function.update_of_ne h, hybrid]
    by_cases hl : j.val < i.val
    · simp [hl, show j.val < i.val + 1 by omega]
    · simp [hl, show ¬ j.val < i.val + 1 by omega]

/-- Adjacent hybrids are one IND-CPA game apart. -/
theorem adjacent {n : ℕ} (S : Scheme K R M C) (D : (Fin n → C) → Bool) (ms ms' : Fin n → M)
    (i : Fin n) :
    |view S (hybrid ms ms' i.val) D - view S (hybrid ms ms' (i.val + 1)) D| =
      cpaAdv S (reduction D ms ms' i) (ms i) (ms' i) := by
  unfold cpaAdv
  rw [game_reduction, game_reduction, (update_hybrid ms ms' i).1, (update_hybrid ms ms' i).2]

theorem hybrid_zero {n : ℕ} (ms ms' : Fin n → M) : hybrid ms ms' 0 = ms := by
  funext j; simp [hybrid]

theorem hybrid_n {n : ℕ} (ms ms' : Fin n → M) : hybrid ms ms' n = ms' := by
  funext j; simp [hybrid, j.isLt]

/-- **Hybrid argument.** A distinguisher of two views of `n` ciphertexts
yields `n` explicit IND-CPA adversaries whose advantages sum to at least its
own. -/
theorem view_hybrid {n : ℕ} (S : Scheme K R M C) (D : (Fin n → C) → Bool) (ms ms' : Fin n → M) :
    viewAdv S D ms ms' ≤ ∑ i : Fin n, cpaAdv S (reduction D ms ms' i) (ms i) (ms' i) := by
  let H : ℕ → ℝ := fun m => view S (hybrid ms ms' m) D
  -- telescoping: |H 0 − H m| ≤ Σ_{i<m} |H i − H (i+1)|
  have tele : ∀ m, |H 0 - H m| ≤ ∑ i ∈ range m, |H i - H (i + 1)| := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ]
      calc |H 0 - H (m + 1)| ≤ |H 0 - H m| + |H m - H (m + 1)| := abs_sub_le _ _ _
        _ ≤ _ := by gcongr
  calc viewAdv S D ms ms' = |H 0 - H n| := by
        simp only [viewAdv, H, hybrid_zero, hybrid_n]
    _ ≤ ∑ i ∈ range n, |H i - H (i + 1)| := tele n
    _ = ∑ i : Fin n, |H i.val - H (i.val + 1)| :=
        (Fin.sum_univ_eq_sum_range (fun i => |H i - H (i + 1)|) n).symm
    _ = ∑ i : Fin n, cpaAdv S (reduction D ms ms' i) (ms i) (ms' i) := by
        congr 1; funext i; exact adjacent S D ms ms' i

/-- **Views are indistinguishable** when the scheme is: under the assumption
that every non-adaptive IND-CPA adversary has advantage at most `ε` (a named
hypothesis, not an axiom), views of `n` ciphertexts are `n·ε`-close. -/
theorem view_bound {n : ℕ} (S : Scheme K R M C) (ε : ℝ)
    (hcpa : ∀ (B : Adversary M C n) (m₀ m₁ : M), cpaAdv S B m₀ m₁ ≤ ε)
    (D : (Fin n → C) → Bool) (ms ms' : Fin n → M) :
    viewAdv S D ms ms' ≤ n * ε := by
  calc viewAdv S D ms ms' ≤ ∑ i : Fin n, cpaAdv S (reduction D ms ms' i) (ms i) (ms' i) :=
        view_hybrid S D ms ms'
    _ ≤ ∑ _i : Fin n, ε := sum_le_sum fun i _ => hcpa _ _ _
    _ = n * ε := by simp

/-- A view with a public part: whatever the party sees besides ciphertexts is
a function of what it may learn (`pub`), so leakage-equivalent inputs
(`pub x = pub x'`, the structural theorems) give views as close as their
ciphertexts. -/
theorem leakage_bound {X P : Type} {n : ℕ} (S : Scheme K R M C) (ε : ℝ)
    (hcpa : ∀ (B : Adversary M C n) (m₀ m₁ : M), cpaAdv S B m₀ m₁ ≤ ε)
    (pub : X → P) (secret : X → Fin n → M) (D : P → (Fin n → C) → Bool) (x x' : X)
    (h : pub x = pub x') :
    |view S (secret x) (D (pub x)) - view S (secret x') (D (pub x'))| ≤ n * ε := by
  rw [← h]
  exact view_bound S ε hcpa (D (pub x)) (secret x) (secret x')

/-! ## Zero knowledge: Schnorr's protocol in the exponent model

Group elements `g^x` are represented by their exponents `x : ZMod q`, so a
statement is `h = w`, a commitment `t = r`, and verification `g^z = t·h^c`
reads `z = t + c·h`. -/

variable {q : ℕ} [Fact q.Prime]

structure Transcript (q : ℕ) where
  t : ZMod q
  c : ZMod q
  z : ZMod q
  deriving DecidableEq

def verifies (h : ZMod q) (tr : Transcript q) : Prop := tr.z = tr.t + tr.c * h

def respond (w r c : ZMod q) : Transcript q := ⟨r, c, r + c * w⟩

def simulate (h c z : ZMod q) : Transcript q := ⟨z - c * h, c, z⟩

/-- **Completeness.** -/
theorem completeness (w r c : ZMod q) : verifies w (respond w r c) := by
  simp [verifies, respond]

/-- **Special soundness**: two accepting transcripts with one commitment and
distinct challenges determine the witness. -/
theorem special_soundness (h : ZMod q) (a b : Transcript q) (ha : verifies h a) (hb : verifies h b)
    (ht : a.t = b.t) (hc : a.c ≠ b.c) : (a.z - b.z) / (a.c - b.c) = h := by
  unfold verifies at ha hb
  have hne : a.c - b.c ≠ 0 := sub_ne_zero.mpr hc
  rw [ha, hb, ht, div_eq_iff hne]
  ring

/-- The simulator's transcripts always verify. -/
theorem simulate_verifies (h c z : ZMod q) : verifies h (simulate h c z) := by
  simp [verifies, simulate]

/-- **Perfect honest-verifier zero knowledge**: for each challenge, the map
from the prover's nonce to the simulator's response is a bijection carrying
real transcripts to simulated ones; so the two distributions are equal. -/
theorem hvzk (w c : ZMod q) :
    ∃ e : ZMod q ≃ ZMod q, ∀ r, respond w r c = simulate w c (e r) := by
  refine ⟨Equiv.addRight (c * w), fun r => ?_⟩
  simp [respond, simulate]

/-- The same, as equal probabilities of every event over uniform nonces and
uniform simulator responses. -/
theorem hvzk_prob (w c : ZMod q) (E : Transcript q → Bool) :
    prob (fun r : ZMod q => E (respond w r c)) = prob (fun z : ZMod q => E (simulate w c z)) := by
  obtain ⟨e, he⟩ := hvzk w c
  simp_rw [he]
  exact prob_equiv e (fun z => E (simulate w c z))

end TclMeshProof.Security
