import Std

/-!
P2b acceptance-boundary abstraction, not a proof of FHE or Erlang refinement.
`correct` is ghost information, unavailable to the present toy verifier.
All cryptographic soundness appears as an explicit theorem hypothesis.
-/
namespace TclMesh.Q45Adversarial

structure Binding where
  session : Nat
  ciphertext : Nat
  quorum : List Nat
  deriving DecidableEq, Repr

structure Contribution where
  sender : Nat
  binding : Binding
  nonempty : Bool
  canonical : Bool
  authenticated : Bool
  correct : Bool
  deriving DecidableEq, Repr

structure State where
  binding : Binding
  partials : List Contribution
  deriving DecidableEq, Repr

/-- Local P1 envelope checks at the frozen-partials phase. Encoding is opaque. -/
def envelope (s : State) (c : Contribution) : Prop :=
  c.binding = s.binding ∧ c.sender ∈ s.binding.quorum ∧
  c.sender ∉ s.partials.map Contribution.sender ∧ c.nonempty = true

instance (s : State) (c : Contribution) : Decidable (envelope s c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def submit (s : State) (c : Contribution) : State :=
  if envelope s c then {s with partials := c :: s.partials} else s

def wellBound (s : State) : Prop :=
  (s.partials.map Contribution.sender).Nodup ∧
  ∀ c ∈ s.partials, c.binding = s.binding ∧ c.sender ∈ s.binding.quorum

theorem submit_preserves_wellBound (s : State) (c : Contribution)
    (h : wellBound s) : wellBound (submit s c) := by
  unfold submit
  split
  · rename_i hc
    refine ⟨List.nodup_cons.mpr ⟨hc.2.2.1, h.1⟩, ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨hc.1, hc.2.1⟩
    · exact h.2 d hd
  · exact h

theorem duplicate_rejected (s : State) (c : Contribution)
    (h : c.sender ∈ s.partials.map Contribution.sender) : submit s c = s := by
  simp [submit, envelope, h]

theorem foreign_binding_rejected (s : State) (c : Contribution)
    (h : c.binding ≠ s.binding) : submit s c = s := by
  simp [submit, envelope, h]

theorem submissions_preserve_wellBound (cs : List Contribution) (s : State)
    (h : wellBound s) : wellBound (cs.foldl submit s) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih => exact ih _ (submit_preserves_wellBound s c h)

/-- Envelope admission cannot distinguish correctness or canonical encoding. -/
theorem envelope_ignores_ghost_correctness (s : State) (c : Contribution) (b : Bool) :
    envelope s {c with correct := b} ↔ envelope s c := Iff.rfl

theorem envelope_ignores_encoding (s : State) (c : Contribution) (b : Bool) :
    envelope s {c with canonical := b} ↔ envelope s c := Iff.rfl

def certified (s : State) : Prop := ∀ c ∈ s.partials, c.correct = true

/-- Proposed verification interface, not an implementation of a share proof. -/
def submitVerified (verify : Contribution → Bool) (s : State) (c : Contribution) : State :=
  if verify c then submit s c else s

theorem verified_submission_preserves_correctness
    (verify : Contribution → Bool)
    (soundness : ∀ c, verify c = true → c.correct = true)
    (s : State) (c : Contribution) (h : certified s) :
    certified (submitVerified verify s c) := by
  unfold submitVerified
  split
  · rename_i hv
    unfold submit
    split
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact soundness d hv
      · exact h d hd
    · exact h
  · exact h

theorem verified_submissions_preserve_correctness
    (verify : Contribution → Bool)
    (soundness : ∀ c, verify c = true → c.correct = true)
    (cs : List Contribution) (s : State) (h : certified s) :
    certified (cs.foldl (submitVerified verify) s) := by
  induction cs generalizing s with
  | nil => exact h
  | cons c cs ih =>
    exact ih _ (verified_submission_preserves_correctness verify soundness s c h)

/-- A real signature can authenticate an incorrect contribution. -/
def bad : Contribution := ⟨1, ⟨0, 0, [1, 2, 3, 4]⟩, true, true, true, false⟩
def empty : State := ⟨bad.binding, []⟩

theorem canonical_bad_partial_is_admitted : bad ∈ (submit empty bad).partials := by decide
theorem envelope_admission_does_not_imply_correctness : ¬ certified (submit empty bad) := by
  intro h
  have hf := h bad canonical_bad_partial_is_admitted
  contradiction
theorem signatures_alone_are_not_a_sound_verifier :
    ¬ (∀ c : Contribution, c.authenticated = true → c.correct = true) := by
  intro h
  have hf := h bad rfl
  contradiction

/-- Canonical ring residues remain canonical after any attacker-chosen offset. -/
theorem offset_is_canonical (q x offset : Nat) (hq : 0 < q) :
    (x + offset) % q < q := Nat.mod_lt _ hq

/-- The unverified combiner's phase is translation-equivariant in one partial.
This algebraic fact does not assert BFV decoding or any noise distribution. -/
def phase (q c₀ head rest : Nat) : Nat := (c₀ + head + rest) % q

theorem phase_offset (q c₀ head rest offset : Nat) :
    phase q c₀ ((head + offset) % q) rest =
      (phase q c₀ head rest + offset) % q := by
  unfold phase
  calc
    (c₀ + (head + offset) % q + rest) % q =
        ((c₀ + (head + offset) % q) % q + rest) % q :=
      (Nat.mod_add_mod _ q rest).symm
    _ = ((c₀ + (head + offset)) % q + rest) % q := by rw [Nat.add_mod_mod]
    _ = (c₀ + (head + offset) + rest) % q := Nat.mod_add_mod _ q rest
    _ = (c₀ + head + rest + offset) % q := by congr 1; omega
    _ = ((c₀ + head + rest) % q + offset) % q :=
      (Nat.mod_add_mod _ q offset).symm

/-- Exact finite counterexample at the toy q, with zero honest noise. -/
def q : Nat := 2^127 - 1
def delta : Nat := q / 2
def decode (x : Nat) : Nat := ((4 * x + q) / (2 * q)) % 2

theorem exact_zero_phase_bit_flip : decode 0 = 0 ∧ decode delta = 1 := by decide
theorem exact_one_phase_bit_flip : decode delta = 1 ∧ decode ((delta + delta) % q) = 0 := by decide

/-- Honest residual magnitudes must each be bounded before summing budgets. -/
theorem sum_of_bounded (xs : List Nat) (B : Nat) (h : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hs := ih (by intro a ha; exact h a (by simp [ha]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Total decoding headroom cannot certify the bound of each individual mask. -/
theorem decoding_budget_does_not_enforce_masks (B : Nat) (h : 0 < B) :
    ∃ r : Nat, B < r ∧ r ≤ 4 * B := by
  exact ⟨B + 1, by omega, by omega⟩

/-- Conditional arithmetic headroom, using the measured corpus's 34-bit bound.
This hypothesis is NOT proved for arbitrary or adversarial ciphertexts. -/
theorem honest_80_bit_headroom (E : Nat) (hE : E < 2^34) :
    E + 4 * 2^80 < delta / 2 := by
  have hnum : (2^34 : Nat) + 4 * 2^80 < delta / 2 := by decide
  omega

theorem measured_width_has_80_bit_margin (w : Nat) (h : w ≤ 34) : w + 40 ≤ 80 := by omega
theorem width_33_misses_72_bit_margin : ¬ (33 + 40 ≤ 72) := by decide

end TclMesh.Q45Adversarial
