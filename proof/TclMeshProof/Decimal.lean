import TclMeshProof.Core.Core
import TclMeshProof.Digits
import TclMesh.Decimal

/-!
# Refinement: Rust decimal comparison = specification

`tclmesh_kernel_core::decimal::compare`, translated by Aeneas, computes the
exact order `TclMesh.Decimal.Dec.cmp` on well-formed decimals: digits in
`0..=9`, no leading zero, length within `u32`.
-/

open Aeneas Aeneas.Std Result
open tclmesh_kernel_core
open TclMeshProof.Digits

set_option linter.tacticAnalysis.rwaSuggestion false

-- Casts are reasoned about by value, with their (provable) bounds as side goals.
attribute [-step] UScalar.cast.step_spec IScalar.cast.step_spec UScalar.hcast.step_spec
  IScalar.hcast.step_spec
attribute [local step] UScalar.cast_inBounds_spec IScalar.cast_inBounds_spec
  UScalar.hcast_inBounds_spec IScalar.hcast_inBounds_spec

namespace TclMeshProof.Decimal

/-- Digit values of a slice. -/
def nat (s : Slice Std.U8) : List Nat := s.val.map (·.val)

/-- The slice followed by `p` zeros: the digits of `value · 10^p`. -/
def pad (s : Slice Std.U8) (p : Nat) : List Nat := nat s ++ List.replicate p 0

def absO : Order → Ordering
  | .Lt => .lt
  | .Eq => .eq
  | .Gt => .gt

theorem length_nat (s : Slice Std.U8) : (nat s).length = s.length := by
  simp [nat, Slice.length]

theorem length_pad (s : Slice Std.U8) (p : Nat) : (pad s p).length = s.length + p := by
  simp [pad, length_nat]

theorem getElem_pad_lt (s : Slice Std.U8) (p i : Nat) (h : i < s.length) :
    (pad s p)[i]'(by rw [length_pad]; omega) = (s.val[i]'(by simpa [Slice.length] using h)).val := by
  unfold pad nat
  rw [List.getElem_append_left (by simpa [Slice.length] using h)]
  simp

theorem getElem_pad_ge (s : Slice Std.U8) (p i : Nat) (h₁ : s.length ≤ i) (h₂ : i < s.length + p) :
    (pad s p)[i]'(by rw [length_pad]; exact h₂) = 0 := by
  simp only [pad]
  rw [List.getElem_append_right (by simpa [length_nat] using h₁)]
  simp

theorem getElem_pad (s : Slice Std.U8) (p i : Nat) (h : i < s.length + p) :
    (pad s p)[i]'(by rw [length_pad]; exact h) = (nat s).getD i 0 := by
  by_cases hi : i < s.length
  · rw [getElem_pad_lt _ _ _ hi, List.getD_eq_getElem _ _ (by rw [length_nat]; exact hi)]
    simp [nat]
  · rw [getElem_pad_ge _ _ _ (by omega) h, List.getD_eq_default _ _ (by rw [length_nat]; omega)]

@[step]
theorem padded_spec (s : Slice Std.U8) (i : Std.U64) (hs : s.length < 2 ^ 32) :
    decimal.padded s i ⦃ d => d.val = (nat s).getD i.val 0 ⦄ := by
  unfold decimal.padded
  step*
  · rw [d_post, List.getD_eq_getElem _ _ (by rw [length_nat]; scalar_tac)]
    simp [nat, i3_post]
  · rw [List.getD_eq_default _ _ (by rw [length_nat]; scalar_tac)]
    rfl

/-- Unrolling the padded strings one digit at `i`. -/
theorem drop_pad (s : Slice Std.U8) (p i : Nat) (h : i < s.length + p) :
    (pad s p).drop i = (nat s).getD i 0 :: (pad s p).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [length_pad]; exact h), getElem_pad _ _ _ h]

theorem compare_magnitude_loop_spec (a b : Slice Std.U8) (pa pb : Nat) (la : Std.U64)
    (order : Order) (i : Std.U64)
    (ha : a.length < 2 ^ 32) (hb : b.length < 2 ^ 32)
    (hla : la.val = a.length + pa) (hlb : la.val = b.length + pb) (hi : i.val ≤ la.val) :
    decimal.compare_magnitude_loop a b la order i ⦃ r => absO r =
      match order with
      | .Eq => lex ((pad a pa).drop i.val) ((pad b pb).drop i.val)
      | o => absO o ⦄ := by
  unfold decimal.compare_magnitude_loop
  cases order
  · -- Lt: decided, scan on
    step*
  · -- Eq: compare the digits at i
    by_cases hlt : i < la
    · have hia : i.val < a.length + pa := by scalar_tac
      have hib : i.val < b.length + pb := by scalar_tac
      simp only [hlt, ite_true]
      step as ⟨da, hda⟩
      step as ⟨db, hdb⟩
      rw [drop_pad a pa i.val hia, drop_pad b pb i.val hib]
      by_cases h1 : da < db
      · simp only [h1, ite_true]
        step*
        simp_all [lex, absO]
      · by_cases h2 : da > db
        · simp only [h1, h2, ite_true, ite_false]
          step*
          simp_all [lex, absO]
        · simp only [h1, h2, ite_false]
          step*
          have heq : (nat a).getD i.val 0 = (nat b).getD i.val 0 := by
            rw [← hda, ← hdb]; scalar_tac
          rw [r_post, i1_post, heq]
          simp [lex]
    · -- past the end: both remaining strings are empty
      have hge : la.val ≤ i.val := by scalar_tac
      simp only [hlt, ite_false, WP.spec_ok]
      rw [List.drop_eq_nil_of_le (by rw [length_pad]; omega),
        List.drop_eq_nil_of_le (by rw [length_pad]; omega)]
      rfl
  · -- Gt: decided, scan on
    step*
termination_by la.val - i.val
decreasing_by all_goals scalar_tac

/-- A nonzero canonical digit string: digits `0..=9`, nonzero leading digit, `u32` length. -/
structure NZ (s : Slice Std.U8) : Prop where
  digits : IsDigits (nat s)
  lead : ∃ d ds, nat s = d :: ds ∧ d ≠ 0
  len : s.length < 2 ^ 32

theorem isDigits_pad {s : Slice Std.U8} (h : IsDigits (nat s)) (p : Nat) : IsDigits (pad s p) := by
  intro d hd
  simp only [pad, List.mem_append, List.mem_replicate] at hd
  rcases hd with hd | ⟨_, rfl⟩
  · exact h d hd
  · omega

theorem val_pad (s : Slice Std.U8) (p : Nat) : val (pad s p) = val (nat s) * 10 ^ p :=
  val_append_zeros _ _

theorem val_pad_lt {s : Slice Std.U8} (h : IsDigits (nat s)) (p : Nat) :
    val (pad s p) < 10 ^ (s.length + p) := by
  have := val_lt (isDigits_pad h p)
  rwa [length_pad] at this

theorem val_pad_ge {s : Slice Std.U8} (h : NZ s) (p : Nat) :
    10 ^ (s.length + p - 1) ≤ val (pad s p) := by
  obtain ⟨d, ds, hds, hd⟩ := h.lead
  have hlen : s.length = ds.length + 1 := by rw [← length_nat, hds]; rfl
  have : pad s p = d :: (ds ++ List.replicate p 0) := by simp [pad, hds]
  rw [this]
  have := val_ge (ds := ds ++ List.replicate p 0) hd
  simp only [List.length_append, List.length_replicate] at this
  rwa [hlen, show ds.length + 1 + p - 1 = ds.length + p by omega]

/-- Strings of different padded length compare by length. -/
theorem shorter_lt {a b : Slice Std.U8} (ha : NZ a) (hb : NZ b) {pa pb : Nat}
    (h : a.length + pa < b.length + pb) : val (pad a pa) < val (pad b pb) :=
  Nat.lt_of_lt_of_le (val_pad_lt ha.digits pa)
    (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (val_pad_ge hb pb))

@[step]
theorem compare_magnitude_spec (a b : Slice Std.U8) (pa pb : Std.U64) (ha : NZ a) (hb : NZ b)
    (hpa : pa.val < 2 ^ 40) (hpb : pb.val < 2 ^ 40) :
    decimal.compare_magnitude a pa b pb ⦃ r =>
      absO r = compare (val (nat a) * 10 ^ pa.val) (val (nat b) * 10 ^ pb.val) ⦄ := by
  have hla := ha.len
  have hlb := hb.len
  unfold decimal.compare_magnitude
  step*
  · rw [← val_pad, ← val_pad, Nat.compare_eq_lt.mpr (shorter_lt ha hb (by scalar_tac))]; rfl
  · rw [← val_pad, ← val_pad, Nat.compare_eq_gt.mpr (shorter_lt hb ha (by scalar_tac))]; rfl
  · step with compare_magnitude_loop_spec a b pa.val pb.val
    rw [r_post, List.drop_zero, List.drop_zero, ← val_pad, ← val_pad]
    exact lex_eq_compare (isDigits_pad ha.digits _) (isDigits_pad hb.digits _)
      (by rw [length_pad, length_pad]; scalar_tac)

/-! ## Top-level comparison -/

def digitsOf (d : decimal.Dec) : List Nat := d.digits.val.map (·.val)

/-- The specification's view of a kernel decimal: `±val(digits) · 10^(exp - frac_len)`. -/
def absDec (d : decimal.Dec) : TclMesh.Decimal.Dec :=
  ⟨d.negative, val (digitsOf d), d.exp.val - d.frac_len.val⟩

/-- Well-formed decimals, as `parse` produces them. -/
structure WF (d : decimal.Dec) : Prop where
  digits : IsDigits (digitsOf d)
  lead : ∀ x xs, digitsOf d = x :: xs → x ≠ 0
  len : d.digits.length < 2 ^ 32
  exp : -1000 ≤ d.exp.val ∧ d.exp.val ≤ 1000
  frac : d.frac_len.val < 2 ^ 32

theorem nat_deref (d : decimal.Dec) : nat (alloc.vec.Vec.deref d.digits) = digitsOf d := by
  simp [nat, digitsOf, alloc.vec.Vec.deref]

theorem length_deref (d : decimal.Dec) :
    (alloc.vec.Vec.deref d.digits).length = d.digits.length := by
  simp [alloc.vec.Vec.deref, Slice.length]

theorem WF.nz {d : decimal.Dec} (h : WF d) (hne : d.digits.length ≠ 0) :
    NZ (alloc.vec.Vec.deref d.digits) := by
  refine ⟨by rw [nat_deref]; exact h.digits, ?_, by rw [length_deref]; exact h.len⟩
  rw [nat_deref]
  cases hds : digitsOf d with
  | nil => simp [digitsOf] at hds; simp [hds] at hne
  | cons x xs => exact ⟨x, xs, rfl, h.lead x xs hds⟩

theorem WF.val_pos {d : decimal.Dec} (h : WF d) (hne : d.digits.length ≠ 0) :
    0 < val (digitsOf d) := by
  obtain ⟨x, xs, hx, hx0⟩ := (h.nz hne).lead
  rw [nat_deref] at hx
  rw [hx]
  exact Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) (val_ge hx0)

theorem WF.val_zero {d : decimal.Dec} (hz : d.digits.length = 0) : val (digitsOf d) = 0 := by
  have : d.digits.val = [] := List.eq_nil_of_length_eq_zero hz
  simp [digitsOf, this, val]

theorem len_eq_zero (v : alloc.vec.Vec Std.U8) : (v.len = 0#usize) ↔ v.length = 0 := by
  constructor
  · intro h; have := congrArg UScalar.val h; simpa [alloc.vec.Vec.len_val] using this
  · intro h; apply UScalar.eq_of_val_eq; simp [h]

/-! Specification side: the scaled values. -/

open TclMesh.Decimal in
theorem scaled_of_zero (x : Dec) (hx : x.mant = 0) (E : Int) : x.scaled E = 0 := by
  simp [Dec.scaled, hx]

open TclMesh.Decimal in
theorem scaled_of_pos (x : Dec) (hx : x.neg = false) (E : Int) :
    x.scaled E = ((x.mant * 10 ^ (x.exp - E).toNat : Nat) : Int) := by
  simp [Dec.scaled, hx]

open TclMesh.Decimal in
theorem scaled_of_neg (x : Dec) (hx : x.neg = true) (E : Int) :
    x.scaled E = -((x.mant * 10 ^ (x.exp - E).toNat : Nat) : Int) := by
  simp [Dec.scaled, hx]

theorem compare_cast (m n : Nat) : compare (m : Int) (n : Int) = compare m n := by
  rcases Nat.lt_trichotomy m n with h | rfl | h
  · rw [Nat.compare_eq_lt.mpr h, Int.compare_eq_lt.mpr (by omega)]
  · simp
  · rw [Nat.compare_eq_gt.mpr h, Int.compare_eq_gt.mpr (by omega)]

theorem compare_neg_cast (m n : Nat) : compare (-(m : Int)) (-(n : Int)) = compare n m := by
  rcases Nat.lt_trichotomy m n with h | rfl | h
  · rw [Nat.compare_eq_gt.mpr h, Int.compare_eq_gt.mpr (by omega)]
  · simp
  · rw [Nat.compare_eq_lt.mpr h, Int.compare_eq_lt.mpr (by omega)]

theorem pos_mul_pow {m : Nat} (hm : 0 < m) (k : Nat) : 0 < m * 10 ^ k :=
  Nat.mul_pos hm (Nat.pow_pos (by decide))

/-- Exponent shift of `x` to the common exponent with `y`. -/
def shift (x y : decimal.Dec) : Nat :=
  ((absDec x).exp - min (absDec x).exp (absDec y).exp).toNat

@[step]
theorem magnitude_spec (a b : decimal.Dec) (ha : WF a) (hb : WF b)
    (hza : a.digits.length ≠ 0) (hzb : b.digits.length ≠ 0) :
    decimal.magnitude a b ⦃ r =>
      absO r = compare (val (digitsOf a) * 10 ^ shift a b) (val (digitsOf b) * 10 ^ shift b a) ⦄ := by
  have hea := ha.exp
  have heb := hb.exp
  have hfa := ha.frac
  have hfb := hb.frac
  have hna := ha.nz hza
  have hnb := hb.nz hzb
  unfold decimal.magnitude
  step*
  have hsa : ∀ e : Int, e = min (a.exp.val - (a.frac_len.val : Int)) (b.exp.val - (b.frac_len.val : Int)) →
      shift a b = (a.exp.val - (a.frac_len.val : Int) - e).toNat := by
    intro e he; simp [shift, absDec, he]
  have hsb : ∀ e : Int, e = min (a.exp.val - (a.frac_len.val : Int)) (b.exp.val - (b.frac_len.val : Int)) →
      shift b a = (b.exp.val - (b.frac_len.val : Int) - e).toNat := by
    intro e he; simp [shift, absDec, he, Int.min_comm]
  split
  · step*
    rw [r_post, nat_deref, nat_deref, hsa ea.val (by scalar_tac), hsb ea.val (by scalar_tac)]
    fcongr 3
    · scalar_tac
    · scalar_tac
  · step*
    rw [r_post, nat_deref, nat_deref, hsa eb.val (by scalar_tac), hsb eb.val (by scalar_tac)]
    fcongr 3
    · scalar_tac
    · scalar_tac

theorem mant_zero {d : decimal.Dec} (h : d.digits.len = 0#usize) : (absDec d).mant = 0 :=
  WF.val_zero ((len_eq_zero _).mp h)

theorem scaled_pos {d : decimal.Dec} (hw : WF d) (h : ¬d.digits.len = 0#usize) (E : Int) :
    0 < (absDec d).mant * 10 ^ ((absDec d).exp - E).toNat :=
  pos_mul_pow (hw.val_pos (by rwa [len_eq_zero] at h)) _

@[step]
theorem reverse_spec (o : Order) : decimal.reverse o ⦃ r => absO r = (absO o).swap ⦄ := by
  cases o <;> simp [decimal.reverse, absO]

theorem compare_swap_nat (m n : Nat) : (compare m n).swap = compare n m := by
  rcases Nat.lt_trichotomy m n with h | rfl | h
  · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_gt.mpr h]; rfl
  · simp
  · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_lt.mpr h]; rfl

theorem shift_eq (a b : decimal.Dec) :
    shift b a = ((absDec b).exp - min (absDec a).exp (absDec b).exp).toNat := by
  simp [shift, Int.min_comm]

/-- **Refinement.** Rust `compare` computes the exact order of the specification. -/
@[step]
theorem compare_spec (a b : decimal.Dec) (ha : WF a) (hb : WF b) :
    decimal.compare a b ⦃ r => absO r = (absDec a).cmp (absDec b) ⦄ := by
  unfold decimal.compare TclMesh.Decimal.Dec.cmp
  step*
  · -- zero = zero
    rename_i hza hzb
    rw [scaled_of_zero _ (mant_zero hza), scaled_of_zero _ (mant_zero hzb)]; rfl
  · -- zero > negative
    rename_i hza hzb hnb
    have := scaled_pos hb hzb (min (absDec a).exp (absDec b).exp)
    rw [scaled_of_zero _ (mant_zero hza), scaled_of_neg (absDec b) hnb,
      Int.compare_eq_gt.mpr (by omega)]; rfl
  · -- zero < positive
    rename_i hza hzb hnb
    have := scaled_pos hb hzb (min (absDec a).exp (absDec b).exp)
    rw [scaled_of_zero _ (mant_zero hza),
      scaled_of_pos (absDec b) (show b.negative = false by simpa using hnb),
      Int.compare_eq_lt.mpr (by omega)]; rfl
  · -- negative < zero
    rename_i hza hzb hna
    have := scaled_pos ha hza (min (absDec a).exp (absDec b).exp)
    rw [scaled_of_neg (absDec a) hna, scaled_of_zero _ (mant_zero hzb),
      Int.compare_eq_lt.mpr (by omega)]; rfl
  · -- positive > zero
    rename_i hza hzb hna
    have := scaled_pos ha hza (min (absDec a).exp (absDec b).exp)
    rw [scaled_of_pos (absDec a) (show a.negative = false by simpa using hna),
      scaled_of_zero _ (mant_zero hzb), Int.compare_eq_gt.mpr (by omega)]; rfl
  · -- negative < positive
    rename_i hza hzb hne hna
    have hnb : b.negative = false := by
      cases h : b.negative
      · rfl
      · rw [hna, h] at hne; exact absurd hne (by decide)
    have := scaled_pos ha hza (min (absDec a).exp (absDec b).exp)
    have := scaled_pos hb hzb (min (absDec a).exp (absDec b).exp)
    rw [scaled_of_neg (absDec a) hna, scaled_of_pos (absDec b) hnb,
      Int.compare_eq_lt.mpr (by omega)]; rfl
  · -- positive > negative
    rename_i hza hzb hne hna
    have hna' : a.negative = false := by simpa using hna
    have hnb : b.negative = true := by
      cases h : b.negative
      · rw [hna', h] at hne; exact absurd hne (by decide)
      · rfl
    have := scaled_pos ha hza (min (absDec a).exp (absDec b).exp)
    have := scaled_pos hb hzb (min (absDec a).exp (absDec b).exp)
    rw [scaled_of_pos (absDec a) hna', scaled_of_neg (absDec b) hnb,
      Int.compare_eq_gt.mpr (by omega)]; rfl
  · -- both negative: reversed magnitude
    have hna : a.negative = true := ‹_›
    have hnb : b.negative = true := by
      have := ‹¬(a.negative != b.negative) = true›
      cases h : b.negative
      · rw [hna, h] at this; exact absurd (by decide) this
      · rfl
    rw [r_post, o_post, scaled_of_neg (absDec a) hna, scaled_of_neg (absDec b) hnb,
      compare_neg_cast, compare_swap_nat, shift_eq]
    rfl
  · -- both positive: magnitude
    have hna : a.negative = false := by simpa using ‹¬a.negative = true›
    have hnb : b.negative = false := by
      have := ‹¬(a.negative != b.negative) = true›
      cases h : b.negative
      · rfl
      · rw [hna, h] at this; exact absurd (by decide) this
    rw [r_post, scaled_of_pos (absDec a) hna, scaled_of_pos (absDec b) hnb, compare_cast,
      shift_eq a b]
    rfl

end TclMeshProof.Decimal
