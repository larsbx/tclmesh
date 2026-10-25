import TclMeshProof.Decimal

/-!
# Refinement: Rust decimal parsing = specification

`tclmesh_kernel_core::decimal::parse`, translated by Aeneas, returns exactly
`TclMesh.Decimal.parseBytes` of the input bytes (under `absDec`), and every
decimal it returns is well formed (`WF`), so `compare_spec` applies to it.
-/

open Aeneas Aeneas.Std Result
open tclmesh_kernel_core
open TclMeshProof.Digits TclMeshProof.Decimal
open TclMesh.Decimal (isDigit takeDigits digitsVal boundedExp parseBytes signPart intOk fracPart
  expSign expPart)

set_option linter.tacticAnalysis.rwaSuggestion false

-- Casts by value (see `Casts`): drop the default bit-vector cast specifications.
attribute [-step] UScalar.cast.step_spec IScalar.cast.step_spec UScalar.hcast.step_spec
  IScalar.hcast.step_spec

namespace TclMeshProof.Parse

/-- The specification's byte for a kernel `u8`. -/
def byte (b : Std.U8) : UInt8 := b.val.toUInt8

def bytes (s : Slice Std.U8) : List UInt8 := s.val.map byte

theorem toNat_byte (b : Std.U8) : (byte b).toNat = b.val := by
  have : b.val < 256 := by scalar_tac
  simp [byte, Nat.toUInt8, Nat.mod_eq_of_lt this]

theorem length_bytes (s : Slice Std.U8) : (bytes s).length = s.length := by
  simp [bytes, Slice.length]

theorem drop_bytes (s : Slice Std.U8) (i : Nat) (h : i < s.length) :
    (bytes s).drop i = byte (s.val[i]'(by simpa [Slice.length] using h)) :: (bytes s).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by rw [length_bytes]; exact h)]
  simp [bytes]

theorem isDigit_byte (b : Std.U8) : isDigit (byte b) = (48 ≤ b.val && b.val ≤ 57) := by
  simp [isDigit, toNat_byte]

@[step]
theorem is_digit_spec (b : Std.U8) :
    decimal.is_digit b ⦃ r => r = isDigit (byte b) ⦄ := by
  unfold decimal.is_digit
  rw [isDigit_byte]
  step*

theorem takeDigits_cons (b : UInt8) (bs : List UInt8) :
    takeDigits (b :: bs) =
      if isDigit b then (b :: (takeDigits bs).1, (takeDigits bs).2) else ([], b :: bs) := by
  simp [takeDigits]

/-- `digits_end` is the end of the run that `takeDigits` splits off. -/
@[step]
theorem digits_end_loop_spec (s : Slice Std.U8) (i : Std.Usize) (hi : i.val ≤ s.length) :
    decimal.digits_end_loop s i ⦃ j =>
      j.val = i.val + (takeDigits ((bytes s).drop i.val)).1.length ∧ j.val ≤ s.length ⦄ := by
  unfold decimal.digits_end_loop
  step*
  · -- a digit: the run continues past `i`
    have hlt : i.val < s.length := by scalar_tac
    rw [drop_bytes s i.val hlt, takeDigits_cons, ← i2_post, ← b_post]
    simp only [‹b = true›, ite_true, List.length_cons]
    constructor
    · rw [j_post, i3_post]; omega
    · exact j_post1
  · -- not a digit: the run ends at `i`
    have hlt : i.val < s.length := by scalar_tac
    rw [drop_bytes s i.val hlt, takeDigits_cons, ← i2_post, ← b_post]
    simp [‹¬b = true›]; scalar_tac
  · -- past the end
    have hge : s.length ≤ i.val := by scalar_tac
    rw [List.drop_eq_nil_of_le (by rw [length_bytes]; exact hge)]
    simp [takeDigits]; scalar_tac
termination_by s.length - i.val
decreasing_by all_goals scalar_tac

/-! ## Pure facts about `takeDigits` -/

theorem takeDigits_split (l : List UInt8) :
    takeDigits l = (l.take (takeDigits l).1.length, l.drop (takeDigits l).1.length) := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
    rw [takeDigits_cons]
    split
    · conv_lhs => rw [ih]
      simp
    · simp

theorem takeDigits_digits (l : List UInt8) : ∀ b ∈ (takeDigits l).1, isDigit b = true := by
  induction l with
  | nil => simp [takeDigits]
  | cons b bs ih =>
    rw [takeDigits_cons]
    split
    · rename_i h; intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h
      · exact ih x hx
    · simp

/-- `digits_end` in split form: the digit run is `bytes[i, j)` and the rest starts at `j`. -/
theorem digits_split (s : Slice Std.U8) (i j : Nat)
    (hj : j = i + (takeDigits ((bytes s).drop i)).1.length) :
    takeDigits ((bytes s).drop i) = (((bytes s).take j).drop i, (bytes s).drop j) := by
  have h := takeDigits_split ((bytes s).drop i)
  rw [h]
  subst hj
  simp only [List.drop_take, List.drop_drop, Nat.add_sub_cancel_left]

/-! ## Sign, integer part, fraction -/

theorem byte_eq_iff (b : Std.U8) (n : UInt8) : byte b = n ↔ b.val = n.toNat := by
  rw [← toNat_byte, UInt8.toNat_inj]

theorem signPart_cons (b : UInt8) (rest : List UInt8) :
    signPart (b :: rest) = if b = 45 then (true, rest) else (false, b :: rest) := by
  unfold signPart; split <;> simp_all

theorem fracPart_cons (b : UInt8) (rest : List UInt8) :
    fracPart (b :: rest) =
      if b = 46 then (if (takeDigits rest).1 = [] then none else some (takeDigits rest))
      else some ([], b :: rest) := by
  unfold fracPart; split <;> simp_all

theorem expSign_cons (b : UInt8) (rest : List UInt8) :
    expSign (b :: rest) = if b = 45 then (-1, rest) else if b = 43 then (1, rest) else (1, b :: rest) := by
  unfold expSign; split <;> simp_all

theorem bytes_head (s : Slice Std.U8) (h : 0 < s.length) :
    bytes s = byte (s.val[0]'(by simpa [Slice.length] using h)) :: (bytes s).drop 1 := by
  have := drop_bytes s 0 h
  simpa using this

@[step]
theorem sign_end_spec (s : Slice Std.U8) :
    decimal.sign_end s ⦃ r =>
      (r.val = 0 ∨ r.val = 1) ∧ r.val ≤ s.length ∧
      signPart (bytes s) = (decide (r.val = 1), (bytes s).drop r.val) ⦄ := by
  unfold decimal.sign_end
  step*
  · -- leading '-'
    have h0 : 0 < s.length := by scalar_tac
    rw [bytes_head s h0, signPart_cons, ite_eq_left (by rw [byte_eq_iff]; subst_vars; simp_all)]
    simp; scalar_tac
  · -- another byte
    have h0 : 0 < s.length := by scalar_tac
    have hne : byte (s.val[0]'(by simpa [Slice.length] using h0)) ≠ 45 := by
      rw [ne_eq, byte_eq_iff]; intro hv; subst_vars
      exact ‹¬_ = 45#u8› (UScalar.eq_of_val_eq (by simpa using hv))
    rw [bytes_head s h0, signPart_cons, ite_eq_right hne]
    simp
  · -- empty
    have : s.val = [] := by
      have : s.length = 0 := by scalar_tac
      simpa [Slice.length] using this
    simp [bytes, this, signPart]

/-- The bytes `[start, end)` of `s`. -/
def range (s : Slice Std.U8) (start stop : Nat) : List UInt8 := ((bytes s).take stop).drop start

theorem length_range (s : Slice Std.U8) (a b : Nat) (h : b ≤ s.length) :
    (range s a b).length = b - a := by
  simp [range, length_bytes, Nat.min_eq_left h]


theorem bne_lit (b : Std.U8) (n : Std.U8) :
    (b != n) = decide (byte b ≠ byte n) := by
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq, byte_eq_iff, toNat_byte]
  exact ⟨fun h hv => h (UScalar.eq_of_val_eq hv), fun h hb => h (by rw [hb])⟩

theorem range_head (s : Slice Std.U8) (a b : Nat) (hab : a < b) (hb : b ≤ s.length) :
    (range s a b).head? = some (byte (s.val[a]'(by simp [Slice.length] at hb; omega))) := by
  simp only [range]
  rw [List.head?_drop, List.getElem?_take_of_lt hab]
  simp only [bytes, List.getElem?_map]
  rw [List.getElem?_eq_getElem]; rfl

@[step]
theorem integer_ok_spec (s : Slice Std.U8) (start stop : Std.Usize) (h1 : start.val ≤ stop.val)
    (h2 : stop.val ≤ s.length) :
    decimal.integer_ok s start stop ⦃ r => r = intOk (range s start.val stop.val) ⦄ := by
  have hlen := length_range s start.val stop.val h2
  unfold decimal.integer_ok intOk
  step*
  · -- two or more digits: the first must not be '0'
    have hlt : start.val < stop.val := by scalar_tac
    have hnn : range s start.val stop.val ≠ [] := by
      intro h; have := congrArg List.length h; rw [hlen, List.length_nil] at this; omega
    have hne1 : stop.val - start.val ≠ 1 := by
      intro h; apply ‹¬i = 1#usize›; apply UScalar.eq_of_val_eq; simp [i_post, h]
    rw [range_head s _ _ hlt h2, ← i1_post, bne_lit]
    simp only [ne_eq, hnn, not_false_eq_true, decide_true, Bool.true_and, hlen, hne1,
      decide_false, Bool.false_or, Option.some.injEq]
    rfl
  · -- empty
    have : range s start.val stop.val = [] := by
      have : stop.val = start.val := by simp at *; scalar_tac
      rw [← List.length_eq_zero_iff, hlen]; omega
    simp [this]

theorem range_empty (s : Slice Std.U8) (a b : Nat) (h : b ≤ a) : range s a b = [] := by
  simp only [range]
  apply List.drop_eq_nil_of_le
  simp; omega

theorem fracPart_nil : fracPart [] = some ([], []) := rfl

@[step]
theorem fraction_end_spec (s : Slice Std.U8) (i : Std.Usize) (hi : i.val ≤ s.length) :
    decimal.fraction_end s i ⦃ o =>
      fracPart ((bytes s).drop i.val) =
        o.map (fun e => (range s (i.val + 1) e.val, (bytes s).drop e.val)) ∧
      ∀ e, o = some e → i.val ≤ e.val ∧ e.val ≤ s.length ⦄ := by
  unfold decimal.fraction_end
  step*
  · -- '.' not followed by a digit
    have heq := congrArg UScalar.val ‹«end» = i3›
    have hj : «end».val = (i.val + 1) + (takeDigits ((bytes s).drop (i.val + 1))).1.length := by
      rw [end_post, i3_post]
    have hle : «end».val ≤ i.val + 1 := by omega
    have hlt : i.val < s.length := by omega
    clear end_post heq
    have hdot : byte (s.val[i.val]'(by simpa [Slice.length] using hlt)) = 46 := by
      rw [byte_eq_iff, ← i2_post, ‹i2 = 46#u8›]; rfl
    have he : ((bytes s).take «end».val).drop (i.val + 1) = [] := range_empty s _ _ hle
    rw [drop_bytes s i.val hlt, fracPart_cons, ite_eq_left hdot, digits_split s _ _ hj,
      ite_eq_left he]
    simp only [Option.map_none, true_and]
    intro e he; cases he
  · -- '.' followed by digits
    have hlt : i.val < s.length := by scalar_tac
    have hdot : byte (s.val[i.val]'(by simpa [Slice.length] using hlt)) = 46 := by
      rw [byte_eq_iff, ← i2_post, ‹i2 = 46#u8›]; rfl
    have hj : «end».val = (i.val + 1) + (takeDigits ((bytes s).drop (i.val + 1))).1.length := by
      rw [end_post, i3_post]
    have hne : range s (i.val + 1) «end».val ≠ [] := by
      intro h; have := congrArg List.length h
      rw [length_range _ _ _ end_post1, List.length_nil] at this
      apply ‹¬«end» = i3›; apply UScalar.eq_of_val_eq; scalar_tac
    have hne' : ((bytes s).take «end».val).drop (i.val + 1) ≠ [] := hne
    rw [drop_bytes s i.val hlt, fracPart_cons, ite_eq_left hdot, digits_split s _ _ hj, ite_eq_right hne']
    refine ⟨rfl, ?_⟩
    intro e he; cases he; scalar_tac
  · -- another byte: no fraction
    have hlt : i.val < s.length := by scalar_tac
    have hnd : byte (s.val[i.val]'(by simpa [Slice.length] using hlt)) ≠ 46 := by
      rw [ne_eq, byte_eq_iff, ← i2_post]; intro hv
      exact ‹¬i2 = 46#u8› (UScalar.eq_of_val_eq (by simpa using hv))
    simp only [Option.map_some]
    rw [range_empty s _ _ (by omega)]
    rw [drop_bytes s i.val hlt, fracPart_cons, ite_eq_right hnd, ← drop_bytes s i.val hlt]
    simp only [true_and]
    intro e he; cases he; exact ⟨le_refl _, hi⟩
  · -- at the end: no fraction
    have hge : s.length ≤ i.val := by scalar_tac
    simp only [Option.map_some]
    rw [range_empty s _ _ (by omega), List.drop_eq_nil_of_le (by rw [length_bytes]; exact hge),
      fracPart_nil]
    simp only [true_and]
    intro e he; cases he; exact ⟨le_refl _, hi⟩

end TclMeshProof.Parse
