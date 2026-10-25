import TclMeshProof.Parse
import TclMesh.Predicate

/-!
# Refinement: Rust predicate decisions = specification

`tclmesh_kernel_core::predicate::eval`, translated by Aeneas, decides a
resolved predicate exactly as `TclMesh.Kernel.Pred.eval` does, under the
abstraction of byte vectors as byte lists and of fault indices as the
caller's faults.
-/

open Aeneas Aeneas.Std Result
open tclmesh_kernel_core
open TclMeshProof.Parse
open TclMesh.Kernel (Bytes isSpace braced listElems parseList plainElement isInfix)

set_option linter.tacticAnalysis.rwaSuggestion false

attribute [-step] UScalar.cast.step_spec IScalar.cast.step_spec UScalar.hcast.step_spec
  IScalar.hcast.step_spec

namespace TclMeshProof.Predicate

theorem byte_inj {a b : Std.U8} : byte a = byte b ↔ a = b := by
  rw [byte_eq_iff, toNat_byte]
  exact ⟨UScalar.eq_of_val_eq, fun h => by rw [h]⟩

theorem getElem_bytes (s : Slice Std.U8) (i : Nat) (h : i < s.length) :
    (bytes s)[i]'(by rw [length_bytes]; exact h) =
      byte (s.val[i]'(by simpa [Slice.length] using h)) := by
  simp [bytes]

/-! ## Byte equality -/

@[step]
theorem range_eq_loop_spec (a b : Slice Std.U8) (start i : Std.Usize) (same : Bool)
    (hb : start.val + b.length ≤ a.length) (hi : i.val ≤ b.length) :
    predicate.range_eq_loop a start b same i ⦃ r =>
      r = (same && decide (((bytes a).drop (start.val + i.val)).take (b.length - i.val) =
        (bytes b).drop i.val)) ⦄ := by
  unfold predicate.range_eq_loop
  step*
  · have hlt : i.val < b.length := by scalar_tac
    have hlta : start.val + i.val < a.length := by omega
    rw [r_post, i5_post, eq_lit, drop_bytes a _ hlta, drop_bytes b _ hlt,
      show b.length - i.val = (b.length - (i.val + 1)) + 1 by omega, List.take_succ_cons]
    simp only [List.cons.injEq, Bool.decide_and, i3_post, i4_post, i2_post, Nat.add_assoc,
      Bool.and_assoc]
  · have : i.val = b.length := by scalar_tac
    simp [this, length_bytes]
termination_by b.length - i.val
decreasing_by all_goals scalar_tac

@[step]
theorem range_eq_spec (a b : Slice Std.U8) (start stop : Std.Usize) (h1 : start.val ≤ stop.val)
    (h2 : stop.val ≤ a.length) :
    predicate.range_eq a start stop b ⦃ r => r = decide (range a start.val stop.val = bytes b) ⦄ := by
  unfold predicate.range_eq
  step*
  · -- lengths differ
    have hl : (range a start.val stop.val).length ≠ (bytes b).length := by
      rw [length_range _ _ _ h2, length_bytes]; scalar_tac
    rw [eq_comm, decide_eq_false_iff_not]; exact fun h => hl (by rw [h])
  · -- same length: the loop compares them
    have hl : stop.val - start.val = b.length := by scalar_tac
    rw [r_post]
    simp only [range, List.drop_take, Nat.add_zero, Bool.true_and, Nat.sub_zero, List.drop_zero, hl]

@[step]
theorem bytes_eq_spec (a b : Slice Std.U8) :
    predicate.bytes_eq a b ⦃ r => r = decide (bytes a = bytes b) ⦄ := by
  unfold predicate.bytes_eq
  step*
  rw [r_post]
  simp [range, List.take_of_length_le, length_bytes, Slice.length]

/-! ## Containment -/

theorem isInfix_long {n l : Bytes} (hn : n ≠ []) (hl : l.length < n.length) : isInfix n l = false := by
  induction l with
  | nil => cases n <;> simp_all [isInfix]
  | cons x xs ih =>
    unfold isInfix
    simp only [Bool.or_eq_false_iff]
    simp only [List.length_cons] at hl
    refine ⟨?_, ih (by omega)⟩
    rw [Bool.eq_false_iff]; intro h
    have := (List.isPrefixOf_iff_prefix.mp h).length_le
    simp only [List.length_cons] at this; omega

theorem isInfix_nil_left (l : Bytes) : isInfix [] l = true := by
  cases l <;> simp [isInfix]

theorem isPrefixOf_iff_take (n l : Bytes) : n.isPrefixOf l = decide (l.take n.length = n) := by
  rw [Bool.eq_iff_iff, List.isPrefixOf_iff_prefix, decide_eq_true_eq, List.prefix_iff_eq_take]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

@[step]
theorem is_infix_loop_spec (needle hay : Slice Std.U8) (found : Bool) (i : Std.Usize)
    (hn : bytes needle ≠ []) :
    predicate.is_infix_loop needle hay found i ⦃ r =>
      r = (found || isInfix (bytes needle) ((bytes hay).drop i.val)) ⦄ := by
  have hpos : 0 < needle.length := by rw [← length_bytes]; exact List.length_pos_of_ne_nil hn
  unfold predicate.is_infix_loop
  step*
  · -- a window fits at `i`
    have hlt : i.val < hay.length := by scalar_tac
    rw [r_post, i7_post, b_post, drop_bytes hay _ hlt]
    conv_rhs => rw [isInfix]
    rw [← drop_bytes hay _ hlt, isPrefixOf_iff_take]
    simp only [range, List.drop_take, length_bytes, i6_post, Nat.add_sub_cancel_left, Bool.or_assoc,
      Slice.len_val]
  · -- the rest is shorter than the needle
    rw [isInfix_long hn (by rw [List.length_drop, length_bytes, length_bytes]; scalar_tac)]
    simp
  · -- at the end
    rw [isInfix_long hn (by rw [List.length_drop, length_bytes, length_bytes]; scalar_tac)]
    simp
termination_by hay.length - i.val
decreasing_by all_goals scalar_tac

@[step]
theorem is_infix_spec (needle hay : Slice Std.U8) :
    predicate.is_infix needle hay ⦃ r => r = isInfix (bytes needle) (bytes hay) ⦄ := by
  unfold predicate.is_infix
  step*
  · have : bytes needle = [] := by
      rw [← List.length_eq_zero_iff, length_bytes]; scalar_tac
    rw [this, isInfix_nil_left]
  · intro h; have := congrArg List.length h; rw [length_bytes] at this; simp at this; scalar_tac
  · simp [r_post]

/-! ## Plain elements and quotes -/

@[step]
theorem is_quote_spec (b : Std.U8) :
    predicate.is_quote b ⦃ r => r = (byte b = 92 || byte b = 34) ⦄ := by
  unfold predicate.is_quote
  split
  · rename_i h; subst h; simp; decide
  · rename_i h
    have hne : byte b ≠ 92 := byte_ne b 92#u8 h
    rw [eq_lit]; simp [hne]; rfl

@[step]
theorem has_quote_loop_spec (b : Slice Std.U8) (found : Bool) (i : Std.Usize) :
    predicate.has_quote_loop b found i ⦃ r =>
      r = (found || ((bytes b).drop i.val).any (fun x => x = 92 || x = 34)) ⦄ := by
  unfold predicate.has_quote_loop
  step*
  · have hlt : i.val < b.length := by scalar_tac
    rw [r_post, i3_post, drop_bytes b _ hlt, List.any_cons, b1_post, ← i2_post]
    simp [Bool.or_assoc]
  · rw [List.drop_eq_nil_of_le (by rw [length_bytes]; scalar_tac)]
    simp
termination_by b.length - i.val
decreasing_by all_goals scalar_tac

/-- One step of `plainElement`. -/
def pstep (d : Option Nat) (b : UInt8) : Option Nat := d.bind fun d =>
  if b = 92 || b = 34 then none
  else if b = 123 then some (d + 1)
  else if b = 125 then (if d = 0 then none else some (d - 1))
  else some d

theorem plainElement_foldl (bs : Bytes) : plainElement bs = decide (bs.foldl pstep (some 0) = some 0) := rfl

theorem foldl_pstep_none (bs : Bytes) : bs.foldl pstep none = none := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [pstep] using ih

/-- The loop's state as the specification's: `none` once not plain. -/
def pstate (ok : Bool) (depth : Std.Usize) : Option Nat := if ok then some depth.val else none

@[step]
theorem plain_step_spec (ok : Bool) (depth : Std.Usize) (b : Std.U8) (cap : Std.Usize)
    (hd : ok → depth.val < cap.val) :
    predicate.plain_step ok depth b cap ⦃ r =>
      pstate r.1 r.2 = pstep (pstate ok depth) (byte b) ∧ (r.1 → r.2.val ≤ depth.val + 1) ⦄ := by
  have h123 : byte 123#u8 = 123 := by decide
  have h125 : byte 125#u8 = 125 := by decide
  unfold predicate.plain_step
  step*
  · -- a quote
    have hq : byte b = 92 ∨ byte b = 34 := by simpa [b1_post] using ‹b1 = true›
    rcases hq with h | h <;> cases ok <;> simp [pstate, pstep, h]
  · -- '{'
    cases ok <;> simp [pstate, pstep, h123, i_post]
  · -- '{' at the cap: unreachable while plain
    cases ok
    · simp [pstate, pstep]
    · exact absurd (hd rfl) (by scalar_tac)
  · -- '}' at depth zero
    cases ok <;> simp [pstate, pstep, h125]
  · -- '}'
    have : depth.val ≠ 0 := by scalar_tac
    cases ok <;> simp [pstate, pstep, h125, i_post, this]
    omega
  · -- another byte
    have hq : ¬ (byte b = 92 ∨ byte b = 34) := by simpa [b1_post] using ‹¬b1 = true›
    have h1 := byte_ne b 123#u8 ‹_›
    have h2 := byte_ne b 125#u8 ‹_›
    rw [h123] at h1; rw [h125] at h2
    simp only [not_or] at hq
    cases ok <;> simp [pstate, pstep, hq.1, hq.2, h1, h2]

@[step]
theorem plain_element_loop_spec (b : Slice Std.U8) (ok : Bool) (depth i : Std.Usize)
    (hi : i.val ≤ b.length) (hd : ok → depth.val ≤ i.val) :
    predicate.plain_element_loop b ok depth i ⦃ r =>
      pstate r.1 r.2 = ((bytes b).drop i.val).foldl pstep (pstate ok depth) ⦄ := by
  unfold predicate.plain_element_loop
  step*
  · intro h
    have hok : ok = true := by
      cases ok
      · simp [pstate, pstep, h] at o_post
      · rfl
    have := hd hok; have := o_post1 h; scalar_tac
  · have hlt : i.val < b.length := by scalar_tac
    rw [r_post, drop_bytes b _ hlt, List.foldl_cons, i4_post, ← i2_post, ← o_post]
  · rw [List.drop_eq_nil_of_le (by rw [length_bytes]; scalar_tac)]; rfl
termination_by b.length - i.val
decreasing_by all_goals scalar_tac

@[step]
theorem plain_element_spec (b : Slice Std.U8) :
    predicate.plain_element b ⦃ r => r = plainElement (bytes b) ⦄ := by
  unfold predicate.plain_element
  step*
  all_goals rw [plainElement_foldl, List.drop_zero] at *
  · rw [show pstate true 0#usize = some 0 from rfl] at ok1_post
    rw [← ok1_post]; simp [pstate, ‹ok1 = true›]
    exact ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq h⟩
  · rw [show pstate true 0#usize = some 0 from rfl] at ok1_post
    rw [← ok1_post]; simp [pstate, ‹¬ok1 = true›]

/-! ## Canonical lists -/

theorem isSpace_byte (b : Std.U8) : isSpace (byte b) =
    (decide (b = 32#u8) || decide (b = 9#u8) || decide (b = 10#u8) || decide (b = 11#u8) ||
      decide (b = 12#u8) || decide (b = 13#u8)) := by
  simp only [isSpace, eq_lit]; rfl

@[step]
theorem is_space_spec (b : Std.U8) : predicate.is_space b ⦃ r => r = isSpace (byte b) ⦄ := by
  rw [isSpace_byte]
  unfold predicate.is_space
  repeat' split
  all_goals simp_all

end TclMeshProof.Predicate
