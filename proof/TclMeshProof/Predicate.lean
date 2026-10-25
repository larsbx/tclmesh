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

@[step]
theorem skip_space_loop_spec (b : Slice Std.U8) (i : Std.Usize) (hi : i.val ≤ b.length) :
    predicate.skip_space_loop b i ⦃ j =>
      (bytes b).drop j.val = ((bytes b).drop i.val).dropWhile isSpace ∧
      i.val ≤ j.val ∧ j.val ≤ b.length ⦄ := by
  unfold predicate.skip_space_loop
  step*
  · have hlt : i.val < b.length := by scalar_tac
    rw [drop_bytes b _ hlt, List.dropWhile_cons, ← i2_post, ← b1_post, ite_eq_left ‹_›, ← i3_post]
    exact ⟨j_post, by scalar_tac, j_post2⟩
  · have hlt : i.val < b.length := by scalar_tac
    rw [drop_bytes b _ hlt, List.dropWhile_cons, ← i2_post, ← b1_post, ite_eq_right ‹_›]
    exact ⟨rfl, le_refl _, hi⟩
  · rw [List.drop_eq_nil_of_le (by rw [length_bytes]; scalar_tac)]
    simp; scalar_tac
termination_by b.length - i.val
decreasing_by all_goals scalar_tac

@[step]
theorem word_end_loop_spec (b : Slice Std.U8) (i : Std.Usize) (hi : i.val ≤ b.length) :
    predicate.word_end_loop b i ⦃ j =>
      (bytes b).drop j.val = ((bytes b).drop i.val).dropWhile (fun x => !isSpace x) ∧
      range b i.val j.val = ((bytes b).drop i.val).takeWhile (fun x => !isSpace x) ∧
      i.val ≤ j.val ∧ j.val ≤ b.length ⦄ := by
  unfold predicate.word_end_loop
  step*
  · -- a space ends the word
    have hlt : i.val < b.length := by scalar_tac
    have hs : (!isSpace (byte (b.val[i.val]'(by simpa [Slice.length] using hlt)))) = false := by
      rw [← i2_post, ← b1_post, ‹b1 = true›]; rfl
    rw [drop_bytes b _ hlt, List.dropWhile_cons, List.takeWhile_cons, ite_eq_right (by simp [hs]),
      ite_eq_right (by simp [hs]), range_empty _ _ _ (le_refl _)]
    exact ⟨(drop_bytes b _ hlt).symm ▸ rfl, rfl, le_refl _, hi⟩
  · have hlt : i.val < b.length := by scalar_tac
    have hs : (!isSpace (byte (b.val[i.val]'(by simpa [Slice.length] using hlt)))) = true := by
      rw [← i2_post, ← b1_post]; simpa using ‹¬b1 = true›
    rw [drop_bytes b _ hlt, List.dropWhile_cons, List.takeWhile_cons, ite_eq_left hs, ite_eq_left hs,
      ← i3_post, range_cons b _ _ (by scalar_tac) j_post3, ← i3_post]
    exact ⟨j_post, by rw [j_post1], by scalar_tac, j_post3⟩
  · have : i.val = b.length := by scalar_tac
    rw [List.drop_eq_nil_of_le (by rw [length_bytes]; scalar_tac), range_empty _ _ _ (le_refl _)]
    simp [this]
termination_by b.length - i.val
decreasing_by all_goals scalar_tac

theorem braced_close_zero (rest acc : Bytes) : braced 0 (125 :: rest) acc = some (acc.reverse, rest) := by
  simp [braced]

theorem braced_close_succ (d : Nat) (rest acc : Bytes) :
    braced (d + 1) (125 :: rest) acc = braced d rest (125 :: acc) := by
  simp [braced]

theorem braced_open (d : Nat) (rest acc : Bytes) :
    braced d (123 :: rest) acc = braced (d + 1) rest (123 :: acc) := by
  cases d <;> simp [braced]

theorem braced_other (d : Nat) (c : UInt8) (rest acc : Bytes) (h1 : c ≠ 123) (h2 : c ≠ 125) :
    braced d (c :: rest) acc = braced d rest (c :: acc) := by
  cases d <;> simp [braced, h2]

theorem braced_nil (d : Nat) (acc : Bytes) : braced d [] acc = none := by
  cases d <;> simp [braced]

@[step]
theorem group_step_spec (depth : Std.Usize) (b : Std.U8) (cap : Std.Usize) (hd : 0 < depth.val)
    (hc : depth.val < cap.val) :
    predicate.group_step depth b cap ⦃ r =>
      r.val = if byte b = 123 then depth.val + 1 else if byte b = 125 then depth.val - 1
        else depth.val ⦄ := by
  have e1 : byte b = 123 ↔ b = 123#u8 := by rw [← show byte 123#u8 = 123 by decide]; exact byte_inj
  have e2 : byte b = 125 ↔ b = 125#u8 := by rw [← show byte 125#u8 = 125 by decide]; exact byte_inj
  simp only [e1, e2]
  unfold predicate.group_step
  step*

/-- Pushing the byte at `i` onto `braced`'s accumulator. -/
theorem braced_push (b : Slice Std.U8) (i j : Nat) (acc : Bytes) (dep : Nat) (hi : i < b.length)
    (X : Option (Bytes × Bytes))
    (H : X = if dep = 0 then
      some ((byte (b.val[i]'(by simpa [Slice.length] using hi)) :: acc).reverse ++ range b (i + 1) (j - 1),
        (bytes b).drop j) else none)
    (hj : dep = 0 → i + 1 < j ∧ j ≤ b.length) :
    X = if dep = 0 then some (acc.reverse ++ range b i (j - 1), (bytes b).drop j) else none := by
  rw [H]
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := hj h
    rw [range_cons b i (j - 1) (by omega) (by omega)]
    simp
  · rfl

/-- `group_end` scans what `braced` does: `depth` is one more than its nesting. -/
@[step]
theorem group_end_loop_spec (b : Slice Std.U8) (i depth : Std.Usize) (hc : depth.val ≤ i.val)
    (hi : i.val ≤ b.length) :
    predicate.group_end_loop b i depth ⦃ r =>
      (depth.val = 0 → r = (depth, i)) ∧
      (0 < depth.val → ∀ acc, braced (depth.val - 1) ((bytes b).drop i.val) acc =
          (if r.1.val = 0 then some (acc.reverse ++ range b i.val (r.2.val - 1), (bytes b).drop r.2.val)
           else none) ∧
        (r.1.val = 0 → i.val < r.2.val ∧ r.2.val ≤ b.length)) ∧
      i.val ≤ r.2.val ∧ r.2.val ≤ b.length ⦄ := by
  unfold predicate.group_end_loop
  step*
  · -- the depth stays within the bytes read
    rw [depth1_post]; split <;> (try split) <;> scalar_tac
  · have hd0 : 0 < depth.val := by scalar_tac
    have hlt : i.val < b.length := by scalar_tac
    refine ⟨fun h => absurd h (by omega), fun _ acc => ?_, by scalar_tac, r_post3⟩
    rw [drop_bytes b _ hlt]
    rw [i4_post] at r_post1
    by_cases h1 : byte i2 = 123
    · -- '{' nests deeper
      simp only [h1, ite_true] at depth1_post
      rw [← i2_post, h1, braced_open, show depth.val - 1 + 1 = depth1.val - 1 by omega]
      obtain ⟨e, f⟩ := r_post1 (by omega) (123 :: acc)
      refine ⟨braced_push b i.val r.2.val acc r.1.val hlt _ (by rw [e, ← i2_post, h1]) ?_,
        fun h => by have := f h; omega⟩
      intro h; have := f h; omega
    · by_cases h2 : byte i2 = 125
      · simp [h2] at depth1_post
        by_cases hz : depth.val = 1
        · -- the matching '}'
          have hz1 : depth1.val = 0 := by omega
          have hr := r_post hz1
          rw [← i2_post, h2, hz, show 1 - 1 = 0 by rfl, braced_close_zero, hr]
          have hlt' : i.val < b.val.length := hlt
          simp [hz1, range_empty, i4_post, hlt']
        · -- an inner '}'
          rw [← i2_post, h2, show depth.val - 1 = (depth1.val - 1) + 1 by omega, braced_close_succ]
          obtain ⟨e, f⟩ := r_post1 (by omega) (125 :: acc)
          refine ⟨braced_push b i.val r.2.val acc r.1.val hlt _ (by rw [e, ← i2_post, h2]) ?_,
            fun h => by have := f h; omega⟩
          intro h; have := f h; omega
      · -- any other byte
        simp only [h1, h2, ite_false] at depth1_post
        rw [← i2_post, braced_other _ _ _ _ h1 h2, show depth.val - 1 = depth1.val - 1 by omega]
        obtain ⟨e, f⟩ := r_post1 (by omega) (byte i2 :: acc)
        refine ⟨braced_push b i.val r.2.val acc r.1.val hlt _ (by rw [e, ← i2_post]) ?_,
          fun h => by have := f h; omega⟩
        intro h; have := f h; omega
  · -- out of bytes before the group closed
    have hd0 : depth.val ≠ 0 := by scalar_tac
    rw [List.drop_eq_nil_of_le (by rw [length_bytes]; scalar_tac)]
    simp [braced_nil, hd0]; scalar_tac
termination_by b.length - i.val
decreasing_by all_goals scalar_tac

theorem dropWhile_idem (p : UInt8 → Bool) (l : Bytes) : (l.dropWhile p).dropWhile p = l.dropWhile p := by
  induction l with
  | nil => rfl
  | cons x xs ih => by_cases h : p x <;> simp [h, ih]

theorem listElems_dropWhile (fuel : Nat) (bs : Bytes) :
    listElems fuel (bs.dropWhile isSpace) = listElems fuel bs := by
  cases fuel with
  | zero => rfl
  | succ f => simp only [listElems, dropWhile_idem]

theorem listElems_nil (fuel : Nat) (h : 0 < fuel) : listElems fuel [] = some [] := by
  cases fuel with
  | zero => omega
  | succ f => rfl

/-- One element at a non-space byte, as `listElems` takes it. -/
theorem listElems_word (f : Nat) (c : UInt8) (tail : Bytes) (hc : isSpace c = false) (h123 : c ≠ 123) :
    listElems (f + 1) (c :: tail) =
      ((c :: tail).takeWhile (fun x => !isSpace x) :: ·) <$>
        listElems f ((c :: tail).dropWhile (fun x => !isSpace x)) := by
  conv_lhs => unfold listElems
  simp only [List.dropWhile_cons, hc]
  split <;> simp_all

theorem listElems_group (f : Nat) (tail : Bytes) :
    listElems (f + 1) (123 :: tail) =
      match braced 0 tail [] with
      | none => none
      | some (body, rest) => match rest with
        | x :: _ => if isSpace x then (body :: ·) <$> listElems f rest else none
        | [] => some [body] := by
  conv_lhs => unfold listElems
  simp only [List.dropWhile_cons, show isSpace 123 = false by decide]
  simp only [Bool.false_eq_true, ite_false]
  cases braced 0 tail [] with
  | none => rfl
  | some p => obtain ⟨body, rest⟩ := p; cases rest <;> simp [Option.bind]

@[step]
theorem list_item_spec (text needle : Slice Std.U8) (i : Std.Usize) (hi : i.val < text.length)
    (hns : isSpace (byte (text.val[i.val]'(by simpa [Slice.length] using hi))) = false) :
    predicate.list_item text needle i ⦃ r =>
      i.val < r.2.2.val ∧ r.2.2.val ≤ text.length ∧
      ∃ body, r.2.1 = decide (body = bytes needle) ∧ ∀ f, 0 < f →
        listElems (f + 1) ((bytes text).drop i.val) =
          if r.1 then (body :: ·) <$> listElems f ((bytes text).drop r.2.2.val) else none ⦄ := by
  have h123 : byte 123#u8 = 123 := by decide
  unfold predicate.list_item
  step*
  all_goals try (
    obtain ⟨hbr, hbz⟩ := depth_post1 (by decide) []
    rw [i2_post] at hbr hbz depth_post2
    simp only [Nat.sub_self, List.reverse_nil, List.nil_append] at hbr)
  · -- an unclosed group
    refine ⟨by scalar_tac, depth_post3, 0 :: bytes needle, by simp, fun f hf => ?_⟩
    have hd : depth.val ≠ 0 := by scalar_tac
    rw [drop_bytes text _ hi, ← i1_post, ‹i1 = 123#u8›, h123, listElems_group, hbr]
    simp [hd]
  · have := hbz (by scalar_tac); scalar_tac
  · -- a group ending the text
    have hd : depth.val = 0 := by scalar_tac
    obtain ⟨hlt, hle⟩ := hbz hd
    have hend : «end».val = text.length := by scalar_tac
    refine ⟨by scalar_tac, by scalar_tac, range text (i.val + 1) i3.val, by rw [hit_post, i2_post],
      fun f hf => ?_⟩
    have hdrop : (bytes text).drop «end».val = [] :=
      List.drop_eq_nil_of_le (by rw [length_bytes]; omega)
    have hdrop' : (bytes text).drop text.val.length = [] :=
      List.drop_eq_nil_of_le (by rw [length_bytes])
    rw [drop_bytes text _ hi, ← i1_post, ‹i1 = 123#u8›, h123, listElems_group, hbr]
    simp [hd, i3_post, hdrop, hdrop', listElems_nil f hf]
  · -- a group followed by more text
    have hd : depth.val = 0 := by scalar_tac
    obtain ⟨hlt, hle⟩ := hbz hd
    have hend : «end».val < text.length := by scalar_tac
    refine ⟨by scalar_tac, hle, range text (i.val + 1) i3.val, by rw [hit_post, i2_post],
      fun f hf => ?_⟩
    rw [drop_bytes text _ hi, ← i1_post, ‹i1 = 123#u8›, h123, listElems_group, hbr]
    simp only [hd, ite_true, i3_post]
    rw [drop_bytes text _ hend, b_post, ← i5_post]
  · -- a bare word
    have hne := byte_ne i1 123#u8 ‹_›; rw [h123, i1_post] at hne
    refine ⟨?_, end_post3, range text i.val «end».val, b_post, fun f hf => ?_⟩
    · have := end_post1
      rw [drop_bytes text _ hi, List.takeWhile_cons, ite_eq_left (by simp [hns])] at this
      have hl := congrArg List.length this
      rw [length_range _ _ _ end_post3] at hl; simp at hl; omega
    · simp only [ite_true]
      rw [end_post, end_post1, drop_bytes text _ hi, listElems_word f _ _ hns hne]

theorem contains_cons (x : Bytes) (xs : List Bytes) (n : Bytes) :
    (x :: xs).contains n = (decide (x = n) || xs.contains n) := by
  simp [eq_comm]

@[step]
theorem list_member_loop_spec (text needle : Slice Std.U8) (ok found : Bool) (i : Std.Usize)
    (hsp : ((bytes text).drop i.val).dropWhile isSpace = (bytes text).drop i.val)
    (fuel : Nat) (hf : ((bytes text).drop i.val).length < fuel) :
    predicate.list_member_loop text needle ok found i ⦃ r =>
      (if r.1 then some r.2 else none) =
        (if ok then (listElems fuel ((bytes text).drop i.val)).map
          (fun items => found || items.contains (bytes needle)) else none) ⦄ := by
  unfold predicate.list_member_loop
  split
  · dsimp only
    split
    · -- an element at `i`
      have hlt : i.val < text.length := by scalar_tac
      have hns : isSpace (byte (text.val[i.val]'(by simpa [Slice.length] using hlt))) = false := by
        rw [drop_bytes text _ hlt] at hsp
        by_contra h
        simp only [Bool.not_eq_false] at h
        rw [List.dropWhile_cons, ite_eq_left h] at hsp
        have := congrArg List.length hsp
        have := (List.dropWhile_suffix isSpace (l := (bytes text).drop (i.val + 1))).length_le
        simp at *; omega
      step*
      case fuel => exact fuel - 1
      case hsp => rw [i2_post, dropWhile_idem]
      case hf =>
        have := (List.dropWhile_suffix isSpace (l := (bytes text).drop «end».val)).length_le
        rw [← i2_post] at this
        simp only [List.length_drop, length_bytes] at *; omega
      have hf2 : 0 < fuel - 1 := by simp only [List.length_drop, length_bytes] at hf; omega
      rw [show fuel = (fuel - 1) + 1 by omega, o_post2 (fuel - 1) hf2, ← listElems_dropWhile,
        ← i2_post, r_post]
      cases o
      · simp
      · cases listElems (fuel - 1) ((bytes text).drop i2.val) <;>
          simp [hit_post, Bool.or_assoc, eq_comm]
    · -- the end of the text
      have : (bytes text).drop i.val = [] := List.drop_eq_nil_of_le (by rw [length_bytes]; scalar_tac)
      rw [this] at hf ⊢
      simp [listElems_nil fuel hf, ‹ok = true›]
  · simp [‹¬ok = true›]
termination_by text.length - i.val
decreasing_by all_goals scalar_tac

@[step]
theorem list_member_spec (text needle : Slice Std.U8) :
    predicate.list_member text needle ⦃ r =>
      r = (parseList (bytes text)).map (·.contains (bytes needle)) ⦄ := by
  unfold predicate.list_member
  step*
  case fuel => exact (bytes text).length + 1
  · -- a backslash or quote
    have hq : (bytes text).any (fun x => decide (x = 92) || decide (x = 34)) = true := by
      simpa [b_post] using ‹b = true›
    simp [parseList, hq]
  · rw [i_post, dropWhile_idem]
  · simp only [List.length_drop]; omega
  · have hq : (bytes text).any (fun x => decide (x = 92) || decide (x = 34)) = false := by
      simpa [b_post] using ‹¬b = true›
    have hp : parseList (bytes text) = listElems ((bytes text).length + 1) ((bytes text).drop i.val) := by
      simp only [parseList, hq, Bool.false_eq_true, ite_false, i_post, List.drop_zero,
        listElems_dropWhile]
    rw [hp]
    simp only [ite_true, Bool.false_or] at ok1_post
    split
    · simp only [WP.spec_ok]  
      rw [← ok1_post]; simp [‹ok1 = true›]
    · simp only [WP.spec_ok]
      rw [← ok1_post]; simp [‹¬ok1 = true›]

end TclMeshProof.Predicate
