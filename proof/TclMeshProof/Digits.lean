import Mathlib.Tactic.Ring

/-!
# Decimal digit strings

Arithmetic facts about most-significant-first digit lists, used to show that
comparing padded digit strings (length first, then lexicographically) is
comparing the numbers they denote.
-/

namespace TclMeshProof.Digits

/-- Value of a most-significant-first digit list. -/
def val (ds : List Nat) : Nat := ds.foldl (fun n d => 10 * n + d) 0

def IsDigits (ds : List Nat) : Prop := ∀ d ∈ ds, d ≤ 9

theorem foldl_shift (ds : List Nat) (n : Nat) :
    ds.foldl (fun n d => 10 * n + d) n = n * 10 ^ ds.length + val ds := by
  induction ds generalizing n with
  | nil => simp [val]
  | cons d ds ih =>
    simp only [val, List.foldl_cons, List.length_cons] at *
    rw [ih, ih (10 * 0 + d), Nat.pow_succ]
    ring

theorem val_cons (d : Nat) (ds : List Nat) : val (d :: ds) = d * 10 ^ ds.length + val ds := by
  have := foldl_shift ds d
  simpa [val] using this

theorem val_append_zeros (ds : List Nat) (p : Nat) :
    val (ds ++ List.replicate p 0) = val ds * 10 ^ p := by
  unfold val
  rw [List.foldl_append, foldl_shift]
  have : val (List.replicate p 0) = 0 := by
    induction p with
    | zero => rfl
    | succ p ih => rw [List.replicate_succ, val_cons, ih]; simp
  simp [this]

theorem val_lt {ds : List Nat} (h : IsDigits ds) : val ds < 10 ^ ds.length := by
  induction ds with
  | nil => simp [val]
  | cons d ds ih =>
    have hd : d ≤ 9 := h d (List.mem_cons_self ..)
    have ih := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    rw [val_cons, List.length_cons, Nat.pow_succ]
    have : d * 10 ^ ds.length ≤ 9 * 10 ^ ds.length := Nat.mul_le_mul_right _ hd
    omega

theorem val_ge {d : Nat} {ds : List Nat} (hd : d ≠ 0) : 10 ^ ds.length ≤ val (d :: ds) := by
  rw [val_cons]
  have : 1 * 10 ^ ds.length ≤ d * 10 ^ ds.length := Nat.mul_le_mul_right _ (by omega)
  omega

/-- First difference decides; equal-length lists. -/
def lex : List Nat → List Nat → Ordering
  | x :: xs, y :: ys => if x < y then .lt else if x > y then .gt else lex xs ys
  | _, _ => .eq

/-- For digit lists of equal length, lexicographic order is numeric order. -/
theorem lex_eq_compare {xs ys : List Nat} (hx : IsDigits xs) (hy : IsDigits ys)
    (hl : xs.length = ys.length) : lex xs ys = compare (val xs) (val ys) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [lex, val]
    | cons => simp at hl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      have hx' : IsDigits xs := fun d h => hx d (List.mem_cons_of_mem _ h)
      have hy' : IsDigits ys := fun d h => hy d (List.mem_cons_of_mem _ h)
      have hxs := val_lt hx'
      have hys := val_lt hy'
      rw [hl] at hxs
      simp only [lex, val_cons, hl]
      have key : ∀ a b u v : Nat, u < 10 ^ ys.length → v < 10 ^ ys.length → a < b →
          a * 10 ^ ys.length + u < b * 10 ^ ys.length + v := by
        intro a b u v hu hv hab
        have : (a + 1) * 10 ^ ys.length ≤ b * 10 ^ ys.length := Nat.mul_le_mul_right _ hab
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      split
      · rename_i h; exact (Nat.compare_eq_lt.mpr (key _ _ _ _ hxs hys h)).symm
      · split
        · rename_i _ h; exact (Nat.compare_eq_gt.mpr (key _ _ _ _ hys hxs h)).symm
        · have : x = y := by omega
          subst this
          rw [ih hx' hy' hl]
          rcases Nat.lt_trichotomy (val xs) (val ys) with h | h | h
          · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr (by omega)]
          · rw [h]; simp
          · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr (by omega)]

end TclMeshProof.Digits
