/-!
# Canonical decimal numbers

Ordered comparisons in Tier A operate on exact decimals, not IEEE doubles:

```text
number := "-"? ("0" | [1-9][0-9]*) ("." [0-9]+)? ([eE] [+-]? [0-9]+)?
```

with the written exponent at most `maxExp` in magnitude, which bounds the
cost of comparison. A number denotes `±mant · 10^exp` exactly, so `1e3 = 1000`,
`0.10 = 0.1`, `-0 = 0`, and `0.1 < 0.10000000000000000001`.

Comparison scales both operands to a common exponent and compares integers.
The theorems show the result does not depend on the exponent chosen, and that
the induced relation is a total preorder.
-/

namespace TclMesh.Decimal

def maxExp : Nat := 1000

structure Dec where
  neg : Bool
  mant : Nat
  exp : Int
  deriving DecidableEq, Repr

/-- The value scaled to exponent `E`, exact whenever `E ≤ d.exp`. -/
def Dec.scaled (d : Dec) (E : Int) : Int :=
  (if d.neg then -1 else 1) * ((d.mant : Int) * 10 ^ (d.exp - E).toNat)

def Dec.cmp (a b : Dec) : Ordering :=
  let E := min a.exp b.exp
  compare (a.scaled E) (b.scaled E)

def Dec.le (a b : Dec) : Prop := a.cmp b ≠ .gt

instance : DecidableRel Dec.le := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

/-! ## Scaling is exact -/

theorem pow_pos (k : Nat) : (0 : Int) < 10 ^ k := Int.pow_pos (by decide)

theorem scaled_shift (d : Dec) {E E' : Int} (h₁ : E' ≤ E) (h₂ : E ≤ d.exp) :
    d.scaled E' = d.scaled E * 10 ^ (E - E').toNat := by
  unfold Dec.scaled
  have : (d.exp - E').toNat = (d.exp - E).toNat + (E - E').toNat := by omega
  rw [this, Int.pow_add]
  simp only [Int.mul_assoc]

/-- Order at a common exponent is independent of which (low enough) exponent. -/
theorem scaled_le_iff (a b : Dec) {E E' : Int} (h₁ : E' ≤ E) (ha : E ≤ a.exp) (hb : E ≤ b.exp) :
    a.scaled E' ≤ b.scaled E' ↔ a.scaled E ≤ b.scaled E := by
  rw [scaled_shift a h₁ ha, scaled_shift b h₁ hb]
  exact Int.mul_le_mul_iff_of_pos_right (pow_pos _)

theorem scaled_eq_iff (a b : Dec) {E E' : Int} (h₁ : E' ≤ E) (ha : E ≤ a.exp) (hb : E ≤ b.exp) :
    a.scaled E' = b.scaled E' ↔ a.scaled E = b.scaled E := by
  rw [scaled_shift a h₁ ha, scaled_shift b h₁ hb]
  exact ⟨Int.eq_of_mul_eq_mul_right (Int.ne_of_gt (pow_pos _)), fun h => by rw [h]⟩

theorem le_iff_scaled (a b : Dec) : a.le b ↔ a.scaled (min a.exp b.exp) ≤ b.scaled (min a.exp b.exp) := by
  unfold Dec.le Dec.cmp
  simp only [ne_eq]
  generalize a.scaled _ = x
  generalize b.scaled _ = y
  rw [← Int.not_lt]
  simp only [compare, compareOfLessAndEq]
  split <;> rename_i h1 <;> (try split) <;> simp_all <;> omega

/-- `a ≤ b` may be decided at any exponent at or below both. -/
theorem le_iff_at (a b : Dec) {E : Int} (ha : E ≤ a.exp) (hb : E ≤ b.exp) :
    a.le b ↔ a.scaled E ≤ b.scaled E := by
  rw [le_iff_scaled]
  exact (scaled_le_iff a b (by omega) (by omega) (by omega)).symm

/-! ## Total preorder -/

theorem le_refl (a : Dec) : a.le a := (le_iff_at a a (Int.le_refl _) (Int.le_refl _)).mpr (Int.le_refl _)

theorem le_trans {a b c : Dec} (hab : a.le b) (hbc : b.le c) : a.le c := by
  let E := min a.exp (min b.exp c.exp)
  have ha : E ≤ a.exp := by omega
  have hb : E ≤ b.exp := by omega
  have hc : E ≤ c.exp := by omega
  exact (le_iff_at a c ha hc).mpr
    (Int.le_trans ((le_iff_at a b ha hb).mp hab) ((le_iff_at b c hb hc).mp hbc))

theorem le_total (a b : Dec) : a.le b ∨ b.le a := by
  let E := min a.exp b.exp
  rw [le_iff_at a b (E := E) (by omega) (by omega), le_iff_at b a (E := E) (by omega) (by omega)]
  exact Int.le_total _ _

/-- Signed zero is zero. -/
theorem neg_zero (e : Int) : (Dec.mk true 0 e).scaled e = (Dec.mk false 0 e).scaled e := by
  simp [Dec.scaled]

/-! ## Parsing -/

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- Splits a maximal run of ASCII digits off the front. -/
def takeDigits : List Char → List Char × List Char
  | c :: cs => if c.isDigit then let (d, r) := takeDigits cs; (c :: d, r) else ([], c :: cs)
  | [] => ([], [])

def digitsVal (ds : List Char) : Nat := ds.foldl (fun n c => 10 * n + digitVal c) 0

/-- The exponent's magnitude after removing leading zeros, if within `maxExp`. -/
def boundedExp (ds : List Char) : Option Nat :=
  let ds := ds.dropWhile (· == '0')
  if ds.length ≤ 4 && digitsVal ds ≤ maxExp then some (digitsVal ds) else none

def parseChars (cs : List Char) : Option Dec := do
  let (neg, cs) := match cs with
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  let (int, cs) := takeDigits cs
  guard (int ≠ [] && (int.length = 1 || int.head? ≠ some '0'))
  let (frac, cs) ← match cs with
    | '.' :: rest =>
        let (f, r) := takeDigits rest
        if f = [] then none else some (f, r)
    | _ => some ([], cs)
  let (e, cs) ← match cs with
    | c :: rest =>
        if c = 'e' || c = 'E' then
          let (sign, rest) := match rest with
            | '-' :: r => (-1, r)
            | '+' :: r => (1, r)
            | _ => (1, rest)
          let (ds, r) := takeDigits rest
          if ds = [] then none else do
            let m ← boundedExp ds
            some (sign * (m : Int), r)
        else some (0, c :: rest)
    | [] => some (0, [])
  guard (cs = [])
  pure ⟨neg, digitsVal (int ++ frac), e - frac.length⟩

def parse (s : String) : Option Dec := parseChars s.toList

/-- Comparison of two operand strings: `none` if either is not canonical. -/
def compareStrings (a b : String) : Option Ordering := do
  pure ((← parse a).cmp (← parse b))

/-! ## The canonical domain, by example (checked by evaluation) -/

example : compareStrings "1e3" "1000" = some .eq := by decide
example : compareStrings "0.10" "0.1" = some .eq := by decide
example : compareStrings "-0" "0" = some .eq := by decide
example : compareStrings "-0.0" "0" = some .eq := by decide
example : compareStrings "0.1" "0.10000000000000000001" = some .lt := by decide
example : compareStrings "9007199254740993" "9007199254740992.0" = some .gt := by decide
example : compareStrings "-2.5" "-3" = some .gt := by decide
example : compareStrings "1E-2" "0.01" = some .eq := by decide
example : compareStrings "1e1000" "1e999" = some .gt := by decide
example : parse "1e1001" = none := by decide
example : parse "1e0000000000000001000" ≠ none := by decide
example : parse "007" = none := by decide
example : parse "0x10" = none := by decide
example : parse " 1" = none := by decide
example : parse "+1" = none := by decide
example : parse ".5" = none := by decide
example : parse "1." = none := by decide
example : parse "1e" = none := by decide
example : parse "Inf" = none := by decide
example : parse "" = none := by decide

end TclMesh.Decimal
