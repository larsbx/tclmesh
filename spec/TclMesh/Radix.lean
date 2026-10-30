import TclMesh.Noise
import TclMesh.Range

/-!
# Radix integers as block gate programs: addition

TFHE-rs represents an integer of `2n` bits as `n` shortint blocks of 2-bit
messages, least significant first (`FheInt32`: 16 blocks). Addition adds the
blocks pairwise and propagates carries: block `i` holds `aᵢ + bᵢ + cᵢ`, and two
bootstraps extract its message `(·) % 4` and its carry `(·) / 4` into block
`i + 1`. This file writes that sequential ripple-carry adder as a gate program
(`addProg n`) and proves, for every `n`:

* `add_check`: the noise checker of `TclMesh.Noise` accepts it under `tfhe22`,
  so `Noise.bootstrapped_sound` applies (`add_sound`);
* `add_digits`: its output digits are those of `(A + B) mod 4^n`;
* `add_wrap32`: at `n = 16`, read as a two's-complement word, the result is
  `Range.wrap 32 (a + b)`, the operation `Range.wrapped 32` assigns to `add`.

So for this adder the hypothesis `Range` names, that TFHE computes
`wrapped 32`, is discharged down to the per-bootstrap contract. TFHE-rs also
has parallel carry propagation, which is a different gate program; that the
gate program `FheInt32 + FheInt32` actually runs is this one (or computes the
same digits) is not proved here.
-/

namespace TclMesh.Radix

open TclMesh.Noise

def modLut : List Int := (List.range 16).map fun x => ((x % 4 : Nat) : Int)
def divLut : List Int := (List.range 16).map fun x => ((x / 4 : Nat) : Int)

/-- Wires: `0 … n-1` hold `a`'s blocks, `n … 2n-1` `b`'s, `2n` is a zero carry,
and block `i` adds three wires from `2n + 1 + 3i`: sum, message, carry. The
carry into block `i` is wire `2n + 3i`. -/
def block (n i : Nat) : List Gate :=
  [.lin [(1, i), (1, n + i), (1, 2 * n + 3 * i)] 0,
    .pbs modLut 3 (2 * n + 1 + 3 * i), .pbs divLut 3 (2 * n + 1 + 3 * i)]

def addGates (n : Nat) : List Gate :=
  (List.range (2 * n)).map Gate.input ++ [.lin [] 0] ++ (List.range n).flatMap (block n)

def msgWire (n k : Nat) : Nat := 2 * n + 2 + 3 * k

def addProg (n : Nat) : Prog := ⟨addGates n, (List.range n).map (msgWire n)⟩

/-! ## The checker accepts every width -/

theorem getD_append_lt {α} (l l' : List α) (d : α) {j : Nat} (h : j < l.length) :
    (l ++ l').getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_len {α} (l l' : List α) (d : α) (t : Nat) :
    (l ++ l').getD (l.length + t) d = l'.getD t d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem getD_append_len0 {α} (l l' : List α) (d : α) : (l ++ l').getD l.length d = l'.getD 0 d :=
  getD_append_len l l' d 0

/-- After `i` blocks: inputs are fresh blocks, the carry into block `i` is a
bit-sized block of level at most 1, and every message produced is level 1. -/
def AInv (n i : Nat) (s : List Abs) : Prop :=
  s.length = 2 * n + 1 + 3 * i ∧ (∀ j < 2 * n, s.getD j zeroAbs = ⟨0, 3, 1⟩) ∧
    (s.getD (2 * n + 3 * i) zeroAbs).lo = 0 ∧ (s.getD (2 * n + 3 * i) zeroAbs).hi ≤ 3 ∧
    (s.getD (2 * n + 3 * i) zeroAbs).level ≤ 1 ∧
    ∀ k < i, (s.getD (msgWire n k) zeroAbs).level = 1

theorem block_check (n i : Nat) (hi : i < n) (s : List Abs) (h : AInv n i s) :
    ∃ s', analyze tfhe22 s (block n i) = some s' ∧ AInv n (i + 1) s' := by
  obtain ⟨hl, hin, clo, chi, clev, hmsg⟩ := h
  have ha := hin i (by omega)
  have hb := hin (n + i) (by omega)
  generalize hc : s.getD (2 * n + 3 * i) zeroAbs = c at clo chi clev
  obtain ⟨clo', chi', clev'⟩ := c
  simp only at clo chi clev
  subst clo
  let sum : Abs := ⟨0, 3 + (3 + chi'), 1 + (1 + clev')⟩
  refine ⟨s ++ [sum, ⟨0, 3, 1⟩, ⟨0, 3, 1⟩], ?_, ?_⟩
  · have hm : lutIn modLut 3 = true := by decide
    have hd : lutIn divLut 3 = true := by decide
    simp only [block, analyze, stepAbs, linLo, linHi, linLevel, ha, hb, hc, hl, List.all_cons,
      List.all_nil]
    rw [show 2 * n + 1 + 3 * i = s.length by omega]
    simp [hm, hd, tfhe22, sum, show i < s.length by omega,
      show n + i < s.length by omega, show 2 * n + 3 * i < s.length by omega]
    split <;> first | rfl | omega
  · refine ⟨by simp [hl]; omega, fun j hj => ?_, ?_⟩
    · rw [getD_append_lt _ _ _ (by omega)]; exact hin j hj
    · rw [show 2 * n + 3 * (i + 1) = s.length + 2 by omega, getD_append_len]
      refine ⟨rfl, by simp, by simp, fun k hk => ?_⟩
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [getD_append_lt _ _ _ (by simp [msgWire]; omega)]; exact hmsg k hk'
      · rw [show msgWire n k = s.length + 1 by simp [msgWire]; omega, getD_append_len]; rfl

def prefixGates (n : Nat) : List Gate := (List.range (2 * n)).map Gate.input ++ [.lin [] 0]

theorem addGates_eq (n : Nat) : addGates n = prefixGates n ++ (List.range n).flatMap (block n) := rfl

theorem blocks_check (n : Nat) : ∀ i ≤ n, ∃ s,
    analyze tfhe22 [] (prefixGates n ++ (List.range i).flatMap (block n)) = some s ∧ AInv n i s := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨(List.range (2 * n)).map (fun _ => ⟨0, 3, 1⟩) ++ [zeroAbs], ?_, ?_⟩
    · simp [prefixGates, analyze_append, analyze_inputs, analyze, stepAbs, linLo, linHi, linLevel,
        tfhe22, zeroAbs]
    · refine ⟨by simp, fun j hj => ?_, ?_⟩
      · rw [getD_append_lt _ _ _ (by simpa using hj)]
        simp [List.getD_eq_getElem?_getD, hj]
      · simp [zeroAbs]
  | succ i ih =>
    intro hi
    obtain ⟨s, hs, hI⟩ := ih (by omega)
    obtain ⟨s', hs', hI'⟩ := block_check n i (by omega) s hI
    exact ⟨s', by rw [List.range_succ, List.flatMap_append, ← List.append_assoc, analyze_append, hs,
      List.flatMap_singleton]; exact hs', hI'⟩

/-- **The checker accepts the adder at every width.** -/
theorem add_check (n : Nat) : check tfhe22 (addProg n) = true := by
  obtain ⟨s, hs, hl, -, -, -, -, hmsg⟩ := blocks_check n n (Nat.le_refl n)
  simp only [check, addProg, addGates_eq, hs, List.all_eq_true, List.mem_map, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq]
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨by simp [msgWire]; omega, by rw [hmsg k hk]; decide⟩

/-! ## The adder computes `(A + B) mod 4^n` -/

/-- `Σ_{k<i} f k · 4^k`: the integer whose base-4 digits are `f`. -/
def val (f : Nat → Int) : Nat → Int
  | 0 => 0
  | i + 1 => val f i + f i * 4 ^ i

theorem val_congr {f g : Nat → Int} : ∀ i, (∀ k < i, f k = g k) → val f i = val g i
  | 0, _ => rfl
  | i + 1, h => by
    simp only [val]; rw [val_congr i (fun k hk => h k (by omega)), h i (by omega)]

theorem val_add (f g : Nat → Int) : ∀ i, val (fun k => f k + g k) i = val f i + val g i
  | 0 => rfl
  | i + 1 => by simp only [val, val_add f g i, Int.add_mul]; omega

theorem val_bound {f : Nat → Int} : ∀ i, (∀ k < i, 0 ≤ f k ∧ f k ≤ 3) → 0 ≤ val f i ∧ val f i < 4 ^ i
  | 0, _ => by simp [val]
  | i + 1, h => by
    obtain ⟨l, u⟩ := val_bound i fun k hk => h k (by omega)
    obtain ⟨fl, fu⟩ := h i (by omega)
    have hp : (0 : Int) < 4 ^ i := Int.pow_pos (by decide)
    have m1 : 0 ≤ f i * 4 ^ i := Int.mul_nonneg fl (by omega)
    have m2 : f i * 4 ^ i ≤ 3 * 4 ^ i := Int.mul_le_mul_of_nonneg_right fu (by omega)
    simp only [val, Int.pow_succ]
    omega

theorem lut_mod {x : Int} (h0 : 0 ≤ x) (h1 : x < 16) : modLut.getD x.toNat 0 = x % 4 := by
  have h : ∀ m < 16, modLut.getD m 0 = ((m % 4 : Nat) : Int) := by decide
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [Int.toNat_natCast, h m (by omega)]; omega

theorem lut_div {x : Int} (h0 : 0 ≤ x) (h1 : x < 16) : divLut.getD x.toNat 0 = x / 4 := by
  have h : ∀ m < 16, divLut.getD m 0 = ((m / 4 : Nat) : Int) := by decide
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  rw [Int.toNat_natCast, h m (by omega)]; omega

/-- After `i` blocks: inputs are the digits `v`, the carry is a bit, messages
are digits, and messages plus the carry weigh what the inputs' first `i`
digit pairs weigh. -/
def VInv (n i : Nat) (v : Nat → Int) (xs : List Int) : Prop :=
  xs.length = 2 * n + 1 + 3 * i ∧ (∀ j < 2 * n, xs.getD j 0 = v j) ∧
    0 ≤ xs.getD (2 * n + 3 * i) 0 ∧ xs.getD (2 * n + 3 * i) 0 ≤ 1 ∧
    (∀ k < i, 0 ≤ xs.getD (msgWire n k) 0 ∧ xs.getD (msgWire n k) 0 ≤ 3) ∧
    val (fun k => xs.getD (msgWire n k) 0) i + xs.getD (2 * n + 3 * i) 0 * 4 ^ i =
      val (fun k => v k + v (n + k)) i

theorem block_eval (n i : Nat) (hi : i < n) (v : Nat → Int) (hv : ∀ j < 2 * n, 0 ≤ v j ∧ v j ≤ 3)
    (xs : List Int) (h : VInv n i v xs) : VInv n (i + 1) v (evalV v xs (block n i)) := by
  obtain ⟨hl, hin, c0, c1, hmsg, hsum⟩ := h
  have ha := hin i (by omega)
  have hb := hin (n + i) (by omega)
  generalize hc : xs.getD (2 * n + 3 * i) 0 = c at c0 c1 hsum
  obtain ⟨a0, a1⟩ := hv i (by omega)
  obtain ⟨b0, b1⟩ := hv (n + i) (by omega)
  let S := v i + v (n + i) + c
  have e : evalV v xs (block n i) = xs ++ [S, S % 4, S / 4] := by
    simp only [block, evalV, stepV, linV, ha, hb, hc]
    rw [show 2 * n + 1 + 3 * i = xs.length by omega]
    simp only [List.append_assoc, List.cons_append, List.nil_append, getD_append_len0,
      List.getD_cons_zero]
    rw [lut_mod (by omega) (by omega), lut_div (by omega) (by omega)]
    simp [S]; omega
  rw [e]
  refine ⟨by simp [hl]; omega, fun j hj => ?_, ?_, ?_, fun k hk => ?_, ?_⟩
  · rw [getD_append_lt _ _ _ (by omega)]; exact hin j hj
  · rw [show 2 * n + 3 * (i + 1) = xs.length + 2 by omega, getD_append_len]; simp; omega
  · rw [show 2 * n + 3 * (i + 1) = xs.length + 2 by omega, getD_append_len]; simp; omega
  · rcases Nat.lt_or_ge k i with hk' | hk'
    · rw [getD_append_lt _ _ _ (by simp [msgWire]; omega)]; exact hmsg k hk'
    · rw [show msgWire n k = xs.length + 1 by simp [msgWire]; omega, getD_append_len]; simp; omega
  · have old : val (fun k => (xs ++ [S, S % 4, S / 4]).getD (msgWire n k) 0) i =
        val (fun k => xs.getD (msgWire n k) 0) i :=
      val_congr i fun k hk => getD_append_lt _ _ _ (by simp [msgWire]; omega)
    have hm : (xs ++ [S, S % 4, S / 4]).getD (msgWire n i) 0 = S % 4 := by
      rw [show msgWire n i = xs.length + 1 by simp [msgWire]; omega, getD_append_len]; rfl
    have hcar : (xs ++ [S, S % 4, S / 4]).getD (2 * n + 3 * (i + 1)) 0 = S / 4 := by
      rw [show 2 * n + 3 * (i + 1) = xs.length + 2 by omega, getD_append_len]; rfl
    simp only [val, old, hm, hcar]
    have hdiv : S % 4 * 4 ^ i + 4 * (S / 4 * 4 ^ i) = S * 4 ^ i := by
      rw [← Int.mul_assoc, ← Int.add_mul, show S % 4 + 4 * (S / 4) = S by omega]
    have hS : S * 4 ^ i = v i * 4 ^ i + v (n + i) * 4 ^ i + c * 4 ^ i := by
      simp only [S, Int.add_mul]
    rw [Int.pow_succ, show S / 4 * (4 ^ i * 4) = 4 * (S / 4 * 4 ^ i) by
      rw [Int.mul_comm (4 ^ i) 4, ← Int.mul_assoc, Int.mul_comm (S / 4) 4, Int.mul_assoc], Int.add_mul]
    omega

theorem blocks_eval (n : Nat) (v : Nat → Int) (hv : ∀ j < 2 * n, 0 ≤ v j ∧ v j ≤ 3) :
    ∀ i ≤ n, VInv n i v (evalV v [] (prefixGates n ++ (List.range i).flatMap (block n))) := by
  intro i
  induction i with
  | zero =>
    intro _
    have e : evalV v [] (prefixGates n) = (List.range (2 * n)).map v ++ [0] := by
      simp [prefixGates, evalV_append, evalV_inputs, evalV, stepV, linV]
    simp only [List.range_zero, List.flatMap_nil, List.append_nil, e]
    refine ⟨by simp, fun j hj => ?_, ?_, ?_, fun k hk => absurd hk (by omega), by simp [val]⟩
    · rw [getD_append_lt _ _ _ (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, hj]
    all_goals simp
  | succ i ih =>
    intro hi
    rw [List.range_succ, List.flatMap_append, ← List.append_assoc, evalV_append,
      List.flatMap_singleton]
    exact block_eval n i (by omega) v hv _ (by simpa [evalV_append] using ih (by omega))

/-- The adder's output digits. -/
def outDigits (n : Nat) (xs : List Int) (k : Nat) : Int := xs.getD (msgWire n k) 0

/-- **The adder computes `(A + B) mod 4^n`** on digits `v`: `A`'s are `v 0 … v (n-1)`,
`B`'s are `v n … v (2n-1)`. -/
theorem add_digits (n : Nat) (v : Nat → Int) (hv : ∀ j < 2 * n, 0 ≤ v j ∧ v j ≤ 3) :
    (∀ k < n, 0 ≤ outDigits n (evalV v [] (addGates n)) k ∧ outDigits n (evalV v [] (addGates n)) k ≤ 3) ∧
    val (outDigits n (evalV v [] (addGates n))) n = (val v n + val (fun k => v (n + k)) n) % 4 ^ n := by
  obtain ⟨-, -, c0, -, hmsg, hsum⟩ := blocks_eval n v hv n (Nat.le_refl n)
  rw [← addGates_eq] at c0 hmsg hsum
  refine ⟨hmsg, ?_⟩
  obtain ⟨l, u⟩ := val_bound n hmsg
  rw [← val_add, ← hsum, Int.add_mul_emod_self_right, Int.emod_eq_of_lt l u]
  rfl

/-- **Encrypted addition decrypts to `(A + B) mod 4^n`**, at any width, under
the hypotheses of `Noise.bootstrapped_sound`. -/
theorem add_sound (n delta fresh : Nat) (hdec : 2 * (tfhe22.maxLevel * fresh) < delta)
    (boots : Nat → Boot) (inp : Nat → Ct) (hinp : Fresh tfhe22 fresh inp)
    (hgood : ∀ i lut hi j, (addGates n)[i]? = some (.pbs lut hi j) → Good tfhe22 fresh (boots i)) :
    let d := fun k => decode delta ((evalCt boots inp [] (addGates n)).getD (msgWire n k) zeroCt)
    val d n = (val (fun k => (inp k).m) n + val (fun k => (inp (n + k)).m) n) % 4 ^ n := by
  intro d
  have hv : ∀ j < 2 * n, 0 ≤ (inp j).m ∧ (inp j).m ≤ 3 := fun j _ => ⟨(hinp j).1, (hinp j).2.1⟩
  rw [← (add_digits n _ hv).2]
  exact val_congr n fun k hk => bootstrapped_sound tfhe22 delta fresh hdec (addProg n) (add_check n)
    boots inp hinp hgood _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)

/-! ## Two's complement: the 32-bit word -/

/-- A 32-bit two's-complement pattern read as a signed word. -/
def signed32 (u : Int) : Int := if u < 2 ^ 31 then u else u - 2 ^ 32

theorem half32 : Range.half 32 = 2 ^ 31 := by decide

/-- Adding two's-complement patterns modulo `2^32` is `Range.wrap 32` of the sum. -/
theorem signed32_add (a b : Int) :
    signed32 ((a % 2 ^ 32 + b % 2 ^ 32) % 2 ^ 32) = Range.wrap 32 (a + b) := by
  simp only [signed32, Range.wrap, half32]
  split <;> omega

/-- **Ripple-carry addition of 16 blocks is `Range.wrapped 32`**: blocks
encoding the words `a` and `b` decrypt, read as a signed word, to the value
`Range` assigns to `add`. -/
theorem add_wrap32 (delta fresh : Nat) (hdec : 2 * (tfhe22.maxLevel * fresh) < delta)
    (boots : Nat → Boot) (inp : Nat → Ct) (hinp : Fresh tfhe22 fresh inp)
    (hgood : ∀ i lut hi j, (addGates 16)[i]? = some (.pbs lut hi j) → Good tfhe22 fresh (boots i))
    (a b : Int) (ha : val (fun k => (inp k).m) 16 = a % 2 ^ 32)
    (hb : val (fun k => (inp (16 + k)).m) 16 = b % 2 ^ 32) :
    signed32 (val (fun k => decode delta ((evalCt boots inp [] (addGates 16)).getD (msgWire 16 k) zeroCt)) 16) =
      Range.wrapped 32 ["add", "x", "y"] [a, b] := by
  rw [add_sound 16 delta fresh hdec boots inp hinp hgood, ha, hb,
    show (4 : Int) ^ 16 = 2 ^ 32 by decide, signed32_add]
  rfl

example : check tfhe22 (addProg 16) = true := add_check 16

end TclMesh.Radix
