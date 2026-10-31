import TclMesh.Noise
import TclMesh.Range

/-!
# Radix integers as block gate programs: addition and subtraction

TFHE-rs represents an integer of `2n` bits as `n` shortint blocks of 2-bit
messages, least significant first (`FheInt32`: 16 blocks). Addition adds the
blocks pairwise and propagates carries: block `i` holds `aᵢ + bᵢ + cᵢ`, and two
bootstraps extract its message `(·) % 4` and its carry `(·) / 4` into block
`i + 1`. Subtraction is the same adder on the complement: `A - B = A + ~B + 1`
modulo `4^n`, with digits `3 - bᵢ` (a cleartext weight and offset, no
bootstrap) and a carry of `1` into block `0`.

This file writes that sequential ripple-carry adder as a gate program
(`radixProg n neg`, subtracting when `neg`) and proves, for every `n`:

* `radix_check`: the noise checker of `TclMesh.Noise` accepts it under
  `tfhe22`, so `Noise.bootstrapped_sound` applies (`radix_sound`);
* `add_digits`, `sub_digits`: its output digits are those of `(A + B) mod 4^n`,
  respectively `(A - B) mod 4^n`;
* `add_wrap32`, `sub_wrap32`: at `n = 16`, read as a two's-complement word, the
  result is `Range.wrapped 32` of `add`, respectively `subtract`.

So for these programs the hypothesis `Range` names, that TFHE computes
`wrapped 32`, reduces to the hypotheses of `Noise.bootstrapped_sound`: fresh
bounded input noise, `2·maxLevel·fresh < Δ`, and success of the actual PBS
calls (`CallsGood`); their correspondence with native TFHE-rs is the open
audit of `docs/noise-correspondence.md`. TFHE-rs also
has parallel carry propagation, which is a different gate program; that the
gate program `FheInt32 + FheInt32` (or `-`) actually runs is this one (or
computes the same digits) is not proved here.
-/

namespace TclMesh.Radix

open TclMesh.Noise

def modLut : List Int := (List.range 16).map fun x => ((x % 4 : Nat) : Int)
def divLut : List Int := (List.range 16).map fun x => ((x / 4 : Nat) : Int)

/-- The second operand's digit is `bw·b + bk`: `b` for addition, `3 - b` for
subtraction, whose carry into block `0` is `cin = 1`. -/
def bw (neg : Bool) : Int := if neg then -1 else 1
def bk (neg : Bool) : Int := if neg then 3 else 0
def cin (neg : Bool) : Int := if neg then 1 else 0
def bdig (neg : Bool) (x : Int) : Int := bw neg * x + bk neg

/-- Wires: `0 … n-1` hold `a`'s blocks, `n … 2n-1` `b`'s, `2n` the carry `cin`,
and block `i` adds three wires from `2n + 1 + 3i`: sum, message, carry. The
carry into block `i` is wire `2n + 3i`. -/
def terms (n : Nat) (neg : Bool) (i : Nat) : List (Int × Nat) :=
  [(1, i), (bw neg, n + i), (1, 2 * n + 3 * i)]

def block (n : Nat) (neg : Bool) (i : Nat) : List Gate :=
  [.lin (terms n neg i) (bk neg), .pbs modLut 3 (2 * n + 1 + 3 * i), .pbs divLut 3 (2 * n + 1 + 3 * i)]

def prefixGates (n : Nat) (neg : Bool) : List Gate :=
  (List.range (2 * n)).map Gate.input ++ [.lin [] (cin neg)]

def radixGates (n : Nat) (neg : Bool) : List Gate :=
  prefixGates n neg ++ (List.range n).flatMap (block n neg)

def msgWire (n k : Nat) : Nat := 2 * n + 2 + 3 * k

def radixProg (n : Nat) (neg : Bool) : Prog := ⟨radixGates n neg, (List.range n).map (msgWire n)⟩

abbrev addGates (n : Nat) : List Gate := radixGates n false
abbrev subGates (n : Nat) : List Gate := radixGates n true

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
nonempty interval within `[0, 3]` of level at most 1, and every message
produced is a fresh-looking block. -/
def AInv (n i : Nat) (s : List Abs) : Prop :=
  s.length = 2 * n + 1 + 3 * i ∧ (∀ j < 2 * n, s.getD j zeroAbs = ⟨0, 3, 1⟩) ∧
    0 ≤ (s.getD (2 * n + 3 * i) zeroAbs).lo ∧
    (s.getD (2 * n + 3 * i) zeroAbs).lo ≤ (s.getD (2 * n + 3 * i) zeroAbs).hi ∧
    (s.getD (2 * n + 3 * i) zeroAbs).hi ≤ 3 ∧ (s.getD (2 * n + 3 * i) zeroAbs).level ≤ 1 ∧
    ∀ k < i, s.getD (msgWire n k) zeroAbs = ⟨0, 3, 1⟩

theorem block_check (n : Nat) (neg : Bool) (i : Nat) (hi : i < n) (s : List Abs) (h : AInv n i s) :
    ∃ s', analyze tfhe22 s (block n neg i) = some s' ∧ AInv n (i + 1) s' := by
  obtain ⟨hl, hin, clo, cord, chi, clev, hmsg⟩ := h
  have ha := hin i (by omega)
  have hb := hin (n + i) (by omega)
  generalize hc : s.getD (2 * n + 3 * i) zeroAbs = c at clo cord chi clev
  let sum : Abs := ⟨linLo s (terms n neg i) + bk neg, linHi s (terms n neg i) + bk neg,
    linLevel s (terms n neg i)⟩
  have hlo : 0 ≤ sum.lo := by
    simp only [sum, terms, linLo, ha, hb, hc]; cases neg <;> simp [bw, bk] <;> omega
  have hord : sum.lo ≤ sum.hi := by
    simp only [sum, terms, linLo, linHi, ha, hb, hc]; cases neg <;> simp [bw, bk] <;> omega
  have hhi : sum.hi ≤ 15 := by
    simp only [sum, terms, linHi, ha, hb, hc]; cases neg <;> simp [bw, bk] <;> omega
  have hlev : sum.level ≤ 5 := by
    simp only [sum, terms, linLevel, ha, hb, hc]; cases neg <;> simp [bw] <;> omega
  refine ⟨s ++ [sum, ⟨0, 3, 1⟩, ⟨0, 3, 1⟩], ?_, ?_⟩
  · have hall : ((terms n neg i).all fun t => decide (t.2 < s.length)) = true := by
      simp [terms]; omega
    have hm : lutIn modLut 3 = true := by decide
    have hd : lutIn divLut 3 = true := by decide
    have hadm : admissible tfhe22 sum = true := by
      simp [admissible, tfhe22, hlo, hord, hhi, hlev]
    simp only [block, analyze, checkedStep, stepAbs, hall, ite_true, Option.bind_some]
    simp only [sum] at hadm
    simp only [hadm, ite_true, Option.bind_some]
    rw [show 2 * n + 1 + 3 * i = s.length by omega]
    simp only [List.append_assoc, List.cons_append, List.nil_append, getD_append_len0,
      List.getD_cons_zero]
    simp only [sum] at hlo hhi hlev
    simp [hlo, hhi, hlev, hm, hd, tfhe22, admissible, sum]
  · refine ⟨by simp [hl]; omega, fun j hj => ?_, ?_⟩
    · rw [getD_append_lt _ _ _ (by omega)]; exact hin j hj
    · rw [show 2 * n + 3 * (i + 1) = s.length + 2 by omega, getD_append_len]
      refine ⟨by simp, by simp, by simp, by simp, fun k hk => ?_⟩
      rcases Nat.lt_or_ge k i with hk' | hk'
      · rw [getD_append_lt _ _ _ (by simp [msgWire]; omega)]; exact hmsg k hk'
      · rw [show msgWire n k = s.length + 1 by simp [msgWire]; omega, getD_append_len]; rfl

theorem blocks_check (n : Nat) (neg : Bool) : ∀ i ≤ n, ∃ s,
    analyze tfhe22 [] (prefixGates n neg ++ (List.range i).flatMap (block n neg)) = some s ∧
      AInv n i s := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨(List.range (2 * n)).map (fun _ => ⟨0, 3, 1⟩) ++ [⟨cin neg, cin neg, 0⟩], ?_, ?_⟩
    · have hD : admissible tfhe22 ⟨0, tfhe22.msgMax, 1⟩ = true := by decide
      simp only [prefixGates, analyze_append, analyze_inputs tfhe22 hD, Option.bind_some]
      cases neg <;> simp [analyze, checkedStep, stepAbs, admissible, linLo, linHi, linLevel, cin,
        tfhe22]
    · refine ⟨by simp, fun j hj => ?_, ?_⟩
      · rw [getD_append_lt _ _ _ (by simpa using hj)]
        simp [List.getD_eq_getElem?_getD, hj]
      · cases neg <;> simp [cin]
  | succ i ih =>
    intro hi
    obtain ⟨s, hs, hI⟩ := ih (by omega)
    obtain ⟨s', hs', hI'⟩ := block_check n neg i (by omega) s hI
    exact ⟨s', by rw [List.range_succ, List.flatMap_append, ← List.append_assoc, analyze_append, hs,
      List.flatMap_singleton]; exact hs', hI'⟩

/-- **The checker accepts the adder and the subtracter at every width.** -/
theorem radix_check (n : Nat) (neg : Bool) : check tfhe22 (radixProg n neg) = true := by
  obtain ⟨s, hs, hl, -, -, -, -, -, hmsg⟩ := blocks_check n neg n (Nat.le_refl n)
  simp only [check, radixProg, radixGates, hs, List.all_eq_true, List.mem_map, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq]
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨by simp [msgWire]; omega, by rw [hmsg k hk]; decide⟩

/-! ## The digits -/

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

/-- Complementing every digit: `~B = 4^n - 1 - B`. -/
theorem val_compl (f : Nat → Int) : ∀ i, val (fun k => 3 - f k) i = 4 ^ i - 1 - val f i
  | 0 => by simp [val]
  | i + 1 => by simp only [val, val_compl f i, Int.sub_mul, Int.pow_succ]; omega

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

theorem bdig_bound (neg : Bool) {x : Int} (h0 : 0 ≤ x) (h1 : x ≤ 3) : 0 ≤ bdig neg x ∧ bdig neg x ≤ 3 := by
  cases neg <;> simp [bdig, bw, bk] <;> omega

/-- After `i` blocks: inputs are the digits `v`, the carry is a bit, messages
are digits, and messages plus the carry weigh what the first `i` digit pairs
and the carry in weigh. -/
def VInv (n : Nat) (neg : Bool) (i : Nat) (v : Nat → Int) (xs : List Int) : Prop :=
  xs.length = 2 * n + 1 + 3 * i ∧ (∀ j < 2 * n, xs.getD j 0 = v j) ∧
    0 ≤ xs.getD (2 * n + 3 * i) 0 ∧ xs.getD (2 * n + 3 * i) 0 ≤ 1 ∧
    (∀ k < i, 0 ≤ xs.getD (msgWire n k) 0 ∧ xs.getD (msgWire n k) 0 ≤ 3) ∧
    val (fun k => xs.getD (msgWire n k) 0) i + xs.getD (2 * n + 3 * i) 0 * 4 ^ i =
      val (fun k => v k + bdig neg (v (n + k))) i + cin neg

theorem block_eval (n : Nat) (neg : Bool) (i : Nat) (hi : i < n) (v : Nat → Int)
    (hv : ∀ j < 2 * n, 0 ≤ v j ∧ v j ≤ 3) (xs : List Int) (h : VInv n neg i v xs) :
    VInv n neg (i + 1) v (evalV v xs (block n neg i)) := by
  obtain ⟨hl, hin, c0, c1, hmsg, hsum⟩ := h
  have ha := hin i (by omega)
  have hb := hin (n + i) (by omega)
  generalize hc : xs.getD (2 * n + 3 * i) 0 = c at c0 c1 hsum
  obtain ⟨a0, a1⟩ := hv i (by omega)
  obtain ⟨b0, b1⟩ := bdig_bound neg (hv (n + i) (by omega)).1 (hv (n + i) (by omega)).2
  let S := v i + bdig neg (v (n + i)) + c
  have hlin : linV xs (terms n neg i) + bk neg = S := by
    simp only [terms, linV, ha, hb, hc, S, bdig]; omega
  have e : evalV v xs (block n neg i) = xs ++ [S, S % 4, S / 4] := by
    simp only [block, evalV, stepV, hlin]
    rw [show 2 * n + 1 + 3 * i = xs.length by omega]
    simp only [List.append_assoc, List.cons_append, List.nil_append, getD_append_len0,
      List.getD_cons_zero]
    rw [lut_mod (by omega) (by omega), lut_div (by omega) (by omega)]
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
    have hS : S * 4 ^ i = v i * 4 ^ i + bdig neg (v (n + i)) * 4 ^ i + c * 4 ^ i := by
      simp only [S, Int.add_mul]
    rw [Int.pow_succ, show S / 4 * (4 ^ i * 4) = 4 * (S / 4 * 4 ^ i) by
      rw [Int.mul_comm (4 ^ i) 4, ← Int.mul_assoc, Int.mul_comm (S / 4) 4, Int.mul_assoc], Int.add_mul]
    omega

theorem blocks_eval (n : Nat) (neg : Bool) (v : Nat → Int) (hv : ∀ j < 2 * n, 0 ≤ v j ∧ v j ≤ 3) :
    ∀ i ≤ n, VInv n neg i v (evalV v [] (prefixGates n neg ++ (List.range i).flatMap (block n neg))) := by
  intro i
  induction i with
  | zero =>
    intro _
    have e : evalV v [] (prefixGates n neg) = (List.range (2 * n)).map v ++ [cin neg] := by
      simp [prefixGates, evalV_append, evalV_inputs, evalV, stepV, linV]
    simp only [List.range_zero, List.flatMap_nil, List.append_nil, e]
    refine ⟨by simp, fun j hj => ?_, ?_, ?_, fun k hk => absurd hk (by omega), by simp [val]⟩
    · rw [getD_append_lt _ _ _ (by simpa using hj)]; simp [List.getD_eq_getElem?_getD, hj]
    all_goals cases neg <;> simp [cin]
  | succ i ih =>
    intro hi
    rw [List.range_succ, List.flatMap_append, ← List.append_assoc, evalV_append,
      List.flatMap_singleton]
    exact block_eval n neg i (by omega) v hv _ (by simpa [evalV_append] using ih (by omega))

/-- The output digits. -/
def outDigits (n : Nat) (xs : List Int) (k : Nat) : Int := xs.getD (msgWire n k) 0

/-- The output digits are those of `(A + B' + cin) mod 4^n`, `B'` the second
operand's digits through `bdig`. -/
theorem radix_digits (n : Nat) (neg : Bool) (v : Nat → Int) (hv : ∀ j < 2 * n, 0 ≤ v j ∧ v j ≤ 3) :
    (∀ k < n, 0 ≤ outDigits n (evalV v [] (radixGates n neg)) k ∧
      outDigits n (evalV v [] (radixGates n neg)) k ≤ 3) ∧
    val (outDigits n (evalV v [] (radixGates n neg))) n =
      (val v n + val (fun k => bdig neg (v (n + k))) n + cin neg) % 4 ^ n := by
  obtain ⟨-, -, -, -, hmsg, hsum⟩ := blocks_eval n neg v hv n (Nat.le_refl n)
  refine ⟨hmsg, ?_⟩
  obtain ⟨l, u⟩ := val_bound n hmsg
  rw [← val_add, ← hsum, Int.add_mul_emod_self_right, Int.emod_eq_of_lt l u]
  rfl

/-- **The adder computes `(A + B) mod 4^n`** on digits `v`: `A`'s are `v 0 … v (n-1)`,
`B`'s are `v n … v (2n-1)`. -/
theorem add_digits (n : Nat) (v : Nat → Int) (hv : ∀ j < 2 * n, 0 ≤ v j ∧ v j ≤ 3) :
    val (outDigits n (evalV v [] (addGates n))) n = (val v n + val (fun k => v (n + k)) n) % 4 ^ n := by
  have hb : val (fun k => bdig false (v (n + k))) n = val (fun k => v (n + k)) n :=
    val_congr n fun k _ => by simp [bdig, bw, bk]
  rw [(radix_digits n false v hv).2, hb]
  simp [cin]

/-- **The subtracter computes `(A - B) mod 4^n`.** -/
theorem sub_digits (n : Nat) (v : Nat → Int) (hv : ∀ j < 2 * n, 0 ≤ v j ∧ v j ≤ 3) :
    val (outDigits n (evalV v [] (subGates n))) n = (val v n - val (fun k => v (n + k)) n) % 4 ^ n := by
  have hb : val (fun k => bdig true (v (n + k))) n = val (fun k => 3 - v (n + k)) n :=
    val_congr n fun k _ => by simp [bdig, bw, bk]; omega
  rw [(radix_digits n true v hv).2, hb, val_compl]
  simp only [cin, ite_true]
  rw [show val v n + (4 ^ n - 1 - val (fun k => v (n + k)) n) + 1 =
      val v n - val (fun k => v (n + k)) n + 4 ^ n by omega, ← Int.emod_eq_add_self_emod]

/-- **Encrypted, the program decrypts to its cleartext digits**, at any width,
under the hypotheses of `Noise.bootstrapped_sound`. -/
theorem radix_sound (n : Nat) (neg : Bool) (delta fresh : Nat)
    (hdec : 2 * (tfhe22.maxLevel * fresh) < delta)
    (boots : Nat → Boot) (inp : Nat → Ct) (hinp : Fresh tfhe22 fresh inp)
    (hgood : CallsGood fresh boots inp [] (radixGates n neg)) :
    val (fun k => decode delta ((evalCt boots inp [] (radixGates n neg)).getD (msgWire n k) zeroCt)) n =
      val (outDigits n (evalV (fun j => (inp j).m) [] (radixGates n neg))) n :=
  val_congr n fun k hk => bootstrapped_sound tfhe22 delta fresh hdec (radixProg n neg)
    (radix_check n neg) boots inp hinp hgood _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)

theorem fresh_digits {fresh : Nat} {inp : Nat → Ct} (hinp : Fresh tfhe22 fresh inp) (n : Nat) :
    ∀ j < 2 * n, 0 ≤ (inp j).m ∧ (inp j).m ≤ 3 := fun j _ => ⟨(hinp j).1, (hinp j).2.1⟩

/-! ## Two's complement: the 32-bit word -/

/-- A 32-bit two's-complement pattern read as a signed word. -/
def signed32 (u : Int) : Int := if u < 2 ^ 31 then u else u - 2 ^ 32

theorem half32 : Range.half 32 = 2 ^ 31 := by decide

/-- Adding two's-complement patterns modulo `2^32` is `Range.wrap 32` of the sum. -/
theorem signed32_add (a b : Int) :
    signed32 ((a % 2 ^ 32 + b % 2 ^ 32) % 2 ^ 32) = Range.wrap 32 (a + b) := by
  simp only [signed32, Range.wrap, half32]
  split <;> omega

/-- Subtracting two's-complement patterns modulo `2^32` is `Range.wrap 32` of
the difference. -/
theorem signed32_sub (a b : Int) :
    signed32 ((a % 2 ^ 32 - b % 2 ^ 32) % 2 ^ 32) = Range.wrap 32 (a - b) := by
  simp only [signed32, Range.wrap, half32]
  split <;> omega

/-- The 16 blocks of the first operand encode `a`, those of the second `b`. -/
def Encodes32 (inp : Nat → Ct) (a b : Int) : Prop :=
  val (fun k => (inp k).m) 16 = a % 2 ^ 32 ∧ val (fun k => (inp (16 + k)).m) 16 = b % 2 ^ 32

/-- The decrypted 16 output blocks of `radixGates 16 neg`, read as a signed word. -/
def result32 (neg : Bool) (delta : Nat) (boots : Nat → Boot) (inp : Nat → Ct) : Int :=
  signed32 (val (fun k => decode delta ((evalCt boots inp [] (radixGates 16 neg)).getD
    (msgWire 16 k) zeroCt)) 16)

/-- **Ripple-carry addition of 16 blocks is `Range.wrapped 32` of `add`.** -/
theorem add_wrap32 (delta fresh : Nat) (hdec : 2 * (tfhe22.maxLevel * fresh) < delta)
    (boots : Nat → Boot) (inp : Nat → Ct) (hinp : Fresh tfhe22 fresh inp)
    (hgood : CallsGood fresh boots inp [] (addGates 16))
    (a b : Int) (he : Encodes32 inp a b) :
    result32 false delta boots inp = Range.wrapped 32 ["add", "x", "y"] [a, b] := by
  rw [result32, radix_sound 16 false delta fresh hdec boots inp hinp hgood,
    add_digits 16 _ (fresh_digits hinp 16), he.1, he.2, show (4 : Int) ^ 16 = 2 ^ 32 by decide,
    signed32_add]
  rfl

/-- **Ripple-carry subtraction of 16 blocks is `Range.wrapped 32` of `subtract`.** -/
theorem sub_wrap32 (delta fresh : Nat) (hdec : 2 * (tfhe22.maxLevel * fresh) < delta)
    (boots : Nat → Boot) (inp : Nat → Ct) (hinp : Fresh tfhe22 fresh inp)
    (hgood : CallsGood fresh boots inp [] (subGates 16))
    (a b : Int) (he : Encodes32 inp a b) :
    result32 true delta boots inp = Range.wrapped 32 ["subtract", "x", "y"] [a, b] := by
  rw [result32, radix_sound 16 true delta fresh hdec boots inp hinp hgood,
    sub_digits 16 _ (fresh_digits hinp 16), he.1, he.2, show (4 : Int) ^ 16 = 2 ^ 32 by decide,
    signed32_sub]
  rfl

example : check tfhe22 (radixProg 16 false) = true := radix_check 16 false
example : pbsCount (radixProg 16 true) = 32 := by decide

end TclMesh.Radix
