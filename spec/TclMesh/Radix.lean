import TclMesh.Noise
import TclMesh.Range

/-!
# Radix integers as block gate programs: addition, subtraction, select

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
  result is `Range.wrapped 32` of `add`, respectively `subtract`;
* `sel_check`, `sel_digits`, `sel_wrap32`: oblivious `select c a b` on a
  condition bit, two bootstraps per block, accepted at every width and equal
  to `Range.wrapped 32` of `select` at 16 blocks.

Each program's inputs are fresh blocks; composing programs (a comparison's
bit feeding `select`, say) means checking the composed gate program.

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

/-! ## Oblivious select

`select c a b` on words, with `c` a block holding a bit: block `i` bootstraps
`4c + aᵢ` through `lutA` (`aᵢ` when `c = 1`, else `0`) and `4c + bᵢ` through
`lutB` (`bᵢ` when `c = 0`, else `0`), and adds the two. Each block costs two
bootstraps, and `4c + aᵢ` reaches exactly the limits: cleartext 15, level 5.
Wires: `0` is `c`, `1 … n` `a`'s blocks, `n+1 … 2n` `b`'s, and block `i` adds
five wires from `2n + 1 + 5i`. -/

def lutA : List Int := (List.range 16).map fun x => if 4 ≤ x then (((x - 4) % 4 : Nat) : Int) else 0
def lutB : List Int := (List.range 16).map fun (x : Nat) => if x < 4 then (x : Int) else 0

def selBase (n i : Nat) : Nat := 2 * n + 1 + 5 * i
def outWire (n k : Nat) : Nat := selBase n k + 4

def selBlock (n i : Nat) : List Gate :=
  [.lin [(4, 0), (1, 1 + i)] 0, .pbs lutA 3 (selBase n i),
    .lin [(4, 0), (1, n + 1 + i)] 0, .pbs lutB 3 (selBase n i + 2),
    .lin [(1, selBase n i + 1), (1, selBase n i + 3)] 0]

def selInputs (n : Nat) : List Gate := (List.range (2 * n + 1)).map Gate.input

def selGates (n : Nat) : List Gate := selInputs n ++ (List.range n).flatMap (selBlock n)

def selProg (n : Nat) : Prog := ⟨selGates n, (List.range n).map (outWire n)⟩

def SAInv (n i : Nat) (s : List Abs) : Prop :=
  s.length = 2 * n + 1 + 5 * i ∧ (∀ j < 2 * n + 1, s.getD j zeroAbs = ⟨0, 3, 1⟩) ∧
    ∀ k < i, s.getD (outWire n k) zeroAbs = ⟨0, 6, 2⟩

theorem selBlock_check (n i : Nat) (hi : i < n) (s : List Abs) (h : SAInv n i s) :
    ∃ s', analyze tfhe22 s (selBlock n i) = some s' ∧ SAInv n (i + 1) s' := by
  obtain ⟨hl, hin, hout⟩ := h
  have pre : ∀ j < 2 * n + 1, ∀ l', (s ++ l').getD j zeroAbs = ⟨0, 3, 1⟩ := fun j hj l' => by
    rw [getD_append_lt _ _ _ (by omega)]; exact hin j hj
  have hA : lutIn lutA 3 = true := by decide
  have hB : lutIn lutB 3 = true := by decide
  refine ⟨s ++ [⟨0, 15, 5⟩, ⟨0, 3, 1⟩, ⟨0, 15, 5⟩, ⟨0, 3, 1⟩, ⟨0, 6, 2⟩], ?_, ?_⟩
  · simp only [selBlock, selBase, analyze, checkedStep, stepAbs, linLo, linHi, linLevel,
      hin 0 (by omega), hin (1 + i) (by omega), List.all_cons, List.all_nil]
    rw [show 2 * n + 1 + 5 * i = s.length by omega]
    simp only [List.append_assoc, List.cons_append, List.nil_append, getD_append_len0,
      getD_append_len, List.getD_cons_zero, List.getD_cons_succ, pre 0 (by omega),
      pre (n + 1 + i) (by omega)]
    simp [admissible, tfhe22, hA, hB, show 0 < s.length by omega, show 1 + i < s.length by omega,
      show n + 1 + i < s.length + 2 by omega]
  · refine ⟨by simp [hl]; omega, fun j hj => pre j hj _, fun k hk => ?_⟩
    rcases Nat.lt_or_ge k i with hk' | hk'
    · rw [getD_append_lt _ _ _ (by simp [outWire, selBase]; omega)]; exact hout k hk'
    · rw [show outWire n k = s.length + 4 by simp [outWire, selBase]; omega, getD_append_len]; rfl

theorem selBlocks_check (n : Nat) : ∀ i ≤ n, ∃ s,
    analyze tfhe22 [] (selInputs n ++ (List.range i).flatMap (selBlock n)) = some s ∧ SAInv n i s := by
  intro i
  induction i with
  | zero =>
    intro _
    have hD : admissible tfhe22 ⟨0, tfhe22.msgMax, 1⟩ = true := by decide
    refine ⟨(List.range (2 * n + 1)).map fun _ => ⟨0, 3, 1⟩, ?_, by simp, fun j hj => ?_,
      fun k hk => absurd hk (by omega)⟩
    · simpa [selInputs, tfhe22] using analyze_inputs tfhe22 hD [] (List.range (2 * n + 1))
    · simp [List.getD_eq_getElem?_getD, hj]
  | succ i ih =>
    intro hi
    obtain ⟨s, hs, hI⟩ := ih (by omega)
    obtain ⟨s', hs', hI'⟩ := selBlock_check n i (by omega) s hI
    exact ⟨s', by rw [List.range_succ, List.flatMap_append, ← List.append_assoc, analyze_append, hs,
      List.flatMap_singleton]; exact hs', hI'⟩

/-- **The checker accepts `select` at every width.** -/
theorem sel_check (n : Nat) : check tfhe22 (selProg n) = true := by
  obtain ⟨s, hs, hl, -, hout⟩ := selBlocks_check n n (Nat.le_refl n)
  simp only [check, selProg, selGates, hs, List.all_eq_true, List.mem_map, List.mem_range,
    Bool.and_eq_true, decide_eq_true_eq]
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨by simp [outWire, selBase]; omega, by rw [hout k hk]; decide⟩

theorem lut_sel {c x : Int} (hc : c = 0 ∨ c = 1) (h0 : 0 ≤ x) (h1 : x ≤ 3) :
    lutA.getD (4 * c + x).toNat 0 = (if c = 1 then x else 0) ∧
      lutB.getD (4 * c + x).toNat 0 = (if c = 1 then 0 else x) := by
  have h : ∀ m < 4, lutA.getD m 0 = 0 ∧ lutB.getD m 0 = (m : Int) ∧
      lutA.getD (4 + m) 0 = (m : Int) ∧ lutB.getD (4 + m) 0 = 0 := by decide
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨e0, e1, e2, e3⟩ := h m (by omega)
  rcases hc with rfl | rfl
  · rw [show (4 * (0 : Int) + m).toNat = m by omega, e0, e1]; simp
  · rw [show (4 * (1 : Int) + m).toNat = 4 + m by omega, e2, e3]; simp

def SVInv (n i : Nat) (v : Nat → Int) (xs : List Int) : Prop :=
  xs.length = 2 * n + 1 + 5 * i ∧ (∀ j < 2 * n + 1, xs.getD j 0 = v j) ∧
    ∀ k < i, xs.getD (outWire n k) 0 = if v 0 = 1 then v (1 + k) else v (n + 1 + k)

theorem selBlock_eval (n i : Nat) (hi : i < n) (v : Nat → Int) (hc : v 0 = 0 ∨ v 0 = 1)
    (hv : ∀ j < 2 * n + 1, 0 ≤ v j ∧ v j ≤ 3) (xs : List Int) (h : SVInv n i v xs) :
    SVInv n (i + 1) v (evalV v xs (selBlock n i)) := by
  obtain ⟨hl, hin, hout⟩ := h
  have pre : ∀ j < 2 * n + 1, ∀ l', (xs ++ l').getD j 0 = v j := fun j hj l' => by
    rw [getD_append_lt _ _ _ (by omega)]; exact hin j hj
  obtain ⟨a0, a1⟩ := hv (1 + i) (by omega)
  obtain ⟨b0, b1⟩ := hv (n + 1 + i) (by omega)
  obtain ⟨sa, -⟩ := lut_sel hc a0 a1
  obtain ⟨-, sb⟩ := lut_sel hc b0 b1
  let A := if v 0 = 1 then v (1 + i) else 0
  let B := if v 0 = 1 then 0 else v (n + 1 + i)
  have e : evalV v xs (selBlock n i) =
      xs ++ [4 * v 0 + v (1 + i), A, 4 * v 0 + v (n + 1 + i), B, A + B] := by
    simp only [selBlock, selBase, evalV, stepV, linV, hin 0 (by omega), hin (1 + i) (by omega)]
    rw [show 2 * n + 1 + 5 * i = xs.length by omega]
    simp only [List.append_assoc, List.cons_append, List.nil_append, getD_append_len0,
      getD_append_len, List.getD_cons_zero, List.getD_cons_succ, pre 0 (by omega),
      pre (n + 1 + i) (by omega), Int.one_mul, Int.add_zero]
    rw [sa, sb]
  rw [e]
  refine ⟨by simp [hl]; omega, fun j hj => pre j hj _, fun k hk => ?_⟩
  rcases Nat.lt_or_ge k i with hk' | hk'
  · rw [getD_append_lt _ _ _ (by simp [outWire, selBase]; omega)]; exact hout k hk'
  · rw [show outWire n k = xs.length + 4 by simp [outWire, selBase]; omega, getD_append_len,
      show k = i by omega]
    simp only [A, B, List.getD_cons_succ, List.getD_cons_zero]
    split <;> omega

theorem selBlocks_eval (n : Nat) (v : Nat → Int) (hc : v 0 = 0 ∨ v 0 = 1)
    (hv : ∀ j < 2 * n + 1, 0 ≤ v j ∧ v j ≤ 3) :
    ∀ i ≤ n, SVInv n i v (evalV v [] (selInputs n ++ (List.range i).flatMap (selBlock n))) := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [List.range_zero, List.flatMap_nil, List.append_nil, selInputs, evalV_inputs,
      List.nil_append]
    exact ⟨by simp, fun j hj => by simp [List.getD_eq_getElem?_getD, hj],
      fun k hk => absurd hk (by omega)⟩
  | succ i ih =>
    intro hi
    rw [List.range_succ, List.flatMap_append, ← List.append_assoc, evalV_append,
      List.flatMap_singleton]
    exact selBlock_eval n i (by omega) v hc hv _ (by simpa [evalV_append] using ih (by omega))

/-- **`select` picks `A` when `c = 1` and `B` when `c = 0`**, digit by digit. -/
theorem sel_digits (n : Nat) (v : Nat → Int) (hc : v 0 = 0 ∨ v 0 = 1)
    (hv : ∀ j < 2 * n + 1, 0 ≤ v j ∧ v j ≤ 3) :
    val (fun k => (evalV v [] (selGates n)).getD (outWire n k) 0) n =
      if v 0 = 1 then val (fun k => v (1 + k)) n else val (fun k => v (n + 1 + k)) n := by
  obtain ⟨-, -, hout⟩ := selBlocks_eval n v hc hv n (Nat.le_refl n)
  unfold selGates
  rw [val_congr n fun k hk => hout k hk]
  split <;> exact val_congr n fun k _ => by simp [*]

theorem signed32_mod {a : Int} (lo : Range.wordMin 32 ≤ a) (hi : a ≤ Range.wordMax 32) :
    signed32 (a % 2 ^ 32) = a := by
  simp only [Range.wordMin, Range.wordMax, half32] at lo hi
  simp only [signed32]; split <;> omega

/-- **Encrypted `select` on 16 blocks is `Range.wrapped 32` of `select`**, for a
condition bit `c` and words `a`, `b`, under the hypotheses of
`Noise.bootstrapped_sound`. -/
theorem sel_wrap32 (delta fresh : Nat) (hdec : 2 * (tfhe22.maxLevel * fresh) < delta)
    (boots : Nat → Boot) (inp : Nat → Ct) (hinp : Fresh tfhe22 fresh inp)
    (hgood : CallsGood fresh boots inp [] (selGates 16))
    (c a b : Int) (hc : (inp 0).m = c) (hbit : c = 0 ∨ c = 1)
    (ha : val (fun k => (inp (1 + k)).m) 16 = a % 2 ^ 32)
    (hb : val (fun k => (inp (17 + k)).m) 16 = b % 2 ^ 32)
    (wa : Range.wordMin 32 ≤ a ∧ a ≤ Range.wordMax 32) (wb : Range.wordMin 32 ≤ b ∧ b ≤ Range.wordMax 32) :
    signed32 (val (fun k => decode delta ((evalCt boots inp [] (selGates 16)).getD (outWire 16 k) zeroCt)) 16) =
      Range.wrapped 32 ["select", "c", "x", "y"] [c, a, b] := by
  have hv : ∀ j < 2 * 16 + 1, 0 ≤ (inp j).m ∧ (inp j).m ≤ 3 := fun j _ => ⟨(hinp j).1, (hinp j).2.1⟩
  have key : ∀ k < 16, decode delta ((evalCt boots inp [] (selGates 16)).getD (outWire 16 k) zeroCt) =
      (evalV (fun j => (inp j).m) [] (selGates 16)).getD (outWire 16 k) 0 := fun k hk =>
    bootstrapped_sound tfhe22 delta fresh hdec (selProg 16) (sel_check 16)
      boots inp hinp hgood _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  rw [val_congr 16 key, sel_digits 16 _ (hc ▸ hbit) hv, hc]
  simp only [Range.wrapped, Range.semWith]
  rcases hbit with rfl | rfl
  · simp only [show (17 : Nat) = 16 + 1 by rfl] at hb; simp [hb]; exact signed32_mod wb.1 wb.2
  · simp [ha]; exact signed32_mod wa.1 wa.2

example : pbsCount (selProg 16) = 32 := by decide

end TclMesh.Radix
