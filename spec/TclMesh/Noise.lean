/-!
# Noise budgets: bootstrapped circuits decrypt at any depth

A TFHE ciphertext encrypts a cleartext `m` as a phase `Δ·m + e`; decryption
rounds the phase to the nearest multiple of `Δ` and is correct whenever
`2|e| < Δ`. Linear operations combine phases, so their noises combine too: a
sum `Σ wᵢ·cᵢ + k` has noise `Σ wᵢ·eᵢ`, bounded by `Σ |wᵢ|·|eᵢ|`. Unchecked,
noise grows with depth. A programmable bootstrap (PBS: keyswitch, modulus
switch, blind rotation of a lookup table) reads a ciphertext whose noise and
cleartext are within bounds and returns `lut[m]` with fresh noise, whatever
the depth of its input.

TFHE-rs's checked shortint operations track a degree and a noise level;
unchecked APIs can bypass their checks. Its nominal noise metadata supports
a target PBS error rate, not the absolute phase bound assumed in this model.
The computation parameters selected by `backends/tfhe` have message modulus
4, carry modulus 4, `max_degree = 15`, and `max_noise_level = 5`.

This file states that discipline as a static checker over block-level gate
programs (`check`) and proves it sound (`bootstrapped_sound`): if the checker
accepts and every bootstrap the evaluation performs meets its contract, every
output decrypts to the cleartext evaluation. No hypothesis mentions depth;
`chain_check` exhibits accepted circuits of every depth, and `leveled_rejected`
shows that without bootstraps the same discipline stops after two doublings.

Named hypotheses, outside this model:

* `CallsGood`: the result of each actual PBS invocation has the specified
  cleartext and bounded noise. No claim quantifies over unused arguments.
* `Fresh`: input encryptions have bounded noise and cleartexts in range.
* `2·maxLevel·fresh < Δ`: an explicit integer-phase decoding premise.

`checkedStep` requires EVERY wire to have a nonnegative interval below
`maxDeg` and an admitted noise level, including unused intermediates and
PBS outputs. The integer phase is a lift, not the unsigned torus residue:
negative noise at cleartext zero can cross the torus boundary. The separate
modular rounding theorem below states the exact wrap correspondence.

This is a conditional abstract block theorem. It does not verify TFHE-rs's
native algorithms, nor identify its statistical noise metadata with a hard
absolute phase bound. See docs/noise-correspondence.md for the versioned audit
and the additional conditional assumptions needed for a probability claim.
-/

namespace TclMesh.Noise

/-! ## Ciphertexts and decryption -/

/-- An LWE ciphertext seen through its phase `Δ·m + e`: the cleartext and the
noise. Keys and masks are abstracted away. -/
structure Ct where
  m : Int
  e : Int
  deriving Repr, DecidableEq

def zeroCt : Ct := ⟨0, 0⟩

/-- Round the phase to the nearest multiple of `Δ`. -/
def decode (delta : Nat) (c : Ct) : Int :=
  ((delta : Int) * c.m + c.e + ((delta / 2 : Nat) : Int)) / (delta : Int)

/-- **Decryption is correct while `2|e| < Δ`.** -/
theorem decode_correct {delta : Nat} {c : Ct} (h : 2 * c.e.natAbs < delta) :
    decode delta c = c.m := by
  unfold decode
  have hd : (delta : Int) ≠ 0 := by omega
  have hb : 0 ≤ c.e + ((delta / 2 : Nat) : Int) ∧ c.e + ((delta / 2 : Nat) : Int) < delta := by
    rcases Int.natAbs_eq c.e with he | he <;> omega
  rw [show (delta : Int) * c.m + c.e + ((delta / 2 : Nat) : Int)
      = (c.e + ((delta / 2 : Nat) : Int)) + (delta : Int) * c.m by omega,
    Int.add_mul_ediv_left _ _ hd, Int.ediv_eq_zero_of_lt hb.1 hb.2, Int.zero_add]

/-! ## Gate programs -/

/-- The per-block discipline: a fresh cleartext lies in `[0, msgMax]`; a
bootstrap reads cleartexts in `[0, maxDeg]` (message and carry, padding bit
clear) and noise levels up to `maxLevel`, as does decryption. -/
structure Discipline where
  msgMax : Nat
  maxDeg : Nat
  maxLevel : Nat

/-- `PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128`, the `backends/tfhe` parameters. -/
def tfhe22 : Discipline := ⟨3, 15, 5⟩

/-- A straight-line program over blocks; gate `j` defines wire `j` from
earlier wires. -/
inductive Gate where
  /-- a fresh encryption of input `i` -/
  | input (i : Nat)
  /-- `Σ w·wire j + k`, cleartext weights and constant -/
  | lin (terms : List (Int × Nat)) (k : Int)
  /-- a programmable bootstrap of wire `j` through `lut`, whose entries lie in `[0, hi]` -/
  | pbs (lut : List Int) (hi : Nat) (j : Nat)
  deriving Repr

structure Prog where
  gates : List Gate
  outputs : List Nat
  deriving Repr

def pbsCount (p : Prog) : Nat := (p.gates.filter fun | .pbs .. => true | _ => false).length

/-! ## The checker: degrees and noise levels, from public data -/

/-- What the checker knows of a wire: its cleartext interval and noise level. -/
structure Abs where
  lo : Int
  hi : Int
  level : Nat
  deriving Repr, DecidableEq

def zeroAbs : Abs := ⟨0, 0, 0⟩

def linLo (s : List Abs) : List (Int × Nat) → Int
  | [] => 0
  | (w, j) :: ts => (if 0 ≤ w then w * (s.getD j zeroAbs).lo else w * (s.getD j zeroAbs).hi) + linLo s ts

def linHi (s : List Abs) : List (Int × Nat) → Int
  | [] => 0
  | (w, j) :: ts => (if 0 ≤ w then w * (s.getD j zeroAbs).hi else w * (s.getD j zeroAbs).lo) + linHi s ts

/-- The noise level of a linear combination: `Σ |w|·level`, TFHE-rs's accounting. -/
def linLevel (s : List Abs) : List (Int × Nat) → Nat
  | [] => 0
  | (w, j) :: ts => w.natAbs * (s.getD j zeroAbs).level + linLevel s ts

def lutIn (lut : List Int) (hi : Nat) : Bool := lut.all fun v => decide (0 ≤ v) && decide (v ≤ (hi : Int))

def stepAbs (D : Discipline) (s : List Abs) : Gate → Option Abs
  | .input _ => some ⟨0, D.msgMax, 1⟩
  | .lin ts k =>
    if ts.all (fun t => decide (t.2 < s.length)) then
      some ⟨linLo s ts + k, linHi s ts + k, linLevel s ts⟩
    else none
  | .pbs lut hi j =>
    let a := s.getD j zeroAbs
    if decide (j < s.length) && decide (0 ≤ a.lo) && decide (a.hi ≤ (D.maxDeg : Int)) &&
        decide (a.level ≤ D.maxLevel) && lutIn lut hi then
      some ⟨0, hi, 1⟩
    else none

/-- Representable, ordered interval and an admitted noise level. -/
def admissible (D : Discipline) (a : Abs) : Bool :=
  decide (0 ≤ a.lo) && decide (a.lo ≤ a.hi) &&
    decide (a.hi ≤ (D.maxDeg : Int)) && decide (a.level ≤ D.maxLevel)

/-- Validate every result, not just operands of PBS or selected outputs. -/
def checkedStep (D : Discipline) (s : List Abs) (g : Gate) : Option Abs :=
  (stepAbs D s g).bind fun a => if admissible D a then some a else none

def analyze (D : Discipline) : List Abs → List Gate → Option (List Abs)
  | s, [] => some s
  | s, g :: gs => (checkedStep D s g).bind fun a => analyze D (s ++ [a]) gs

/-- Accept a program when every bootstrap input is within degree and noise
level, every wire is representable, and every output is decryptable. -/
def check (D : Discipline) (p : Prog) : Bool :=
  match analyze D [] p.gates with
  | some s => p.outputs.all fun o => decide (o < s.length) && admissible D (s.getD o zeroAbs)
  | none => false

/-! ## Evaluation: cleartext, and over ciphertext -/

def linV (xs : List Int) : List (Int × Nat) → Int
  | [] => 0
  | (w, j) :: ts => w * xs.getD j 0 + linV xs ts

def stepV (inp : Nat → Int) (xs : List Int) : Gate → Int
  | .input i => inp i
  | .lin ts k => linV xs ts + k
  | .pbs lut _ j => lut.getD (xs.getD j 0).toNat 0

def evalV (inp : Nat → Int) : List Int → List Gate → List Int
  | xs, [] => xs
  | xs, g :: gs => evalV inp (xs ++ [stepV inp xs g]) gs

/-- A bootstrap: keyswitch, modulus switch and blind rotation of a lookup table. -/
abbrev Boot := List Int → Ct → Ct

/-- The bootstrap at wire `n` is `boots n`. No independence is assumed. -/
def stepCt (boots : Nat → Boot) (inp : Nat → Ct) (cs : List Ct) : Gate → Ct
  | .input i => inp i
  | .lin ts k => ⟨linV (cs.map Ct.m) ts + k, linV (cs.map Ct.e) ts⟩
  | .pbs lut _ j => boots cs.length lut (cs.getD j zeroCt)

def evalCt (boots : Nat → Boot) (inp : Nat → Ct) : List Ct → List Gate → List Ct
  | cs, [] => cs
  | cs, g :: gs => evalCt boots inp (cs ++ [stepCt boots inp cs g]) gs

/-- Success of ONE invocation at its actual LUT and ciphertext. This is
an event, not a universal property of the sampled bootstrap function. -/
def CallGood (fresh : Nat) (b : Boot) (lut : List Int) (c : Ct) : Prop :=
  (b lut c).m = lut.getD c.m.toNat 0 ∧ (b lut c).e.natAbs ≤ fresh

/-- Actual invocation contract of a single gate. -/
def StepGood (fresh : Nat) (boots : Nat → Boot) (cs : List Ct) : Gate → Prop
  | .pbs lut _ j => CallGood fresh (boots cs.length) lut (cs.getD j zeroCt)
  | _ => True

/-- Success along the actual evolving execution, including prior PBS results.
There is no quantifier over unused LUTs or counterfactual ciphertexts. -/
def CallsGood (fresh : Nat) (boots : Nat → Boot) (inp : Nat → Ct) :
    List Ct → List Gate → Prop
  | _, [] => True
  | cs, g :: gs => StepGood fresh boots cs g ∧
      CallsGood fresh boots inp (cs ++ [stepCt boots inp cs g]) gs

/-- Fresh encryptions: cleartext in `[0, msgMax]`, noise at most `fresh`. -/
def Fresh (D : Discipline) (fresh : Nat) (inp : Nat → Ct) : Prop :=
  ∀ i, 0 ≤ (inp i).m ∧ (inp i).m ≤ (D.msgMax : Int) ∧ (inp i).e.natAbs ≤ fresh

/-! ## Soundness -/

/-- Wires agree with the cleartext evaluation, lie in their intervals, and
carry noise at most `level·fresh`. -/
def Inv (fresh : Nat) (s : List Abs) (cs : List Ct) (xs : List Int) : Prop :=
  cs.map Ct.m = xs ∧ s.length = cs.length ∧
    ∀ j < cs.length, (s.getD j zeroAbs).lo ≤ xs.getD j 0 ∧ xs.getD j 0 ≤ (s.getD j zeroAbs).hi ∧
      (cs.getD j zeroCt).e.natAbs ≤ (s.getD j zeroAbs).level * fresh

theorem getD_map_e (cs : List Ct) (j : Nat) : (cs.map Ct.e).getD j 0 = (cs.getD j zeroCt).e := by
  simp [List.getD_eq_getElem?_getD]; cases cs[j]? <;> rfl

theorem getD_map_m (cs : List Ct) (j : Nat) : (cs.map Ct.m).getD j 0 = (cs.getD j zeroCt).m := by
  simp [List.getD_eq_getElem?_getD]; cases cs[j]? <;> rfl

theorem getD_snoc_lt {α} (l : List α) (a d : α) {j : Nat} (h : j < l.length) :
    (l ++ [a]).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq {α} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

/-- A linear combination lies in the interval extension of its operands'. -/
theorem lin_bounds (s : List Abs) (xs : List Int)
    (hx : ∀ j < s.length, (s.getD j zeroAbs).lo ≤ xs.getD j 0 ∧ xs.getD j 0 ≤ (s.getD j zeroAbs).hi) :
    ∀ ts : List (Int × Nat), (∀ t ∈ ts, t.2 < s.length) →
      linLo s ts ≤ linV xs ts ∧ linV xs ts ≤ linHi s ts := by
  intro ts
  induction ts with
  | nil => intro _; simp [linLo, linV, linHi]
  | cons t ts ih =>
    obtain ⟨w, j⟩ := t
    intro hts
    obtain ⟨hl, hh⟩ := ih fun t ht => hts t (List.mem_cons_of_mem _ ht)
    obtain ⟨xl, xh⟩ := hx j (hts _ List.mem_cons_self)
    simp only [linLo, linV, linHi]
    split
    · rename_i hw
      exact ⟨Int.add_le_add (Int.mul_le_mul_of_nonneg_left xl hw) hl,
        Int.add_le_add (Int.mul_le_mul_of_nonneg_left xh hw) hh⟩
    · rename_i hw
      have hw : w ≤ 0 := by omega
      exact ⟨Int.add_le_add (Int.mul_le_mul_of_nonpos_left hw xh) hl,
        Int.add_le_add (Int.mul_le_mul_of_nonpos_left hw xl) hh⟩

/-- The noise of a linear combination is at most its level times `fresh`. -/
theorem lin_noise (fresh : Nat) (s : List Abs) (cs : List Ct)
    (he : ∀ j < s.length, (cs.getD j zeroCt).e.natAbs ≤ (s.getD j zeroAbs).level * fresh) :
    ∀ ts : List (Int × Nat), (∀ t ∈ ts, t.2 < s.length) →
      (linV (cs.map Ct.e) ts).natAbs ≤ linLevel s ts * fresh := by
  intro ts
  induction ts with
  | nil => intro _; simp [linV, linLevel]
  | cons t ts ih =>
    obtain ⟨w, j⟩ := t
    intro hts
    have hr := ih fun t ht => hts t (List.mem_cons_of_mem _ ht)
    have hj := he j (hts _ List.mem_cons_self)
    simp only [linV, linLevel, getD_map_e]
    refine Nat.le_trans (Int.natAbs_add_le _ _) ?_
    rw [Int.natAbs_mul, Nat.add_mul, Nat.mul_assoc]
    exact Nat.add_le_add (Nat.mul_le_mul_left _ hj) hr

theorem lutIn_getD {lut : List Int} {hi : Nat} (h : lutIn lut hi = true) (n : Nat) :
    0 ≤ lut.getD n 0 ∧ lut.getD n 0 ≤ (hi : Int) := by
  simp only [lutIn, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [List.getD_eq_getElem?_getD]
  cases hn : lut[n]? with
  | none => simp
  | some v => exact h v (List.mem_of_getElem? hn)

/-- One gate preserves the invariant. -/
theorem step_sound (D : Discipline) (fresh : Nat) (boots : Nat → Boot) (inp : Nat → Ct)
    (hinp : Fresh D fresh inp) (s : List Abs) (cs : List Ct) (g : Gate) (a : Abs)
    (hs : stepAbs D s g = some a) (hI : Inv fresh s cs (cs.map Ct.m))
    (hg : StepGood fresh boots cs g) :
    Inv fresh (s ++ [a]) (cs ++ [stepCt boots inp cs g])
      (cs.map Ct.m ++ [stepV (fun i => (inp i).m) (cs.map Ct.m) g]) := by
  obtain ⟨-, hlen, hw⟩ := hI
  -- the new wire: its value, interval and noise
  have hnew : (stepCt boots inp cs g).m = stepV (fun i => (inp i).m) (cs.map Ct.m) g ∧
      a.lo ≤ stepV (fun i => (inp i).m) (cs.map Ct.m) g ∧
      stepV (fun i => (inp i).m) (cs.map Ct.m) g ≤ a.hi ∧
      (stepCt boots inp cs g).e.natAbs ≤ a.level * fresh := by
    cases g with
    | input i =>
      simp only [stepAbs, Option.some.injEq] at hs; subst hs
      obtain ⟨h0, h1, h2⟩ := hinp i
      exact ⟨rfl, h0, h1, by simpa [stepCt] using h2⟩
    | lin ts k =>
      simp only [stepAbs] at hs
      split at hs
      · rename_i hts
        simp only [Option.some.injEq] at hs; subst hs
        simp only [List.all_eq_true, decide_eq_true_eq] at hts
        obtain ⟨bl, bh⟩ := lin_bounds s (cs.map Ct.m)
          (fun j hj => let h := hw j (hlen ▸ hj); ⟨h.1, h.2.1⟩) ts hts
        exact ⟨rfl, by simp only [stepV]; omega, by simp only [stepV]; omega,
          lin_noise fresh s cs (fun j hj => (hw j (hlen ▸ hj)).2.2) ts hts⟩
      · exact absurd hs (by simp)
    | pbs lut hi j =>
      simp only [stepAbs] at hs
      split at hs
      · rename_i hc
        simp only [Option.some.injEq] at hs; subst hs
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨⟨⟨⟨hj, hlo⟩, hhi⟩, hlev⟩, hlut⟩ := hc
        obtain ⟨xl, xh, xe⟩ := hw j (hlen ▸ hj)
        rw [getD_map_m] at xl xh
        obtain ⟨hm, hn⟩ := hg
        have hv : stepV (fun i => (inp i).m) (cs.map Ct.m) (.pbs lut hi j) =
            lut.getD (cs.getD j zeroCt).m.toNat 0 := by simp only [stepV, getD_map_m]
        obtain ⟨l0, l1⟩ := lutIn_getD hlut ((cs.getD j zeroCt).m.toNat)
        refine ⟨by simp only [stepCt]; rw [hm, hv], by rw [hv]; exact l0, by rw [hv]; exact l1, ?_⟩
        simpa [stepCt] using hn
      · exact absurd hs (by simp)
  refine ⟨by simp [hnew.1], by simp [hlen], fun j hj => ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil] at hj
  rcases Nat.lt_or_ge j cs.length with hj' | hj'
  · rw [getD_snoc_lt _ _ _ (hlen ▸ hj'), getD_snoc_lt _ _ _ (by simpa using hj'),
      getD_snoc_lt _ _ _ hj']
    exact hw j hj'
  · have : j = cs.length := by omega
    subst this
    have e1 := getD_snoc_eq (cs.map Ct.m) (stepV (fun i => (inp i).m) (cs.map Ct.m) g) 0
    rw [List.length_map] at e1
    have e2 := getD_snoc_eq s a zeroAbs
    rw [hlen] at e2
    rw [e1, e2, getD_snoc_eq cs _ zeroCt]
    exact hnew.2

theorem analyze_sound (D : Discipline) (fresh : Nat) (boots : Nat → Boot) (inp : Nat → Ct)
    (hinp : Fresh D fresh inp) :
    ∀ (gs : List Gate) (s : List Abs) (cs : List Ct) (s' : List Abs),
      analyze D s gs = some s' → Inv fresh s cs (cs.map Ct.m) →
      (CallsGood fresh boots inp cs gs) →
      Inv fresh s' (evalCt boots inp cs gs) (evalV (fun i => (inp i).m) (cs.map Ct.m) gs) := by
  intro gs
  induction gs with
  | nil => intro s cs s' h hI _; simp only [analyze, Option.some.injEq] at h; subst h; exact hI
  | cons g gs ih =>
    intro s cs s' h hI hgood
    simp only [analyze, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, hrest⟩ := h
    have hraw : stepAbs D s g = some a := by
      simp only [checkedStep, Option.bind_eq_some_iff] at ha
      obtain ⟨b, hb, hab⟩ := ha
      split at hab
      · simp only [Option.some.injEq] at hab; subst hab; exact hb
      · contradiction
    have hstep := step_sound D fresh boots inp hinp s cs g a hraw hI hgood.1
    have hm : (cs ++ [stepCt boots inp cs g]).map Ct.m =
        cs.map Ct.m ++ [stepV (fun i => (inp i).m) (cs.map Ct.m) g] := by
      simp [hstep.1.symm]
    simp only [evalCt, evalV]
    rw [← hm]
    exact ih _ _ _ hrest (hm ▸ hstep) hgood.2

/-- **Noise-budget soundness of bootstrapped circuits.** If the checker accepts
a gate program, inputs are fresh encryptions, the parameters decrypt every
admitted level, and each bootstrap the evaluation runs (one per `pbs` gate)
meets its contract, then every output decrypts to the cleartext evaluation.
Nothing bounds the program's depth. -/
theorem bootstrapped_sound (D : Discipline) (delta fresh : Nat)
    (hdec : 2 * (D.maxLevel * fresh) < delta) (p : Prog) (hc : check D p = true)
    (boots : Nat → Boot) (inp : Nat → Ct) (hinp : Fresh D fresh inp)
    (hgood : CallsGood fresh boots inp [] p.gates) :
    ∀ o ∈ p.outputs, decode delta ((evalCt boots inp [] p.gates).getD o zeroCt) =
      (evalV (fun i => (inp i).m) [] p.gates).getD o 0 := by
  intro o ho
  unfold check at hc
  split at hc
  · rename_i s hs
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hlt, hadm⟩ := hc o ho
    have hlev : (s.getD o zeroAbs).level ≤ D.maxLevel := by
      simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at hadm
      exact hadm.2
    obtain ⟨hm, hlen, hw⟩ := analyze_sound D fresh boots inp hinp p.gates [] [] s hs
      ⟨rfl, rfl, by simp⟩ hgood
    simp only [List.map_nil] at hm
    have hn := (hw o (hlen ▸ hlt)).2.2
    rw [decode_correct (by have := Nat.mul_le_mul_right fresh hlev; omega), ← hm, getD_map_m]
  · exact absurd hc (by simp)

/-- The checker admits only representable abstract wires, including unused
intermediates. This property is independent of successful bootstraps. -/
theorem analyze_admissible (D : Discipline) (gs : List Gate) (s s' : List Abs)
    (hs : analyze D s gs = some s') (hstart : s.all (admissible D) = true) :
    s'.all (admissible D) = true := by
  induction gs generalizing s with
  | nil =>
    simp only [analyze, Option.some.injEq] at hs
    subst s'; exact hstart
  | cons g gs ih =>
    simp only [analyze, Option.bind_eq_some_iff] at hs
    obtain ⟨a, ha, htail⟩ := hs
    have hadm : admissible D a = true := by
      simp only [checkedStep, Option.bind_eq_some_iff] at ha
      obtain ⟨b, _, hb⟩ := ha
      split at hb
      · rename_i h
        simp only [Option.some.injEq] at hb; subst hb; exact h
      · contradiction
    exact ih _ htail (by simp [List.all_append, hstart, hadm])

/-- Every actual wire is representable on a successful checked execution. -/
theorem bootstrapped_representable (D : Discipline) (fresh : Nat) (p : Prog)
    (hc : check D p = true) (boots : Nat → Boot) (inp : Nat → Ct)
    (hinp : Fresh D fresh inp) (hg : CallsGood fresh boots inp [] p.gates) :
    ∀ j < (evalCt boots inp [] p.gates).length,
      0 ≤ ((evalCt boots inp [] p.gates).getD j zeroCt).m ∧
      ((evalCt boots inp [] p.gates).getD j zeroCt).m ≤ (D.maxDeg : Int) := by
  unfold check at hc
  split at hc
  · rename_i s hs
    have ha := analyze_admissible D p.gates [] s hs (by simp)
    have hI := analyze_sound D fresh boots inp hinp p.gates [] [] s hs
      ⟨rfl, rfl, by simp⟩ hg
    obtain ⟨hm, hlen, hw⟩ := hI
    intro j hj
    have habs := (List.all_eq_true.mp ha) (s.getD j zeroAbs)
      (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen ▸ hj)]; simp)
    simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at habs
    have hb := hw j hj
    rw [← hm, getD_map_m] at hb
    exact ⟨by omega, by omega⟩
  · contradiction

/-- Rounded torus decoding, with a cleartext space including the padding bit. -/
def torusDecode (delta modulus : Int) (c : Ct) : Int :=
  (((delta * c.m + c.e) % (delta * modulus) + delta / 2) / delta) % modulus

/-- Exact native-u64 encoding correspondence at the audited 2+2 parameters:
Δ = 2^59 and q = 32Δ = 2^64. Reduction of a negative phase at zero is allowed.
This models rounding arithmetic, not native LWE/PBS correctness. -/
theorem torus_decode_tfhe22 (c : Ct) (hm : 0 ≤ c.m ∧ c.m ≤ 15)
    (he : 2 * c.e.natAbs < 2^59) : torusDecode (2^59) 32 c = c.m := by
  have hd := decode_correct he
  simp only [decode] at hd
  unfold torusDecode
  change (((576460752303423488 * c.m + c.e) % 18446744073709551616 +
    288230376151711744) / 576460752303423488) % 32 = c.m
  change (576460752303423488 * c.m + c.e + 288230376151711744) / 576460752303423488 = c.m at hd
  omega

/-- Checked output correctness for the audited rounded torus encoding.
This still assumes the modeled phase/actual-call contracts; it is not a
refinement proof for the native cryptographic implementation. -/
theorem bootstrapped_torus_sound (fresh : Nat)
    (hdec : 2 * (tfhe22.maxLevel * fresh) < 2^59)
    (p : Prog) (hc : check tfhe22 p = true) (boots : Nat → Boot) (inp : Nat → Ct)
    (hinp : Fresh tfhe22 fresh inp) (hg : CallsGood fresh boots inp [] p.gates) :
    ∀ o ∈ p.outputs, torusDecode (2^59) 32 ((evalCt boots inp [] p.gates).getD o zeroCt) =
      (evalV (fun i => (inp i).m) [] p.gates).getD o 0 := by
  intro o ho
  unfold check at hc
  split at hc
  · rename_i s hs
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨hlt, hadm⟩ := hc o ho
    simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at hadm
    obtain ⟨hm, hlen, hw⟩ := analyze_sound tfhe22 fresh boots inp hinp p.gates [] [] s hs
      ⟨rfl, rfl, by simp⟩ hg
    have hb := hw o (hlen ▸ hlt)
    simp only [List.map_nil] at hm hb
    rw [← hm, getD_map_m] at hb
    have hmrange : 0 ≤ ((evalCt boots inp [] p.gates).getD o zeroCt).m ∧
        ((evalCt boots inp [] p.gates).getD o zeroCt).m ≤ 15 := by
      simp only [tfhe22] at hadm
      omega
    have he : 2 * ((evalCt boots inp [] p.gates).getD o zeroCt).e.natAbs < 2^59 := by
      have := Nat.mul_le_mul_right fresh hadm.2
      omega
    rw [torus_decode_tfhe22 _ hmrange he, ← hm, getD_map_m]
  · contradiction

/-! ## Depth -/

/-- `x ↦ 2x mod 4` on cleartexts `[0, 15]`. -/
def double : List Int := (List.range 16).map fun n => (2 * n % 4 : Nat)

/-- One stage reading wire `2k`: double it, then bootstrap. -/
def stage (k : Nat) : List Gate := [.lin [(2, 2 * k)] 0, .pbs double 3 (2 * k + 1)]

/-- `n` bootstrapped doublings of one input: depth `2n`. -/
def chain (n : Nat) : Prog := ⟨.input 0 :: (List.range n).flatMap stage, [2 * n]⟩

theorem analyze_append (D : Discipline) :
    ∀ (s : List Abs) (a b : List Gate), analyze D s (a ++ b) = (analyze D s a).bind (analyze D · b) := by
  intro s a
  induction a generalizing s with
  | nil => intro b; simp [analyze]
  | cons g gs ih => intro b; simp only [List.cons_append, analyze, ih]; cases checkedStep D s g <;> simp

theorem getD_getElem {α} {l : List α} {j : Nat} {d a : α} (hj : j < l.length)
    (h : l.getD j d = a) : l[j] = a := by
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h

theorem stage_step (s : List Abs) (k : Nat) (hl : s.length = 2 * k + 1)
    (hlast : s.getD (2 * k) zeroAbs = ⟨0, 3, 1⟩) :
    analyze tfhe22 s (stage k) = some (s ++ [⟨0, 6, 2⟩] ++ [⟨0, 3, 1⟩]) := by
  have h0 := getD_getElem (by omega) hlast
  have hd : lutIn double 3 = true := by decide
  simp [stage, analyze, checkedStep, admissible, stepAbs, linLo, linHi, linLevel, hl, h0, hd, tfhe22,
    List.getD_eq_getElem?_getD]

/-- **Every depth is accepted**: the checker admits `chain n` for all `n`. -/
theorem chain_check (n : Nat) : check tfhe22 (chain n) = true := by
  suffices h : ∀ n, ∃ s, analyze tfhe22 [] (.input 0 :: (List.range n).flatMap stage) = some s ∧
      s.length = 2 * n + 1 ∧ s.getD (2 * n) zeroAbs = ⟨0, 3, 1⟩ by
    obtain ⟨s, hs, hl, hlast⟩ := h n
    simp only [check, chain]
    rw [hs]
    simp [admissible, hl, getD_getElem (by omega) hlast, tfhe22]
  intro n
  induction n with
  | zero => exact ⟨[⟨0, 3, 1⟩], by simp [analyze, checkedStep, admissible, stepAbs, tfhe22], rfl, rfl⟩
  | succ n ih =>
    obtain ⟨s, hs, hl, hlast⟩ := ih
    refine ⟨s ++ [⟨0, 6, 2⟩] ++ [⟨0, 3, 1⟩], ?_, by simp [hl]; omega, ?_⟩
    · rw [List.range_succ, List.flatMap_append, ← List.cons_append, analyze_append, hs]
      simpa using stage_step s n hl hlast
    · rw [show 2 * (n + 1) = (s ++ [(⟨0, 6, 2⟩ : Abs)]).length by simp [hl]; omega]
      exact getD_snoc_eq _ _ _

/-- Without bootstraps the noise level doubles with each doubling: two are
admitted (level 4), three are not (level 8 > 5). -/
def leveled (n : Nat) : Prog :=
  ⟨.input 0 :: (List.range n).map (fun k => .lin [(2, k)] 0), [n]⟩

example : check tfhe22 (leveled 2) = true := by decide
theorem leveled_rejected : check tfhe22 (leveled 3) = false := by decide

example : check tfhe22 (chain 3) = true := by decide
example : pbsCount (chain 3) = 3 := by decide

/-- A bootstrap reading a cleartext beyond its degree is rejected: `8x`
reaches 24 > 15 (its level, 8, is over the limit too). -/
example : check tfhe22 ⟨[.input 0, .lin [(4, 0)] 0, .lin [(2, 1)] 0, .pbs double 3 2], [3]⟩ = false := by
  decide

end TclMesh.Noise
