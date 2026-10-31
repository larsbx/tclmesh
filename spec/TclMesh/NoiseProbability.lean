import TclMesh.Noise

/-! Exact finite weighted executions. A sample contains a complete joint tape,
including keys and input noise. No independence is assumed. The conditional
premise bounds BOTH message errors and absolute output-noise failures at
actual calls; this premise is not established for TFHE-rs by this model. -/
namespace TclMesh.Noise

structure Trial where
  weight : Nat
  boots : Nat → Boot
  inp : Nat → Ct
  cs : List Ct

def Trial.next (t : Trial) (g : Gate) : Trial :=
  { t with cs := t.cs ++ [stepCt t.boots t.inp t.cs g] }

def passes (fresh : Nat) (g : Gate) (t : Trial) : Bool :=
  match g with
  | .pbs lut _ j => decide ((t.boots t.cs.length lut (t.cs.getD j zeroCt)).m = lut.getD (t.cs.getD j zeroCt).m.toNat 0 ∧
      (t.boots t.cs.length lut (t.cs.getD j zeroCt)).e.natAbs ≤ fresh)
  | _ => true

theorem passes_iff (fresh : Nat) (g : Gate) (t : Trial) :
    passes fresh g t = true ↔ StepGood fresh t.boots t.cs g := by
  cases g <;> simp [passes, StepGood, CallGood]

@[simp] theorem filter_false_trials (ts : List Trial) : ts.filter (fun _ => false) = [] := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [ih]

def mass (ts : List Trial) : Nat := (ts.map Trial.weight).sum

def survivors (fresh : Nat) (g : Gate) (ts : List Trial) : List Trial :=
  (ts.filter (passes fresh g)).map (fun t => t.next g)

def rejected (fresh : Nat) (g : Gate) (ts : List Trial) : Nat :=
  mass (ts.filter fun t => !(passes fresh g t))

theorem mass_partition (fresh : Nat) (g : Gate) (ts : List Trial) :
    rejected fresh g ts + mass (survivors fresh g ts) = mass ts := by
  induction ts with
  | nil => simp [rejected, survivors, mass]
  | cons t ts ih =>
    cases h : passes fresh g t <;>
      simp [rejected, survivors, mass, h, Trial.next] at * <;> omega

/-- Mass of first failures on the actual evolving execution. -/
def failureMass (fresh : Nat) : List Gate → List Trial → Nat
  | [], _ => 0
  | g :: gs, ts => rejected fresh g ts + failureMass fresh gs (survivors fresh g ts)

/-- Conditional bound num/den at each PBS after a successful prefix.
Zero-mass prefixes are harmless; require a positive denominator to interpret
this exact integer inequality as a probability bound. -/
def ConditionalBound (fresh num den : Nat) : List Gate → List Trial → Prop
  | [], _ => True
  | g :: gs, ts =>
      (match g with
       | .pbs .. => den * rejected fresh g ts ≤ num * mass ts
       | _ => True) ∧
      ConditionalBound fresh num den gs (survivors fresh g ts)

/-- Adaptive union bound. Arbitrary correlation is allowed. -/
theorem conditional_union_bound (fresh num den : Nat) (gs : List Gate) (ts : List Trial)
    (h : ConditionalBound fresh num den gs ts) :
    den * failureMass fresh gs ts ≤ (pbsCount ⟨gs, []⟩) * num * mass ts := by
  induction gs generalizing ts with
  | nil => simp [failureMass, pbsCount]
  | cons g gs ih =>
    have hr := ih (survivors fresh g ts) h.2
    have hm := mass_partition fresh g ts
    have hle : mass (survivors fresh g ts) ≤ mass ts := by omega
    have hr' := Nat.le_trans hr (Nat.mul_le_mul_left ((pbsCount ⟨gs, []⟩) * num) hle)
    cases g with
    | input i =>
      have hz : rejected fresh (.input i) ts = 0 := by simp [rejected, passes, mass, filter_false_trials]
      simpa [failureMass, hz, pbsCount] using hr'
    | lin terms k =>
      have hz : rejected fresh (.lin terms k) ts = 0 := by simp [rejected, passes, mass, filter_false_trials]
      simpa [failureMass, hz, pbsCount] using hr'
    | pbs lut hi j =>
      have hb : den * rejected fresh (.pbs lut hi j) ts ≤ num * mass ts := h.1
      simp only [failureMass, Nat.mul_add]
      have := Nat.add_le_add hb hr'
      simpa [pbsCount, Nat.add_mul, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using this

def traceOK (fresh : Nat) : List Gate → Trial → Bool
  | [], _ => true
  | g :: gs, t => passes fresh g t && traceOK fresh gs (t.next g)

theorem traceOK_iff (fresh : Nat) (gs : List Gate) (t : Trial) :
    traceOK fresh gs t = true ↔ CallsGood fresh t.boots t.inp t.cs gs := by
  induction gs generalizing t with
  | nil => simp [traceOK, CallsGood]
  | cons g gs ih => simp [traceOK, CallsGood, Bool.and_eq_true, passes_iff, ih, Trial.next]

/-- The bounded quantity is exactly the mass of failed actual traces. -/
theorem failureMass_eq (fresh : Nat) (gs : List Gate) (ts : List Trial) :
    failureMass fresh gs ts = mass (ts.filter fun t => !(traceOK fresh gs t)) := by
  induction gs generalizing ts with
  | nil => simp [failureMass, traceOK, mass, filter_false_trials]
  | cons g gs ih =>
    simp only [failureMass, ih]
    induction ts with
    | nil => simp [rejected, survivors, mass]
    | cons t ts iht =>
      cases hp : passes fresh g t <;> cases ht : traceOK fresh gs (t.next g) <;>
        simp [rejected, survivors, mass, traceOK, hp, ht, Trial.next] at * <;> omega

/-- An incorrect decoded output entails a failed actual-call event. -/
theorem incorrect_implies_trace_failure (D : Discipline) (delta fresh : Nat)
    (hdec : 2 * (D.maxLevel * fresh) < delta) (p : Prog) (hc : check D p = true)
    (t : Trial) (hstart : t.cs = []) (hinp : Fresh D fresh t.inp)
    (hbad : ∃ o ∈ p.outputs, decode delta ((evalCt t.boots t.inp [] p.gates).getD o zeroCt) ≠
      (evalV (fun i => (t.inp i).m) [] p.gates).getD o 0) :
    traceOK fresh p.gates t = false := by
  cases h : traceOK fresh p.gates t with
  | false => rfl
  | true =>
    have hg := (traceOK_iff fresh p.gates t).mp h
    rw [hstart] at hg
    obtain ⟨o, ho, hne⟩ := hbad
    exact False.elim (hne (bootstrapped_sound D delta fresh hdec p hc t.boots t.inp hinp hg o ho))

theorem mass_filter_mono (ts : List Trial) (f g : Trial → Bool)
    (h : ∀ t ∈ ts, f t = true → g t = true) :
    mass (ts.filter f) ≤ mass (ts.filter g) := by
  induction ts with
  | nil => simp [mass]
  | cons t ts ih =>
    have hr := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    have hh := h t List.mem_cons_self
    cases hf : f t <;> cases hg : g t <;> simp [mass, hf, hg] at * <;> omega

/-- The actual output-error event, evaluated from an empty initial state. -/
def wrongOutput (delta : Nat) (p : Prog) (t : Trial) : Bool :=
  p.outputs.any fun o => decide (
    decode delta ((evalCt t.boots t.inp [] p.gates).getD o zeroCt) ≠
      (evalV (fun i => (t.inp i).m) [] p.gates).getD o 0)

/-- Exact finite probability theorem: after division by positive `den` and
positive total mass, output failure probability is at most pbsCount*num/den.
Freshness is required on every positive OR zero-weight listed tape; it can
instead be charged as a separate bad-input event by callers. -/
theorem output_failure_bound (D : Discipline) (delta fresh num den : Nat)
    (p : Prog) (hc : check D p = true) (hdec : 2 * (D.maxLevel * fresh) < delta)
    (ts : List Trial) (hstart : ∀ t ∈ ts, t.cs = [])
    (hinp : ∀ t ∈ ts, Fresh D fresh t.inp)
    (hcond : ConditionalBound fresh num den p.gates ts) :
    den * mass (ts.filter (wrongOutput delta p)) ≤ pbsCount p * num * mass ts := by
  have hm := mass_filter_mono ts (wrongOutput delta p)
    (fun t => !(traceOK fresh p.gates t)) (by
      intro t ht hb
      simp only [wrongOutput, List.any_eq_true, decide_eq_true_eq] at hb
      have hf := incorrect_implies_trace_failure D delta fresh hdec p hc t
        (hstart t ht) (hinp t ht) hb
      simp [hf])
  have hu := conditional_union_bound fresh num den p.gates ts hcond
  rw [failureMass_eq] at hu
  exact Nat.le_trans (Nat.mul_le_mul_left den hm) hu

end TclMesh.Noise
