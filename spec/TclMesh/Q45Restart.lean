import Std

/-!
INV-Q9 restart extension for one fixed session identifier. The durable result
and its logical completion record are committed atomically. A crash discards
only volatile availability; recovery retains the durable store. Eligibility is
needed only for a first commit. An occupied session returns its original receipt
or rejects a conflicting result, without another durable write or completion.

These are assumptions of the abstract storage transition, not a refinement proof
of SQLite or the actor. `completionRecords` counts durable logical records, not
volatile `q45_complete` messages or delivery to an external consumer. A process
may crash after commit and before sending any notification; no delivery liveness
or exactly-once external delivery is asserted.
-/

namespace TclMesh.Q45Restart

structure Result where
  binding : Nat
  bit : Bool
  deriving DecidableEq, Repr

structure Receipt where
  result : Result
  token : Nat
  deriving DecidableEq, Repr

structure State where
  online : Bool
  durable : Option Receipt
  resultWrites : Nat
  completionRecords : Nat
  deriving DecidableEq, Repr

def initial : State := ⟨true, none, 0, 0⟩

inductive Command where
  | crash
  | recover
  | finalize (candidate : Result) (proposedToken : Nat) (eligible : Bool)

inductive Reply where
  | noReply
  | offline
  | ineligible
  | recorded (receipt : Receipt)
  | replay (receipt : Receipt)
  | conflict
  deriving DecidableEq, Repr

def step (s : State) : Command → State × Reply
  | .crash => ({s with online := false}, .noReply)
  | .recover => ({s with online := true}, .noReply)
  | .finalize candidate proposedToken eligible =>
    if s.online then
      match s.durable with
      | some receipt =>
        (s, if receipt.result = candidate then .replay receipt else .conflict)
      | none =>
        if eligible then
          let receipt : Receipt := ⟨candidate, proposedToken⟩
          ({s with durable := some receipt,
                   resultWrites := s.resultWrites + 1,
                   completionRecords := s.completionRecords + 1}, .recorded receipt)
        else (s, .ineligible)
    else (s, .offline)

def run (s : State) : List Command → State
  | [] => s
  | command :: rest => run (step s command).1 rest

/-- Exactly one logical completion accompanies the sole durable result write. -/
def DurableInvariant (s : State) : Prop :=
  match s.durable with
  | none => s.resultWrites = 0 ∧ s.completionRecords = 0
  | some _ => s.resultWrites = 1 ∧ s.completionRecords = 1

theorem initialInvariant : DurableInvariant initial := by
  simp [DurableInvariant, initial]

theorem firstWrite (candidate : Result) (token : Nat) :
    step initial (.finalize candidate token true) =
      (⟨true, some ⟨candidate, token⟩, 1, 1⟩, .recorded ⟨candidate, token⟩) := rfl

theorem stepInvariant (s : State) (command : Command)
    (h : DurableInvariant s) : DurableInvariant (step s command).1 := by
  cases command with
  | crash => simpa [step, DurableInvariant] using h
  | recover => simpa [step, DurableInvariant] using h
  | finalize candidate token eligible =>
    by_cases live : s.online = true
    · cases stored : s.durable with
      | none =>
        by_cases allowed : eligible = true
        · simp [DurableInvariant, stored] at h
          simp [step, live, stored, allowed, DurableInvariant, h.1, h.2]
        · simpa [step, live, stored, allowed] using h
      | some receipt => simpa [step, live, stored] using h
    · simpa [step, live] using h

/-- Preservation for every finite command trace, including any number of restarts. -/
theorem traceInvariant (commands : List Command) (s : State)
    (h : DurableInvariant s) : DurableInvariant (run s commands) := by
  induction commands generalizing s with
  | nil => exact h
  | cons command rest ih => exact ih (step s command).1 (stepInvariant s command h)

theorem reachableInvariant (commands : List Command) :
    DurableInvariant (run initial commands) :=
  traceInvariant commands initial initialInvariant

theorem invariantCounts (s : State) (h : DurableInvariant s) :
    s.resultWrites = s.completionRecords ∧
    s.resultWrites ≤ 1 ∧ s.completionRecords ≤ 1 := by
  cases stored : s.durable <;> simp [DurableInvariant, stored] at h <;> omega

theorem noSecondWriteOrCompletion (commands : List Command) :
    (run initial commands).resultWrites = (run initial commands).completionRecords ∧
    (run initial commands).resultWrites ≤ 1 ∧
    (run initial commands).completionRecords ≤ 1 :=
  invariantCounts (run initial commands) (reachableInvariant commands)

/-- Durable projection deliberately excludes volatile process availability. -/
def durableView (s : State) : Option Receipt × Nat × Nat :=
  (s.durable, s.resultWrites, s.completionRecords)

theorem occupiedStepPreservesDurable (s : State) (command : Command) (receipt : Receipt)
    (h : s.durable = some receipt) :
    durableView (step s command).1 = durableView s := by
  cases command with
  | crash => rfl
  | recover => rfl
  | finalize candidate token eligible =>
    by_cases live : s.online = true
    · simp [step, live, h]
    · simp [step, live]

theorem preservesRecorded (s : State) (command : Command) (receipt : Receipt)
    (h : s.durable = some receipt) :
    (step s command).1.durable = some receipt := by
  have p := occupiedStepPreservesDurable s command receipt h
  have q := congrArg Prod.fst p
  simpa [durableView, h] using q

/-- After the first commit, the complete receipt and both counters are immutable. -/
theorem recordedRemains (commands : List Command) (s : State) (receipt : Receipt)
    (h : s.durable = some receipt) : durableView (run s commands) = durableView s := by
  induction commands generalizing s with
  | nil => rfl
  | cons command rest ih =>
    exact (ih (step s command).1 (preservesRecorded s command receipt h)).trans
      (occupiedStepPreservesDurable s command receipt h)

/-- Proposed receipt tokens and renewed eligibility cannot change an existing receipt. -/
theorem recoveredIdentical (receipt : Receipt) (proposedToken writes completions : Nat)
    (eligible : Bool) :
    step (step ⟨false, some receipt, writes, completions⟩ .recover).1
      (.finalize receipt.result proposedToken eligible) =
      (⟨true, some receipt, writes, completions⟩, .replay receipt) := by
  simp [step]

theorem recoveredConflict (receipt : Receipt) (candidate : Result)
    (proposedToken writes completions : Nat) (eligible : Bool)
    (h : receipt.result ≠ candidate) :
    step (step ⟨false, some receipt, writes, completions⟩ .recover).1
      (.finalize candidate proposedToken eligible) =
      (⟨true, some receipt, writes, completions⟩, .conflict) := by
  simp [step, h]

#print axioms noSecondWriteOrCompletion
#print axioms recordedRemains
#print axioms recoveredIdentical
#print axioms recoveredConflict

end TclMesh.Q45Restart
