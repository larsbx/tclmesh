import TclMesh.NoiseProbability

namespace TclMesh.Noise

-- Exact reported counterexample and adjacent representability boundaries.
example : check tfhe22 ⟨[.lin [] 32], [0]⟩ = false := by decide
example : check tfhe22 ⟨[.lin [] 16], [0]⟩ = false := by decide
example : check tfhe22 ⟨[.lin [] (-1)], [0]⟩ = false := by decide
example : check tfhe22 ⟨[.lin [] 15], [0]⟩ = true := by decide
example : check tfhe22 ⟨[.lin [] 0], [0]⟩ = true := by decide
-- Dead or subsequently cancelled overflow is still refused.
example : check tfhe22 ⟨[.lin [] 32, .lin [] 0], [1]⟩ = false := by decide
example : check tfhe22 ⟨[.lin [] 32, .lin [(1, 0)] (-32)], [1]⟩ = false := by decide
example : check tfhe22 ⟨[.lin [] 0, .pbs [16] 16 0], [1]⟩ = false := by decide
example : check tfhe22 ⟨[.lin [] 0, .pbs [(-1)] 0 0], [1]⟩ = false := by decide
example : check tfhe22 ⟨[.lin [] 0, .pbs [15] 15 0], [1]⟩ = true := by decide
-- Noise guard isolated from the degree guard (PBS output has degree zero).
example : check tfhe22 ⟨[.input 0, .pbs [0,0,0,0] 0 0, .lin [(5,1)] 0], [2]⟩ = true := by decide
example : check tfhe22 ⟨[.input 0, .pbs [0,0,0,0] 0 0, .lin [(6,1)] 0], [2]⟩ = false := by decide
example : check ⟨16,15,5⟩ ⟨[.input 0], [0]⟩ = false := by decide
example : check ⟨3,15,0⟩ ⟨[.input 0], [0]⟩ = false := by decide
example : check tfhe22 ⟨[.lin [(1,0)] 0], [0]⟩ = false := by decide
example : check tfhe22 ⟨[.lin [] 0], [1]⟩ = false := by decide
-- Negative noise can wrap the phase at zero, while rounded decoding is right.
example : torusDecode (2^59) 32 ⟨0, -1⟩ = 0 := by decide
example : torusDecode (2^59) 32 ⟨32, 0⟩ = 0 := by decide
example : decode (2^59) ⟨32, 0⟩ = 32 := by decide

-- A concrete function correct on the actual call but wrong on an unused input.
def unusedBad : Boot := fun lut c =>
  if c.m = 1 then ⟨99, 0⟩ else ⟨lut.getD c.m.toNat 0, 0⟩
example : CallsGood 0 (fun _ => unusedBad) (fun _ => zeroCt) []
    [.lin [] 0, .pbs [0,0] 0 0] := by
  simp [CallsGood, StepGood, CallGood, stepCt, unusedBad, linV, zeroCt]
example : ¬ (∀ c : Ct, 0 ≤ c.m → c.m ≤ 15 → c.e.natAbs ≤ 0 →
    CallGood 0 unusedBad [0,0] c) := by
  intro h
  have := h ⟨1,0⟩ (by decide) (by decide) (by decide)
  simp [CallGood, unusedBad] at this

-- Every sampled function has some bad input; per-fixed-input failure is 1/2.
def needle (bad : Int) : Boot := fun lut c =>
  if c.m = bad then ⟨99,0⟩ else ⟨lut.getD c.m.toNat 0,0⟩
example : ¬ CallGood 0 (needle 0) [0,0] ⟨0,0⟩ ∧
    CallGood 0 (needle 1) [0,0] ⟨0,0⟩ ∧
    CallGood 0 (needle 0) [0,0] ⟨1,0⟩ ∧
    ¬ CallGood 0 (needle 1) [0,0] ⟨1,0⟩ := by simp [CallGood, needle]

-- Correlation: the second call always fails after surviving the first.
-- Each call's unconditional failure frequency is 1/2; the required conditional
-- bound of 1/2 correctly fails on the surviving prefix.
def correlated (badWire : Nat) : Trial :=
  ⟨1, fun n lut c => if n = badWire then ⟨99,0⟩ else ⟨lut.getD c.m.toNat 0,0⟩,
    fun _ => zeroCt, [zeroCt]⟩
def twoCalls : List Gate := [.pbs [0] 0 0, .pbs [0] 0 0]
example : rejected 0 (.pbs [0] 0 0) [correlated 1, correlated 2] = 1 := by decide
example : failureMass 0 twoCalls [correlated 1, correlated 2] = 2 := by decide
example : ¬ ConditionalBound 0 1 2 twoCalls [correlated 1, correlated 2] := by
  simp only [twoCalls, ConditionalBound]; decide
example : ConditionalBound 0 1 1 twoCalls [correlated 1, correlated 2] := by
  simp only [twoCalls, ConditionalBound]; decide

end TclMesh.Noise
