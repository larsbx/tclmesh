import TclMesh.Q45Adversarial
open TclMesh.Q45Adversarial

-- Deliberately false: the server runner requires the specific decide/false diagnostic.
example : (2^80 + 1 : Nat) ≤ 2^80 := by decide
