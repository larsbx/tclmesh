import TclMesh.Q45Adversarial
open TclMesh.Q45Adversarial

-- Deliberately false: the server runner requires the specific decide/false diagnostic.
example : envelope empty {bad with binding := {bad.binding with session := 1}} := by decide
