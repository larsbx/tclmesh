import TclMesh.Q45Adversarial
open TclMesh.Q45Adversarial

-- Deliberately false: the server runner requires the specific decide/false diagnostic.
example : bad.authenticated = true → bad.correct = true := by decide
