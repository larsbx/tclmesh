import TclMesh
import Lean

/-!
Fails unless every `TclMesh` declaration depends only on Lean's standard
axioms. `sorry` would appear as `sorryAx` and fail the audit. Run with
`lake env lean Audit.lean`.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

elab "#audit_axioms" : command => do
  let env ← getEnv
  let mut checked := 0
  let mut theorems := 0
  for (name, info) in env.constants.toList do
    unless (`TclMesh).isPrefixOf name && !name.isInternal do continue
    checked := checked + 1
    if info matches .thmInfo _ then theorems := theorems + 1
    for ax in ← collectAxioms name do
      unless allowedAxioms.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"
  logInfo m!"audited {checked} declarations ({theorems} theorems): standard axioms only"

#audit_axioms
