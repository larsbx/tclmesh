import TclMeshProof
import Lean

/-!
Fails unless every refinement theorem, and every definition of the Aeneas
translation of `kernel/core`, depends only on Lean's standard axioms.
`sorry` would appear as `sorryAx`. Run with `lake env lean Audit.lean`.
-/

open Lean Elab Command

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (decl, _) in env.constants.toList do
    unless ((`TclMeshProof).isPrefixOf decl || (`tclmesh_kernel_core).isPrefixOf decl) &&
      !decl.isInternal do continue
    count := count + 1
    for ax in ← collectAxioms decl do
      unless allowedAxioms.contains ax do
        throwError "{decl} depends on disallowed axiom {ax}"
  logInfo m!"audited {count} declarations: standard axioms only"

