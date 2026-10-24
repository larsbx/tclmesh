import TclMeshProof.Core.Core
import TclMesh.Deontic

/-!
# Refinement: Rust deontic resolution = specification

`tclmesh_kernel_core::deontic::{resolve, admits}`, translated by Aeneas, compute
exactly `TclMesh.Deontic.{resolve, admits}` on the abstracted verdicts.
-/

open Aeneas Aeneas.Std Result
open tclmesh_kernel_core

-- The suggested `rwa` does not close the goal it is suggested for.
set_option linter.tacticAnalysis.rwaSuggestion false

namespace TclMeshProof.Deontic

def abs : deontic.Verdict → TclMesh.Deontic.Verdict
  | .W => .W | .N => .N | .M => .M | .K => .K | .H => .H

def absJ : deontic.Judgment → TclMesh.Deontic.Judgment
  | .Inapplicable => .inapplicable
  | .Determinate v => .determinate (abs v)
  | .Conflicted => .conflicted

@[step]
theorem same_spec (a b : deontic.Verdict) :
    deontic.same a b ⦃ r => r = (abs a == abs b) ⦄ := by
  cases a <;> cases b <;> simp [deontic.same, abs]

@[step]
theorem resolve_loop_spec (vs : Slice deontic.Verdict) (first : deontic.Verdict) (i : Usize)
    (hi : i.val ≤ vs.length) :
    deontic.resolve_loop vs first i ⦃ j => absJ j =
      if (vs.val.drop i.val).all (fun v => abs v == abs first)
      then .determinate (abs first) else .conflicted ⦄ := by
  unfold deontic.resolve_loop
  step*
  · -- the verdict at `i` agrees: continue from `i + 1`
    have hlt : i.val < vs.val.length := by scalar_tac
    have hv : (abs vs.val[i.val] == abs first) = true := by rw [← v_post, ← b_post]; assumption
    rw [j_post, i2_post, List.drop_eq_getElem_cons hlt, List.all_cons, hv, Bool.true_and]
  · -- the verdict at `i` differs: conflicted
    have hlt : i.val < vs.val.length := by scalar_tac
    have hv : (abs vs.val[i.val] == abs first) = false := by
      rw [← v_post, ← b_post]; simpa using ‹¬b = true›
    rw [List.drop_eq_getElem_cons hlt, List.all_cons, hv, Bool.false_and]
    simp [absJ]
  · -- past the end: every verdict agreed
    have hge : vs.val.length ≤ i.val := by scalar_tac
    simp [absJ, List.drop_eq_nil_of_le hge]
termination_by vs.length - i.val
decreasing_by agrind

/-- **Refinement.** Rust `resolve` computes the specification's judgment. -/
@[step]
theorem resolve_spec (vs : Slice deontic.Verdict) :
    deontic.resolve vs ⦃ j => absJ j = TclMesh.Deontic.resolve (vs.val.map abs) ⦄ := by
  unfold deontic.resolve
  step*
  · -- empty: inapplicable
    have h0 : vs.val = [] := by
      have : vs.length = 0 := b_post ▸ ‹b = true›
      simpa [Slice.length] using this
    simp [absJ, h0, TclMesh.Deontic.resolve]
  · -- nonempty: the loop checks the rest against the first verdict
    obtain ⟨x, xs, hx⟩ : ∃ x xs, vs.val = x :: xs := by
      cases h : vs.val
      · have : vs.length = 0 := by simp [Slice.length, h]
        exact absurd (b_post ▸ this) ‹¬b = true›
      · exact ⟨_, _, rfl⟩
    rw [j_post]
    simp [hx, first_post, TclMesh.Deontic.resolve, List.all_map, Function.comp_def]

/-- **Refinement.** Rust `admits` decides the specification's admission. -/
@[step]
theorem admits_spec (vs : Slice deontic.Verdict) :
    deontic.admits vs ⦃ b => b = TclMesh.Deontic.admits (vs.val.map abs) ⦄ := by
  unfold deontic.admits TclMesh.Deontic.admits
  step*
  · subst_vars; rw [← j_post]; simp [absJ]
  · subst_vars; rw [← j_post]; cases v <;> simp [absJ, abs]
  · subst_vars; rw [← j_post]; simp [absJ]

end TclMeshProof.Deontic
