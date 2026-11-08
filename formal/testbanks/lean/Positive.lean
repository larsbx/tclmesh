import TclMesh.Q45Adversarial
import Lean

/-! Server testbank. These are acceptance-model obligations, not FHE proofs.
This file is deliberately outside the automatic `TclMesh` library target.
-/
namespace TclMesh.Q45Testbank
open TclMesh.Q45Adversarial

def good (i : Nat) : Contribution := {bad with sender := i, correct := true}
def goodFour : List Contribution := [good 1, good 2, good 3, good 4]
def four : State := goodFour.foldl submit empty

theorem LP001_session_mismatch :
    submit empty {bad with binding := {bad.binding with session := 1}} = empty := by decide
theorem LP002_ciphertext_mismatch :
    submit empty {bad with binding := {bad.binding with ciphertext := 1}} = empty := by decide
theorem LP003_quorum_order_mismatch :
    submit empty {bad with binding := {bad.binding with quorum := [4, 3, 2, 1]}} = empty := by decide
theorem LP004_outside_holder : submit empty {bad with sender := 5} = empty := by decide
theorem LP005_empty_payload : submit empty {bad with nonempty := false} = empty := by decide
theorem LP006_duplicate_altered_payload :
    submit (submit empty bad) {bad with correct := true} = submit empty bad := by decide

theorem LP007_four_distinct_bound : wellBound four := by
  apply submissions_preserve_wellBound goodFour empty
  constructor
  · decide
  · intro c hc
    simp [empty] at hc

theorem LP008_four_labels_count : (four.partials.map Contribution.sender).length = 4 := by decide
theorem LP009_opaque_noncanonical_admitted :
    {bad with canonical := false} ∈ (submit empty {bad with canonical := false}).partials := by decide
theorem LP010_authenticated_incorrect_admitted :
    bad.authenticated = true ∧ bad ∈ (submit empty bad).partials := by decide
theorem LP011_one_wrong_holder_invalidates_certification :
    ¬ certified ((bad :: [good 2, good 3, good 4]).foldl submit empty) := by
  intro h
  have hm : bad ∈ ((bad :: [good 2, good 3, good 4]).foldl submit empty).partials := by decide
  have hf := h bad hm
  contradiction

theorem LP012_ideal_verifier_filters_wrong_holder :
    certified ((bad :: goodFour).foldl (submitVerified (fun c => c.correct)) empty) := by
  exact verified_submissions_preserve_correctness (fun c => c.correct)
    (by intro c hc; exact hc) (bad :: goodFour) empty
    (by intro c hc; simp [empty] at hc)

theorem LP013_four_bounded_masks :
    ([2^80, 2^80, 2^80, 2^80] : List Nat).sum = 4 * 2^80 := by decide
theorem LP014_overbound_inside_total_budget :
    (2^80 : Nat) < 2^80 + 1 ∧ 2^80 + 1 ≤ 4 * 2^80 := by decide
theorem LP015_zero_phase_flips : decode 0 = 0 ∧ decode delta = 1 := exact_zero_phase_bit_flip
theorem LP016_one_phase_flips :
    decode delta = 1 ∧ decode ((delta + delta) % q) = 0 := exact_one_phase_bit_flip
theorem LP017_max_measured_noise_headroom :
    (2^34 - 1 : Nat) + 4 * 2^80 < delta / 2 := by
  apply honest_80_bit_headroom
  decide
theorem LP018_width_margin : (34 : Nat) + 40 ≤ 80 := by decide
theorem LP019_arbitrary_offset_canonical (modulus x offset : Nat) (h : 0 < modulus) :
    (x + offset) % modulus < modulus := offset_is_canonical modulus x offset h
theorem LP020_phase_translation (modulus c0 head rest offset : Nat) :
    phase modulus c0 ((head + offset) % modulus) rest =
      (phase modulus c0 head rest + offset) % modulus :=
  phase_offset modulus c0 head rest offset

end TclMesh.Q45Testbank

open Lean Elab Command
elab "#audit_q45_testbank" : command => do
  let env ← getEnv
  let mut count := 0
  for (name, info) in env.constants.toList do
    unless (`TclMesh.Q45Testbank).isPrefixOf name && !name.isInternal do continue
    if info matches .thmInfo _ then count := count + 1
    for ax in ← collectAxioms name do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "{name} depends on disallowed axiom {ax}"
  unless count == 20 do throwError "expected 20 bank theorems, found {count}"
  logInfo "Q45_LEAN_TESTBANK: 20 cases; standard axioms only"

#audit_q45_testbank
#check TclMesh.Q45Testbank.LP001_session_mismatch
#check TclMesh.Q45Testbank.LP002_ciphertext_mismatch
#check TclMesh.Q45Testbank.LP003_quorum_order_mismatch
#check TclMesh.Q45Testbank.LP004_outside_holder
#check TclMesh.Q45Testbank.LP005_empty_payload
#check TclMesh.Q45Testbank.LP006_duplicate_altered_payload
#check TclMesh.Q45Testbank.LP007_four_distinct_bound
#check TclMesh.Q45Testbank.LP008_four_labels_count
#check TclMesh.Q45Testbank.LP009_opaque_noncanonical_admitted
#check TclMesh.Q45Testbank.LP010_authenticated_incorrect_admitted
#check TclMesh.Q45Testbank.LP011_one_wrong_holder_invalidates_certification
#check TclMesh.Q45Testbank.LP012_ideal_verifier_filters_wrong_holder
#check TclMesh.Q45Testbank.LP013_four_bounded_masks
#check TclMesh.Q45Testbank.LP014_overbound_inside_total_budget
#check TclMesh.Q45Testbank.LP015_zero_phase_flips
#check TclMesh.Q45Testbank.LP016_one_phase_flips
#check TclMesh.Q45Testbank.LP017_max_measured_noise_headroom
#check TclMesh.Q45Testbank.LP018_width_margin
#check TclMesh.Q45Testbank.LP019_arbitrary_offset_canonical
#check TclMesh.Q45Testbank.LP020_phase_translation
