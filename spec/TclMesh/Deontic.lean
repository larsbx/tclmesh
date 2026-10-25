/-!
# Fivefold deontic resolution

Verdicts `W` (perform required), `N` (perform preferred), `M` (neutral),
`K` (omit preferred), and `H` (omit required). A set of verdicts admits
execution exactly when it is a single verdict other than `H`, mirroring
`::tclmesh::deontic::resolve` and the kernel's `admits_execution`.
-/

namespace TclMesh.Deontic

inductive Verdict where
  | W | N | M | K | H
  deriving DecidableEq, Repr

open Verdict

inductive Judgment where
  | inapplicable
  | determinate (v : Verdict)
  | conflicted
  deriving DecidableEq, Repr

/-- Duplicates collapse; distinct verdicts conflict. -/
def resolve : List Verdict → Judgment
  | [] => .inapplicable
  | v :: rest => if rest.all (· == v) then .determinate v else .conflicted

def admits (vs : List Verdict) : Bool :=
  match resolve vs with
  | .determinate v => v != H
  | _ => false

theorem resolve_determinate {vs : List Verdict} {v : Verdict} :
    resolve vs = .determinate v ↔ vs ≠ [] ∧ ∀ u ∈ vs, u = v := by
  cases vs with
  | nil => simp [resolve]
  | cons w rest =>
    simp only [resolve]
    split
    · rename_i h
      simp only [List.all_eq_true, beq_iff_eq] at h
      simp only [Judgment.determinate.injEq, ne_eq, reduceCtorEq, not_false_eq_true,
        List.mem_cons, forall_eq_or_imp, true_and]
      constructor
      · rintro rfl; exact ⟨rfl, h⟩
      · rintro ⟨rfl, _⟩; rfl
    · rename_i h
      simp only [List.all_eq_true, beq_iff_eq] at h
      simp only [reduceCtorEq, ne_eq, not_false_eq_true, List.mem_cons, forall_eq_or_imp,
        true_and, false_iff, not_and]
      intro hw hall
      exact h (fun u hu => (hall u hu).trans hw.symm)

/-- **Admission.** Execution is admitted iff every verdict is one and the same
verdict, other than `H`. -/
theorem admits_iff {vs : List Verdict} :
    admits vs = true ↔ ∃ v, v ≠ H ∧ vs ≠ [] ∧ ∀ u ∈ vs, u = v := by
  unfold admits
  split
  · rename_i v hv
    rw [resolve_determinate] at hv
    simp only [bne_iff_ne, ne_eq]
    constructor
    · intro h; exact ⟨v, h, hv⟩
    · rintro ⟨w, hw, -, hall⟩
      obtain ⟨hne, hallv⟩ := hv
      obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil vs hne
      rw [← hallv u hu, hall u hu]; exact hw
  · rename_i hnot
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro v _ hne hall
    exact hnot v (resolve_determinate.mpr ⟨hne, hall⟩)

/-- Admission depends only on which verdicts occur, not on order or repetition. -/
theorem admits_congr {vs ws : List Verdict} (h : ∀ u, u ∈ vs ↔ u ∈ ws) :
    admits vs = admits ws := by
  have key : ∀ {as bs : List Verdict}, (∀ u, u ∈ as ↔ u ∈ bs) →
      admits as = true → admits bs = true := by
    intro as bs h ha
    obtain ⟨v, hv, hne, hall⟩ := admits_iff.mp ha
    refine admits_iff.mpr ⟨v, hv, ?_, fun u hu => hall u ((h u).mpr hu)⟩
    intro hnil
    obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil as hne
    have := (h u).mp hu
    rw [hnil] at this; cases this
  cases ha : admits vs <;> cases hb : admits ws
  · rfl
  · exact absurd (key (fun u => (h u).symm) hb) (by simp [ha])
  · exact absurd (key h ha) (by simp [hb])
  · rfl

/-- Omit-required always blocks execution, whatever else is present. -/
theorem H_blocks {vs : List Verdict} (h : H ∈ vs) : admits vs = false := by
  cases ha : admits vs
  · rfl
  · obtain ⟨v, hv, -, hall⟩ := admits_iff.mp ha
    exact absurd (hall H h).symm hv

/-- Hard and preference conflicts block execution. -/
theorem conflict_blocks {vs : List Verdict} {a b : Verdict} (ha : a ∈ vs) (hb : b ∈ vs)
    (hab : a ≠ b) : admits vs = false := by
  cases h : admits vs
  · rfl
  · obtain ⟨v, -, -, hall⟩ := admits_iff.mp h
    exact absurd ((hall a ha).trans (hall b hb).symm) hab

end TclMesh.Deontic
