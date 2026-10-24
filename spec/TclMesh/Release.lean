/-!
# Threshold release

A release request succeeds only with shares from at least `threshold` distinct
holders that the policy authorizes, all bound to that request. Shares for
other requests, duplicates, and shares from outsiders count for nothing.

Cryptographic share validity (that a share really is a partial decryption by
its holder) is a backend obligation and appears here as `valid`.
-/

namespace TclMesh.Release

structure Share where
  holder : String
  request : Nat
  deriving DecidableEq, Repr

structure Policy where
  holders : List String
  threshold : Nat

/-- Remove duplicates, keeping first occurrences. -/
def dedup : List String → List String
  | [] => []
  | x :: xs => if x ∈ dedup xs then dedup xs else x :: dedup xs

theorem mem_dedup {x : String} : ∀ {xs : List String}, x ∈ dedup xs ↔ x ∈ xs
  | [] => by simp [dedup]
  | y :: ys => by
    unfold dedup
    split
    · rename_i h
      rw [mem_dedup]
      constructor
      · exact List.mem_cons_of_mem y
      · intro hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact mem_dedup.mp h
        · exact hm
    · simp [mem_dedup]

theorem nodup_dedup : ∀ xs : List String, (dedup xs).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    unfold dedup
    split
    · exact nodup_dedup xs
    · rename_i h
      exact List.nodup_cons.mpr ⟨h, nodup_dedup xs⟩

/-- Distinct authorized holders with a valid share for `request`. -/
def signers (p : Policy) (valid : Share → Bool) (request : Nat) (shares : List Share) :
    List String :=
  dedup ((shares.filter fun s => s.request == request && s.holder ∈ p.holders && valid s).map
    Share.holder)

def accepts (p : Policy) (valid : Share → Bool) (request : Nat) (shares : List Share) : Bool :=
  p.threshold ≤ (signers p valid request shares).length

/-- **Quorum safety.** An accepted release is backed by at least `threshold`
distinct authorized holders, each of whom contributed a valid share bound to
this request. -/
theorem accepts_quorum {p : Policy} {valid : Share → Bool} {request : Nat}
    {shares : List Share} (h : accepts p valid request shares = true) :
    ∃ hs : List String, hs.Nodup ∧ p.threshold ≤ hs.length ∧
      ∀ x ∈ hs, x ∈ p.holders ∧
        ∃ s ∈ shares, s.holder = x ∧ s.request = request ∧ valid s = true := by
  refine ⟨signers p valid request shares, nodup_dedup _, of_decide_eq_true h, ?_⟩
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (mem_dedup.mp hx)
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp hs
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
  exact ⟨hcond.1.2, s, hmem, rfl, hcond.1.1, hcond.2⟩

/-- **No replay.** Shares bound to other requests do not affect acceptance. -/
theorem accepts_ignores_other_requests (p : Policy) (valid : Share → Bool) (request : Nat)
    (shares : List Share) :
    accepts p valid request shares =
      accepts p valid request (shares.filter fun s => s.request == request) := by
  unfold accepts signers
  rw [List.filter_filter]
  have h : ∀ s : Share, (s.request == request && decide (s.holder ∈ p.holders) && valid s &&
      s.request == request) = (s.request == request && decide (s.holder ∈ p.holders) && valid s) := by
    intro s; cases s.request == request <;> simp
  simp only [h]

/-- **Duplicates do not count.** Repeating any share does not change acceptance. -/
theorem accepts_duplicate (p : Policy) (valid : Share → Bool) (request : Nat)
    (s : Share) (shares : List Share) (hs : s ∈ shares) :
    accepts p valid request (s :: shares) = accepts p valid request shares := by
  unfold accepts signers
  simp only [List.filter_cons]
  split
  · rename_i hcond
    simp only [List.map_cons, dedup]
    have : s.holder ∈ dedup ((shares.filter fun s => s.request == request &&
        s.holder ∈ p.holders && valid s).map Share.holder) :=
      mem_dedup.mpr (List.mem_map.mpr ⟨s, List.mem_filter.mpr ⟨hs, hcond⟩, rfl⟩)
    simp [this]
  · rfl

end TclMesh.Release
