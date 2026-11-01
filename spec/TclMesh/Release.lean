/-!
# Release quorum (abstract model)

A release request succeeds only with shares from at least `threshold` distinct
holders that the policy authorizes, all bound to that request. Shares for
other requests, duplicates, and shares from outsiders count for nothing.

The legacy `valid` predicate is abstract, not an implementation of cryptography.
The Verified namespace below separates signature and proof verification and
states cryptographic soundness as a named theorem hypothesis.
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

/-! Cryptographic acceptance specification only; no backend currently implements it.
The binding digest denotes canonical domain-separated bytes covering the manifest,
policy, ciphertext, circuit/output, purpose, recipients, nonce and expiry. -/
namespace TclMesh.Release.Verified

structure Binding where
  request : Nat
  keyset : String
  epoch : Nat
  digest : String
  deriving DecidableEq, Repr

structure Contribution where
  holder : String
  binding : Binding
  payload : String
  signature : String
  proof : String

structure Policy where
  holders : List String
  threshold : Nat
  recipient : String

/-- Neither an authenticated holder nor a signature alone verifies a share. -/
def validShare (authorized : Contribution → Bool)
    (verifySignature verifyProof : Contribution → Bool)
    (binding : Binding) (s : Contribution) : Bool :=
  s.binding == binding && authorized s && verifySignature s && verifyProof s

def signers (p : Policy) (authorized verifySignature verifyProof : Contribution → Bool)
    (binding : Binding) (shares : List Contribution) : List String :=
  dedup ((shares.filter fun s => s.holder ∈ p.holders &&
    validShare authorized verifySignature verifyProof binding s).map Contribution.holder)

def canCombine (p : Policy) (authorized verifySignature verifyProof : Contribution → Bool)
    (binding : Binding) (shares : List Contribution) : Prop :=
  0 < p.threshold ∧ p.threshold ≤
    (signers p authorized verifySignature verifyProof binding shares).length

theorem verified_quorum {p : Policy} {auth sig proof : Contribution → Bool}
    {binding : Binding} {shares : List Contribution}
    (h : canCombine p auth sig proof binding shares) :
    ∃ hs : List String, hs.Nodup ∧ p.threshold ≤ hs.length ∧
      ∀ x ∈ hs, x ∈ p.holders ∧ ∃ s ∈ shares,
        s.holder = x ∧ s.binding = binding ∧ auth s = true ∧
        sig s = true ∧ proof s = true := by
  refine ⟨signers p auth sig proof binding shares, nodup_dedup _, h.2, ?_⟩
  intro x hx
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (mem_dedup.mp hx)
  obtain ⟨hmem, hcond⟩ := List.mem_filter.mp hs
  simp only [Bool.and_eq_true, decide_eq_true_eq, validShare, beq_iff_eq] at hcond
  exact ⟨hcond.1, s, hmem, rfl, hcond.2.1.1.1, hcond.2.1.1.2,
    hcond.2.1.2, hcond.2.2⟩

theorem epoch_fencing {auth sig proof : Contribution → Bool}
    {binding : Binding} {s : Contribution} (h : s.binding.epoch ≠ binding.epoch) :
    validShare auth sig proof binding s = false := by
  have hb : s.binding ≠ binding := fun he => h (congrArg Binding.epoch he)
  simp [validShare, hb]

theorem keyset_fencing {auth sig proof : Contribution → Bool}
    {binding : Binding} {s : Contribution} (h : s.binding.keyset ≠ binding.keyset) :
    validShare auth sig proof binding s = false := by
  have hb : s.binding ≠ binding := fun he => h (congrArg Binding.keyset he)
  simp [validShare, hb]

theorem no_combine_before_threshold {p : Policy} {auth sig proof : Contribution → Bool}
    {binding : Binding} {shares : List Contribution}
    (h : (signers p auth sig proof binding shares).length < p.threshold) :
    ¬ canCombine p auth sig proof binding shares := by
  intro hc
  exact Nat.not_le_of_lt h hc.2

/-- Every executable combination/release transition carries quorum evidence.
This abstract transition relation does not model durable storage or network crypto. -/
inductive Phase where
  | collecting | combined | released
  deriving DecidableEq

inductive Transition (p : Policy) (auth sig proof : Contribution → Bool)
    (binding : Binding) (shares : List Contribution) (recipient : String) : Phase → Phase → Prop where
  | combine (quorum : canCombine p auth sig proof binding shares) :
      Transition p auth sig proof binding shares recipient .collecting .combined
  | release (quorum : canCombine p auth sig proof binding shares)
      (recipientBound : recipient = p.recipient) :
      Transition p auth sig proof binding shares recipient .combined .released

theorem combination_requires_verified_threshold {p : Policy} {auth sig proof : Contribution → Bool}
    {binding : Binding} {shares : List Contribution} {recipient : String}
    (h : Transition p auth sig proof binding shares recipient .collecting .combined) :
    canCombine p auth sig proof binding shares := by cases h with | combine quorum => exact quorum

theorem release_requires_verified_threshold_and_recipient {p : Policy}
    {auth sig proof : Contribution → Bool} {binding : Binding}
    {shares : List Contribution} {recipient : String}
    (h : Transition p auth sig proof binding shares recipient .combined .released) :
    canCombine p auth sig proof binding shares ∧ recipient = p.recipient := by
  cases h with | release quorum bound => exact ⟨quorum, bound⟩

theorem invalid_signature_rejected {auth sig proof : Contribution → Bool}
    {binding : Binding} {s : Contribution} (h : sig s = false) :
    validShare auth sig proof binding s = false := by simp [validShare, h]

theorem invalid_proof_rejected {auth sig proof : Contribution → Bool}
    {binding : Binding} {s : Contribution} (h : proof s = false) :
    validShare auth sig proof binding s = false := by simp [validShare, h]

theorem duplicate_holder_does_not_advance (p : Policy) (auth sig proof : Contribution → Bool)
    (binding : Binding) (shares : List Contribution) (s : Contribution)
    (h : s.holder ∈ signers p auth sig proof binding shares) :
    signers p auth sig proof binding (s :: shares) = signers p auth sig proof binding shares := by
  unfold signers
  simp only [List.filter_cons]
  split
  · simp only [List.map_cons, dedup]
    exact ite_eq_left h
  · rfl

/-- Explicit cryptographic assumption, not an axiom or a claimed proof of TFHE.
A future implementation must justify signature/proof soundness over the exact
binding and payload, including active participant verification material. -/
theorem cryptographic_quorum {p : Policy} {auth sig proof : Contribution → Bool}
    {binding : Binding} {shares : List Contribution}
    (cryptographicPartial : Contribution → Prop)
    (cryptographicSoundness : ∀ s, validShare auth sig proof binding s = true →
      cryptographicPartial s)
    (h : canCombine p auth sig proof binding shares) :
    ∃ hs : List String, hs.Nodup ∧ p.threshold ≤ hs.length ∧
      ∀ x ∈ hs, ∃ s ∈ shares, s.holder = x ∧ cryptographicPartial s := by
  obtain ⟨hs, hn, ht, hall⟩ := verified_quorum h
  refine ⟨hs, hn, ht, ?_⟩
  intro x hx
  obtain ⟨_, s, hm, hh, hb, ha, hs, hp⟩ := hall x hx
  refine ⟨s, hm, hh, cryptographicSoundness s ?_⟩
  simp [validShare, hb, ha, hs, hp]

end TclMesh.Release.Verified
