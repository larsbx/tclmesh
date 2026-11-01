/-!
# Necessary threat-model conditions for cryptographic threshold release

Issue #36 distinguishes a policy's cryptographic quorum from a provider's
Byzantine fault bound and number of client responses. These are *necessary*
conditions for a claimed q-of-n secrecy boundary, never a certificate of
a concrete cryptosystem. No backend is enabled by this model.

The actual privacy claim, any-q-subset liveness, independent key custody,
share verification, and recipient-bound decryption still require an audited
scheme and a native implementation.
-/

namespace TclMesh.ThresholdSecurity

/-- Separate policy quorum, claimed collusion bound, fault budget and response count.
These numbers are descriptive claims and have no cryptographic authority. -/
structure Claim where
  parties : Nat
  releaseQuorum : Nat
  privacyCorruptions : Nat
  byzantineFaults : Nat
  clientResponses : Nat
  deriving Repr, DecidableEq

/-- A q-of-n secrecy claim must cover all coalitions of fewer than q
share holders. A provider claiming protection for only f < q-1 corrupt
holders cannot justify q-of-n secrecy. -/
def privacyNecessary (c : Claim) : Prop :=
  0 < c.releaseQuorum ∧ c.releaseQuorum ≤ c.parties ∧
  c.releaseQuorum - 1 ≤ c.privacyCorruptions

/-- A claimed any-q-subset output protocol cannot require more than q
participant responses for a successful release. This is not a proof that
*every* q-subset actually completes the protocol. -/
def responseNecessary (c : Claim) : Prop :=
  0 < c.clientResponses ∧ c.clientResponses ≤ c.releaseQuorum

def numericallyConsistent (c : Claim) : Prop :=
  privacyNecessary c ∧ responseNecessary c

theorem consistent_requires_privacy {c : Claim}
    (h : numericallyConsistent c) :
    c.releaseQuorum - 1 ≤ c.privacyCorruptions := h.1.2.2

theorem consistent_requires_responses {c : Claim}
    (h : numericallyConsistent c) :
    c.clientResponses ≤ c.releaseQuorum := h.2.2

theorem insufficient_privacy_cannot_be_consistent {c : Claim}
    (h : c.privacyCorruptions < c.releaseQuorum - 1) :
    ¬ numericallyConsistent c := by
  intro hc
  exact Nat.not_le_of_gt h (consistent_requires_privacy hc)

/-- Published example: four parties, one guaranteed corrupt-party tolerance,
three client responses. Three responses do NOT establish 3-of-4 secrecy. -/
def kmsFourPartyExample : Claim :=
  ⟨4, 3, 1, 1, 3⟩

theorem kms_four_party_not_three_of_four_secrecy :
    ¬ numericallyConsistent kmsFourPartyExample := by decide

/-- Passing numerical checks is a *hypothetical* profile, not a
cryptographic proof of key custody, ZK verification or reconstruction. -/
def numericallyPossibleExample : Claim :=
  ⟨4, 3, 2, 0, 3⟩

theorem possible_example_only_meets_necessary_conditions :
    numericallyConsistent numericallyPossibleExample := by decide

/-- Keep the provider's fault tolerance out of the secrecy implication.
The privacy and response conditions make no use of byzantineFaults. -/
theorem fault_budget_is_not_privacy_proof (c : Claim) (f : Nat) :
    numericallyConsistent {c with byzantineFaults := f} ↔
    numericallyConsistent c := by
  rfl

end TclMesh.ThresholdSecurity
