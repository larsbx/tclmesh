/-!
# Proof-context claims: at most one accepted import per keyset and context

A proven ciphertext is bound to a context `C` under a keyset `K` (the backend's
key pair). Accepting the same `(K, C)` twice would let one proof stand for two
inputs. Handle stores cannot prevent that alone: processes sharing `K` may use
different stores. So every accepting backend first makes a durable claim on
`(K, C)` with an atomic compare-and-claim (the TFHE backend: a file created
exclusively in the keyset's claims directory, `backends/tfhe/src/main.rs`),
and only then exposes a handle.

This file models that protocol over every process and store at once:

- the `Ledger` is durable and append-only: claims are never removed, so
  crashes and destroyed handles do not release a context;
- `exposed` records every import any process ever accepted;
- an import that crashes after its claim and before exposing (`interrupted`)
  leaves the context held: it is never accepted, now or later.

`at_most_one_accepted_per_keyset_context`: on every trace, each `(K, C)` was
accepted at most once. `claimed_never_accepted_again`: once claimed, an import
of the same `(K, C)` exposes nothing.
-/

namespace TclMesh.Claims

/-- A keyset identity and a proof context. -/
abbrev Key := String × String

structure Claim where
  key : Key
  /-- Digest of the public statement (context, offset, width, bound, word). -/
  statement : String
  attempt : Nat
  deriving DecidableEq

abbrev Ledger := List Claim

def claimed (l : Ledger) (k : Key) : Bool := l.any (·.key == k)

/-- Compare-and-claim: succeeds exactly when nothing has claimed the key. -/
def claim (l : Ledger) (c : Claim) : Option Ledger :=
  if claimed l c.key then none else some (c :: l)

inductive Event
  /-- A verified import: claim, then expose its handle. -/
  | accept (c : Claim)
  /-- A verified import whose process stops after the claim, before exposing. -/
  | interrupted (c : Claim)
  /-- A process stops; only durable state survives. -/
  | crash
  /-- The handle was persisted, but its response was lost. No new admission. -/
  | lostAck
  /-- Read the existing durable outcome; never mint another authorization. -/
  | recover
  /-- A handle is destroyed. -/
  | destroy

structure State where
  ledger : Ledger := []
  /-- Every import any process accepted, newest first. -/
  exposed : List Claim := []

def step (s : State) : Event → State
  | .accept c =>
    match claim s.ledger c with
    | some l => { ledger := l, exposed := c :: s.exposed }
    | none => s
  | .interrupted c =>
    match claim s.ledger c with
    | some l => { s with ledger := l }
    | none => s
  | .crash | .lostAck | .recover | .destroy => s

def run (es : List Event) : State := es.foldl step {}

/-- Ledger keys are distinct, and every exposed import holds a claim. -/
def Inv (s : State) : Prop :=
  (s.ledger.map (·.key)).Nodup ∧ s.exposed.Sublist s.ledger

theorem claimed_false {l : Ledger} {k : Key} (h : claimed l k = false) :
    k ∉ l.map (·.key) := by
  intro hk
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
  have : claimed l c.key = true := List.any_eq_true.mpr ⟨c, hc, by simp⟩
  simp_all

theorem claim_some {l l' : Ledger} {c : Claim} (h : claim l c = some l') :
    l' = c :: l ∧ c.key ∉ l.map (·.key) := by
  unfold claim at h
  split at h
  · contradiction
  · rename_i hc
    exact ⟨(Option.some.inj h).symm, claimed_false (Bool.eq_false_iff.mpr hc)⟩

theorem step_inv {s : State} (h : Inv s) (e : Event) : Inv (step s e) := by
  obtain ⟨hn, hs⟩ := h
  cases e with
  | accept c =>
    simp only [step]
    split
    · rename_i l hl
      obtain ⟨rfl, hk⟩ := claim_some hl
      exact ⟨List.nodup_cons.mpr ⟨hk, hn⟩, hs.cons_cons c⟩
    · exact ⟨hn, hs⟩
  | interrupted c =>
    simp only [step]
    split
    · rename_i l hl
      obtain ⟨rfl, hk⟩ := claim_some hl
      exact ⟨List.nodup_cons.mpr ⟨hk, hn⟩, hs.cons c⟩
    · exact ⟨hn, hs⟩
  | crash | lostAck | recover | destroy => exact ⟨hn, hs⟩

theorem run_inv (es : List Event) : Inv (run es) := by
  unfold run
  suffices ∀ s, Inv s → Inv (es.foldl step s) from this {} ⟨List.nodup_nil, List.Sublist.slnil⟩
  induction es with
  | nil => exact fun _ h => h
  | cons e es ih => exact fun s h => ih _ (step_inv h e)

/-- **At most one accepted import per keyset and context**, over every trace
of imports, interruptions, crashes and destroyed handles. -/
theorem at_most_one_accepted_per_keyset_context (es : List Event) (k : Key) :
    ((run es).exposed.map (·.key)).count k ≤ 1 := by
  obtain ⟨hn, hs⟩ := run_inv es
  exact List.nodup_iff_count.mp ((hs.map _).nodup hn) k

/-- Claims are monotone: a claimed key stays claimed after any event. -/
theorem claimed_step {s : State} {k : Key} (h : claimed s.ledger k = true) (e : Event) :
    claimed (step s e).ledger k = true := by
  cases e with
  | accept c | interrupted c =>
    simp only [step]
    split
    · rename_i l hl
      obtain ⟨rfl, _⟩ := claim_some hl
      unfold claimed at h ⊢
      rw [List.any_cons, h, Bool.or_true]
    · exact h
  | crash | lostAck | recover | destroy => exact h

/-- **Fail closed**: once `(K, C)` is claimed (accepted, or interrupted after
its claim), a later import of it exposes nothing. -/
theorem claimed_never_accepted_again {s : State} {c : Claim}
    (h : claimed s.ledger c.key = true) : (step s (.accept c)).exposed = s.exposed := by
  simp [step, claim, h]

example : ((run [.accept ⟨("K", "ctx/1"), "s", 1⟩, .crash,
    .accept ⟨("K", "ctx/1"), "s", 2⟩]).exposed.map (·.attempt)) = [1] := by decide
example : ((run [.interrupted ⟨("K", "ctx/1"), "s", 1⟩,
    .accept ⟨("K", "ctx/1"), "s", 2⟩]).exposed) = [] := by decide

/-- Every accepted import has a committed claim in the owning authority. -/
theorem commit_before_expose (es : List Event) :
    (run es).exposed.Sublist (run es).ledger := (run_inv es).2

-- Recovery preserves the original authorization, even with a changed statement.
example : ((run [.accept ⟨("K", "ctx/ack"), "s", 1⟩, .lostAck, .crash, .recover,
    .accept ⟨("K", "ctx/ack"), "changed", 2⟩, .destroy,
    .accept ⟨("K", "ctx/ack"), "s", 3⟩]).exposed.map (·.attempt)) = [1] := by decide

-- The theorem assumes ONE ledger for each keyset: two independent authorities
-- each admit the same key. Local persistence cannot establish global uniqueness.
example :
    let c : Claim := ⟨("K", "ctx/split"), "s", 1⟩
    ((run [.accept c]).exposed ++ (run [.accept c]).exposed).length = 2 := by decide

end TclMesh.Claims
