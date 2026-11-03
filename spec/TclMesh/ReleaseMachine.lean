import TclMesh.Release

/-!
# Release state machine (durable journal, live authority, crash and retry)

`Release.Verified` proves quorum facts about one abstract transition. This
file models the executable lifecycle of `src/release.tcl` with its governed
policy layer (`src/release_policy.tcl`):

* requests are stored durably, each with a **canonical binding** fixed at
  creation (its own request id, keyset, the epoch then current, and digest);
* **authority is live**: holders can be revoked and the epoch can rotate at any
  time, and every governed transition re-checks the authority current at that
  step, for every recorded contribution;
* `combine` durably journals an `Attempt` **before** the backend is invoked
  (write-ahead), recording the signer set and the authority it was verified
  under; backend responses are accepted only for calls in flight;
* `crash` loses every volatile in-flight call and keeps the durable state;
  `recoverRetry` re-arms a crashed or failed attempt only with an idempotent
  backend; `recoverReleased`/`recoverFailed` resolve it.

`reachable_inv` proves, for every reachable state, the release-state
invariant: every journaled attempt is backed by a verified quorum of distinct,
unrevoked holders under the epoch of the request's canonical binding and is
addressed to the policy recipient; every released output has such an attempt;
and without idempotency each request reaches the backend at most once,
across any number of crashes. `sig` and `proof` remain abstract predicates:
`Verified.cryptographic_quorum` states their soundness as a hypothesis, and no
backend discharges it. `tools/release_conformance.tcl` replays the same traces
against the Tcl implementation and requires identical observations
(`spec-eval --release`).
-/

namespace TclMesh.Release.Machine

open TclMesh.Release (dedup mem_dedup nodup_dedup)
open TclMesh.Release.Verified (Binding Contribution)

abbrev Policy := TclMesh.Release.Verified.Policy

inductive Status where
  | collecting | quorumReached | combining | released | failed | rejected | expired
  deriving DecidableEq, Repr

def Status.name : Status → String
  | .collecting => "collecting"
  | .quorumReached => "quorum-reached"
  | .combining => "combining"
  | .released => "released"
  | .failed => "failed"
  | .rejected => "rejected"
  | .expired => "expired"

/-- Live authority: the current epoch and the (permanently) revoked holders. -/
structure Authority where
  epoch : Nat
  revoked : List String
  deriving DecidableEq, Repr

/-- Abstract verifiers: a signature over the binding and a share proof. -/
structure Verifiers where
  sig : Contribution → Bool
  proof : Contribution → Bool

structure Config where
  idempotent : Bool

structure Req where
  binding : Binding
  policy : Policy
  status : Status
  contributions : List Contribution
  output : Option String

/-- A durably journaled backend invocation, committed before the call. -/
structure Attempt where
  id : Nat
  binding : Binding
  recipient : String
  signers : List String
  authority : Authority

structure State where
  authority : Authority
  requests : List Req
  journal : List Attempt
  /-- Volatile: backend calls in flight in this process, lost on `crash`. -/
  inflight : List Nat

def State.init : State := ⟨⟨0, []⟩, [], [], []⟩

inductive Err where
  | policy | unknown | stale | revoked | unauthorized | state | duplicate
  | invalid | quorum | idempotency | notInflight
  deriving DecidableEq, Repr

def Err.name : Err → String
  | .policy => "policy" | .unknown => "unknown" | .stale => "stale"
  | .revoked => "revoked" | .unauthorized => "unauthorized" | .state => "state"
  | .duplicate => "duplicate" | .invalid => "invalid" | .quorum => "quorum"
  | .idempotency => "idempotency" | .notInflight => "not-inflight"

inductive Event where
  | create (keyset digest : String) (policy : Policy)
  | contribute (id : Nat) (c : Contribution)
  | revoke (holder : String)
  | rotate
  | combine (id : Nat)
  | backendOk (id : Nat) (result : String)
  | backendFail (id : Nat)
  | crash
  | recoverRetry (id : Nat)
  | recoverReleased (id : Nat) (result : String)
  | recoverFailed (id : Nat)
  | reject (id : Nat)
  | expire (id : Nat)

/-- A contribution verifies for `r` under authority `a`: authorized holder,
bound to the request's canonical binding, at the current epoch, not revoked,
with a valid signature and proof. -/
def valid (V : Verifiers) (a : Authority) (r : Req) (c : Contribution) : Bool :=
  decide (c.holder ∈ r.policy.holders) && c.binding == r.binding &&
    r.binding.epoch == a.epoch && decide (c.holder ∉ a.revoked) && V.sig c && V.proof c

def signers (V : Verifiers) (a : Authority) (r : Req) : List String :=
  dedup ((r.contributions.filter (valid V a r)).map Contribution.holder)

def wellFormed (p : Policy) : Bool :=
  decide (0 < p.threshold) && decide (p.threshold ≤ p.holders.length) && decide p.holders.Nodup

/-- The re-check every governed transition performs (`_transition_authority`):
the request exists, its epoch is current, and no recorded contributor is revoked. -/
def guard (s : State) (id : Nat) : Except Err Req :=
  match s.requests[id]? with
  | none => .error .unknown
  | some r =>
    if r.binding.epoch ≠ s.authority.epoch then .error .stale
    else if r.contributions.any (fun c => decide (c.holder ∈ s.authority.revoked)) then .error .revoked
    else .ok r

def update (s : State) (id : Nat) (r : Req) : State := { s with requests := s.requests.set id r }

/-- Status-only transition of a guarded request whose status is in `from`. -/
def move (s : State) (id : Nat) (src : List Status) (dst : Status) (out : Option String) :
    Except Err State :=
  match guard s id with
  | .error e => .error e
  | .ok r => if r.status ∈ src then .ok (update s id { r with status := dst, output := out })
    else .error .state

/-- Backend response for an in-flight call. -/
def respond (s : State) (id : Nat) (dst : Status) (out : Option String) : Except Err State :=
  if id ∉ s.inflight then .error .notInflight else
  match s.requests[id]? with
  | none => .error .unknown
  | some r => if r.status ≠ .combining then .error .state else
    .ok { (update s id { r with status := dst, output := out }) with inflight := s.inflight.erase id }

def step (V : Verifiers) (cfg : Config) (s : State) : Event → Except Err State
  | .create keyset digest p =>
    if wellFormed p then
      .ok { s with requests := s.requests ++
        [⟨⟨s.requests.length, keyset, s.authority.epoch, digest⟩, p, .collecting, [], none⟩] }
    else .error .policy
  | .contribute id c =>
    match guard s id with
    | .error e => .error e
    | .ok r =>
      if c.holder ∈ s.authority.revoked then .error .revoked
      else if c.holder ∉ r.policy.holders then .error .unauthorized
      else if r.status ≠ .collecting then .error .state
      else if r.contributions.any (fun d => d.holder == c.holder) then .error .duplicate
      else if valid V s.authority r c = false then .error .invalid
      else
        let cs := r.contributions ++ [c]
        let st := if r.policy.threshold ≤ cs.length then Status.quorumReached else .collecting
        .ok (update s id { r with contributions := cs, status := st })
  | .revoke h => .ok { s with authority := { s.authority with revoked := h :: s.authority.revoked } }
  | .rotate => .ok { s with authority := { s.authority with epoch := s.authority.epoch + 1 } }
  | .combine id =>
    match guard s id with
    | .error e => .error e
    | .ok r =>
      if r.status ≠ .quorumReached then .error .state
      else if r.policy.threshold ≤ (signers V s.authority r).length then
        .ok { (update s id { r with status := .combining }) with
          journal := s.journal ++ [⟨id, r.binding, r.policy.recipient, signers V s.authority r, s.authority⟩],
          inflight := id :: s.inflight }
      else .error .quorum
  | .backendOk id out => respond s id .released (some out)
  | .backendFail id => respond s id .failed none
  | .crash => .ok { s with inflight := [] }
  | .recoverRetry id =>
    if cfg.idempotent then move s id [.combining, .failed] .quorumReached none
    else match guard s id with
      | .error e => .error e
      | .ok r => if r.status ∈ [.combining, .failed] then .error .idempotency else .error .state
  | .recoverReleased id out => move s id [.combining, .failed] .released (some out)
  | .recoverFailed id => move s id [.combining, .failed] .failed none
  | .reject id => move s id [.collecting, .quorumReached] .rejected none
  | .expire id => move s id [.collecting, .quorumReached] .expired none

inductive Reachable (V : Verifiers) (cfg : Config) : State → Prop where
  | init : Reachable V cfg State.init
  | step {s s' : State} (e : Event) : Reachable V cfg s → step V cfg s e = .ok s' →
      Reachable V cfg s'

/-! ## The release-state invariant -/

def attemptsFor (s : State) (id : Nat) : Nat := (s.journal.filter (fun a => a.id == id)).length

/-- A journaled attempt is backed by a verified quorum for its request. -/
def Sound (V : Verifiers) (s : State) (a : Attempt) : Prop :=
  ∃ r, s.requests[a.id]? = some r ∧ a.binding = r.binding ∧ a.recipient = r.policy.recipient ∧
    a.signers.Nodup ∧ 0 < r.policy.threshold ∧ r.policy.threshold ≤ a.signers.length ∧
    ∀ h ∈ a.signers, ∃ c ∈ r.contributions, c.holder = h ∧ valid V a.authority r c = true

def Active (st : Status) : Prop := st = .combining ∨ st = .released ∨ st = .failed
def Idle (st : Status) : Prop := st = .collecting ∨ st = .quorumReached

structure Inv (V : Verifiers) (cfg : Config) (s : State) : Prop where
  sound : ∀ a ∈ s.journal, Sound V s a
  canonical : ∀ (i : Nat) (r : Req), s.requests[i]? = some r → r.binding.request = i
  wf : ∀ (i : Nat) (r : Req), s.requests[i]? = some r → 0 < r.policy.threshold
  attempted : ∀ (i : Nat) (r : Req), s.requests[i]? = some r →
    Active r.status → 0 < attemptsFor s i
  output : ∀ (i : Nat) (r : Req), s.requests[i]? = some r → r.output.isSome → r.status = .released
  once : cfg.idempotent = false → ∀ (i : Nat) (r : Req), s.requests[i]? = some r → attemptsFor s i ≤ 1 ∧
    (Idle r.status → attemptsFor s i = 0)

/-! ### Request extension: bindings and policies never change, contributions only grow. -/

def Ext (r r' : Req) : Prop :=
  r'.binding = r.binding ∧ r'.policy = r.policy ∧ ∀ c ∈ r.contributions, c ∈ r'.contributions

theorem ext_refl (r : Req) : Ext r r := ⟨rfl, rfl, fun _ h => h⟩

theorem valid_ext {V : Verifiers} {a : Authority} {r r' : Req} (h : Ext r r') (c : Contribution) :
    valid V a r' c = valid V a r c := by
  obtain ⟨hb, hp, _⟩ := h
  simp [valid, hb, hp]

theorem sound_mono {V : Verifiers} {s s' : State} {a : Attempt}
    (hg : ∀ (i : Nat) (q : Req), s.requests[i]? = some q →
      ∃ q', s'.requests[i]? = some q' ∧ Ext q q')
    (h : Sound V s a) : Sound V s' a := by
  obtain ⟨r, hr, hb, hrc, hn, h0, ht, hall⟩ := h
  obtain ⟨r', hr', hx⟩ := hg _ _ hr
  obtain ⟨eb, ep, ec⟩ := hx
  refine ⟨r', hr', hb.trans eb.symm, hrc.trans (by rw [ep]), hn, by rw [ep]; exact h0,
    by rw [ep]; exact ht, ?_⟩
  intro h hm
  obtain ⟨c, hc, hh, hv⟩ := hall h hm
  exact ⟨c, ec c hc, hh, by rw [valid_ext ⟨eb, ep, ec⟩]; exact hv⟩

/-- Looking up an index after `set`: the new request, or an untouched one. -/
theorem lookup_set {l : List Req} {id i : Nat} {r x q : Req} (hr : l[id]? = some r)
    (hq : (l.set id x)[i]? = some q) : (i = id ∧ q = x) ∨ (i ≠ id ∧ l[i]? = some q) := by
  have hlt : id < l.length := (List.getElem?_eq_some_iff.mp hr).1
  by_cases hi : id = i
  · subst hi
    left
    simp [hlt] at hq
    exact ⟨rfl, hq.symm⟩
  · right
    refine ⟨Ne.symm hi, ?_⟩
    simpa [List.getElem?_set, hi] using hq

theorem lookup_set_self {l : List Req} {id : Nat} {r x : Req} (hr : l[id]? = some r) :
    (l.set id x)[id]? = some x := by
  have hlt : id < l.length := (List.getElem?_eq_some_iff.mp hr).1
  simp [hlt]

theorem grows_set {l : List Req} {id : Nat} {r x : Req} (hr : l[id]? = some r) (hx : Ext r x) :
    ∀ (i : Nat) (q : Req), l[i]? = some q → ∃ q', (l.set id x)[i]? = some q' ∧ Ext q q' := by
  intro i q hq
  by_cases hi : i = id
  · subst hi
    rw [hr] at hq
    cases hq
    exact ⟨x, lookup_set_self hr, hx⟩
  · refine ⟨q, ?_, ext_refl q⟩
    simpa [List.getElem?_set, Ne.symm hi] using hq

theorem guard_ok {s : State} {id : Nat} {r : Req} (h : guard s id = .ok r) :
    s.requests[id]? = some r ∧ r.binding.epoch = s.authority.epoch ∧
      ∀ c ∈ r.contributions, c.holder ∉ s.authority.revoked := by
  unfold guard at h
  split at h
  · cases h
  · rename_i r' hr
    split at h
    · cases h
    · rename_i he
      split at h
      · cases h
      · rename_i hrev
        cases h
        refine ⟨hr, by simpa using he, ?_⟩
        intro c hc hm
        exact hrev (List.any_eq_true.mpr ⟨c, hc, by simpa using hm⟩)

/-- Replacing one request (journal unchanged) preserves the invariant when the
replacement extends the old request and its status/output obligations hold. -/
theorem inv_set {V : Verifiers} {cfg : Config} {s s' : State} {id : Nat} {r x : Req}
    (inv : Inv V cfg s) (hr : s.requests[id]? = some r)
    (hreq : s'.requests = s.requests.set id x) (hj : s'.journal = s.journal) (hext : Ext r x)
    (hatt : Active x.status → 0 < attemptsFor s id)
    (hout : x.output.isSome → x.status = .released)
    (honce : cfg.idempotent = false → Idle x.status → attemptsFor s id = 0) :
    Inv V cfg s' := by
  have hcount : ∀ i, attemptsFor s' i = attemptsFor s i := by intro i; simp [attemptsFor, hj]
  constructor
  · intro a ha
    rw [hj] at ha
    have := sound_mono (s' := s') (by rw [hreq]; exact grows_set hr hext) (inv.sound a ha)
    exact this
  · intro i q hq
    rw [hreq] at hq
    rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨_, hq⟩
    · rw [hext.1]; exact inv.canonical _ _ hr
    · exact inv.canonical _ _ hq
  · intro i q hq
    rw [hreq] at hq
    rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨_, hq⟩
    · rw [hext.2.1]; exact inv.wf _ _ hr
    · exact inv.wf _ _ hq
  · intro i q hq hs
    rw [hcount]
    rw [hreq] at hq
    rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨_, hq⟩
    · exact hatt hs
    · exact inv.attempted _ _ hq hs
  · intro i q hq hs
    rw [hreq] at hq
    rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨_, hq⟩
    · exact hout hs
    · exact inv.output _ _ hq hs
  · intro hc i q hq
    simp only [hcount]
    rw [hreq] at hq
    rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨_, hq⟩
    · exact ⟨(inv.once hc _ _ hr).1, honce hc⟩
    · exact inv.once hc _ _ hq

theorem inv_move {V : Verifiers} {cfg : Config} {s s' : State} {id : Nat} {src : List Status}
    {dst : Status} {o : Option String} (inv : Inv V cfg s)
    (hatt : ∀ x ∈ src, Active dst → Active x)
    (hout : o.isSome → dst = .released)
    (honce : ∀ x ∈ src, cfg.idempotent = false → Idle dst → Idle x)
    (h : move s id src dst o = .ok s') : Inv V cfg s' := by
  unfold move at h
  split at h
  · cases h
  · rename_i r hgd
    have hr := (guard_ok hgd).1
    split at h
    · rename_i hm
      cases h
      exact inv_set inv hr rfl rfl (ext_refl r) (fun hd => inv.attempted _ _ hr (hatt _ hm hd))
        hout (fun hc hd => (inv.once hc _ _ hr).2 (honce _ hm hc hd))
    · cases h

theorem inv_respond {V : Verifiers} {cfg : Config} {s s' : State} {id : Nat} {dst : Status}
    {o : Option String} (inv : Inv V cfg s) (hout : o.isSome → dst = .released)
    (hidle : ¬ Idle dst) (h : respond s id dst o = .ok s') : Inv V cfg s' := by
  unfold respond at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i r hr
      split at h
      · cases h
      · rename_i hst
        cases h
        have hst' : r.status = .combining := by simpa using hst
        exact inv_set inv hr rfl rfl (ext_refl r)
          (fun _ => inv.attempted _ _ hr (Or.inl hst')) hout (fun _ hd => absurd hd hidle)

theorem attempt_lt {V : Verifiers} {cfg : Config} {s : State} (inv : Inv V cfg s) :
    ∀ a ∈ s.journal, a.id < s.requests.length := by
  intro a ha
  obtain ⟨r, hr, _⟩ := inv.sound a ha
  exact (List.getElem?_eq_some_iff.mp hr).1

theorem attemptsFor_fresh {V : Verifiers} {cfg : Config} {s : State} (inv : Inv V cfg s) :
    attemptsFor s s.requests.length = 0 := by
  unfold attemptsFor
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro a ha
  have := attempt_lt inv a ha
  simp only [beq_iff_eq]
  omega

theorem signers_sound {V : Verifiers} {a : Authority} {r : Req} :
    ∀ h ∈ signers V a r, ∃ c ∈ r.contributions, c.holder = h ∧ valid V a r c = true := by
  intro h hm
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (mem_dedup.mp hm)
  obtain ⟨hmem, hv⟩ := List.mem_filter.mp hc
  exact ⟨c, hmem, rfl, hv⟩

theorem step_create {V : Verifiers} {cfg : Config} {s s' : State} {k d : String} {p : Policy}
    (inv : Inv V cfg s) (h : step V cfg s (.create k d p) = .ok s') : Inv V cfg s' := by
  simp only [step] at h
  split at h
  · rename_i hwf
    cases h
    have hwf' : 0 < p.threshold := by
      simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hwf
      exact hwf.1.1
    have hfresh := attemptsFor_fresh inv
    -- the appended request
    generalize hn : (⟨⟨s.requests.length, k, s.authority.epoch, d⟩, p, .collecting, [], none⟩ : Req) = n
    have hcases : ∀ (i : Nat) (q : Req), (s.requests ++ [n])[i]? = some q →
        s.requests[i]? = some q ∨ (i = s.requests.length ∧ q = n) := by
      intro i q hq
      rcases Nat.lt_or_ge i s.requests.length with hi | hi
      · left; rwa [List.getElem?_append_left hi] at hq
      · right
        rw [List.getElem?_append_right hi] at hq
        rcases Nat.lt_or_ge i (s.requests.length + 1) with hi' | hi'
        · have : i - s.requests.length = 0 := by omega
          rw [this] at hq
          simp at hq
          exact ⟨by omega, hq.symm⟩
        · obtain ⟨k, hk⟩ : ∃ k, i - s.requests.length = k + 1 :=
            ⟨i - s.requests.length - 1, by omega⟩
          rw [hk] at hq
          simp at hq
    have hold : ∀ (i : Nat) (q : Req), s.requests[i]? = some q →
        ∃ q', (s.requests ++ [n])[i]? = some q' ∧ Ext q q' := fun i q hq =>
      ⟨q, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hq).1]; exact hq,
        ext_refl q⟩
    constructor
    · intro a ha
      exact sound_mono (s' := { s with requests := s.requests ++ [n] }) hold (inv.sound a ha)
    · intro i q hq
      rcases hcases i q hq with hq | ⟨rfl, rfl⟩
      · exact inv.canonical _ _ hq
      · rw [← hn]
    · intro i q hq
      rcases hcases i q hq with hq | ⟨rfl, rfl⟩
      · exact inv.wf _ _ hq
      · rw [← hn]; exact hwf'
    · intro i q hq hs
      rcases hcases i q hq with hq | ⟨rfl, rfl⟩
      · exact inv.attempted _ _ hq hs
      · rw [← hn] at hs; simp [Active] at hs
    · intro i q hq hs
      rcases hcases i q hq with hq | ⟨rfl, rfl⟩
      · exact inv.output _ _ hq hs
      · rw [← hn] at hs; simp at hs
    · intro hc i q hq
      rcases hcases i q hq with hq | ⟨rfl, rfl⟩
      · exact inv.once hc _ _ hq
      · exact ⟨Nat.le_trans (Nat.le_of_eq hfresh) (Nat.zero_le _), fun _ => hfresh⟩
  · cases h

theorem step_contribute {V : Verifiers} {cfg : Config} {s s' : State} {id : Nat}
    {c : Contribution} (inv : Inv V cfg s) (h : step V cfg s (.contribute id c) = .ok s') :
    Inv V cfg s' := by
  simp only [step] at h
  split at h
  · cases h
  · rename_i r hgd
    have hr := (guard_ok hgd).1
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i hst
    split at h; · cases h
    split at h; · cases h
    cases h
    have hst' : r.status = .collecting := by simpa using hst
    refine inv_set inv hr rfl rfl ⟨rfl, rfl, fun d hd => List.mem_append_left _ hd⟩ ?_ ?_ ?_
    · intro hs
      simp only [Active] at hs
      split at hs <;> simp at hs
    · intro ho
      have := inv.output _ _ hr ho
      rw [hst'] at this
      cases this
    · intro hc _
      exact (inv.once hc _ _ hr).2 (Or.inl hst')

theorem step_combine {V : Verifiers} {cfg : Config} {s s' : State} {id : Nat}
    (inv : Inv V cfg s) (h : step V cfg s (.combine id) = .ok s') : Inv V cfg s' := by
  simp only [step] at h
  split at h
  · cases h
  · rename_i r hgd
    have hr := (guard_ok hgd).1
    split at h; · cases h
    rename_i hst
    have hst' : r.status = .quorumReached := by simpa using hst
    split at h
    · rename_i hq
      cases h
      generalize ha : (⟨id, r.binding, r.policy.recipient, signers V s.authority r, s.authority⟩
        : Attempt) = att
      generalize hx : ({ r with status := .combining } : Req) = x
      have hext : Ext r x := by rw [← hx]; exact ext_refl r
      have hcount : ∀ i, ((s.journal ++ [att]).filter (fun b => b.id == i)).length =
          attemptsFor s i + if id = i then 1 else 0 := by
        intro i
        by_cases hi : id = i <;> simp [attemptsFor, List.filter_append, ← ha, hi]
      constructor
      · intro a hm
        rcases List.mem_append.mp hm with hm | hm
        · exact sound_mono (s' := { (update s id x) with
              journal := s.journal ++ [att], inflight := id :: s.inflight })
            (grows_set hr hext) (inv.sound a hm)
        · simp at hm
          subst hm
          rw [← ha]
          refine ⟨x, lookup_set_self hr, by rw [hext.1], by rw [hext.2.1], nodup_dedup _,
            by rw [hext.2.1]; exact inv.wf _ _ hr, by rw [hext.2.1]; exact hq, ?_⟩
          intro h' hm
          obtain ⟨c, hc, hh, hv⟩ := signers_sound h' hm
          exact ⟨c, hext.2.2 c hc, hh, by rw [valid_ext hext]; exact hv⟩
      · intro i q hq
        rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨_, hq⟩
        · rw [hext.1]; exact inv.canonical _ _ hr
        · exact inv.canonical _ _ hq
      · intro i q hq
        rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨_, hq⟩
        · rw [hext.2.1]; exact inv.wf _ _ hr
        · exact inv.wf _ _ hq
      · intro i q hq hs
        show 0 < ((s.journal ++ [att]).filter (fun b => b.id == i)).length
        rw [hcount]
        rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨hi, hq⟩
        · simp
        · have := inv.attempted _ _ hq hs; omega
      · intro i q hq hs
        rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨_, hq⟩
        · have := inv.output _ _ hr (by rw [← hx] at hs; exact hs)
          rw [hst'] at this
          cases this
        · exact inv.output _ _ hq hs
      · intro hc i q hq
        show ((s.journal ++ [att]).filter (fun b => b.id == i)).length ≤ 1 ∧
          (Idle q.status → ((s.journal ++ [att]).filter (fun b => b.id == i)).length = 0)
        rw [hcount]
        rcases lookup_set hr hq with ⟨rfl, rfl⟩ | ⟨hi, hq⟩
        · have := (inv.once hc _ _ hr).2 (Or.inr hst')
          refine ⟨by simp; omega, fun hs => ?_⟩
          rw [← hx] at hs
          simp [Idle] at hs
        · have := inv.once hc _ _ hq
          simpa [Ne.symm hi] using this
    · cases h

theorem step_inv {V : Verifiers} {cfg : Config} {s s' : State} {e : Event}
    (inv : Inv V cfg s) (h : step V cfg s e = .ok s') : Inv V cfg s' := by
  cases e with
  | create k d p => exact step_create inv h
  | contribute id c => exact step_contribute inv h
  | combine id => exact step_combine inv h
  | revoke holder =>
    simp only [step] at h; cases h
    exact ⟨inv.sound, inv.canonical, inv.wf, inv.attempted, inv.output, inv.once⟩
  | rotate =>
    simp only [step] at h; cases h
    exact ⟨inv.sound, inv.canonical, inv.wf, inv.attempted, inv.output, inv.once⟩
  | crash =>
    simp only [step] at h; cases h
    exact ⟨inv.sound, inv.canonical, inv.wf, inv.attempted, inv.output, inv.once⟩
  | backendOk id out =>
    exact inv_respond inv (fun _ => rfl) (by simp [Idle]) h
  | backendFail id =>
    exact inv_respond inv (by simp) (by simp [Idle]) h
  | recoverRetry id =>
    simp only [step] at h
    split at h
    · rename_i hc
      refine inv_move inv (by simp [Active]) (by simp) ?_ h
      intro _ _ hn
      rw [hn] at hc
      cases hc
    · split at h
      · cases h
      · split at h <;> cases h
  | recoverReleased id out =>
    exact inv_move inv (by simp [Active]) (fun _ => rfl) (by simp [Idle]) h
  | recoverFailed id =>
    exact inv_move inv (by simp [Active]) (by simp) (by simp [Idle]) h
  | reject id =>
    exact inv_move inv (by simp [Active]) (by simp) (by simp [Idle]) h
  | expire id =>
    exact inv_move inv (by simp [Active]) (by simp) (by simp [Idle]) h

theorem init_inv (V : Verifiers) (cfg : Config) : Inv V cfg State.init := by
  constructor <;> intros <;> simp_all [State.init]

/-- **Release-state invariant** for every reachable state. -/
theorem reachable_inv {V : Verifiers} {cfg : Config} {s : State} (h : Reachable V cfg s) :
    Inv V cfg s := by
  induction h with
  | init => exact init_inv V cfg
  | step e _ hs ih => exact step_inv ih hs

/-! ## Consequences -/

/-- **Recipient-bound, quorum-backed output.** A request that holds an output
was released through a journaled attempt bound to its canonical binding
(which names the request itself), addressed to the policy recipient, and
backed by at least `threshold` distinct holders, each with a contribution that
verified under the authority current when the attempt was journaled: the
binding's epoch, the holder authorized and unrevoked, signature and proof valid. -/
theorem output_bound {V : Verifiers} {cfg : Config} {s : State} (hs : Reachable V cfg s)
    {i : Nat} {r : Req} (hr : s.requests[i]? = some r) (ho : r.output.isSome) :
    r.status = .released ∧ r.binding.request = i ∧ ∃ a ∈ s.journal, a.id = i ∧
      a.binding = r.binding ∧ a.recipient = r.policy.recipient ∧ a.signers.Nodup ∧
      r.policy.threshold ≤ a.signers.length ∧ ∀ h ∈ a.signers, h ∈ r.policy.holders ∧
        h ∉ a.authority.revoked ∧ a.authority.epoch = r.binding.epoch ∧
        ∃ c ∈ r.contributions, c.holder = h ∧ c.binding = r.binding ∧
          V.sig c = true ∧ V.proof c = true := by
  have inv := reachable_inv hs
  have hrel := inv.output _ _ hr ho
  have hpos := inv.attempted _ _ hr (Or.inr (Or.inl hrel))
  unfold attemptsFor at hpos
  obtain ⟨a, ha, hid⟩ := List.exists_mem_of_length_pos hpos |>.imp fun a h => List.mem_filter.mp h
  have hid : a.id = i := by simpa using hid
  obtain ⟨r', hr', hb, hrc, hn, _, ht, hall⟩ := inv.sound a ha
  rw [hid, hr] at hr'
  cases hr'
  refine ⟨hrel, inv.canonical _ _ hr, a, ha, hid, hb, hrc, hn, ht, ?_⟩
  intro h hm
  obtain ⟨c, hc, rfl, hv⟩ := hall h hm
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hv
  exact ⟨hv.1.1.1.1.1, hv.1.1.2, hv.1.1.1.2.symm, c, hc, rfl, hv.1.1.1.1.2, hv.1.2, hv.2⟩

/-- **At most once.** Without an idempotent backend, no request reaches the
backend twice, whatever crashes, failures and recoveries occur. -/
theorem at_most_once {V : Verifiers} {s : State} (hs : Reachable V ⟨false⟩ s) {i : Nat}
    {r : Req} (hr : s.requests[i]? = some r) : attemptsFor s i ≤ 1 :=
  ((reachable_inv hs).once rfl _ _ hr).1

/-- **Live revocation.** If any recorded contributor is revoked now, `combine` fails
and journals nothing. -/
theorem revoked_blocks_combine {V : Verifiers} {cfg : Config} {s : State} {id : Nat} {r : Req}
    (hr : s.requests[id]? = some r) (hep : r.binding.epoch = s.authority.epoch)
    {c : Contribution} (hc : c ∈ r.contributions) (hrev : c.holder ∈ s.authority.revoked) :
    step V cfg s (.combine id) = .error .revoked := by
  have hany : r.contributions.any (fun c => decide (c.holder ∈ s.authority.revoked)) = true :=
    List.any_eq_true.mpr ⟨c, hc, by simpa using hrev⟩
  simp [step, guard, hr, hep, hany]

/-- **Epoch fencing.** After rotation, a request bound to an older epoch can no
longer change state through any governed transition. -/
theorem stale_blocks_combine {V : Verifiers} {cfg : Config} {s : State} {id : Nat} {r : Req}
    (hr : s.requests[id]? = some r) (hep : r.binding.epoch ≠ s.authority.epoch) :
    step V cfg s (.combine id) = .error .stale := by
  simp [step, guard, hr, hep]

/-- **Crash keeps the durable state** and drops every in-flight backend call, so a
lost response can never complete a release afterwards. -/
theorem crash_durable (V : Verifiers) (cfg : Config) (s : State) :
    step V cfg s .crash = .ok { s with inflight := [] } := rfl

theorem no_response_after_crash (V : Verifiers) (cfg : Config) (s : State) (id : Nat) (o : String) :
    step V cfg { s with inflight := [] } (.backendOk id o) = .error .notInflight := by
  simp [step, respond]

/-! ## Executable traces (shared with `tools/release_conformance.tcl`)

A trace drives the machine through the event alphabet both implementations
share. `combine` carries the backend outcome, and `ok` is the journaled attempt
followed by a response. `fail` reports `backend-failed`, as Tcl's
`COMBINE_FAILED`, and `crash` is process loss after the attempt is journaled.
In conformance runs the verifiers accept every contribution. The authorization
layer (live revocation, epochs, membership) is what Tcl implements today. -/

inductive Outcome where | ok | fail | crash

inductive TraceEvent where
  | create | contribute (id : Nat) (holder : String) | revoke (holder : String) | rotate
  | combine (id : Nat) (o : Outcome) | crash | recover (id : Nat) (disposition : String)
  | reject (id : Nat) | expire (id : Nat)

/-- Observation after a step: `ok` or the error class, then the status and the
journaled attempt count of the step's request (if it exists). -/
structure Obs where
  result : String
  status : Option String
  attempts : Nat

def observe (s : State) (id : Option Nat) (result : String) : Obs :=
  match id with
  | some i => match s.requests[i]? with
    | some r => ⟨result, some r.status.name, attemptsFor s i⟩
    | none => ⟨result, none, 0⟩
  | none => ⟨result, none, 0⟩

def run (V : Verifiers) (cfg : Config) (s : State) (e : Event) : String × State :=
  match step V cfg s e with
  | .ok s' => ("ok", s')
  | .error err => (err.name, s)

def exec (V : Verifiers) (cfg : Config) (p : Policy) (s : State) : TraceEvent → Obs × State
  | .create =>
    let (r, s') := run V cfg s (.create "keyset" "digest" p)
    (observe s' (if r = "ok" then some s.requests.length else none) r, s')
  | .contribute i h =>
    let b := (s.requests[i]?.map Req.binding).getD ⟨i, "", 0, ""⟩
    let (r, s') := run V cfg s (.contribute i ⟨h, b, "", "", ""⟩)
    (observe s' (some i) r, s')
  | .revoke h => let (r, s') := run V cfg s (.revoke h); (observe s' none r, s')
  | .rotate => let (r, s') := run V cfg s .rotate; (observe s' none r, s')
  | .crash => let (r, s') := run V cfg s .crash; (observe s' none r, s')
  | .combine i o =>
    let (r, s') := match step V cfg s (.combine i) with
      | .error err => (err.name, s)
      | .ok s₁ => match o with
        | .ok => run V cfg s₁ (.backendOk i "released")
        | .fail => ("backend-failed", (run V cfg s₁ (.backendFail i)).2)
        | .crash => ("ok", (run V cfg s₁ .crash).2)
    (observe s' (some i) r, s')
  | .recover i d =>
    let e := match d with
      | "retry" => Event.recoverRetry i
      | "released" => .recoverReleased i "recovered"
      | _ => .recoverFailed i
    let (r, s') := run V cfg s e
    (observe s' (some i) r, s')
  | .reject i => let (r, s') := run V cfg s (.reject i); (observe s' (some i) r, s')
  | .expire i => let (r, s') := run V cfg s (.expire i); (observe s' (some i) r, s')

def replay (V : Verifiers) (cfg : Config) (p : Policy) (events : List TraceEvent) : List Obs :=
  (events.foldl (fun (s, acc) e => let (o, s') := exec V cfg p s e; (s', o :: acc))
    (State.init, [])).2.reverse

end TclMesh.Release.Machine
