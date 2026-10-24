import TclMesh.Decimal

/-!
# Fail-closed canonical predicates

The predicate language of today's Tier A action descriptors
(`::tclmesh::action::evaluate`, `tclmesh-kernel`). Evaluation either succeeds
with a Boolean or faults; a fault is never turned into permission.

Number comparison and list parsing are parameters of the general theorems; only
their partiality matters there (`none` outside the canonical domain).
`canonicalDomain` instantiates numbers with the exact decimals of
`TclMesh.Decimal`.
-/

namespace TclMesh.Canonical

inductive Fault where
  | missingField | missingRequest | nonNumeric | nonCanonicalList
  deriving DecidableEq, Repr

inductive Term where
  | literal (s : String)
  | field (path : List String)
  | request (path : List String)
  deriving Repr

inductive Cmp where
  | lt | lte | gt | gte
  deriving DecidableEq, Repr

inductive Pred where
  | tt | ff
  | eq (a b : Term) | neq (a b : Term)
  | cmp (c : Cmp) (a b : Term)
  | mem (needle haystack : Term)
  | contains (haystack needle : Term)
  | and (p q : Pred) | or (p q : Pred) | not (p : Pred)
  deriving Repr

structure Env where
  field : List String → Option String
  request : List String → Option String

/-- Canonical-domain parsers: number comparison and list elements. -/
structure Domain where
  compare : String → String → Option Ordering
  list : String → Option (List String)

def Term.eval (env : Env) : Term → Except Fault String
  | .literal s => .ok s
  | .field p => match env.field p with
    | some v => .ok v
    | none => .error .missingField
  | .request p => match env.request p with
    | some v => .ok v
    | none => .error .missingRequest

def Cmp.holds : Cmp → Ordering → Bool
  | .lt, o => o == .lt
  | .lte, o => o != .gt
  | .gt, o => o == .gt
  | .gte, o => o != .lt

def compareTerms (d : Domain) (l r : String) : Except Fault Ordering :=
  match d.compare l r with
  | some o => .ok o
  | none => .error .nonNumeric

def Pred.eval (d : Domain) (env : Env) : Pred → Except Fault Bool
  | .tt => .ok true
  | .ff => .ok false
  | .eq a b => do pure ((← a.eval env) == (← b.eval env))
  | .neq a b => do pure ((← a.eval env) != (← b.eval env))
  | .cmp c a b => do
      -- both operands are evaluated before either is parsed
      let l ← a.eval env
      let r ← b.eval env
      pure (c.holds (← compareTerms d l r))
  | .mem n h => do
      let needle ← n.eval env
      let hay ← h.eval env
      match d.list hay with
      | some items => pure (items.contains needle)
      | none => .error .nonCanonicalList
  | .contains h n => do
      let hay ← h.eval env
      let needle ← n.eval env
      pure (!needle.isEmpty && (hay.splitOn needle).length > 1)
  | .and p q => do if (← p.eval d env) then q.eval d env else pure false
  | .or p q => do if (← p.eval d env) then pure true else q.eval d env
  | .not p => do pure !(← p.eval d env)

/-- Authorization by `permit-if p`. -/
def permits (d : Domain) (env : Env) (p : Pred) : Prop := p.eval d env = .ok true

theorem not_fault {d env p f} : (Pred.not p).eval d env = .error f ↔ p.eval d env = .error f := by
  simp only [Pred.eval]
  cases p.eval d env <;> simp [bind, Except.bind, pure, Except.pure]

/-- **Negation cannot launder a fault.** `not p` permits only when `p`
evaluated successfully to `false`. -/
theorem permits_not {d env p} : permits d env (.not p) ↔ p.eval d env = .ok false := by
  unfold permits
  simp only [Pred.eval]
  cases h : p.eval d env with
  | error f => simp [bind, Except.bind]
  | ok b => cases b <;> simp [bind, Except.bind, pure, Except.pure]

/-- A fault in a conjunct that is reached blocks the conjunction. -/
theorem and_fault_left {d env p q f} (h : p.eval d env = .error f) :
    (Pred.and p q).eval d env = .error f := by
  simp [Pred.eval, h, bind, Except.bind]

/-- Short-circuiting: a false left conjunct decides, even if the right would fault. -/
theorem and_false_left {d env p q} (h : p.eval d env = .ok false) :
    (Pred.and p q).eval d env = .ok false := by
  simp [Pred.eval, h, bind, Except.bind, pure, Except.pure]

theorem or_true_left {d env p q} (h : p.eval d env = .ok true) :
    (Pred.or p q).eval d env = .ok true := by
  simp [Pred.eval, h, bind, Except.bind, pure, Except.pure]

/-- **Comparisons are fail-closed.** A comparison that succeeds had both operands
present and inside the canonical numeric domain. -/
theorem cmp_ok {d env c a b r} (h : (Pred.cmp c a b).eval d env = .ok r) :
    ∃ l r' o, a.eval env = .ok l ∧ b.eval env = .ok r' ∧ d.compare l r' = some o ∧
      r = c.holds o := by
  simp only [Pred.eval] at h
  cases ha : a.eval env with
  | error f => simp [ha, bind, Except.bind] at h
  | ok l =>
    cases hb : b.eval env with
    | error f => simp [ha, hb, bind, Except.bind] at h
    | ok r' =>
      simp only [ha, hb, compareTerms, bind, Except.bind] at h
      cases ho : d.compare l r' with
      | none => simp [ho] at h
      | some o =>
        simp only [ho, pure, Except.pure, Except.ok.injEq] at h
        exact ⟨l, r', o, rfl, rfl, ho, h.symm⟩

/-- The canonical numeric domain: exact decimals. -/
def canonicalDomain (list : String → Option (List String)) : Domain :=
  ⟨Decimal.compareStrings, list⟩

/-- In the canonical domain a successful comparison had two canonical decimals
and reports their exact order. -/
theorem cmp_ok_canonical {list env c a b r} (h : (Pred.cmp c a b).eval (canonicalDomain list) env = .ok r) :
    ∃ l r' x y, a.eval env = .ok l ∧ b.eval env = .ok r' ∧
      Decimal.parse l = some x ∧ Decimal.parse r' = some y ∧ r = c.holds (x.cmp y) := by
  obtain ⟨l, r', o, ha, hb, ho, rfl⟩ := cmp_ok h
  simp only [canonicalDomain, Decimal.compareStrings, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at ho
  obtain ⟨x, hx, y, hy, rfl⟩ := ho
  exact ⟨l, r', x, y, ha, hb, hx, hy, rfl⟩

/-- Membership succeeds only on a canonical list. -/
theorem mem_ok {d env n h r} (hok : (Pred.mem n h).eval d env = .ok r) :
    ∃ hay items, h.eval env = .ok hay ∧ d.list hay = some items := by
  simp only [Pred.eval] at hok
  cases hn : n.eval env with
  | error f => simp [hn, bind, Except.bind] at hok
  | ok needle =>
    cases hh : h.eval env with
    | error f => simp [hn, hh, bind, Except.bind] at hok
    | ok hay =>
      simp only [hn, hh, bind, Except.bind] at hok
      cases hl : d.list hay with
      | none => simp [hl] at hok
      | some items => exact ⟨hay, items, rfl, hl⟩

end TclMesh.Canonical
