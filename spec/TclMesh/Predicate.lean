import TclMesh.Decimal

/-!
# Predicate decisions

The decision half of Tier A predicate evaluation. `Kernel.lower` resolves a
predicate's operands against the state and request and yields a `Pred`, whose
leaves are already-resolved operands (`Res`): UTF-8 bytes, a list of elements,
or the fault that resolution raised. `Pred.eval` then decides it.

This is the part of the kernel that `kernel/core` implements and `proof/`
proves equal, so it works on bytes, as the Rust kernel does: a Lean `String`
is its UTF-8 bytes (`String.toByteArray`). Every byte the canonical syntax
singles out is ASCII, and no byte of a multi-byte UTF-8 sequence is.
-/

namespace TclMesh.Kernel

abbrev Fault := List String
abbrev R := Except Fault

def fault (code : List String) : Fault := "TCLMESH" :: code
def refusal (reason : String) : Fault := fault ["KERNEL", "NON_CANONICAL", reason]
def refuse {α} (reason : String) : R α := .error (refusal reason)

abbrev Bytes := List UInt8

/-- The UTF-8 bytes of a string. -/
def utf8 (s : String) : Bytes := s.toByteArray.toList

/-! ## Canonical lists -/

def isSpace (b : UInt8) : Bool := b = 32 || b = 9 || b = 10 || b = 11 || b = 12 || b = 13

/-- Content of a brace group up to its matching close, and the rest. -/
def braced : Nat → Bytes → Bytes → Option (Bytes × Bytes)
  | _, [], _ => none
  | 0, 125 :: rest, acc => some (acc.reverse, rest)
  | d + 1, 125 :: rest, acc => braced d rest (125 :: acc)
  | d, 123 :: rest, acc => braced (d + 1) rest (123 :: acc)
  | d, b :: rest, acc => braced d rest (b :: acc)

def listElems : (fuel : Nat) → Bytes → Option (List Bytes)
  | 0, _ => none
  | fuel + 1, bs =>
    match bs.dropWhile isSpace with
    | [] => some []
    | 123 :: rest => do
        let (body, rest) ← braced 0 rest []
        match rest with
        | b :: _ => if isSpace b then (body :: ·) <$> listElems fuel rest else none
        | [] => some [body]
    | bs' =>
        (bs'.takeWhile (fun b => !isSpace b) :: ·) <$> listElems fuel (bs'.dropWhile (fun b => !isSpace b))

/-- Bare words and brace groups only: no backslash, no double quote. -/
def parseList (bs : Bytes) : Option (List Bytes) :=
  if bs.any (fun b => b = 92 || b = 34) then none else listElems (bs.length + 1) bs

/-- A list element Tcl renders without backslashes or quotes. -/
def plainElement (bs : Bytes) : Bool :=
  let step : Option Nat → UInt8 → Option Nat := fun d b => d.bind fun d =>
    if b = 92 || b = 34 then none
    else if b = 123 then some (d + 1)
    else if b = 125 then (if d = 0 then none else some (d - 1))
    else some d
  bs.foldl step (some 0) = some 0

def isInfix (needle hay : Bytes) : Bool :=
  match hay with
  | [] => needle.isEmpty
  | _ :: rest => needle.isPrefixOf hay || isInfix needle rest

/-! ## Resolved predicates -/

/-- A resolved operand: a scalar, a list value (each element a scalar or not),
any other value, or the fault its resolution raised. -/
inductive Res where
  | fault (f : Fault)
  | str (b : Bytes)
  | arr (items : List (Option Bytes))
  | other
  deriving Repr, Inhabited

inductive CmpOp where
  | lt | lte | gt | gte
  deriving Repr, DecidableEq

def CmpOp.name : CmpOp → String
  | .lt => "lt" | .lte => "lte" | .gt => "gt" | .gte => "gte"

def CmpOp.holds : CmpOp → Ordering → Bool
  | .lt, o => o == .lt
  | .lte, o => o != .gt
  | .gt, o => o == .gt
  | .gte, o => o != .lt

/-- A predicate whose operands are resolved. `fail` is a structural fault met
while lowering; `and` and `or` are binary, right-nested. -/
inductive Pred where
  | fail (f : Fault)
  | tt
  | ff
  | eq (a b : Res)
  | neq (a b : Res)
  | cmp (op : CmpOp) (a b : Res)
  | mem (needle haystack : Res)
  | contains (haystack needle : Res)
  | not (p : Pred)
  | and (p q : Pred)
  | or (p q : Pred)
  deriving Repr, Inhabited

def nonCanonicalList {α} : R α := throw (fault ["ACTION", "PREDICATE", "NON_CANONICAL_LIST"])

def Res.scalar : Res → R Bytes
  | .fault f => .error f
  | .str b => pure b
  | _ => refuse "scalar"

/-- The elements of a list value: every one must be a plain scalar. -/
def elements : List (Option Bytes) → R (List Bytes)
  | [] => pure []
  | none :: _ => refuse "scalar"
  | some b :: rest => if plainElement b then (b :: ·) <$> elements rest else nonCanonicalList

/-- Membership. Over a list value every element is validated first, as Tcl
renders the whole list: one non-canonical element rejects it. -/
def Res.member (needle : Bytes) : Res → R Bool
  | .fault f => .error f
  | .str text => match parseList text with
    | some items => pure (items.contains needle)
    | none => nonCanonicalList
  | .arr items => do pure ((← elements items).contains needle)
  | .other => refuse "list"

def number (op : CmpOp) (bs : Bytes) : R Decimal.Dec :=
  match Decimal.parseBytes bs with
  | some n => pure n
  | none => throw (fault ["ACTION", "PREDICATE", "NON_NUMERIC", op.name])

def Pred.eval : Pred → R Bool
  | .fail f => .error f
  | .tt => pure true
  | .ff => pure false
  | .eq a b => do pure ((← a.scalar) == (← b.scalar))
  | .neq a b => do pure ((← a.scalar) != (← b.scalar))
  | .cmp op a b => do
      -- both operands are resolved before either is parsed
      let l ← a.scalar
      let r ← b.scalar
      pure (op.holds ((← number op l).cmp (← number op r)))
  | .mem n h => do h.member (← n.scalar)
  | .contains h n => do
      let hay ← h.scalar
      let needle ← n.scalar
      pure (!needle.isEmpty && isInfix needle hay)
  | .not p => (!·) <$> p.eval
  | .and p q => do if ← p.eval then q.eval else pure false
  | .or p q => do if ← p.eval then pure true else q.eval

/-! ## Properties -/

/-- **Negation cannot launder a fault.** -/
theorem not_ok_true (p : Pred) : (Pred.not p).eval = .ok true ↔ p.eval = .ok false := by
  simp only [Pred.eval]
  cases p.eval with
  | error f => simp [Functor.map, Except.map]
  | ok b => cases b <;> simp [Functor.map, Except.map]

/-- **Ordered comparisons are fail-closed**: success means both operands were
canonical decimals, compared exactly. -/
theorem cmp_ok (op : CmpOp) (a b : Res) (r : Bool) (h : (Pred.cmp op a b).eval = .ok r) :
    ∃ l r' x y, a.scalar = .ok l ∧ b.scalar = .ok r' ∧ Decimal.parseBytes l = some x ∧
      Decimal.parseBytes r' = some y ∧ r = op.holds (x.cmp y) := by
  simp only [Pred.eval, bind, Except.bind, pure, Except.pure] at h
  cases ha : a.scalar with
  | error f => simp [ha] at h
  | ok l =>
    cases hb : b.scalar with
    | error f => simp [ha, hb] at h
    | ok r' =>
      cases hx : Decimal.parseBytes l with
      | none => simp [ha, hb, number, hx, throw, throwThe, MonadExceptOf.throw] at h
      | some x =>
        cases hy : Decimal.parseBytes r' with
        | none => simp [ha, hb, number, hx, hy, throw, throwThe, MonadExceptOf.throw, pure,
            Except.pure] at h
        | some y =>
          simp [ha, hb, number, hx, hy, pure, Except.pure] at h
          exact ⟨l, r', x, y, rfl, rfl, hx, hy, h.symm⟩

end TclMesh.Kernel
