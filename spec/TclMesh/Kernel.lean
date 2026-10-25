import TclMesh.Decimal
import TclMesh.Deontic

/-!
# The Tier A kernel, executable

A total model of `tclmesh-kernel`'s `evaluate`: descriptor validation, then
authorization, deontic judgment, validations, sequential changes, and effect
proposals, over the typed data model (strings, lists, dicts). Numbers use
`Decimal`; verdicts use `Deontic.resolve`.

`Oracle.lean` runs this model on the conformance vectors. The Rust kernel must
produce *exactly* the same outcome on every vector, refusals included, and the
Tcl reference must agree with it up to kernel refusals.
-/

namespace TclMesh.Kernel

inductive Value where
  | str (s : String)
  | arr (xs : List Value)
  | obj (kvs : List (String × Value))
  /-- JSON numbers, booleans, and null: no canonical meaning. -/
  | other
  deriving Repr, Inhabited

abbrev Fault := List String
abbrev R := Except Fault

def fault (code : List String) : Fault := "TCLMESH" :: code
def refuse {α} (reason : String) : R α := .error (fault ["KERNEL", "NON_CANONICAL", reason])
def noncanonical {α} (id field : String) : R α := .error (fault ["ACTION", "NON_CANONICAL", id, field])

def string : Value → R String
  | .str s => pure s
  | _ => refuse "scalar"

def array : Value → R (List Value)
  | .arr xs => pure xs
  | _ => refuse "shape"

def object : Value → R (List (String × Value))
  | .obj kvs => pure kvs
  | _ => refuse "shape"

/-- Operator word at position `i`, which must be a string when present. -/
def word (items : List Value) (i : Nat) : R (Option String) :=
  match items[i]? with
  | none => pure none
  | some v => some <$> string v

def get (kvs : List (String × Value)) (k : String) : Option Value := kvs.lookup k

def sequence (d : List (String × Value)) (k : String) : R (List Value) :=
  match get d k with
  | none => pure []
  | some v => array v

/-! ## Canonical lists -/

def isSpace (c : Char) : Bool := c = ' ' || c = '\t' || c = '\n' || c = '\x0b' || c = '\x0c' || c = '\r'

/-- Content of a brace group up to its matching close, and the rest. -/
def braced : Nat → List Char → List Char → Option (List Char × List Char)
  | _, [], _ => none
  | 0, '}' :: rest, acc => some (acc.reverse, rest)
  | d + 1, '}' :: rest, acc => braced d rest ('}' :: acc)
  | d, '{' :: rest, acc => braced (d + 1) rest ('{' :: acc)
  | d, c :: rest, acc => braced d rest (c :: acc)

def listElems : (fuel : Nat) → List Char → Option (List String)
  | 0, _ => none
  | fuel + 1, cs =>
    match cs.dropWhile isSpace with
    | [] => some []
    | '{' :: rest => do
        let (body, rest) ← braced 0 rest []
        match rest with
        | c :: _ => if isSpace c then (String.ofList body :: ·) <$> listElems fuel rest else none
        | [] => some [String.ofList body]
    | cs' =>
        let word := cs'.takeWhile (fun c => !isSpace c)
        (String.ofList word :: ·) <$> listElems fuel (cs'.dropWhile (fun c => !isSpace c))

/-- Bare words and brace groups only: no backslash, no double quote. -/
def parseList (s : String) : Option (List String) :=
  let cs := s.toList
  if cs.any (fun c => c = '\\' || c = '"') then none else listElems (cs.length + 1) cs

/-- A list element Tcl renders without backslashes or quotes. -/
def plainElement (s : String) : Bool :=
  let step : Option Nat → Char → Option Nat := fun d c => d.bind fun d =>
    if c = '\\' || c = '"' then none
    else if c = '{' then some (d + 1)
    else if c = '}' then (if d = 0 then none else some (d - 1))
    else some d
  s.toList.foldl step (some 0) = some 0

/-! ## Validation -/

def validateValue (id field : String) (v : Value) : R Unit := do
  let items ← array v
  match ← word items 0 with
  | some "literal" => if items.length = 2 then pure () else noncanonical id field
  | some "field" | some "request" => if items.length ≥ 2 then pure () else noncanonical id field
  | _ => noncanonical id field

def binaryOps : List String := ["eq", "neq", "lt", "lte", "gt", "gte", "in", "contains"]

def validatePredicate (id field : String) : Value → R Unit
  | .arr items => do
    match ← word items 0 with
    | some "true" | some "false" => if items.length = 1 then pure () else noncanonical id field
    | some "and" | some "or" =>
        match items with
        | _ :: rest => if rest.isEmpty then noncanonical id field else validateAll rest
        | [] => noncanonical id field
    | some "not" =>
        match items with
        | [_, child] => validatePredicate id field child
        | _ => noncanonical id field
    | some op =>
        match items with
        | [_, a, b] => if op ∈ binaryOps then do validateValue id field a; validateValue id field b
                       else noncanonical id field
        | _ => noncanonical id field
    | none => noncanonical id field
  | _ => refuse "shape"
where
  validateAll : List Value → R Unit
    | [] => pure ()
    | c :: cs => do validatePredicate id field c; validateAll cs

def verdictOf : String → Option Deontic.Verdict
  | "W" => some .W | "N" => some .N | "M" => some .M | "K" => some .K | "H" => some .H
  | _ => none

def Deontic.Verdict.name : Deontic.Verdict → String
  | .W => "W" | .N => "N" | .M => "M" | .K => "K" | .H => "H"

def validate (id : String) (d : List (String × Value)) : R (List Deontic.Verdict) := do
  if let some spec := get d "authorize" then
    let items ← array spec
    match ← word items 0 with
    | some "permit" | some "deny" => unless items.length = 1 do noncanonical id "authorize"
    | some "permit-if" =>
        match items with
        | [_, p] => validatePredicate id "authorize" p
        | _ => noncanonical id "authorize"
    | _ => noncanonical id "authorize"
  let verdicts ← match get d "deontic" with
    | none => pure [.M]
    | some v => do
        let items ← array v
        if items.isEmpty then noncanonical id "deontic" else
        items.mapM fun v => do
          match verdictOf (← string v) with
          | some verdict => pure verdict
          | none => throw (fault ["DEONTIC", "INVALID_VERDICT"])
  for v in ← sequence d "validations" do
    let items ← array v
    if items.length ≠ 2 then noncanonical id "validations"
    if (← word items 0) ≠ some "assert" then noncanonical id "validations"
    validatePredicate id "validations" items[1]!
  for c in ← sequence d "changes" do
    let items ← array c
    if items.length ≠ 3 then noncanonical id "changes"
    if (← word items 0) ≠ some "set" then noncanonical id "changes"
    if (← word items 1) = some "" then noncanonical id "changes"
    validateValue id "changes" items[2]!
  for e in ← sequence d "effects" do
    let items ← array e
    if items.length < 2 then noncanonical id "effects"
    if (← word items 0) ≠ some "emit" then noncanonical id "effects"
    if (← word items 1) = some "" then noncanonical id "effects"
    if items.length % 2 ≠ 0 then noncanonical id "effects"
    for (name, value) in pairs (items.drop 2) do
      if (← string name).isEmpty then noncanonical id "effects"
      validateValue id "effects" value
  pure verdicts
where
  pairs : List Value → List (Value × Value)
    | a :: b :: rest => (a, b) :: pairs rest
    | _ => []

/-! ## Evaluation -/

structure Scope where
  state : List (String × Value)
  request : List (String × Value)

def walk (root : List (String × Value)) (missing : String) : List Value → R Value
  | [] => refuse "path"
  | [k] => do
      match get root (← string k) with
      | some v => pure v
      | none => throw (fault ["ACTION", "VALUE", missing])
  | k :: rest => do
      match get root (← string k) with
      | none => throw (fault ["ACTION", "VALUE", missing])
      | some (.obj m) => walk m missing rest
      | some _ => refuse "path"

def value (s : Scope) (v : Value) : R Value := do
  let items ← array v
  match ← string items[0]! with
  | "literal" => pure items[1]!
  | "field" => walk s.state "MISSING_FIELD" (items.drop 1)
  | _ => walk s.request "MISSING_REQUEST" (items.drop 1)

def scalar (s : Scope) (v : Value) : R String := do
  match ← value s v with
  | .str x => pure x
  | _ => refuse "scalar"

def number (op text : String) : R Decimal.Dec :=
  match Decimal.parse text with
  | some n => pure n
  | none => throw (fault ["ACTION", "PREDICATE", "NON_NUMERIC", op])

def nonCanonicalList {α} : R α := throw (fault ["ACTION", "PREDICATE", "NON_CANONICAL_LIST"])

/-- Membership. Over a list value every element is validated first, as Tcl
renders the whole list: one non-canonical element rejects it. -/
def member (needle : String) : Value → R Bool
  | .str text => match parseList text with
    | some items => pure (items.contains needle)
    | none => nonCanonicalList
  | .arr items => do pure ((← elements items).contains needle)
  | _ => refuse "list"
where
  elements : List Value → R (List String)
    | [] => pure []
    | x :: xs => do
      let s ← string x
      if !plainElement s then nonCanonicalList else (s :: ·) <$> elements xs

def isInfix (needle hay : List Char) : Bool :=
  match hay with
  | [] => needle.isEmpty
  | _ :: rest => needle.isPrefixOf hay || isInfix needle rest

def holds (op : String) (o : Ordering) : Bool :=
  match op with
  | "lt" => o == .lt
  | "lte" => o != .gt
  | "gt" => o == .gt
  | _ => o != .lt

/-- Non-recursive predicates: constants, comparisons, membership, containment. -/
def leaf (s : Scope) (op : String) (args : List Value) : R Bool :=
  match op, args with
  | "true", _ => pure true
  | "false", _ => pure false
  | "eq", [a, b] => do pure ((← scalar s a) == (← scalar s b))
  | "neq", [a, b] => do pure ((← scalar s a) != (← scalar s b))
  | "in", [n, h] => do
      let needle ← scalar s n
      member needle (← value s h)
  | "contains", [h, n] => do
      let hay ← scalar s h
      let needle ← scalar s n
      pure (!needle.isEmpty && isInfix needle.toList hay.toList)
  | op, [a, b] => do
      -- lt, lte, gt, gte (validated); both operands evaluate before parsing
      let l ← scalar s a
      let r ← scalar s b
      pure (holds op ((← number op l).cmp (← number op r)))
  | _, _ => refuse "shape"

def predicate (s : Scope) : Value → R Bool
  | .arr [.str "not", child] => (!·) <$> predicate s child
  | .arr (.str "and" :: cs) => all cs
  | .arr (.str "or" :: cs) => any cs
  | .arr (op :: args) => do leaf s (← string op) args
  | _ => refuse "shape"
where
  all : List Value → R Bool
    | [] => pure true
    | c :: cs => do if ← predicate s c then all cs else pure false
  any : List Value → R Bool
    | [] => pure false
    | c :: cs => do if ← predicate s c then pure true else any cs

/-- Insert or overwrite in place (Tcl `dict set`). -/
def dictSet (kvs : List (String × α)) (k : String) (v : α) : List (String × α) :=
  if kvs.any (·.1 == k) then kvs.map fun p => if p.1 == k then (k, v) else p else kvs ++ [(k, v)]

structure Evaluation where
  verdict : String
  changes : List (String × String)
  effects : List (List (String × String))

def evaluate (id : String) (descriptor state request : Value) : R Evaluation := do
  let d ← object descriptor
  let verdicts ← validate id d
  let state ← object state
  let request ← object request
  let permitted ← match get d "authorize" with
    | none => pure true
    | some a => do
        let spec ← array a
        match ← string spec[0]! with
        | "permit" => pure true
        | "deny" => pure false
        | _ => predicate ⟨state, request⟩ spec[1]!
  unless permitted do throw (fault ["ACTION", "AUTHORIZATION", "DENIED"])
  let verdict ← match Deontic.resolve verdicts with
    | .determinate .H => throw (fault ["ACTION", "DEONTIC", "FORBIDDEN"])
    | .determinate v => pure v
    | _ => throw (fault ["ACTION", "DEONTIC", "CONFLICT"])
  for v in ← sequence d "validations" do
    unless ← predicate ⟨state, request⟩ (← array v)[1]! do
      throw (fault ["ACTION", "VALIDATION", "FAILED"])
  let mut state := state
  let mut changed : List String := []
  for c in ← sequence d "changes" do
    let items ← array c
    let field ← string items[1]!
    let new ← scalar ⟨state, request⟩ items[2]!
    state := dictSet state field (.str new)
    unless changed.contains field do changed := changed ++ [field]
  let scope : Scope := ⟨state, request⟩
  let effects ← (← sequence d "effects").mapM fun e => do
    let items ← array e
    let mut effect := [("type", ← string items[1]!)]
    for (name, v) in validate.pairs (items.drop 2) do
      effect := dictSet effect (← string name) (← scalar scope v)
    pure effect
  let changes := changed.map fun f => (f, match get state f with
    | some (.str x) => x
    | _ => "")
  pure ⟨Deontic.Verdict.name verdict, changes, effects⟩

end TclMesh.Kernel

namespace TclMesh.Kernel

/-! ## Properties of the executable kernel -/

/-- **Negation cannot launder a fault**, in the executable kernel itself. -/
theorem not_permits (s : Scope) (c : Value) :
    predicate s (.arr [.str "not", c]) = .ok true ↔ predicate s c = .ok false := by
  rw [predicate]
  cases predicate s c with
  | error f => simp [Functor.map, Except.map]
  | ok b => cases b <;> simp [Functor.map, Except.map]

/-- **Ordered comparisons are fail-closed** in the executable kernel: success
means both operands were canonical decimals, compared exactly. -/
theorem cmp_ok (s : Scope) (op : String) (a b : Value) (r : Bool)
    (hop : op ∈ ["lt", "lte", "gt", "gte"])
    (h : leaf s op [a, b] = .ok r) :
    ∃ l r' x y, scalar s a = .ok l ∧ scalar s b = .ok r' ∧ Decimal.parse l = some x ∧
      Decimal.parse r' = some y ∧ r = holds op (x.cmp y) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl <;>
  · simp only [leaf, bind, Except.bind, pure, Except.pure] at h
    cases ha : scalar s a with
    | error f => simp [ha] at h
    | ok l =>
      cases hb : scalar s b with
      | error f => simp [ha, hb] at h
      | ok r' =>
        cases hx : Decimal.parse l with
        | none => simp [ha, hb, number, hx, throw, throwThe, MonadExceptOf.throw] at h
        | some x =>
          cases hy : Decimal.parse r' with
          | none => simp [ha, hb, number, hx, hy, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
          | some y =>
            simp [ha, hb, number, hx, hy, pure, Except.pure] at h
            exact ⟨l, r', x, y, rfl, rfl, hx, hy, h.symm⟩

end TclMesh.Kernel
