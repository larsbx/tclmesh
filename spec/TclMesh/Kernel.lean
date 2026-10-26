import TclMesh.Predicate
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

/-- A resolved operand: bytes, list elements, or the fault resolution raised. -/
def res (s : Scope) (v : Value) : Res :=
  match value s v with
  | .error f => .fault f
  | .ok (.str x) => .str (utf8 x)
  | .ok (.arr xs) => .arr (xs.map fun | .str y => some (utf8 y) | _ => none)
  | .ok _ => .other

/-- Constants, comparisons, membership, containment. -/
def lowerLeaf (s : Scope) : String → List Value → Pred
  | "true", _ => .tt
  | "false", _ => .ff
  | "eq", [a, b] => .eq (res s a) (res s b)
  | "neq", [a, b] => .neq (res s a) (res s b)
  | "lt", [a, b] => .cmp .lt (res s a) (res s b)
  | "lte", [a, b] => .cmp .lte (res s a) (res s b)
  | "gt", [a, b] => .cmp .gt (res s a) (res s b)
  | "gte", [a, b] => .cmp .gte (res s a) (res s b)
  | "in", [n, h] => .mem (res s n) (res s h)
  | "contains", [h, n] => .contains (res s h) (res s n)
  | _, _ => .fail (refusal "shape")

/-- Resolves every operand of a predicate; `and`/`or` become right-nested. -/
def lower (s : Scope) : Value → Pred
  | .arr [.str "not", child] => .not (lower s child)
  | .arr (.str "and" :: cs) => all cs
  | .arr (.str "or" :: cs) => any cs
  | .arr (op :: args) => match string op with
    | .ok o => lowerLeaf s o args
    | .error f => .fail f
  | _ => .fail (refusal "shape")
where
  all : List Value → Pred
    | [] => .tt
    | c :: cs => .and (lower s c) (all cs)
  any : List Value → Pred
    | [] => .ff
    | c :: cs => .or (lower s c) (any cs)

/-- Predicate evaluation: resolution, then decision. Resolution is pure, so
resolving operands that short-circuiting never inspects changes nothing. -/
def predicate (s : Scope) (v : Value) : R Bool := (lower s v).eval

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
  simp only [predicate, lower]
  exact not_ok_true _

end TclMesh.Kernel
