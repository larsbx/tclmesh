import Lean.Data.Json
import TclMesh.Kernel
import TclMesh.Certificate
import TclMesh.Range

/-!
`lake exe spec-eval VECTORS` evaluates every conformance vector with the
executable specification (`TclMesh.Kernel.evaluate`) and prints the outcomes
in the shared encoding: `{"outcomes": {id: outcome}}`.

`lake exe spec-eval --views CIRCUITS` prints, for every circuit vector, the
evaluator's declared view (`TclMesh.Circuit.declared`): `{"views": {id: view}}`.

`lake exe spec-eval --certificates CERTS` checks every certificate with the
proved checker (`TclMesh.Circuit.check`) and prints the verdict and the least
certificate (`certify`): `{"certificates": {id: {accepted, least}}}`.

`lake exe spec-eval --ranges RANGES` checks every range certificate with the
proved checker (`TclMesh.Range.check`) and prints the verdict and the least
certificate, or `null`: `{"ranges": {id: {accepted, least}}}`.

`lake exe spec-eval --word-range CORPUS` replays the upstream word-range
corpus (larsbx/finite-math-kernels, `UPSTREAM.toml`) against
`TclMesh.Range.fit`, `wordOp` and `wrap`, prints
`{"word_range": {"rows": n, "mismatches": [row]}}`, and fails on a mismatch.
-/

open Lean TclMesh.Kernel

partial def toValue : Json → Value
  | .str s => .str s
  | .arr xs => .arr (xs.toList.map toValue)
  | .obj kvs => .obj (kvs.toList.map fun (k, v) => (k, toValue v))
  | _ => .other

def pairsJson (ps : List (String × String)) : Json :=
  Json.arr (ps.toArray.map fun (k, v) => Json.arr #[Json.str k, Json.str v])

def outcome : R Evaluation → Json
  | .ok e => Json.mkObj [
      ("status", "ok"), ("verdict", e.verdict),
      ("changes", pairsJson e.changes),
      ("effects", Json.arr (e.effects.toArray.map pairsJson))]
  | .error code => Json.mkObj [("status", "error"), ("code", Json.arr (code.toArray.map Json.str))]

def field (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD .null

def strings (j : Json) : List String :=
  (j.getArr?.toOption.getD #[]).toList.map fun x => x.getStr?.toOption.getD ""

def entries (j : Json) : List (String × Json) :=
  match j.getObj? with
  | .ok kvs => kvs.toList
  | .error _ => []

def circuitOf (j : Json) : TclMesh.Circuit.Circuit where
  inputs := (entries (field j "inputs")).map fun (k, v) => (k, strings v)
  outputs := (entries (field j "outputs")).map fun (k, v) => (k, strings v)
  nodes := (entries (field j "nodes")).map fun (k, v) => (k, strings v)
  outputNodes := (entries (field j "output_nodes")).map fun (k, v) => (k, v.getStr?.toOption.getD "")

def viewJson (v : TclMesh.Circuit.View) : Json := Json.mkObj [
  ("inputs", Json.mkObj (v.inputs.map fun (k, s) => (k, match s with
    | .pub t x => Json.arr #["public", t, x]
    | .cipher t => Json.arr #["cipher", t]))),
  ("trace", Json.arr (v.trace.toArray.map fun (i, o) => Json.arr #[i, o])),
  ("outputs", Json.mkObj (v.outputs.map fun (k, t) => (k, Json.arr #["cipher", t])))]

def views (path : String) : IO UInt32 := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let vectors ← IO.ofExcept ((json.getObjVal? "vectors").bind Json.getArr?)
  let out := vectors.toList.map fun v =>
    let id := (field v "id").getStr?.toOption.getD "?"
    let publics := (entries (field v "inputs")).map fun (k, x) => (k, x.getStr?.toOption.getD "")
    (id, viewJson (TclMesh.Circuit.declared (circuitOf (field v "circuit")) publics))
  IO.println (Json.mkObj [("views", Json.mkObj out)]).compress
  return 0

def labelOf (j : Json) : TclMesh.Circuit.Label :=
  if j.getStr?.toOption = some "public" then .pub else .cipher

def certificateOf (j : Json) : TclMesh.Circuit.Certificate where
  labels := (entries (field j "labels")).map fun (k, v) => (k, labelOf v)
  oblivious := strings (field j "oblivious")

def certificateJson (cert : TclMesh.Circuit.Certificate) : Json := Json.mkObj [
  ("labels", Json.mkObj (cert.labels.map fun (k, l) =>
    (k, Json.str (match l with | .pub => "public" | .cipher => "cipher")))),
  ("oblivious", Json.arr (cert.oblivious.toArray.map Json.str))]

def certificates (path : String) : IO UInt32 := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let vectors ← IO.ofExcept ((json.getObjVal? "vectors").bind Json.getArr?)
  let out := vectors.toList.map fun v =>
    let id := (field v "id").getStr?.toOption.getD "?"
    let c := circuitOf (field v "circuit")
    (id, Json.mkObj [
      ("accepted", Json.bool (TclMesh.Circuit.check c (certificateOf (field v "certificate")))),
      ("least", certificateJson (TclMesh.Circuit.certify c))])
  IO.println (Json.mkObj [("certificates", Json.mkObj out)]).compress
  return 0

def rngOf (j : Json) : TclMesh.Range.Rng :=
  match strings j with
  | [lo, hi] => ((TclMesh.Range.intOf lo).getD 0, (TclMesh.Range.intOf hi).getD 0)
  | _ => (1, 0)

def rngJson (r : TclMesh.Range.Rng) : Json := Json.arr #[toString r.1, toString r.2]

def ranges (path : String) : IO UInt32 := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let vectors ← IO.ofExcept ((json.getObjVal? "vectors").bind Json.getArr?)
  let out := vectors.toList.map fun v =>
    let id := (field v "id").getStr?.toOption.getD "?"
    let c := circuitOf (field v "circuit")
    let w := (field v "width").getNat?.toOption.getD 0
    let cert := (entries (field v "ranges")).map fun (k, r) => (k, rngOf r)
    (id, Json.mkObj [
      ("accepted", Json.bool (TclMesh.Range.check c cert w)),
      ("least", match TclMesh.Range.certify c w with
        | some least => Json.mkObj (least.map fun (k, r) => (k, rngJson r))
        | none => Json.null)])
  IO.println (Json.mkObj [("ranges", Json.mkObj out)]).compress
  return 0

def cellOf (s : String) : Option TclMesh.Range.Rng :=
  match s.splitOn "," with
  | [lo, hi] => do pure ((← lo.toInt?), (← hi.toInt?))
  | _ => none

/-- `none` when the row is malformed, else whether the model agrees with it. -/
def wordRow (row : String) : Option Bool :=
  match row.splitOn "\t" with
  | ["make", w, lo, hi, want] => do
    pure (TclMesh.Range.fit (← w.toNat?) ((← lo.toInt?), (← hi.toInt?)) = cellOf want)
  | ["wrap", w, x, want] => do
    pure (TclMesh.Range.wrap (← w.toNat?) (← x.toInt?) = (← want.toInt?))
  | ["range", op, w, a, b, want] => do
    let args ← (if b = "-" then [a] else [a, b]).mapM fun t =>
      if t = "refused" then some (1, 0) else cellOf t
    pure (TclMesh.Range.wordOp (← w.toNat?) op args = cellOf want)
  | _ => none

def wordRange (path : String) : IO UInt32 := do
  let rows := ((← IO.FS.readFile path).splitOn "\n").filter fun r => !r.isEmpty && !r.startsWith "#"
  let bad := rows.filter fun r => wordRow r != some true
  IO.println (Json.mkObj [("word_range", Json.mkObj [
    ("rows", Json.num rows.length), ("mismatches", Json.arr (bad.toArray.map Json.str))])]).compress
  return if bad.isEmpty && !rows.isEmpty then 0 else 1

def main (args : List String) : IO UInt32 := do
  if let ["--views", path] := args then return ← views path
  if let ["--certificates", path] := args then return ← certificates path
  if let ["--ranges", path] := args then return ← ranges path
  if let ["--word-range", path] := args then return ← wordRange path
  let [path] := args | IO.eprintln "usage: spec-eval VECTORS | spec-eval --views CIRCUITS"; return 2
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let vectors ← IO.ofExcept ((json.getObjVal? "vectors").bind Json.getArr?)
  let outcomes := vectors.toList.map fun v =>
    let id := (field v "id").getStr?.toOption.getD "?"
    let actionId := (field v "action_id").getStr?.toOption.getD ""
    (id, outcome (evaluate actionId (toValue (field v "descriptor"))
      (toValue (field v "state")) (toValue (field v "request"))))
  IO.println (Json.mkObj [("outcomes", Json.mkObj outcomes)]).compress
  return 0
