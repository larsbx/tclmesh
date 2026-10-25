import Lean.Data.Json
import TclMesh.Kernel
import TclMesh.Circuit

/-!
`lake exe spec-eval VECTORS` evaluates every conformance vector with the
executable specification (`TclMesh.Kernel.evaluate`) and prints the outcomes
in the shared encoding: `{"outcomes": {id: outcome}}`.

`lake exe spec-eval --views CIRCUITS` prints, for every circuit vector, the
evaluator's declared view (`TclMesh.Circuit.declared`): `{"views": {id: view}}`.
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

def main (args : List String) : IO UInt32 := do
  if let ["--views", path] := args then return ← views path
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
