import Lean.Data.Json
import TclMesh.Kernel

/-!
`lake exe spec-eval VECTORS` evaluates every conformance vector with the
executable specification (`TclMesh.Kernel.evaluate`) and prints the outcomes
in the shared encoding: `{"outcomes": {id: outcome}}`.
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

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: spec-eval VECTORS"; return 2
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let vectors ← IO.ofExcept ((json.getObjVal? "vectors").bind Json.getArr?)
  let outcomes := vectors.toList.map fun v =>
    let id := (field v "id").getStr?.toOption.getD "?"
    let actionId := (field v "action_id").getStr?.toOption.getD ""
    (id, outcome (evaluate actionId (toValue (field v "descriptor"))
      (toValue (field v "state")) (toValue (field v "request"))))
  IO.println (Json.mkObj [("outcomes", Json.mkObj outcomes)]).compress
  return 0
