//! `tclmesh-tfhe`: evaluates TclMesh private circuits under TFHE.
//!
//! One JSON request per line on stdin, one JSON response per line on stdout:
//!
//! ```text
//! {"op":"encrypt","type":"int","value":"120"}         → {"token":1,"bytes":N}
//! {"op":"evaluate","inputs":{..},"nodes":{..},
//!  "output_nodes":{..},"input_types":{..}}             → {"outputs":{name:{"token":..,"bytes":..}},"trace":[ids]}
//! {"op":"decrypt","token":1}                           → {"value":"120"}
//! {"op":"destroy","token":1}                           → {}
//! ```
//!
//! Errors are `{"error": message}`. Ciphertexts never leave the process; the
//! runtime holds opaque token numbers and each ciphertext's serialized size.
//! Every node is computed in the syntactic schedule (`spec/TclMesh/Circuit.lean`),
//! whatever the data: `select` is a homomorphic multiplexer.
//!
//! Test deployment: this process holds the client key as well as the server
//! key. A production deployment keeps the client key with the data owner.

use serde_json::{json, Map, Value};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{BufRead, Write};
use tfhe::prelude::*;
use tfhe::{generate_keys, set_server_key, ClientKey, ConfigBuilder, FheBool, FheInt32};

#[derive(Clone)]
enum Val {
    Int(FheInt32),
    Bool(FheBool),
}

impl Val {
    fn int(&self) -> FheInt32 {
        match self {
            Val::Int(x) => x.clone(),
            Val::Bool(b) => FheInt32::cast_from(b.clone()),
        }
    }

    fn bool(&self) -> FheBool {
        match self {
            Val::Bool(b) => b.clone(),
            Val::Int(x) => x.ne(0),
        }
    }

    fn bytes(&self) -> usize {
        let mut buf = Vec::new();
        let limit = 1 << 30;
        match self {
            Val::Int(x) => tfhe::safe_serialization::safe_serialize(x, &mut buf, limit),
            Val::Bool(b) => tfhe::safe_serialization::safe_serialize(b, &mut buf, limit),
        }
        .expect("serialize ciphertext");
        buf.len()
    }
}

struct Backend {
    client: ClientKey,
    store: HashMap<u64, Val>,
    next: u64,
}

type R<T> = Result<T, String>;

fn text(v: &Value) -> R<String> {
    v.as_str()
        .map(String::from)
        .ok_or_else(|| format!("expected a string, got {v}"))
}

fn words(v: &Value) -> R<Vec<String>> {
    v.as_array()
        .ok_or("expected an array")?
        .iter()
        .map(text)
        .collect()
}

fn object(v: &Value) -> R<&Map<String, Value>> {
    v.as_object()
        .ok_or_else(|| "expected an object".to_string())
}

fn int(s: &str) -> R<i32> {
    s.trim().parse().map_err(|_| format!("not an integer: {s}"))
}

fn refs(w: &[String]) -> Vec<String> {
    let op = w.first().map(String::as_str).unwrap_or("");
    let unary = ["negate", "not", "reduce-sum", "rotate", "polynomial"];
    let binary = [
        "add",
        "subtract",
        "multiply",
        "equal",
        "less-than",
        "less-or-equal",
        "greater-than",
        "greater-or-equal",
        "and",
        "or",
        "lookup",
    ];
    if w.len() < 2 {
        vec![]
    } else if unary.contains(&op) {
        vec![w[1].clone()]
    } else if op == "select" {
        w[1..w.len().min(4)].to_vec()
    } else if binary.contains(&op) {
        w[1..w.len().min(3)].to_vec()
    } else {
        vec![]
    }
}

/// Depth-first post-order from the outputs in sorted name order.
fn schedule(
    nodes: &BTreeMap<String, Vec<String>>,
    outputs: &BTreeMap<String, String>,
) -> Vec<String> {
    fn visit(
        id: &str,
        nodes: &BTreeMap<String, Vec<String>>,
        seen: &mut HashSet<String>,
        order: &mut Vec<String>,
    ) {
        if !seen.insert(id.to_string()) {
            return;
        }
        if let Some(w) = nodes.get(id) {
            for r in refs(w) {
                visit(&r, nodes, seen, order);
            }
        }
        order.push(id.to_string());
    }
    let (mut seen, mut order) = (HashSet::new(), Vec::new());
    for node in outputs.values() {
        visit(node, nodes, &mut seen, &mut order);
    }
    order
}

impl Backend {
    fn new() -> Self {
        let (client, server) = generate_keys(ConfigBuilder::default().build());
        set_server_key(server);
        Backend {
            client,
            store: HashMap::new(),
            next: 0,
        }
    }

    fn keep(&mut self, v: Val) -> Value {
        self.next += 1;
        let bytes = v.bytes();
        self.store.insert(self.next, v);
        json!({"token": self.next, "bytes": bytes})
    }

    fn fresh(&self, ty: &str, value: &str) -> R<Val> {
        Ok(match ty {
            "bool" => Val::Bool(FheBool::encrypt(int(value)? != 0, &self.client)),
            "int" => Val::Int(FheInt32::encrypt(int(value)?, &self.client)),
            other => return Err(format!("unsupported type: {other}")),
        })
    }

    fn trivial(ty: &str, value: &str) -> R<Val> {
        Ok(match ty {
            "bool" => Val::Bool(FheBool::encrypt_trivial(int(value)? != 0)),
            _ => Val::Int(FheInt32::encrypt_trivial(int(value)?)),
        })
    }

    fn token(&self, v: &Value) -> R<&Val> {
        let id = v.as_u64().ok_or("token must be a number")?;
        self.store
            .get(&id)
            .ok_or_else(|| format!("unknown token {id}"))
    }

    fn evaluate(&mut self, req: &Value) -> R<Value> {
        let nodes: BTreeMap<String, Vec<String>> = object(&req["nodes"])?
            .iter()
            .map(|(k, v)| Ok((k.clone(), words(v)?)))
            .collect::<R<_>>()?;
        let outputs: BTreeMap<String, String> = object(&req["output_nodes"])?
            .iter()
            .map(|(k, v)| Ok((k.clone(), text(v)?)))
            .collect::<R<_>>()?;
        let types = object(&req["input_types"])?;
        let inputs = object(&req["inputs"])?;
        let order = schedule(&nodes, &outputs);
        let mut vals: HashMap<String, Val> = HashMap::new();
        for id in &order {
            let w = nodes.get(id).ok_or_else(|| format!("unknown node {id}"))?;
            let arg = |i: usize| -> R<Val> {
                let r = w
                    .get(i)
                    .ok_or_else(|| format!("node {id}: missing operand"))?;
                vals.get(r)
                    .cloned()
                    .ok_or_else(|| format!("node {id}: operand {r} not computed"))
            };
            let v = match w[0].as_str() {
                "input" => {
                    let name = &w[1];
                    let input = inputs
                        .get(name)
                        .ok_or_else(|| format!("missing input {name}"))?;
                    let ty = text(types.get(name).ok_or("missing input type")?)?;
                    if let Some(t) = input.get("cipher") {
                        self.token(t)?.clone()
                    } else {
                        Self::trivial(&ty, &text(&input["public"])?)?
                    }
                }
                "constant" => Self::trivial("int", &w[1])?,
                "add" => Val::Int(arg(1)?.int() + arg(2)?.int()),
                "subtract" => Val::Int(arg(1)?.int() - arg(2)?.int()),
                "multiply" => Val::Int(arg(1)?.int() * arg(2)?.int()),
                "negate" => Val::Int(-arg(1)?.int()),
                "equal" => Val::Bool(arg(1)?.int().eq(arg(2)?.int())),
                "less-than" => Val::Bool(arg(1)?.int().lt(arg(2)?.int())),
                "less-or-equal" => Val::Bool(arg(1)?.int().le(arg(2)?.int())),
                "greater-than" => Val::Bool(arg(1)?.int().gt(arg(2)?.int())),
                "greater-or-equal" => Val::Bool(arg(1)?.int().ge(arg(2)?.int())),
                "and" => Val::Bool(arg(1)?.bool() & arg(2)?.bool()),
                "or" => Val::Bool(arg(1)?.bool() | arg(2)?.bool()),
                "not" => Val::Bool(!arg(1)?.bool()),
                "select" => {
                    let c = arg(1)?.bool();
                    match (arg(2)?, arg(3)?) {
                        (Val::Bool(a), Val::Bool(b)) => Val::Bool((&c & &a) | (!&c & &b)),
                        (a, b) => Val::Int(c.select(&a.int(), &b.int())),
                    }
                }
                other => return Err(format!("unsupported operation under TFHE: {other}")),
            };
            vals.insert(id.clone(), v);
        }
        let mut out = Map::new();
        for (name, node) in &outputs {
            let v = vals.get(node).cloned().ok_or("output not computed")?;
            out.insert(name.clone(), self.keep(v));
        }
        Ok(json!({"outputs": out, "trace": order}))
    }

    fn handle(&mut self, req: &Value) -> R<Value> {
        match req["op"].as_str().unwrap_or("") {
            "encrypt" => {
                let v = self.fresh(&text(&req["type"])?, &text(&req["value"])?)?;
                Ok(self.keep(v))
            }
            "evaluate" => self.evaluate(req),
            "decrypt" => Ok(match self.token(&req["token"])? {
                Val::Int(x) => {
                    let n: i32 = x.decrypt(&self.client);
                    json!({"value": n.to_string()})
                }
                Val::Bool(b) => {
                    let v: bool = b.decrypt(&self.client);
                    json!({"value": if v { "1" } else { "0" }})
                }
            }),
            "destroy" => {
                let id = req["token"].as_u64().ok_or("token must be a number")?;
                self.store.remove(&id);
                Ok(json!({}))
            }
            other => Err(format!("unknown operation: {other}")),
        }
    }
}

fn main() {
    let mut backend = Backend::new();
    let stdout = std::io::stdout();
    for line in std::io::stdin().lock().lines() {
        let Ok(line) = line else { break };
        if line.trim().is_empty() {
            continue;
        }
        let response = serde_json::from_str::<Value>(&line)
            .map_err(|e| e.to_string())
            .and_then(|req| backend.handle(&req))
            .unwrap_or_else(|e| json!({"error": e}));
        let mut out = stdout.lock();
        writeln!(out, "{response}").expect("write response");
        out.flush().expect("flush response");
    }
}
