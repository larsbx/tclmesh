//! `tclmesh-tfhe`: evaluates TclMesh private circuits under TFHE.
//!
//! One JSON request per line on stdin, one JSON response per line on stdout:
//!
//! ```text
//! {"op":"encrypt","type":"int","value":"120",
//!  "width":32}                                         → {"token":1,"bytes":N}
//! {"op":"evaluate","inputs":{..},"nodes":{..},
//!  "output_nodes":{..},"input_types":{..},"width":32} → {"outputs":{name:{"token":..,"bytes":..}},"trace":[ids]}
//! {"op":"decrypt","token":1}                           → {"value":"120"}
//! {"op":"destroy","token":1}                           → {}
//! {"op":"publish","dir":"/path","crs":"/path",
//!  "trusted":["/key.pub"]}                             → {"receipts":[..]} (public
//!                                                         key and CRS; "crs" adopts
//!                                                         one made by
//!                                                         `tclmesh-tfhe-crs`, or
//!                                                         verifies a ceremony
//!                                                         directory, requiring a
//!                                                         contribution signed by a
//!                                                         "trusted" key if given,
//!                                                         and adopts its CRS)
//! {"op":"import","proof":"/path","context":"c",
//!  "lo":"-5","bits":8,"hi":"200","width":32}            → {"token":2,"bytes":N}
//! ```
//!
//! `publish` writes what an encrypting party needs to prove an input without
//! the client key (`tclmesh-tfhe-prove`, `src/lib.rs`). `import` verifies such
//! a proof against its context, offset, width and optional upper bound, and
//! yields `lo + a` for the proven `a < 2^bits`, or `min(lo + a, hi)`: a
//! ciphertext whose range is proved, not claimed.
//!
//! Errors are `{"error": message}`. Ciphertexts never leave the process; the
//! runtime holds opaque token numbers and each ciphertext's serialized size.
//! Every node is computed in the syntactic schedule (`spec/TclMesh/Circuit.lean`),
//! whatever the data: `select` is a homomorphic multiplexer.
//!
//! Integers are `W`-bit words, `FheInt32` or `FheInt64` ("width", fixed by
//! the profile), and wrap modulo 2^W: an overflow under encryption cannot be
//! detected. The runtime advertises results as exact only under profile
//! semantics `int<W>-checked`, which admits only circuits whose range
//! certificate proves that no intermediate leaves the word
//! (`spec/TclMesh/Range.lean`).
//!
//! Test deployment: this process holds the client key as well as the server
//! key. A production deployment keeps the client key with the data owner.

use serde_json::{json, Map, Value};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::{BufRead, Write};
use std::path::Path;
use tclmesh_tfhe::{
    ceremony, config, import_proven, lift, load, save, test, upper_bound_ok, Int, CRS,
    CRS_MAX_BITS, LIMIT, PROVEN_BITS, PUBLIC_KEY, WIDTHS,
};
use tfhe::prelude::*;
use tfhe::zk::CompactPkeCrs;
use tfhe::{
    set_server_key, ClientKey, CompactPublicKey, FheBool, ProvenCompactCiphertextList, ServerKey,
};

#[derive(Clone)]
enum Val {
    Int(Int),
    Bool(FheBool),
}

impl Val {
    /// This value as a `width`-bit integer: a bit is `0` or `1`; an integer
    /// of another width is refused, never converted.
    fn int(&self, width: u32) -> R<Int> {
        match self {
            Val::Int(x) if x.width() == width => Ok(x.clone()),
            Val::Int(x) => Err(format!(
                "a {}-bit integer in a {width}-bit circuit",
                x.width()
            )),
            Val::Bool(b) => Int::from_bool(width, b),
        }
    }

    fn bool(&self) -> FheBool {
        match self {
            Val::Bool(b) => b.clone(),
            Val::Int(x) => x.nonzero(),
        }
    }

    fn bytes(&self) -> usize {
        match self {
            Val::Int(x) => x.bytes(),
            Val::Bool(b) => {
                let mut buf = Vec::new();
                tfhe::safe_serialization::safe_serialize(b, &mut buf, LIMIT)
                    .expect("serialize ciphertext");
                buf.len()
            }
        }
    }
}

struct Backend {
    client: ClientKey,
    public: CompactPublicKey,
    crs: Option<CompactPkeCrs>,
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

fn int(s: &str) -> R<i64> {
    s.trim().parse().map_err(|_| format!("not an integer: {s}"))
}

fn width(req: &Value) -> R<u32> {
    req["width"]
        .as_u64()
        .and_then(|w| u32::try_from(w).ok())
        .filter(|w| WIDTHS.contains(w))
        .ok_or_else(|| format!("width must be one of {WIDTHS:?}"))
}

fn refs(w: &[String]) -> Vec<String> {
    let op = w.first().map(String::as_str).unwrap_or("");
    let unary = [
        "negate",
        "not",
        "reduce-sum",
        "rotate",
        "polynomial",
        "clamp",
    ];
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
        let client = ClientKey::generate(config());
        set_server_key(ServerKey::new(&client));
        Backend {
            public: CompactPublicKey::new(&client),
            crs: None,
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

    fn fresh(&self, ty: &str, value: &str, width: u32) -> R<Val> {
        Ok(match ty {
            "bool" => Val::Bool(FheBool::encrypt(int(value)? != 0, &self.client)),
            "int" => Val::Int(Int::encrypt(width, int(value)?, &self.client)?),
            other => return Err(format!("unsupported type: {other}")),
        })
    }

    fn trivial(ty: &str, value: &str, width: u32) -> R<Val> {
        Ok(match ty {
            "bool" => Val::Bool(FheBool::encrypt_trivial(int(value)? != 0)),
            _ => Val::Int(Int::trivial(width, int(value)?)?),
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
        let w = width(req)?;
        let inputs = object(&req["inputs"])?;
        let order = schedule(&nodes, &outputs);
        let mut vals: HashMap<String, Val> = HashMap::new();
        for id in &order {
            let node = nodes.get(id).ok_or_else(|| format!("unknown node {id}"))?;
            let arg = |i: usize| -> R<Val> {
                let r = node
                    .get(i)
                    .ok_or_else(|| format!("node {id}: missing operand"))?;
                vals.get(r)
                    .cloned()
                    .ok_or_else(|| format!("node {id}: operand {r} not computed"))
            };
            let int = |i: usize| arg(i)?.int(w);
            let v = match node[0].as_str() {
                "input" => {
                    let name = &node[1];
                    let input = inputs
                        .get(name)
                        .ok_or_else(|| format!("missing input {name}"))?;
                    let ty = text(types.get(name).ok_or("missing input type")?)?;
                    if let Some(t) = input.get("cipher") {
                        // Identity outputs and Boolean consumers need not
                        // pass through Val::int, so check width at ingress.
                        match self.token(t)? {
                            Val::Int(x) if x.width() != w => {
                                return Err(format!(
                                    "a {}-bit integer in a {w}-bit circuit",
                                    x.width()
                                ));
                            }
                            value => value.clone(),
                        }
                    } else {
                        Self::trivial(&ty, &text(&input["public"])?, w)?
                    }
                }
                "constant" => Self::trivial("int", &node[1], w)?,
                "add" => Val::Int(lift!(|a, b| a + b, int(1)?, int(2)?)?),
                "subtract" => Val::Int(lift!(|a, b| a - b, int(1)?, int(2)?)?),
                "multiply" => Val::Int(lift!(|a, b| a * b, int(1)?, int(2)?)?),
                "negate" => Val::Int(lift!(|a| -a, int(1)?)),
                "equal" => Val::Bool(test!(|a, b| a.eq(b), int(1)?, int(2)?)?),
                "less-than" => Val::Bool(test!(|a, b| a.lt(b), int(1)?, int(2)?)?),
                "less-or-equal" => Val::Bool(test!(|a, b| a.le(b), int(1)?, int(2)?)?),
                "greater-than" => Val::Bool(test!(|a, b| a.gt(b), int(1)?, int(2)?)?),
                "greater-or-equal" => Val::Bool(test!(|a, b| a.ge(b), int(1)?, int(2)?)?),
                "and" => Val::Bool(arg(1)?.bool() & arg(2)?.bool()),
                "or" => Val::Bool(arg(1)?.bool() | arg(2)?.bool()),
                "not" => Val::Bool(!arg(1)?.bool()),
                // max/min never overflow: the declared range holds whatever
                // the ciphertext held (`spec/TclMesh/Range.lean`, `guarded_sound`).
                "clamp" => {
                    let bound = |i: usize| -> R<Int> {
                        let b = node
                            .get(i)
                            .ok_or_else(|| format!("node {id}: missing bound"))?;
                        Int::trivial(w, crate::int(b)?)
                    };
                    let x = lift!(|x, lo| x.max(&lo), int(1)?, bound(2)?)?;
                    Val::Int(lift!(|x, hi| x.min(&hi), x, bound(3)?)?)
                }
                "select" => {
                    let c = arg(1)?.bool();
                    match (arg(2)?, arg(3)?) {
                        (Val::Bool(a), Val::Bool(b)) => Val::Bool((&c & &a) | (!&c & &b)),
                        (a, b) => Val::Int(lift!(|a, b| c.select(&a, &b), a.int(w)?, b.int(w)?)?),
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

    /// The CRS: adopted from `publish` (generated by another party with
    /// `tclmesh-tfhe-crs`, or by a verified ceremony), or else generated here on first use, in which case
    /// this process, which holds the client key, also knows its trapdoor.
    fn crs(&mut self) -> R<&CompactPkeCrs> {
        if self.crs.is_none() {
            self.crs = Some(
                CompactPkeCrs::from_config(config(), CRS_MAX_BITS).map_err(|e| e.to_string())?,
            );
        }
        Ok(self.crs.as_ref().expect("generated above"))
    }

    fn publish(&mut self, req: &Value) -> R<Value> {
        self.publish_with_rng(req, &mut rand::rngs::OsRng)
    }

    fn publish_with_rng(&mut self, req: &Value, rng: &mut dyn rand::RngCore) -> R<Value> {
        let dir = text(&req["dir"])?;
        let dir = Path::new(&dir);
        let mut receipts = Vec::new();
        let trusted = match req.get("trusted") {
            Some(t) => words(t)?
                .iter()
                .map(|p| ceremony::read_public(Path::new(p)))
                .collect::<R<Vec<_>>>()?,
            None => Vec::new(),
        };
        if let Some(path) = req.get("crs") {
            if self.crs.is_some() {
                return Err("the CRS is already fixed for this process".into());
            }
            let path = text(path)?;
            let path = Path::new(&path);
            self.crs = Some(if path.is_dir() {
                let (rs, crs) = ceremony::verify(path, &trusted, rng)?;
                receipts = rs;
                crs
            } else if trusted.is_empty() {
                load(path)?
            } else {
                return Err("trusted contributors need a ceremony directory".into());
            });
        } else if !trusted.is_empty() {
            return Err("trusted contributors need a ceremony directory".into());
        }
        save(&self.public, &dir.join(PUBLIC_KEY))?;
        save(self.crs()?, &dir.join(CRS))?;
        Ok(json!({"receipts": receipts}))
    }

    /// Verify a proven `bits`-bit offset bound to (context, lo, bits) and
    /// return `lo + a` as a `width`-bit word; `[lo, lo + 2^bits - 1]` must
    /// lie in the word.
    fn import(&mut self, req: &Value) -> R<Value> {
        let bits = req["bits"].as_u64().ok_or("bits must be a number")? as usize;
        if !PROVEN_BITS.contains(&bits) {
            return Err(format!("bits must be one of {PROVEN_BITS:?}"));
        }
        let w = width(req)?;
        let lo = int(&text(&req["lo"])?)?;
        let hi = match req.get("hi") {
            Some(h) => {
                let h = int(&text(h)?)?;
                if !upper_bound_ok(lo, bits, h) {
                    return Err("hi must lie in [lo, lo + 2^bits - 1]".into());
                }
                Some(h)
            }
            None => None,
        };
        let list: ProvenCompactCiphertextList = load(Path::new(&text(&req["proof"])?))?;
        let context = text(&req["context"])?;
        let public = self.public.clone();
        let x = import_proven(&list, self.crs()?, &public, &context, w, lo, bits, hi)?;
        Ok(self.keep(Val::Int(x)))
    }

    fn handle(&mut self, req: &Value) -> R<Value> {
        match req["op"].as_str().unwrap_or("") {
            "encrypt" => {
                let ty = text(&req["type"])?;
                let w = if ty == "int" { width(req)? } else { 32 };
                let v = self.fresh(&ty, &text(&req["value"])?, w)?;
                Ok(self.keep(v))
            }
            "evaluate" => self.evaluate(req),
            "publish" => self.publish(req),
            "import" => self.import(req),
            "decrypt" => Ok(match self.token(&req["token"])? {
                Val::Int(x) => json!({"value": x.decrypt(&self.client).to_string()}),
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

#[cfg(test)]
#[path = "../tests/support/mod.rs"]
mod test_support;

#[cfg(test)]
mod tests {
    use super::*;
    use test_support::{crs_bytes, CeremonyRace};

    #[test]
    fn publish_uses_verified_snapshot_when_ceremony_files_are_replaced() {
        let race = CeremonyRace::new("publish");
        let mut backend = Backend::new();
        let mut rng = race.replacing_rng();
        let response = backend
            .publish_with_rng(&json!({"dir": race.output, "crs": race.ceremony}), &mut rng)
            .unwrap();

        race.assert_replaced(&rng);
        assert_eq!(response["receipts"], json!(race.receipts));
        assert!(
            crs_bytes(backend.crs.as_ref().unwrap()) == race.verified,
            "CRS differs from verified snapshot"
        );
        assert!(std::fs::read(race.output.join(CRS)).unwrap() == race.verified);
        let public: CompactPublicKey = load(&race.output.join(PUBLIC_KEY)).unwrap();
        assert_eq!(public, backend.public);

        // Later publication also uses the fixed in-memory object, despite
        // the ceremony directory now containing the public-trapdoor CRS.
        assert_eq!(
            backend.publish(&json!({"dir": race.output})).unwrap(),
            json!({"receipts": []})
        );
        assert!(std::fs::read(race.output.join(CRS)).unwrap() == race.verified);
        assert!(backend
            .publish(&json!({"dir": race.output, "crs": race.ceremony}))
            .unwrap_err()
            .contains("already fixed"));
    }
}
