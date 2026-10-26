//! Tier A evaluation of canonical action descriptors.
//!
//! `evaluate` is a refinement of `::tclmesh::action::evaluate`: on every input
//! it returns the Tcl reference outcome, or fails closed with a
//! `TCLMESH KERNEL NON_CANONICAL` fault where the input relies on Tcl having
//! no value types (a list or dict read as a scalar, a path through a scalar,
//! descriptor parts spelled as strings instead of lists).
//!
//! Data model: JSON strings are Tcl scalars, arrays are Tcl lists, objects are
//! Tcl dicts. Numbers, booleans and null have no canonical meaning.

use crate::deontic;
use serde_json::{json, Map, Value};
use tclmesh_kernel_core::predicate as core;

#[derive(Debug, Clone, PartialEq)]
pub struct Fault {
    pub code: Vec<String>,
}

impl Fault {
    fn new(code: &[&str]) -> Self {
        Fault {
            code: std::iter::once("TCLMESH")
                .chain(code.iter().copied())
                .map(String::from)
                .collect(),
        }
    }

    /// The kernel declines input outside its canonical domain.
    pub fn kernel(reason: &str) -> Self {
        Fault::new(&["KERNEL", "NON_CANONICAL", reason])
    }

    pub fn is_kernel_refusal(&self) -> bool {
        self.code.get(1).map(String::as_str) == Some("KERNEL")
    }
}

pub type Pairs = Vec<(String, String)>;

#[derive(Debug, Clone, PartialEq)]
pub struct Evaluation {
    pub verdict: &'static str,
    /// Final value of each changed field, in first-change order.
    pub changes: Pairs,
    /// Each effect as an ordered dict whose first key is `type`.
    pub effects: Vec<Pairs>,
}

type R<T> = Result<T, Fault>;

fn noncanonical(action_id: &str, field: &str) -> Fault {
    Fault::new(&["ACTION", "NON_CANONICAL", action_id, field])
}

fn string(v: &Value) -> R<&str> {
    v.as_str().ok_or_else(|| Fault::kernel("scalar"))
}

fn array(v: &Value) -> R<&[Value]> {
    v.as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| Fault::kernel("shape"))
}

fn object(v: &Value) -> R<&Map<String, Value>> {
    v.as_object().ok_or_else(|| Fault::kernel("shape"))
}

/// Operator word at position `i`, which must be a string when present.
fn word(items: &[Value], i: usize) -> R<Option<&str>> {
    items.get(i).map(string).transpose()
}

// ---------------------------------------------------------------- validation

fn validate_value(id: &str, field: &str, v: &Value) -> R<()> {
    let items = array(v)?;
    match word(items, 0)? {
        None => Err(noncanonical(id, field)),
        Some("literal") if items.len() == 2 => Ok(()),
        Some("field" | "request") if items.len() >= 2 => Ok(()),
        Some(_) => Err(noncanonical(id, field)),
    }
}

fn validate_predicate(id: &str, field: &str, p: &Value) -> R<()> {
    let items = array(p)?;
    match word(items, 0)? {
        Some("true" | "false") if items.len() == 1 => Ok(()),
        Some("eq" | "neq" | "lt" | "lte" | "gt" | "gte" | "in" | "contains")
            if items.len() == 3 =>
        {
            validate_value(id, field, &items[1])?;
            validate_value(id, field, &items[2])
        }
        Some("and" | "or") if items.len() >= 2 => items[1..]
            .iter()
            .try_for_each(|c| validate_predicate(id, field, c)),
        Some("not") if items.len() == 2 => validate_predicate(id, field, &items[1]),
        _ => Err(noncanonical(id, field)),
    }
}

fn validate(id: &str, d: &Map<String, Value>) -> R<Vec<deontic::Verdict>> {
    if let Some(spec) = d.get("authorize") {
        let items = array(spec)?;
        match word(items, 0)? {
            Some("permit" | "deny") if items.len() == 1 => {}
            Some("permit-if") if items.len() == 2 => {
                validate_predicate(id, "authorize", &items[1])?
            }
            _ => return Err(noncanonical(id, "authorize")),
        }
    }

    let verdicts = match d.get("deontic") {
        None => vec![deontic::Verdict::M],
        Some(v) => {
            let items = array(v)?;
            if items.is_empty() {
                return Err(noncanonical(id, "deontic"));
            }
            items
                .iter()
                .map(|v| {
                    deontic::known(string(v)?)
                        .ok_or_else(|| Fault::new(&["DEONTIC", "INVALID_VERDICT"]))
                })
                .collect::<R<_>>()?
        }
    };

    for v in sequence(d, "validations")? {
        let items = array(v)?;
        if items.len() != 2 || word(items, 0)? != Some("assert") {
            return Err(noncanonical(id, "validations"));
        }
        validate_predicate(id, "validations", &items[1])?;
    }

    for c in sequence(d, "changes")? {
        let items = array(c)?;
        if items.len() != 3 || word(items, 0)? != Some("set") || word(items, 1)? == Some("") {
            return Err(noncanonical(id, "changes"));
        }
        validate_value(id, "changes", &items[2])?;
    }

    for e in sequence(d, "effects")? {
        let items = array(e)?;
        if items.len() < 2
            || word(items, 0)? != Some("emit")
            || word(items, 1)? == Some("")
            || items.len() % 2 != 0
        {
            return Err(noncanonical(id, "effects"));
        }
        for pair in items[2..].chunks(2) {
            if string(&pair[0])?.is_empty() {
                return Err(noncanonical(id, "effects"));
            }
            validate_value(id, "effects", &pair[1])?;
        }
    }

    Ok(verdicts)
}

fn sequence<'a>(d: &'a Map<String, Value>, key: &str) -> R<&'a [Value]> {
    d.get(key).map_or(Ok(&[]), array)
}

// ---------------------------------------------------------------- evaluation

struct Scope<'a> {
    state: &'a Map<String, Value>,
    request: &'a Map<String, Value>,
}

fn walk<'a>(root: &'a Map<String, Value>, path: &[Value], missing: &str) -> R<&'a Value> {
    let mut map = root;
    let (last, init) = path.split_last().expect("validated nonempty path");
    for key in init {
        map = match map.get(string(key)?) {
            None => return Err(Fault::new(&["ACTION", "VALUE", missing])),
            Some(Value::Object(m)) => m,
            Some(_) => return Err(Fault::kernel("path")),
        };
    }
    map.get(string(last)?)
        .ok_or_else(|| Fault::new(&["ACTION", "VALUE", missing]))
}

fn value<'a>(v: &'a Value, s: &Scope<'a>) -> R<&'a Value> {
    let items = array(v)?;
    match string(&items[0])? {
        "literal" => Ok(&items[1]),
        "field" => walk(s.state, &items[1..], "MISSING_FIELD"),
        _ => walk(s.request, &items[1..], "MISSING_REQUEST"),
    }
}

fn scalar<'a>(v: &'a Value, s: &Scope<'a>) -> R<&'a str> {
    value(v, s)?.as_str().ok_or_else(|| Fault::kernel("scalar"))
}

/// Resolves an operand for the verified decision core, recording any fault.
fn res(v: &Value, s: &Scope, faults: &mut Vec<Fault>) -> core::Res {
    match value(v, s) {
        Err(f) => core::Res::Fault(record(faults, f)),
        Ok(Value::String(x)) => core::Res::Str(x.as_bytes().to_vec()),
        Ok(Value::Array(items)) => core::Res::Arr(
            items
                .iter()
                .map(|x| x.as_str().map(|y| y.as_bytes().to_vec()))
                .collect(),
        ),
        Ok(_) => core::Res::Other,
    }
}

fn record(faults: &mut Vec<Fault>, f: Fault) -> usize {
    faults.push(f);
    faults.len() - 1
}

fn lower_leaf(op: &str, args: &[Value], s: &Scope, faults: &mut Vec<Fault>) -> core::Pred {
    use core::{CmpOp, Pred};
    let binary = |f: fn(core::Res, core::Res) -> Pred, faults: &mut Vec<Fault>| {
        let a = res(&args[0], s, faults);
        f(a, res(&args[1], s, faults))
    };
    match (op, args.len()) {
        ("true", _) => Pred::True,
        ("false", _) => Pred::False,
        ("eq", 2) => binary(Pred::Eq, faults),
        ("neq", 2) => binary(Pred::Neq, faults),
        ("lt", 2) => binary(|a, b| Pred::Cmp(CmpOp::Lt, a, b), faults),
        ("lte", 2) => binary(|a, b| Pred::Cmp(CmpOp::Lte, a, b), faults),
        ("gt", 2) => binary(|a, b| Pred::Cmp(CmpOp::Gt, a, b), faults),
        ("gte", 2) => binary(|a, b| Pred::Cmp(CmpOp::Gte, a, b), faults),
        ("in", 2) => binary(Pred::Mem, faults),
        ("contains", 2) => binary(Pred::Contains, faults),
        _ => Pred::Fail(record(faults, Fault::kernel("shape"))),
    }
}

/// Lowers a predicate to the verified core, as `TclMesh.Kernel.lower` does:
/// operands resolved, `and`/`or` right-nested.
fn lower(p: &Value, s: &Scope, faults: &mut Vec<Fault>) -> core::Pred {
    use core::Pred;
    let nested = |cs: &[Value], faults: &mut Vec<Fault>, and: bool| {
        cs.iter()
            .rev()
            .fold(if and { Pred::True } else { Pred::False }, |acc, c| {
                let c = Box::new(lower(c, s, faults));
                if and {
                    Pred::And(c, Box::new(acc))
                } else {
                    Pred::Or(c, Box::new(acc))
                }
            })
    };
    match p.as_array().map(Vec::as_slice) {
        Some([Value::String(not), child]) if not == "not" => {
            Pred::Not(Box::new(lower(child, s, faults)))
        }
        Some([Value::String(and), cs @ ..]) if and == "and" => nested(cs, faults, true),
        Some([Value::String(or), cs @ ..]) if or == "or" => nested(cs, faults, false),
        Some([op, args @ ..]) => match op.as_str() {
            Some(o) => lower_leaf(o, args, s, faults),
            None => Pred::Fail(record(faults, Fault::kernel("scalar"))),
        },
        _ => Pred::Fail(record(faults, Fault::kernel("shape"))),
    }
}

fn op_name(op: core::CmpOp) -> &'static str {
    match op {
        core::CmpOp::Lt => "lt",
        core::CmpOp::Lte => "lte",
        core::CmpOp::Gt => "gt",
        core::CmpOp::Gte => "gte",
    }
}

fn predicate(p: &Value, s: &Scope) -> R<bool> {
    let mut faults = Vec::new();
    let lowered = lower(p, s, &mut faults);
    core::eval(&lowered).map_err(|e| match e {
        core::Error::Given(i) => faults.swap_remove(i),
        core::Error::NotScalar => Fault::kernel("scalar"),
        core::Error::NotList => Fault::kernel("list"),
        core::Error::NonNumeric(op) => {
            Fault::new(&["ACTION", "PREDICATE", "NON_NUMERIC", op_name(op)])
        }
        core::Error::NonCanonicalList => Fault::new(&["ACTION", "PREDICATE", "NON_CANONICAL_LIST"]),
    })
}

/// Inserts or overwrites in place, preserving first-insertion order (Tcl `dict set`).
fn dict_set(pairs: &mut Pairs, key: &str, value: String) {
    match pairs.iter_mut().find(|(k, _)| k == key) {
        Some(slot) => slot.1 = value,
        None => pairs.push((key.to_owned(), value)),
    }
}

pub fn evaluate(
    action_id: &str,
    descriptor: &Value,
    state: &Value,
    request: &Value,
) -> R<Evaluation> {
    let d = object(descriptor)?;
    let verdicts = validate(action_id, d)?;
    let mut state = object(state)?.clone();
    let request = object(request)?;

    let permitted = {
        let scope = Scope {
            state: &state,
            request,
        };
        match d.get("authorize").map(|a| array(a)).transpose()? {
            None => true,
            Some(spec) => match string(&spec[0])? {
                "permit" => true,
                "deny" => false,
                _ => predicate(&spec[1], &scope)?,
            },
        }
    };
    if !permitted {
        return Err(Fault::new(&["ACTION", "AUTHORIZATION", "DENIED"]));
    }

    let verdict = match deontic::resolve(&verdicts) {
        deontic::Judgment::Conflicted | deontic::Judgment::Inapplicable => {
            return Err(Fault::new(&["ACTION", "DEONTIC", "CONFLICT"]))
        }
        deontic::Judgment::Determinate(deontic::Verdict::H) => {
            return Err(Fault::new(&["ACTION", "DEONTIC", "FORBIDDEN"]))
        }
        deontic::Judgment::Determinate(v) => deontic::name(v),
    };

    for v in sequence(d, "validations")? {
        let scope = Scope {
            state: &state,
            request,
        };
        if !predicate(&array(v)?[1], &scope)? {
            return Err(Fault::new(&["ACTION", "VALIDATION", "FAILED"]));
        }
    }

    let mut changed: Vec<String> = Vec::new();
    for c in sequence(d, "changes")? {
        let items = array(c)?;
        let field = string(&items[1])?;
        let new = scalar(
            &items[2],
            &Scope {
                state: &state,
                request,
            },
        )?
        .to_owned();
        state.insert(field.to_owned(), Value::String(new));
        if !changed.iter().any(|f| f == field) {
            changed.push(field.to_owned());
        }
    }

    let scope = Scope {
        state: &state,
        request,
    };
    let effects = sequence(d, "effects")?
        .iter()
        .map(|e| {
            let items = array(e)?;
            let mut effect = vec![("type".to_owned(), string(&items[1])?.to_owned())];
            for pair in items[2..].chunks(2) {
                dict_set(
                    &mut effect,
                    string(&pair[0])?,
                    scalar(&pair[1], &scope)?.to_owned(),
                );
            }
            Ok(effect)
        })
        .collect::<R<_>>()?;

    let changes = changed
        .into_iter()
        .map(|f| {
            let v = state[&f]
                .as_str()
                .expect("changes store scalars")
                .to_owned();
            (f, v)
        })
        .collect();

    Ok(Evaluation {
        verdict,
        changes,
        effects,
    })
}

fn pairs_json(pairs: &Pairs) -> Value {
    pairs.iter().map(|(k, v)| json!([k, v])).collect()
}

/// Outcome in the shared conformance encoding (see `conformance/README.md`).
pub fn outcome(result: &R<Evaluation>) -> Value {
    match result {
        Ok(e) => json!({
            "status": "ok",
            "verdict": e.verdict,
            "changes": pairs_json(&e.changes),
            "effects": e.effects.iter().map(pairs_json).collect::<Vec<_>>(),
        }),
        Err(f) => json!({ "status": "error", "code": f.code }),
    }
}
