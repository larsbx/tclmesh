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

use crate::{deontic, list, num};
use serde_json::{json, Map, Value};
use std::cmp::Ordering;

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

fn number(op: &str, text: &str) -> R<num::Num> {
    num::parse(text).ok_or_else(|| Fault::new(&["ACTION", "PREDICATE", "NON_NUMERIC", op]))
}

fn noncanonical_list() -> Fault {
    Fault::new(&["ACTION", "PREDICATE", "NON_CANONICAL_LIST"])
}

/// A list element that Tcl renders without backslashes or double quotes:
/// none of either, and braces balanced so brace-quoting suffices.
fn plain_element(item: &Value) -> R<&str> {
    let text = string(item)?;
    let depth = text.chars().try_fold(0usize, |depth, c| match c {
        '\\' | '"' => None,
        '{' => Some(depth + 1),
        '}' => depth.checked_sub(1),
        _ => Some(depth),
    });
    match depth {
        Some(0) => Ok(text),
        _ => Err(noncanonical_list()),
    }
}

fn member(needle: &str, haystack: &Value) -> R<bool> {
    match haystack {
        Value::String(text) => Ok(list::parse(text)
            .ok_or_else(noncanonical_list)?
            .contains(&needle)),
        // Every element is validated before membership is decided: Tcl renders
        // the whole list, so one non-canonical element rejects it.
        Value::Array(items) => Ok(items
            .iter()
            .map(plain_element)
            .collect::<R<Vec<_>>>()?
            .contains(&needle)),
        _ => Err(Fault::kernel("list")),
    }
}

fn predicate(p: &Value, s: &Scope) -> R<bool> {
    let items = array(p)?;
    let op = string(&items[0])?;
    match op {
        "true" => Ok(true),
        "false" => Ok(false),
        "eq" => Ok(scalar(&items[1], s)? == scalar(&items[2], s)?),
        "neq" => Ok(scalar(&items[1], s)? != scalar(&items[2], s)?),
        "lt" | "lte" | "gt" | "gte" => {
            // Both operands are evaluated before either is checked, as in Tcl.
            let (left, right) = (scalar(&items[1], s)?, scalar(&items[2], s)?);
            let order = num::compare(&number(op, left)?, &number(op, right)?);
            Ok(match op {
                "lt" => order == Ordering::Less,
                "lte" => order != Ordering::Greater,
                "gt" => order == Ordering::Greater,
                _ => order != Ordering::Less,
            })
        }
        "in" => {
            let needle = scalar(&items[1], s)?;
            member(needle, value(&items[2], s)?)
        }
        "contains" => {
            let haystack = scalar(&items[1], s)?;
            let needle = scalar(&items[2], s)?;
            Ok(!needle.is_empty() && haystack.contains(needle))
        }
        "and" => items[1..]
            .iter()
            .try_fold(true, |acc, c| Ok(acc && predicate(c, s)?)),
        "or" => items[1..]
            .iter()
            .try_fold(false, |acc, c| Ok(acc || predicate(c, s)?)),
        _ => Ok(!predicate(&items[1], s)?),
    }
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
