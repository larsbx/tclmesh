//! Differential conformance against outcomes recorded by the Tcl reference.
//!
//! Relation checked per vector, with `t` the Tcl outcome and `k` the kernel's:
//!
//! * domain `canonical`: `k = t`;
//! * domain `any` (default): `k = t`, or `k` is a kernel refusal (fail closed).
//!
//! Against the executable Lean specification the relation is `Exact`: the
//! kernel must reproduce every outcome, refusals included.

use crate::{evaluate, outcome};
use serde_json::Value;
use std::collections::BTreeMap;

#[derive(Debug, Default)]
pub struct Report {
    pub agreed: usize,
    pub refused: usize,
    /// Refusal reason (last code word) to count, for coverage visibility.
    pub refusals: BTreeMap<String, usize>,
    pub violations: Vec<String>,
}

impl Report {
    pub fn total(&self) -> usize {
        self.agreed + self.refused + self.violations.len()
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Relation {
    /// Against the Tcl reference: equal, or a kernel refusal off the canonical domain.
    Refines,
    /// Against the Lean specification: equal on every vector.
    Exact,
}

pub fn check(vectors: &Value, expected: &Value, relation: Relation) -> Report {
    let mut report = Report::default();
    let empty = Vec::new();
    for v in vectors["vectors"].as_array().unwrap_or(&empty) {
        let id = v["id"].as_str().unwrap_or("?");
        let Some(tcl) = expected["outcomes"].get(id) else {
            report
                .violations
                .push(format!("{id}: no recorded Tcl outcome"));
            continue;
        };
        let result = evaluate(
            v["action_id"].as_str().unwrap_or(""),
            &v["descriptor"],
            &v["state"],
            &v["request"],
        );
        let kernel = outcome(&result);
        let refusal = match &result {
            Err(f) if f.is_kernel_refusal() => f.code.last().cloned(),
            _ => None,
        };
        if &kernel == tcl {
            report.agreed += 1;
        } else if let Some(reason) = refusal
            .filter(|_| relation == Relation::Refines && v["domain"].as_str() != Some("canonical"))
        {
            report.refused += 1;
            *report.refusals.entry(reason).or_default() += 1;
        } else {
            report
                .violations
                .push(format!("{id}: kernel {kernel} but Tcl {tcl}"));
        }
    }
    report
}
