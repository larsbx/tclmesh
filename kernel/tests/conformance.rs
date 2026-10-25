//! The committed vectors and the outcomes the Tcl reference recorded for them.

use serde_json::Value;
use std::{fs, path::Path};
use tclmesh_kernel::conformance::{self, Relation};

fn load(name: &str) -> Value {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../conformance")
        .join(name);
    serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap()
}

#[test]
fn kernel_refines_tcl_reference_on_committed_vectors() {
    let vectors = load("vectors.json");
    let report = conformance::check(&vectors, &load("expected.json"), Relation::Refines);
    assert!(report.violations.is_empty(), "{:#?}", report.violations);
    assert_eq!(report.total(), vectors["vectors"].as_array().unwrap().len());
    assert!(report.agreed > report.refused);
}
