//! TclMesh Tier A kernel: canonical action evaluation in Rust.
//!
//! The Tcl reference (`::tclmesh::action::evaluate`) is the specification;
//! this crate refines it and is checked against it by the shared conformance
//! vectors in `../conformance`.

pub mod conformance;
pub mod deontic;
pub mod eval;
pub mod list;
pub mod num;

pub use eval::{evaluate, outcome, Evaluation, Fault};
