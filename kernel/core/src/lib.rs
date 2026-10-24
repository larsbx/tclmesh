//! Verified core of the TclMesh Tier A kernel.
//!
//! Plain loops over slices, `Vec`, and enums only: the Rust subset that
//! Aeneas translates into Lean, where each function is proved equal to the
//! specification in `spec/` (see `proof/`). No dependencies, no traits beyond
//! derives, no closures, no iterators.

// Range patterns and iterator adaptors are avoided to keep the translation
// to Lean direct.
#![allow(clippy::manual_range_contains)]


pub mod decimal;
pub mod deontic;

/// Three-way order, independent of `core::cmp::Ordering` for translation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Order {
    Lt,
    Eq,
    Gt,
}
