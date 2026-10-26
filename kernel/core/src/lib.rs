//! Verified core of the TclMesh Tier A kernel.
//!
//! Plain loops over slices, `Vec`, and enums only: the Rust subset that
//! Aeneas translates into Lean, where each function is proved equal to the
//! specification in `spec/` (see `proof/`). No dependencies, no traits beyond
//! derives, no closures, no iterators.

// Range patterns, iterator adaptors, `?` on Option, and `Vec::is_empty` are
// avoided (as are closures): Aeneas has no Lean model for them, and the translation must stay
// free of axioms. Loops have no early returns.

#![allow(
    clippy::manual_range_contains,
    clippy::len_zero,
    clippy::question_mark,
    clippy::if_same_then_else,
    clippy::manual_map
)]

pub mod decimal;
pub mod deontic;
pub mod predicate;

/// Three-way order, independent of `core::cmp::Ordering` for translation.
#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Order {
    Lt,
    Eq,
    Gt,
}
