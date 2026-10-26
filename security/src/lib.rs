//! Empirical security games for TclMesh mechanisms (`docs/testing.md`).
//!
//! Semantic security and zero knowledge quantify over all efficient
//! adversaries, so tests cannot establish them; they are proved relative to
//! named assumptions. This crate supplies what tests *can* do:
//!
//! * exact advantages on exhaustive small models (`exact`);
//! * falsification games against a battery of concrete adversaries, with
//!   confidence intervals, calibrated on deliberately broken schemes
//!   (`ind_cpa`, `lwe`);
//! * completeness, extractor, simulator and Fiat–Shamir tests for a Σ-protocol
//!   (`zk`).

pub mod exact;
pub mod ind_cpa;
pub mod lwe;
pub mod rng;
pub mod stats;
pub mod zk;
