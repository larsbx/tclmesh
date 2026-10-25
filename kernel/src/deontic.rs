//! Fivefold deontic verdicts: the verified implementation in
//! `tclmesh-kernel-core` (`core/src/deontic.rs`), refining
//! `spec/TclMesh/Deontic.lean`.

pub use tclmesh_kernel_core::deontic::{resolve, Judgment, Verdict};

pub fn known(name: &str) -> Option<Verdict> {
    match name {
        "W" => Some(Verdict::W),
        "N" => Some(Verdict::N),
        "M" => Some(Verdict::M),
        "K" => Some(Verdict::K),
        "H" => Some(Verdict::H),
        _ => None,
    }
}

pub fn name(v: Verdict) -> &'static str {
    match v {
        Verdict::W => "W",
        Verdict::N => "N",
        Verdict::M => "M",
        Verdict::K => "K",
        Verdict::H => "H",
    }
}
