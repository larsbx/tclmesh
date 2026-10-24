//! Deontic resolution; refines `TclMesh.Deontic.resolve`.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    W,
    N,
    M,
    K,
    H,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Judgment {
    Inapplicable,
    Determinate(Verdict),
    Conflicted,
}

pub fn same(a: Verdict, b: Verdict) -> bool {
    matches!(
        (a, b),
        (Verdict::W, Verdict::W)
            | (Verdict::N, Verdict::N)
            | (Verdict::M, Verdict::M)
            | (Verdict::K, Verdict::K)
            | (Verdict::H, Verdict::H)
    )
}

/// Duplicates collapse; distinct verdicts conflict.
pub fn resolve(vs: &[Verdict]) -> Judgment {
    if vs.is_empty() {
        return Judgment::Inapplicable;
    }
    let first = vs[0];
    let mut i = 1;
    while i < vs.len() {
        if !same(vs[i], first) {
            return Judgment::Conflicted;
        }
        i += 1;
    }
    Judgment::Determinate(first)
}

/// Execution is admitted by a determinate verdict other than `H`.
pub fn admits(vs: &[Verdict]) -> bool {
    match resolve(vs) {
        Judgment::Determinate(v) => !same(v, Verdict::H),
        _ => false,
    }
}
