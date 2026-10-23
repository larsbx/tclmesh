//! Fivefold deontic verdicts (W/N/M/K/H) and their resolution.

pub const VERDICTS: [&str; 5] = ["H", "K", "M", "N", "W"];

#[derive(Debug, PartialEq)]
pub enum Judgment {
    Determinate(&'static str),
    Conflicted(Vec<&'static str>),
}

pub fn known(verdict: &str) -> Option<&'static str> {
    VERDICTS.iter().copied().find(|v| *v == verdict)
}

/// Resolves known verdicts: duplicates collapse, distinct verdicts conflict.
pub fn resolve(verdicts: &[&'static str]) -> Judgment {
    let mut support: Vec<_> = verdicts.to_vec();
    support.sort_unstable();
    support.dedup();
    match support.as_slice() {
        [single] => Judgment::Determinate(single),
        _ => Judgment::Conflicted(support),
    }
}

/// `H` (omit-required) forbids execution; every other verdict admits it.
pub fn admits_execution(verdict: &str) -> bool {
    verdict != "H"
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn duplicates_collapse_and_distinct_conflict() {
        assert_eq!(resolve(&["M", "M"]), Judgment::Determinate("M"));
        assert_eq!(resolve(&["W", "H"]), Judgment::Conflicted(vec!["H", "W"]));
        assert!(!admits_execution("H") && admits_execution("K"));
    }
}
