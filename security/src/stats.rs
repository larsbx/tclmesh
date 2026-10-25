//! Statistics for games: advantage estimates with confidence intervals.

/// Wilson score interval for a binomial proportion at z standard deviations.
pub fn wilson(successes: u64, trials: u64, z: f64) -> (f64, f64) {
    let n = trials as f64;
    let p = successes as f64 / n;
    let denom = 1.0 + z * z / n;
    let centre = (p + z * z / (2.0 * n)) / denom;
    let half = z * (p * (1.0 - p) / n + z * z / (4.0 * n * n)).sqrt() / denom;
    ((centre - half).max(0.0), (centre + half).min(1.0))
}

/// An adversary's measured distinguishing advantage `|2·Pr[win] − 1|`, with
/// the interval implied by the Wilson interval on `Pr[win]`.
#[derive(Clone, Debug)]
pub struct Advantage {
    pub wins: u64,
    pub trials: u64,
    pub estimate: f64,
    pub low: f64,
    pub high: f64,
}

impl Advantage {
    pub fn new(wins: u64, trials: u64, z: f64) -> Self {
        let (lo, hi) = wilson(wins, trials, z);
        let estimate = (2.0 * wins as f64 / trials as f64 - 1.0).abs();
        // |2p − 1| over p ∈ [lo, hi]
        let low = if lo <= 0.5 && hi >= 0.5 {
            0.0
        } else {
            (2.0 * lo - 1.0).abs().min((2.0 * hi - 1.0).abs())
        };
        let high = (2.0 * lo - 1.0).abs().max((2.0 * hi - 1.0).abs());
        Advantage {
            wins,
            trials,
            estimate,
            low,
            high,
        }
    }
}

/// z for a two-sided test at family-wise level `alpha` over `tests` tests
/// (Bonferroni), from a short table: the battery is small.
pub fn bonferroni_z(alpha: f64, tests: usize) -> f64 {
    let per = alpha / tests as f64;
    // z such that P(|Z| > z) = per, tabulated
    let table = [
        (1e-2, 2.576),
        (1e-3, 3.291),
        (1e-4, 3.891),
        (1e-5, 4.417),
        (1e-6, 4.892),
        (1e-7, 5.327),
        (1e-8, 5.731),
    ];
    table
        .iter()
        .find(|(p, _)| per >= *p)
        .map_or(6.109, |(_, z)| *z)
}

/// Total variation distance between two finite distributions given as
/// (outcome, weight) lists with equal total weight.
pub fn total_variation<K: Ord + Clone>(a: &[(K, u64)], b: &[(K, u64)]) -> f64 {
    use std::collections::BTreeMap;
    let mut diff: BTreeMap<K, i128> = BTreeMap::new();
    let (ta, tb): (u64, u64) = (a.iter().map(|x| x.1).sum(), b.iter().map(|x| x.1).sum());
    assert_eq!(ta, tb, "distributions must have the same total weight");
    for (k, w) in a {
        *diff.entry(k.clone()).or_default() += *w as i128;
    }
    for (k, w) in b {
        *diff.entry(k.clone()).or_default() -= *w as i128;
    }
    diff.values().map(|d| d.unsigned_abs()).sum::<u128>() as f64 / (2.0 * ta as f64)
}
