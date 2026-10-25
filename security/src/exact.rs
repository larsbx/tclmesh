//! Exhaustive small models: with toy parameters every distribution is finite,
//! so the best possible single-ciphertext distinguishing advantage is
//! *computed*, not estimated. It is the total variation distance between the
//! ciphertext distributions of the two messages, averaged over keys.

use crate::stats::total_variation;
use std::collections::BTreeMap;

fn tally(map: BTreeMap<Vec<u64>, u64>) -> Vec<(Vec<u64>, u64)> {
    map.into_iter().collect()
}

/// Every vector in `Z_q^n`.
fn vectors(n: usize, q: u64) -> Vec<Vec<u64>> {
    (0..n).fold(vec![vec![]], |acc, _| {
        acc.into_iter()
            .flat_map(|v| {
                (0..q).map(move |x| {
                    let mut w = v.clone();
                    w.push(x);
                    w
                })
            })
            .collect()
    })
}

/// Exact distribution of a Regev ciphertext of `m` over uniform key, `a` and
/// noise in `-noise..=noise`.
pub fn regev_distribution(n: usize, q: u64, noise: i64, m: bool) -> Vec<(Vec<u64>, u64)> {
    let mut out = BTreeMap::new();
    let keys = vectors(n, q);
    let samples = vectors(n, q);
    for s in &keys {
        for a in &samples {
            let dot: u64 = a.iter().zip(s).map(|(x, y)| x * y).sum::<u64>() % q;
            for e in -noise..=noise {
                let b = (dot as i64 + e + if m { (q / 2) as i64 } else { 0 }).rem_euclid(q as i64)
                    as u64;
                let mut ct = a.clone();
                ct.push(b);
                *out.entry(ct).or_insert(0) += 1;
            }
        }
    }
    tally(out)
}

/// The best single-ciphertext advantage against toy Regev: exactly the
/// probability that `a = 0` when the noise supports of `0` and `⌊q/2⌋` are
/// disjoint, that is `q^{-n}`. Negligible in `n`, and never zero.
pub fn regev_advantage(n: usize, q: u64, noise: i64) -> f64 {
    total_variation(
        &regev_distribution(n, q, noise, false),
        &regev_distribution(n, q, noise, true),
    )
}

/// A one-time pad over `Z_q`: perfect secrecy, advantage exactly 0.
pub fn one_time_pad_advantage(q: u64, m0: u64, m1: u64) -> f64 {
    let dist = |m: u64| tally((0..q).map(|k| (vec![(m + k) % q], 1)).collect());
    total_variation(&dist(m0), &dist(m1))
}

/// The same pad with a key drawn from half the range: a calibration break.
pub fn short_key_pad_advantage(q: u64, m0: u64, m1: u64) -> f64 {
    let dist = |m: u64| {
        let mut out = BTreeMap::new();
        for k in 0..q / 2 {
            *out.entry(vec![(m + k) % q]).or_insert(0) += 1;
        }
        tally(out)
    };
    total_variation(&dist(m0), &dist(m1))
}
