//! The IND-CPA game and a battery of concrete adversaries.
//!
//! A pass bounds nothing: semantic security quantifies over all efficient
//! adversaries. A fail is a break. The battery is calibrated: every flawed
//! variant of `lwe::Regev` must be caught by some adversary, and the sound
//! one by none (`calibrate`).

use crate::lwe::{Ct, Regev};
use crate::rng::Rng;
use crate::stats::{bonferroni_z, Advantage};

/// An adversary sees the scheme's public parameters, an encryption oracle,
/// and the challenge; it guesses which bit the challenge encrypts.
pub trait Adversary {
    fn name(&self) -> &'static str;
    fn guess(&self, scheme: &Regev, oracle: &mut dyn FnMut(bool) -> Ct, challenge: &Ct) -> bool;
}

/// Plays `trials` independent games (fresh key, fresh challenge bit) and
/// measures the adversary's advantage.
pub fn play(
    scheme: &Regev,
    adversary: &dyn Adversary,
    trials: u64,
    seed: u64,
    z: f64,
) -> Advantage {
    let mut rng = Rng::new(seed);
    let mut wins = 0;
    for _ in 0..trials {
        let key = scheme.keygen(&mut rng);
        let bit = rng.bit();
        let challenge = scheme.encrypt(&key, bit, &mut rng);
        let mut oracle_rng = Rng::new(rng.next_u64());
        let mut oracle = |m: bool| scheme.encrypt(&key, m, &mut oracle_rng);
        if adversary.guess(scheme, &mut oracle, &challenge) == bit {
            wins += 1;
        }
    }
    Advantage::new(wins, trials, z)
}

/// Equal plaintexts give equal ciphertexts.
pub struct Equality;
impl Adversary for Equality {
    fn name(&self) -> &'static str {
        "equality"
    }
    fn guess(&self, _: &Regev, oracle: &mut dyn FnMut(bool) -> Ct, c: &Ct) -> bool {
        oracle(true) == *c
    }
}

/// Ciphertext length depends on the plaintext.
pub struct Length;
impl Adversary for Length {
    fn name(&self) -> &'static str {
        "length"
    }
    fn guess(&self, _: &Regev, oracle: &mut dyn FnMut(bool) -> Ct, c: &Ct) -> bool {
        oracle(true).len() == c.len() && oracle(false).len() != c.len()
    }
}

/// Nearest centroid, standardized: per-coordinate means and variances of
/// sampled encryptions of 0 and 1, and a diagonal Mahalanobis distance, so a
/// low-magnitude coordinate (an appended bit) is weighed by its variance and
/// not drowned by the uniform ones. (An unstandardized centroid missed the
/// `Appended` break; calibration caught it.)
pub struct Centroid {
    pub samples: usize,
}
impl Adversary for Centroid {
    fn name(&self) -> &'static str {
        "centroid"
    }
    fn guess(&self, s: &Regev, oracle: &mut dyn FnMut(bool) -> Ct, c: &Ct) -> bool {
        let q = s.q as f64;
        // distance on the circle Z_q
        let circ = |x: f64, y: f64| {
            let d = (x - y).abs() % q;
            d.min(q - d)
        };
        let moments = |oracle: &mut dyn FnMut(bool) -> Ct, m: bool| {
            let samples: Vec<Ct> = (0..self.samples).map(|_| oracle(m)).collect();
            (0..c.len())
                .map(|i| {
                    let xs: Vec<f64> = samples
                        .iter()
                        .map(|ct| *ct.get(i).unwrap_or(&0) as f64)
                        .collect();
                    let mean = xs.iter().sum::<f64>() / xs.len() as f64;
                    let var =
                        xs.iter().map(|x| circ(*x, mean).powi(2)).sum::<f64>() / xs.len() as f64;
                    (mean, var)
                })
                .collect::<Vec<_>>()
        };
        let (m0, m1) = (moments(oracle, false), moments(oracle, true));
        let score = |m: &[(f64, f64)]| -> f64 {
            c.iter()
                .zip(m)
                .map(|(x, (mean, var))| circ(*x as f64, *mean).powi(2) / (var + 1e-3))
                .sum()
        };
        score(&m1) < score(&m0)
    }
}

/// With an unchanged `a`, `b − b′ = e − e′ + (m − m′)·⌊q/2⌋`.
pub struct Difference;
impl Adversary for Difference {
    fn name(&self) -> &'static str {
        "difference"
    }
    fn guess(&self, s: &Regev, oracle: &mut dyn FnMut(bool) -> Ct, c: &Ct) -> bool {
        let zero = oracle(false);
        if zero[..s.n] != c[..s.n] {
            return false;
        }
        let d = (c[s.n] + s.q - zero[s.n]) % s.q;
        d.abs_diff(s.q / 2) < d.min(s.q - d)
    }
}

/// Gaussian elimination mod q on encryptions of 0: exact without noise.
pub struct Linear;
impl Adversary for Linear {
    fn name(&self) -> &'static str {
        "linear-algebra"
    }
    fn guess(&self, s: &Regev, oracle: &mut dyn FnMut(bool) -> Ct, c: &Ct) -> bool {
        let rows: Vec<Ct> = (0..s.n + 8).map(|_| oracle(false)).collect();
        match solve_mod(&rows, s.n, s.q) {
            Some(key) => s.decrypt(&key, &c[..=s.n].to_vec()),
            None => false,
        }
    }
}

fn pow_mod(b: u64, mut e: u64, m: u64) -> u64 {
    let mut r = 1u128;
    let mut x = b as u128 % m as u128;
    while e > 0 {
        if e & 1 == 1 {
            r = r * x % m as u128;
        }
        x = x * x % m as u128;
        e >>= 1;
    }
    r as u64
}

/// Solves `a·s = b (mod q)` from rows `a ++ [b]`, `q` prime.
fn solve_mod(rows: &[Ct], n: usize, q: u64) -> Option<Vec<u64>> {
    let mut m: Vec<Vec<u64>> = rows.to_vec();
    for (r, col) in (0..n).enumerate() {
        let pivot = (r..m.len()).find(|&i| !m[i][col].is_multiple_of(q))?;
        m.swap(r, pivot);
        let inv = pow_mod(m[r][col], q - 2, q);
        for x in m[r].iter_mut() {
            *x = (*x as u128 * inv as u128 % q as u128) as u64;
        }
        for i in 0..m.len() {
            if i != r && m[i][col] != 0 {
                let f = m[i][col];
                let row_r = m[r].clone();
                for (x, y) in m[i].iter_mut().zip(row_r) {
                    *x = (*x + q - (f as u128 * y as u128 % q as u128) as u64) % q;
                }
            }
        }
    }
    Some((0..n).map(|i| m[i][n]).collect())
}

pub fn battery() -> Vec<Box<dyn Adversary>> {
    vec![
        Box::new(Equality),
        Box::new(Length),
        Box::new(Centroid { samples: 24 }),
        Box::new(Difference),
        Box::new(Linear),
    ]
}

/// The battery's verdict on one scheme: every adversary's advantage, and
/// whether any is significant at family-wise level `alpha`.
pub struct Verdict {
    pub scheme: String,
    pub results: Vec<(&'static str, Advantage)>,
    pub broken: bool,
}

pub fn assess(scheme: &Regev, trials: u64, seed: u64, alpha: f64) -> Verdict {
    let adversaries = battery();
    let z = bonferroni_z(alpha, adversaries.len());
    let results: Vec<_> = adversaries
        .iter()
        .enumerate()
        .map(|(i, a)| {
            (
                a.name(),
                play(scheme, a.as_ref(), trials, seed ^ (i as u64) << 32, z),
            )
        })
        .collect();
    let broken = results.iter().any(|(_, adv)| adv.low > 0.0);
    Verdict {
        scheme: scheme.name(),
        results,
        broken,
    }
}
