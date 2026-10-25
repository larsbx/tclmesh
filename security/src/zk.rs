//! Zero knowledge, tested: Schnorr's Σ-protocol for knowledge of `w` with
//! `h = g^w` in a prime-order subgroup.
//!
//! * completeness: honest provers are accepted;
//! * special soundness: two accepting transcripts with one commitment and two
//!   challenges yield the witness, so soundness is tested by running the
//!   extractor; a prover that reuses a nonce hands it exactly such a pair;
//! * honest-verifier zero knowledge: the simulator's transcripts have the same
//!   distribution as real ones, compared exactly on a small group;
//! * Fiat–Shamir: the challenge must hash the statement, or a forger proves
//!   statements it has no witness for.

use crate::rng::Rng;
use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};

#[derive(Clone, Copy, Debug)]
pub struct Group {
    pub p: u64,
    pub q: u64,
    pub g: u64,
}

pub fn mul(a: u64, b: u64, m: u64) -> u64 {
    (a as u128 * b as u128 % m as u128) as u64
}

pub fn pow(b: u64, mut e: u64, m: u64) -> u64 {
    let (mut r, mut x) = (1u64, b % m);
    while e > 0 {
        if e & 1 == 1 {
            r = mul(r, x, m);
        }
        x = mul(x, x, m);
        e >>= 1;
    }
    r
}

pub fn inv(a: u64, prime: u64) -> u64 {
    pow(a, prime - 2, prime)
}

fn is_prime(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n.is_multiple_of(p) {
            return n == p;
        }
    }
    let (mut d, mut s) = (n - 1, 0);
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    'witness: for a in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = pow(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 1..s {
            x = mul(x, x, n);
            if x == n - 1 {
                continue 'witness;
            }
        }
        return false;
    }
    true
}

impl Group {
    /// The order-11 subgroup of `Z_23^*`: small enough to enumerate.
    pub fn small() -> Self {
        Group { p: 23, q: 11, g: 4 }
    }

    /// A subgroup of prime order `q = 2^31 − 1` in `Z_p^*`, `p = kq + 1`: too
    /// large to enumerate, so tested by sampling.
    pub fn large() -> Self {
        let q = (1u64 << 31) - 1;
        let k = (2u64..).step_by(2).find(|k| is_prime(k * q + 1)).unwrap();
        let p = k * q + 1;
        let g = (2..).map(|h| pow(h, k, p)).find(|&g| g != 1).unwrap();
        Group { p, q, g }
    }

    pub fn exp(&self, e: u64) -> u64 {
        pow(self.g, e, self.p)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Transcript {
    pub t: u64,
    pub c: u64,
    pub z: u64,
}

pub fn verify(g: &Group, h: u64, tr: &Transcript) -> bool {
    g.exp(tr.z) == mul(tr.t, pow(h, tr.c, g.p), g.p)
}

/// The honest prover's response to challenge `c` with nonce `r`.
pub fn respond(g: &Group, w: u64, r: u64, c: u64) -> Transcript {
    Transcript {
        t: g.exp(r),
        c,
        z: (r as u128 + c as u128 * w as u128).rem_euclid(g.q as u128) as u64,
    }
}

/// The honest-verifier simulator: no witness, just `c, z` and `t = g^z h^{−c}`.
pub fn simulate(g: &Group, h: u64, c: u64, z: u64) -> Transcript {
    let t = mul(g.exp(z), inv(pow(h, c, g.p), g.p), g.p);
    Transcript { t, c, z }
}

/// The special-soundness extractor.
pub fn extract(g: &Group, a: &Transcript, b: &Transcript) -> Option<u64> {
    if a.t != b.t || a.c == b.c {
        return None;
    }
    let dz = (a.z + g.q - b.z) % g.q;
    let dc = (a.c + g.q - b.c) % g.q;
    Some(mul(dz, inv(dc, g.q), g.q))
}

/// Exact distribution of real transcripts (nonces drawn from `nonces`, every
/// challenge) and of simulated ones (every challenge and response).
pub fn real_distribution(g: &Group, w: u64, nonces: &[u64]) -> Vec<(Transcript, u64)> {
    let mut out = BTreeMap::new();
    let weight = g.q / nonces.len() as u64;
    for &r in nonces {
        for c in 0..g.q {
            *out.entry(respond(g, w, r, c)).or_insert(0) += weight;
        }
    }
    out.into_iter().collect()
}

pub fn simulated_distribution(g: &Group, h: u64) -> Vec<(Transcript, u64)> {
    let mut out = BTreeMap::new();
    for c in 0..g.q {
        for z in 0..g.q {
            *out.entry(simulate(g, h, c, z)).or_insert(0) += 1;
        }
    }
    out.into_iter().collect()
}

/// Fiat–Shamir challenges: `strong` hashes the group, statement and
/// commitment; `weak` only the commitment (the "frozen heart" bug class).
pub fn challenge(g: &Group, h: u64, t: u64, strong: bool) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    if strong {
        (g.p, g.q, g.g, h).hash(&mut hasher);
    }
    t.hash(&mut hasher);
    hasher.finish() % g.q
}

pub fn prove(g: &Group, w: u64, rng: &mut Rng, strong: bool) -> (u64, Transcript) {
    let h = g.exp(w);
    let r = rng.below(g.q);
    let t = g.exp(r);
    (h, respond(g, w, r, challenge(g, h, t, strong)))
}

pub fn verify_fs(g: &Group, h: u64, tr: &Transcript, strong: bool) -> bool {
    tr.c == challenge(g, h, tr.t, strong) && verify(g, h, tr)
}

/// A forger with no witness: it picks the commitment and response first,
/// then solves for a statement `h` they prove. It succeeds exactly when the
/// challenge does not depend on `h`.
pub fn forge(g: &Group, rng: &mut Rng, strong: bool) -> Option<(u64, Transcript)> {
    let t = g.exp(rng.below(g.q));
    let z = rng.below(g.q);
    let c = challenge(g, 0, t, false);
    if c == 0 {
        return None;
    }
    // g^z = t · h^c  ⇒  h = (g^z / t)^{1/c}
    let h = pow(mul(g.exp(z), inv(t, g.p), g.p), inv(c, g.q), g.p);
    let tr = Transcript {
        t,
        c: challenge(g, h, t, strong),
        z,
    };
    verify_fs(g, h, &tr, strong).then_some((h, tr))
}
