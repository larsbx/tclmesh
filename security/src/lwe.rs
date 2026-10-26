//! A toy secret-key Regev (LWE) bit-encryption scheme, sound and deliberately
//! broken, to exercise the game runner. Ciphertexts are `a ++ [b]` with
//! `b = ⟨a, s⟩ + e + m·⌊q/2⌋ (mod q)`. Not for use: parameters are tiny.

use crate::rng::Rng;

/// How a variant departs from the sound scheme. Every flaw but `None` is a
/// calibration break the battery must detect.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Flaw {
    None,
    /// No noise: the scheme is linear and falls to Gaussian elimination.
    NoNoise,
    /// Randomness derived from the key and message: equal plaintexts give
    /// equal ciphertexts.
    Deterministic,
    /// The same `a` for every ciphertext under a key.
    ReusedRandomness,
    /// The plaintext bit appended to the ciphertext (the reference backend).
    Appended,
    /// Ciphertexts of `1` carry an extra coordinate.
    SizeLeak,
}

#[derive(Clone, Debug)]
pub struct Regev {
    pub n: usize,
    pub q: u64,
    pub noise: u64,
    pub flaw: Flaw,
}

pub type Key = Vec<u64>;
pub type Ct = Vec<u64>;

impl Regev {
    pub fn sound(n: usize, q: u64, noise: u64) -> Self {
        Regev {
            n,
            q,
            noise,
            flaw: Flaw::None,
        }
    }

    pub fn with_flaw(mut self, flaw: Flaw) -> Self {
        self.flaw = flaw;
        self
    }

    pub fn name(&self) -> String {
        format!(
            "regev(n={}, q={}, B={}, {:?})",
            self.n, self.q, self.noise, self.flaw
        )
    }

    pub fn keygen(&self, rng: &mut Rng) -> Key {
        (0..self.n).map(|_| rng.below(self.q)).collect()
    }

    fn dot(&self, a: &[u64], s: &[u64]) -> u64 {
        a.iter().zip(s).fold(0u128, |acc, (x, y)| {
            (acc + *x as u128 * *y as u128) % self.q as u128
        }) as u64
    }

    fn key_seed(key: &Key) -> u64 {
        key.iter().fold(0xcbf2_9ce4_8422_2325u64, |h, x| {
            (h ^ x).wrapping_mul(0x100_0000_01b3)
        })
    }

    pub fn encrypt(&self, key: &Key, m: bool, rng: &mut Rng) -> Ct {
        let mut local;
        let r: &mut Rng = match self.flaw {
            Flaw::Deterministic => {
                local = Rng::new(Self::key_seed(key) ^ m as u64);
                &mut local
            }
            _ => rng,
        };
        let a: Vec<u64> = if self.flaw == Flaw::ReusedRandomness {
            let mut fixed = Rng::new(Self::key_seed(key));
            (0..self.n).map(|_| fixed.below(self.q)).collect()
        } else {
            (0..self.n).map(|_| r.below(self.q)).collect()
        };
        let e = if self.flaw == Flaw::NoNoise {
            0
        } else {
            r.centered(self.noise)
        };
        let shift = if m { self.q / 2 } else { 0 };
        let b = (self.dot(&a, key) as i64 + e + shift as i64).rem_euclid(self.q as i64) as u64;
        let mut ct = a;
        ct.push(b);
        match self.flaw {
            Flaw::Appended => ct.push(m as u64),
            Flaw::SizeLeak if m => ct.push(0),
            _ => {}
        }
        ct
    }

    pub fn decrypt(&self, key: &Key, ct: &Ct) -> bool {
        let d = (ct[self.n] + self.q - self.dot(&ct[..self.n], key)) % self.q;
        let dist0 = d.min(self.q - d);
        let half = self.q / 2;
        let dist1 = d.abs_diff(half);
        dist1 < dist0
    }
}
