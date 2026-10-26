//! Seeded randomness, so every game and every failure reproduces exactly.

/// SplitMix64: small, fast, statistically good; not for production keys.
#[derive(Clone, Debug)]
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Self {
        Rng(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// Uniform in `0..n` (rejection sampling, no modulo bias).
    pub fn below(&mut self, n: u64) -> u64 {
        assert!(n > 0);
        let zone = u64::MAX - u64::MAX % n;
        loop {
            let x = self.next_u64();
            if x < zone {
                return x % n;
            }
        }
    }

    pub fn bit(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }

    /// Uniform in `-b..=b`.
    pub fn centered(&mut self, b: u64) -> i64 {
        self.below(2 * b + 1) as i64 - b as i64
    }
}
