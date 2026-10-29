//! What the runtime (`tclmesh-tfhe`) and an encrypting party
//! (`tclmesh-tfhe-prove`) must agree on to exchange proven ciphertexts.
//!
//! An encrypting party who holds only the compact public key and the CRS
//! encrypts the offset `a = x - lo` as a packed `k`-bit unsigned integer with
//! a TFHE-rs zero-knowledge proof of encryption (`zk-pok`). The proof binds
//! [`metadata`]: the context, `lo` and `k`. The runtime verifies it, expands
//! the list (unpacking cleans every 2-bit block into `[0, 4)`, so the value
//! is below `4^(k/2) = 2^k`), and computes `x = lo + a` homomorphically. It
//! never sees `x`, and `x` lies in `[lo, lo + 2^k - 1]`
//! (`spec/TclMesh/Range.lean`, `proven_input_range`).
//!
//! Integers are words of one of [`WIDTHS`] bits ([`Int`]): a profile's
//! semantics `int<W>-…` fixes `W` for every value it holds.

pub mod ceremony;

use std::path::Path;
use tfhe::prelude::*;
use tfhe::safe_serialization::{safe_deserialize, safe_serialize};
use tfhe::shortint::parameters::{
    PARAM_KEYSWITCH_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128,
    PARAM_PKE_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128,
};
use tfhe::zk::CompactPkeCrs;
use tfhe::{
    ClientKey, CompactPublicKey, Config, ConfigBuilder, FheBool, FheInt32, FheInt64, FheUint10,
    FheUint12, FheUint14, FheUint16, FheUint2, FheUint32, FheUint4, FheUint6, FheUint8,
    ProvenCompactCiphertextList,
};

/// Word widths: `FheInt32` and `FheInt64`, wrapping modulo `2^W`.
pub const WIDTHS: [u32; 2] = [32, 64];

/// An encrypted signed word.
#[derive(Clone)]
pub enum Int {
    W32(FheInt32),
    W64(FheInt64),
}

/// `x` as a `W`-bit word, if it fits.
fn word<T: TryFrom<i64>>(width: u32, x: i64) -> Result<T, String> {
    T::try_from(x).map_err(|_| format!("{x} does not fit the {width}-bit word"))
}

impl Int {
    pub fn width(&self) -> u32 {
        match self {
            Int::W32(_) => 32,
            Int::W64(_) => 64,
        }
    }

    pub fn encrypt(width: u32, x: i64, key: &ClientKey) -> Result<Int, String> {
        Ok(match width {
            32 => Int::W32(FheInt32::encrypt(word::<i32>(width, x)?, key)),
            64 => Int::W64(FheInt64::encrypt(x, key)),
            _ => return Err(format!("width must be one of {WIDTHS:?}")),
        })
    }

    pub fn trivial(width: u32, x: i64) -> Result<Int, String> {
        Ok(match width {
            32 => Int::W32(FheInt32::encrypt_trivial(word::<i32>(width, x)?)),
            64 => Int::W64(FheInt64::encrypt_trivial(x)),
            _ => return Err(format!("width must be one of {WIDTHS:?}")),
        })
    }

    /// `0` or `1`.
    pub fn from_bool(width: u32, b: &FheBool) -> Result<Int, String> {
        Ok(match width {
            32 => Int::W32(FheInt32::cast_from(b.clone())),
            64 => Int::W64(FheInt64::cast_from(b.clone())),
            _ => return Err(format!("width must be one of {WIDTHS:?}")),
        })
    }

    /// The offset `x < 2^32` as a `width`-bit word: zero-extended at 64 bits;
    /// at 32 bits an `x >= 2^31` wraps to `x - 2^32`, so `lo + x` is still
    /// exact whenever it lies in the word (wrapping is a ring homomorphism).
    fn from_offset(width: u32, x: FheUint32) -> Result<Int, String> {
        Ok(match width {
            32 => Int::W32(FheInt32::cast_from(x)),
            64 => Int::W64(FheInt64::cast_from(x)),
            _ => return Err(format!("width must be one of {WIDTHS:?}")),
        })
    }

    pub fn decrypt(&self, key: &ClientKey) -> i64 {
        match self {
            Int::W32(x) => i64::from(FheDecrypt::<i32>::decrypt(x, key)),
            Int::W64(x) => x.decrypt(key),
        }
    }

    pub fn nonzero(&self) -> FheBool {
        match self {
            Int::W32(x) => x.ne(0),
            Int::W64(x) => x.ne(0),
        }
    }

    pub fn bytes(&self) -> usize {
        let mut buf = Vec::new();
        match self {
            Int::W32(x) => safe_serialize(x, &mut buf, LIMIT),
            Int::W64(x) => safe_serialize(x, &mut buf, LIMIT),
        }
        .expect("serialize ciphertext");
        buf.len()
    }
}

/// Apply `$f` to integers of one width, with the result rewrapped as an
/// [`Int`]; operands of different widths are an error.
#[macro_export]
macro_rules! lift {
    (|$x:ident| $e:expr, $a:expr) => {
        match $a {
            $crate::Int::W32($x) => $crate::Int::W32($e),
            $crate::Int::W64($x) => $crate::Int::W64($e),
        }
    };
    (|$x:ident, $y:ident| $e:expr, $a:expr, $b:expr) => {
        match ($a, $b) {
            ($crate::Int::W32($x), $crate::Int::W32($y)) => Ok($crate::Int::W32($e)),
            ($crate::Int::W64($x), $crate::Int::W64($y)) => Ok($crate::Int::W64($e)),
            _ => Err(String::from("operands of different widths")),
        }
    };
}

/// Like [`lift!`] for operations whose result is not an integer.
#[macro_export]
macro_rules! test {
    (|$x:ident, $y:ident| $e:expr, $a:expr, $b:expr) => {
        match ($a, $b) {
            ($crate::Int::W32($x), $crate::Int::W32($y)) => Ok($e),
            ($crate::Int::W64($x), $crate::Int::W64($y)) => Ok($e),
            _ => Err(String::from("operands of different widths")),
        }
    };
}

/// Proven offsets have these widths: each has an `FheUint` type. A 32-bit
/// offset fills the 32-bit word (only `lo = -2^31` fits there) and leaves
/// room in the 64-bit one.
pub const PROVEN_BITS: [usize; 9] = [2, 4, 6, 8, 10, 12, 14, 16, 32];

/// Largest number of bits one CRS proves.
pub const CRS_MAX_BITS: usize = 32;

/// Serialization limit for keys, CRS and proven lists.
pub const LIMIT: u64 = 1 << 32;

pub const PUBLIC_KEY: &str = "public-key.bin";
pub const CRS: &str = "crs.bin";

pub fn config() -> Config {
    ConfigBuilder::default()
        .use_dedicated_compact_public_key_parameters((
            PARAM_PKE_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128,
            PARAM_KEYSWITCH_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128,
        ))
        .build()
}

/// The statement a proof is bound to: replaying it under another context,
/// offset, width or upper bound fails verification. With `hi`, the encrypting
/// party claims `x` in `[lo, hi]`; the runtime enforces `hi` by `min`, so an
/// honest `x` is unchanged and a dishonest one cannot exceed `hi`.
pub fn metadata(context: &str, lo: i64, bits: usize, hi: Option<i64>) -> Vec<u8> {
    match hi {
        None => format!("tclmesh-proven-int-v1\n{context}\n{lo}\n{bits}"),
        Some(hi) => format!("tclmesh-proven-int-v2\n{context}\n{lo}\n{bits}\n{hi}"),
    }
    .into_bytes()
}

/// The largest value an offset of `bits` bits from `lo` reaches.
fn top(lo: i64, bits: usize) -> i128 {
    i128::from(lo) + (1i128 << bits) - 1
}

/// `hi` is admissible for an offset of `bits` bits from `lo`.
pub fn upper_bound_ok(lo: i64, bits: usize, hi: i64) -> bool {
    (i128::from(lo)..=top(lo, bits)).contains(&i128::from(hi))
}

/// `[lo, lo + 2^bits - 1]` lies in the `width`-bit word.
pub fn proven_range_ok(width: u32, lo: i64, bits: usize) -> bool {
    WIDTHS.contains(&width) && {
        let half = 1i128 << (width - 1);
        -half <= i128::from(lo) && top(lo, bits) < half
    }
}

/// Verify a proven list against its statement and return the input it
/// carries as a `width`-bit word: `lo + a` for the proven `bits`-bit offset
/// `a`, and with `hi`, `min(lo + a, hi)`. `[lo, lo + 2^bits - 1]` must lie in
/// the word, so nothing here can overflow.
#[allow(clippy::too_many_arguments)]
pub fn import_proven(
    list: &ProvenCompactCiphertextList,
    crs: &CompactPkeCrs,
    public: &CompactPublicKey,
    context: &str,
    width: u32,
    lo: i64,
    bits: usize,
    hi: Option<i64>,
) -> Result<Int, String> {
    if !PROVEN_BITS.contains(&bits)
        || !proven_range_ok(width, lo, bits)
        || hi.is_some_and(|h| !upper_bound_ok(lo, bits, h))
    {
        return Err("unsupported proof statement".into());
    }
    let expander = list
        .verify_and_expand(crs, public, &metadata(context, lo, bits, hi))
        .map_err(|e| format!("proof rejected: {e}"))?;
    if expander.len() != 1 {
        return Err("a proven input holds exactly one integer".into());
    }
    macro_rules! offset {
        ($($n:literal => $t:ty),*) => {
            match bits {
                $($n => FheUint32::cast_from(
                    expander.get::<$t>(0).map_err(|e| e.to_string())?.ok_or("empty list")?),)*
                _ => unreachable!("bits checked against PROVEN_BITS"),
            }
        };
    }
    let a = offset!(2 => FheUint2, 4 => FheUint4, 6 => FheUint6, 8 => FheUint8,
        10 => FheUint10, 12 => FheUint12, 14 => FheUint14, 16 => FheUint16, 32 => FheUint32);
    let (lo, hi) = (
        Int::trivial(width, lo)?,
        hi.map(|h| Int::trivial(width, h)).transpose()?,
    );
    let x = lift!(|a, lo| a + lo, Int::from_offset(width, a)?, lo)?;
    match hi {
        Some(hi) => lift!(|x, hi| x.min(&hi), x, hi),
        None => Ok(x),
    }
}

pub fn save<T: serde::Serialize + tfhe::named::Named + tfhe::Versionize>(
    value: &T,
    path: &Path,
) -> Result<(), String> {
    let mut buf = Vec::new();
    safe_serialize(value, &mut buf, LIMIT).map_err(|e| e.to_string())?;
    std::fs::write(path, buf).map_err(|e| format!("{}: {e}", path.display()))
}

pub fn load<T>(path: &Path) -> Result<T, String>
where
    T: serde::de::DeserializeOwned + tfhe::named::Named + tfhe::Unversionize,
{
    let bytes = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    safe_deserialize(bytes.as_slice(), LIMIT).map_err(|e| format!("{}: {e}", path.display()))
}
