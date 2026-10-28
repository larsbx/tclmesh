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
    CompactPublicKey, Config, ConfigBuilder, FheInt32, FheUint10, FheUint12, FheUint14, FheUint16,
    FheUint2, FheUint32, FheUint4, FheUint6, FheUint8, ProvenCompactCiphertextList,
};

/// Proven offsets have these widths: each has an `FheUint` type and fits the
/// 32-bit word with room for the offset.
pub const PROVEN_BITS: [usize; 8] = [2, 4, 6, 8, 10, 12, 14, 16];

/// Largest number of bits one CRS proves.
pub const CRS_MAX_BITS: usize = 16;

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
pub fn metadata(context: &str, lo: i32, bits: usize, hi: Option<i32>) -> Vec<u8> {
    match hi {
        None => format!("tclmesh-proven-int-v1\n{context}\n{lo}\n{bits}"),
        Some(hi) => format!("tclmesh-proven-int-v2\n{context}\n{lo}\n{bits}\n{hi}"),
    }
    .into_bytes()
}

/// `hi` is admissible for an offset of `bits` bits from `lo`.
pub fn upper_bound_ok(lo: i32, bits: usize, hi: i32) -> bool {
    (i64::from(lo)..(i64::from(lo) + (1i64 << bits))).contains(&i64::from(hi))
}

/// Verify a proven list against its statement and return the input it
/// carries: `lo + a` for the proven `bits`-bit offset `a`, and with `hi`,
/// `min(lo + a, hi)`. The caller checks that `[lo, lo + 2^bits - 1]` lies in
/// the word; then nothing here can overflow.
#[allow(clippy::too_many_arguments)]
pub fn import_proven(
    list: &ProvenCompactCiphertextList,
    crs: &CompactPkeCrs,
    public: &CompactPublicKey,
    context: &str,
    lo: i32,
    bits: usize,
    hi: Option<i32>,
) -> Result<FheInt32, String> {
    if !PROVEN_BITS.contains(&bits) || hi.is_some_and(|h| !upper_bound_ok(lo, bits, h)) {
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
        10 => FheUint10, 12 => FheUint12, 14 => FheUint14, 16 => FheUint16);
    let x = FheInt32::cast_from(a) + lo;
    Ok(match hi {
        Some(hi) => x.min(&FheInt32::encrypt_trivial(hi)),
        None => x,
    })
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
