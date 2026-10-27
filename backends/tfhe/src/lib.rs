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

use std::path::Path;
use tfhe::safe_serialization::{safe_deserialize, safe_serialize};
use tfhe::shortint::parameters::{
    PARAM_KEYSWITCH_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128,
    PARAM_PKE_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128,
};
use tfhe::{Config, ConfigBuilder};

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
/// offset or width fails verification.
pub fn metadata(context: &str, lo: i32, bits: usize) -> Vec<u8> {
    format!("tclmesh-proven-int-v1\n{context}\n{lo}\n{bits}").into_bytes()
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
