//! `tclmesh-tfhe-prove DIR CONTEXT LO BITS X OUT [HI]`: the encrypting party's
//! side of a proven input. Reads only the public key and CRS that the runtime
//! published to DIR (`{"op":"publish"}`); no client key is involved. Encrypts
//! `X - LO` as a packed BITS-bit integer with a zero-knowledge proof of
//! encryption bound to CONTEXT, LO, BITS and, if given, HI, and writes it to
//! OUT.
//!
//! An `X` outside `[LO, LO + 2^BITS - 1]` (or `[LO, HI]`) is refused here; a
//! dishonest party who skips this check still cannot make the runtime hold a
//! value outside that range: the ciphertext only has room for BITS bits, and
//! the runtime takes `min` with HI.

use std::path::Path;
use tclmesh_tfhe::{load, metadata, save, upper_bound_ok, CRS, PROVEN_BITS, PUBLIC_KEY};
use tfhe::zk::{CompactPkeCrs, ZkComputeLoad};
use tfhe::{CompactPublicKey, ProvenCompactCiphertextList};

fn run(args: &[String]) -> Result<(), String> {
    let (dir, context, lo, bits, x, out, hi) = match args {
        [d, c, l, b, x, o] => (d, c, l, b, x, o, None),
        [d, c, l, b, x, o, h] => (d, c, l, b, x, o, Some(h)),
        _ => return Err("usage: tclmesh-tfhe-prove DIR CONTEXT LO BITS X OUT [HI]".into()),
    };
    let dir = Path::new(dir);
    let lo: i64 = lo.parse().map_err(|_| format!("LO is not an i64: {lo}"))?;
    let bits: usize = bits
        .parse()
        .map_err(|_| format!("BITS is not a width: {bits}"))?;
    let x: i64 = x.parse().map_err(|_| format!("X is not an integer: {x}"))?;
    if !PROVEN_BITS.contains(&bits) {
        return Err(format!("BITS must be one of {PROVEN_BITS:?}"));
    }
    let hi = match hi {
        Some(h) => {
            let h: i64 = h.parse().map_err(|_| format!("HI is not an i64: {h}"))?;
            if !upper_bound_ok(lo, bits, h) {
                return Err(format!("HI must lie in [LO, LO + 2^{bits} - 1]"));
            }
            Some(h)
        }
        None => None,
    };
    let offset = i128::from(x) - i128::from(lo);
    if !(0..1i128 << bits).contains(&offset) || hi.is_some_and(|h| x > h) {
        return Err("X lies outside the claimed range".into());
    }
    let pk: CompactPublicKey = load(&dir.join(PUBLIC_KEY))?;
    let crs: CompactPkeCrs = load(&dir.join(CRS))?;
    let list = ProvenCompactCiphertextList::builder(&pk)
        .push_with_num_bits(offset as u32, bits)
        .map_err(|e| e.to_string())?
        .build_with_proof_packed(&crs, &metadata(context, lo, bits, hi), ZkComputeLoad::Proof)
        .map_err(|e| e.to_string())?;
    save(&list, Path::new(out))
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Err(e) = run(&args) {
        eprintln!("tclmesh-tfhe-prove: {e}");
        std::process::exit(1);
    }
}
