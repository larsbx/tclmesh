//! The CRS for proven inputs, from public parameters only. Whoever knows its
//! trapdoor can forge proofs, so no prover may know it.
//!
//! `tclmesh-tfhe-crs OUT`: one party generates the CRS and learns the
//! trapdoor; run it by someone other than the key holder and the encrypting
//! parties.
//!
//! A ceremony (`src/ceremony.rs`) needs no such party: the trapdoor stays
//! unknown unless every contributor colludes.
//!
//! - `tclmesh-tfhe-crs keygen SECRET PUBLIC`: a contributor's long-term
//!   signing key; PUBLIC is what verifiers trust.
//! - `tclmesh-tfhe-crs init DIR`: start from the CRS with the public trapdoor 1.
//! - `tclmesh-tfhe-crs contribute DIR [SECRET]`: check the ceremony, add a
//!   contribution with a fresh secret, signed with SECRET if given, and print
//!   its receipt and signer.
//! - `tclmesh-tfhe-crs verify DIR [PUBLIC...]`: check the ceremony and print
//!   every receipt and signer in order (`-` when unsigned); with PUBLIC keys,
//!   require a contribution signed by one of them.
//!
//! The runtime adopts OUT, or verifies and adopts DIR, with
//! `{"op":"publish","crs":OUT|DIR,"trusted":[PUBLIC...]}`.

use std::path::Path;
use tclmesh_tfhe::{ceremony, config, save, CRS_MAX_BITS};
use tfhe::zk::CompactPkeCrs;

fn run(args: &[String]) -> Result<(), String> {
    let rng = &mut rand::rngs::OsRng;
    match args {
        [out] => save(
            &CompactPkeCrs::from_config(config(), CRS_MAX_BITS).map_err(|e| e.to_string())?,
            Path::new(out),
        ),
        [op, secret, public] if op == "keygen" => {
            let key = ceremony::write_keys(Path::new(secret), Path::new(public), rng)?;
            println!("{}", key.fingerprint());
            Ok(())
        }
        [op, dir] if op == "init" => ceremony::init(Path::new(dir)),
        [op, dir, key @ ..] if op == "contribute" && key.len() <= 1 => {
            let key = key
                .first()
                .map(|k| ceremony::read_secret(Path::new(k)))
                .transpose()?;
            ceremony::contribute(Path::new(dir), key.as_ref(), rng).map(|r| println!("{r}"))
        }
        [op, dir, trusted @ ..] if op == "verify" => {
            let trusted = trusted
                .iter()
                .map(|k| ceremony::read_public(Path::new(k)))
                .collect::<Result<Vec<_>, _>>()?;
            ceremony::verify(Path::new(dir), &trusted, rng)
                .map(|(rs, _)| rs.iter().for_each(|r| println!("{r}")))
        }
        _ => Err(
            "usage: tclmesh-tfhe-crs OUT | keygen SECRET PUBLIC | init DIR \
                  | contribute DIR [SECRET] | verify DIR [PUBLIC...]"
                .into(),
        ),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Err(e) = run(&args) {
        eprintln!("tclmesh-tfhe-crs: {e}");
        std::process::exit(1);
    }
}
