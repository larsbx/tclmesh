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
//! - `tclmesh-tfhe-crs init DIR`: start from the CRS with the public trapdoor 1.
//! - `tclmesh-tfhe-crs contribute DIR`: check the ceremony, add a contribution
//!   with a fresh secret, and print its receipt.
//! - `tclmesh-tfhe-crs verify DIR`: check the ceremony and print every
//!   receipt in order; a contributor checks that theirs is listed.
//!
//! The runtime adopts OUT, or verifies and adopts DIR, with
//! `{"op":"publish","crs":OUT|DIR}`.

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
        [op, dir] => {
            let dir = Path::new(dir);
            match op.as_str() {
                "init" => ceremony::init(dir),
                "contribute" => ceremony::contribute(dir, rng).map(|r| println!("{r}")),
                "verify" => ceremony::verify(dir, rng)
                    .map(|(rs, _)| rs.iter().for_each(|r| println!("{r}"))),
                _ => Err(format!("unknown operation {op}")),
            }
        }
        _ => Err("usage: tclmesh-tfhe-crs OUT | (init|contribute|verify) DIR".into()),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Err(e) = run(&args) {
        eprintln!("tclmesh-tfhe-crs: {e}");
        std::process::exit(1);
    }
}
