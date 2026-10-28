//! `tclmesh-tfhe-crs OUT`: generate the CRS for proven inputs, from public
//! parameters only. Whoever runs this learns the CRS trapdoor, and a party
//! holding it could forge proofs, so it should be run by someone other than
//! both the key holder and the encrypting parties (or replaced by a setup
//! ceremony). The runtime adopts it with `{"op":"publish","crs":OUT}`.

use std::path::Path;
use tclmesh_tfhe::{config, save, CRS_MAX_BITS};
use tfhe::zk::CompactPkeCrs;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.as_slice() {
        [out] => CompactPkeCrs::from_config(config(), CRS_MAX_BITS)
            .map_err(|e| e.to_string())
            .and_then(|crs| save(&crs, Path::new(out))),
        _ => Err("usage: tclmesh-tfhe-crs OUT".into()),
    };
    if let Err(e) = result {
        eprintln!("tclmesh-tfhe-crs: {e}");
        std::process::exit(1);
    }
}
