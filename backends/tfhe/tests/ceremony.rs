//! A setup ceremony yields a CRS that proves and verifies inputs, and its
//! verification refuses every transcript that does not chain to that CRS.

use serde_json::Value;
use std::path::{Path, PathBuf};
use tclmesh_tfhe::ceremony::{contribute, init, verify, TRANSCRIPT};
use tclmesh_tfhe::{config, import_proven, metadata, save, CRS};
use tfhe::zk::{CompactPkeCrs, ZkComputeLoad};
use tfhe::{set_server_key, ClientKey, CompactPublicKey, ProvenCompactCiphertextList, ServerKey};

fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tclmesh-ceremony-{name}-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn copy(from: &Path, name: &str) -> PathBuf {
    let to = scratch(name);
    for f in [CRS, TRANSCRIPT] {
        std::fs::copy(from.join(f), to.join(f)).unwrap();
    }
    to
}

/// Rewrite the transcript of a copy of `from`.
fn tampered(from: &Path, name: &str, edit: impl Fn(&mut Vec<Value>)) -> PathBuf {
    let dir = copy(from, name);
    let path = dir.join(TRANSCRIPT);
    let mut t: Value = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
    edit(t["contributions"].as_array_mut().unwrap());
    std::fs::write(&path, t.to_string()).unwrap();
    dir
}

#[test]
fn a_ceremony_crs_proves_inputs_and_tampering_is_refused() {
    let rng = &mut rand::thread_rng();
    let dir = scratch("honest");
    init(&dir).unwrap();
    let start = copy(&dir, "start");
    let receipts = [
        contribute(&dir, rng).unwrap(),
        contribute(&dir, rng).unwrap(),
    ];
    let (listed, crs) = verify(&dir, rng).unwrap();
    assert_eq!(listed, receipts);

    // The CRS works for proofs of encryption.
    let client = ClientKey::generate(config());
    set_server_key(ServerKey::new(&client));
    let pk = CompactPublicKey::new(&client);
    let list = ProvenCompactCiphertextList::builder(&pk)
        .push_with_num_bits(42u32, 8)
        .unwrap()
        .build_with_proof_packed(
            &crs,
            &metadata("ceremony", -10, 8, None),
            ZkComputeLoad::Proof,
        )
        .unwrap();
    let x = import_proven(&list, &crs, &pk, "ceremony", 32, -10, 8, None).unwrap();
    assert_eq!(x.decrypt(&client), 32);

    // Without contributions, the trapdoor is 1.
    assert!(verify(&start, rng).is_err());
    let refused = [
        // A forged proof of knowledge.
        tampered(&dir, "s", |c| c[1]["s"] = c[0]["s"].clone()),
        // A contribution from another chain, or out of its place.
        tampered(&dir, "swap", |c| c.swap(0, 1)),
        tampered(&dir, "copy", |c| c[1] = c[0].clone()),
        // A contribution dropped: the CRS no longer follows from the rest.
        tampered(&dir, "drop", |c| {
            c.remove(0);
        }),
        tampered(&dir, "last", |c| {
            c.pop();
        }),
        // A CRS made by one party, whose trapdoor it knows.
        {
            let d = copy(&dir, "foreign");
            save(
                &CompactPkeCrs::from_config(config(), 16).unwrap(),
                &d.join(CRS),
            )
            .unwrap();
            d
        },
    ];
    for d in refused {
        assert!(verify(&d, rng).is_err(), "{}", d.display());
        assert!(contribute(&d, rng).is_err(), "{}", d.display());
        std::fs::remove_dir_all(d).unwrap();
    }
    for d in [dir, start] {
        std::fs::remove_dir_all(d).unwrap();
    }
}
