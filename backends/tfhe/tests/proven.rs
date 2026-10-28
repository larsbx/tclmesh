//! A dishonest prover calls TFHE-rs directly, skipping `tclmesh-tfhe-prove`'s
//! range check. Whatever it pushes, a verified `bits`-bit list expands to a
//! value below `2^bits`: the bound comes from the ciphertext, not the prover.

use tclmesh_tfhe::{config, import_proven, metadata};
use tfhe::prelude::*;
use tfhe::zk::{CompactPkeCrs, ZkComputeLoad};
use tfhe::{
    set_server_key, ClientKey, CompactPublicKey, FheUint16, FheUint8, ProvenCompactCiphertextList,
    ServerKey,
};

#[test]
fn oversized_offsets_cannot_leave_the_proven_width() {
    let client = ClientKey::generate(config());
    set_server_key(ServerKey::new(&client));
    let pk = CompactPublicKey::new(&client);
    let crs = CompactPkeCrs::from_config(config(), 16).unwrap();
    let statement = metadata("adversary", 0, 8, None);
    for offset in [255u32, 256, 300, 65535, u32::MAX] {
        let list = ProvenCompactCiphertextList::builder(&pk)
            .push_with_num_bits(offset, 8)
            .unwrap()
            .build_with_proof_packed(&crs, &statement, ZkComputeLoad::Proof)
            .unwrap();
        let expander = list.verify_and_expand(&crs, &pk, &statement).unwrap();
        let a: FheUint8 = expander.get(0).unwrap().unwrap();
        let a: u8 = a.decrypt(&client);
        assert_eq!(u32::from(a), offset % 256, "offset {offset}");
        // The width is part of the ciphertext: it cannot be read as wider.
        assert!(expander.get::<FheUint16>(0).is_err());
    }
}

/// With an upper bound, a dishonest prover who encrypts an offset past `hi`
/// gets `hi`: honest inputs are exact, dishonest ones cannot leave `[lo, hi]`.
#[test]
fn upper_bounds_hold_against_a_dishonest_prover() {
    let client = ClientKey::generate(config());
    set_server_key(ServerKey::new(&client));
    let pk = CompactPublicKey::new(&client);
    let crs = CompactPkeCrs::from_config(config(), 16).unwrap();
    let (lo, hi) = (-5, 200);
    for (offset, want) in [(0u32, -5), (205, 200), (206, 200), (255, 200)] {
        let list = ProvenCompactCiphertextList::builder(&pk)
            .push_with_num_bits(offset, 8)
            .unwrap()
            .build_with_proof_packed(
                &crs,
                &metadata("bounded", lo, 8, Some(hi)),
                ZkComputeLoad::Proof,
            )
            .unwrap();
        let x = import_proven(&list, &crs, &pk, "bounded", lo, 8, Some(hi)).unwrap();
        let x: i32 = x.decrypt(&client);
        assert_eq!(x, want, "offset {offset}");
        // Bound to hi: the same proof is refused without it or with another.
        assert!(import_proven(&list, &crs, &pk, "bounded", lo, 8, None).is_err());
        assert!(import_proven(&list, &crs, &pk, "bounded", lo, 8, Some(250)).is_err());
    }
}
