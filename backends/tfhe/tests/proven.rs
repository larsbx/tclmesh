//! A dishonest prover calls TFHE-rs directly, skipping `tclmesh-tfhe-prove`'s
//! range check. Whatever it pushes, a verified `bits`-bit list expands to a
//! value below `2^bits`: the bound comes from the ciphertext, not the prover.

use tclmesh_tfhe::{config, import_proven, metadata, CRS_MAX_BITS};
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
        let x = import_proven(&list, &crs, &pk, "bounded", 32, lo, 8, Some(hi)).unwrap();
        assert_eq!(x.decrypt(&client), want, "offset {offset}");
        // Bound to hi: the same proof is refused without it or with another.
        assert!(import_proven(&list, &crs, &pk, "bounded", 32, lo, 8, None).is_err());
        assert!(import_proven(&list, &crs, &pk, "bounded", 32, lo, 8, Some(250)).is_err());
    }
}

/// A proven range must lie in the word it is imported into: the same proof
/// whose range leaves the 32-bit word is refused there and held exactly as a
/// 64-bit word.
#[test]
fn proven_ranges_fit_the_word_they_are_imported_into() {
    let client = ClientKey::generate(config());
    set_server_key(ServerKey::new(&client));
    let pk = CompactPublicKey::new(&client);
    let crs = CompactPkeCrs::from_config(config(), 16).unwrap();
    for lo in [i64::from(i32::MAX) - 254, 5_000_000_000] {
        let list = ProvenCompactCiphertextList::builder(&pk)
            .push_with_num_bits(7u32, 8)
            .unwrap()
            .build_with_proof_packed(&crs, &metadata("wide", lo, 8, None), ZkComputeLoad::Proof)
            .unwrap();
        assert!(import_proven(&list, &crs, &pk, "wide", 32, lo, 8, None).is_err());
        let x = import_proven(&list, &crs, &pk, "wide", 64, lo, 8, None).unwrap();
        assert_eq!((x.width(), x.decrypt(&client)), (64, lo + 7));
    }
}

/// A proof is bound to the public key it was made under: a runtime with
/// fresh keys (every new `tclmesh-tfhe` process) refuses a replayed proof.
#[test]
fn proofs_do_not_survive_a_change_of_keys() {
    let (first, second) = (ClientKey::generate(config()), ClientKey::generate(config()));
    set_server_key(ServerKey::new(&second));
    let (old, new) = (
        CompactPublicKey::new(&first),
        CompactPublicKey::new(&second),
    );
    let crs = CompactPkeCrs::from_config(config(), 16).unwrap();
    let list = ProvenCompactCiphertextList::builder(&old)
        .push_with_num_bits(7u32, 8)
        .unwrap()
        .build_with_proof_packed(&crs, &metadata("replay", 0, 8, None), ZkComputeLoad::Proof)
        .unwrap();
    assert!(import_proven(&list, &crs, &new, "replay", 32, 0, 8, None).is_err());
    assert!(import_proven(&list, &crs, &old, "replay", 32, 0, 8, None).is_ok());
}

/// 32-bit offsets: zero-extended into the 64-bit word; in the 32-bit word
/// only the whole word fits, and an offset past 2^31 wraps back into it
/// exactly.
#[test]
fn thirty_two_bit_offsets_are_exact_in_either_word() {
    let client = ClientKey::generate(config());
    set_server_key(ServerKey::new(&client));
    let pk = CompactPublicKey::new(&client);
    let crs = CompactPkeCrs::from_config(config(), CRS_MAX_BITS).unwrap();
    let min = i64::from(i32::MIN);
    for (width, lo, offset) in [
        (64, 0, u32::MAX),
        (64, -7, 3_000_000_000),
        (32, min, 4_000_000_000),
        (32, min, 5),
    ] {
        let list = ProvenCompactCiphertextList::builder(&pk)
            .push_with_num_bits(offset, 32)
            .unwrap()
            .build_with_proof_packed(&crs, &metadata("wide", lo, 32, None), ZkComputeLoad::Proof)
            .unwrap();
        let x = import_proven(&list, &crs, &pk, "wide", width, lo, 32, None).unwrap();
        assert_eq!(
            x.decrypt(&client),
            lo + i64::from(offset),
            "{width} {lo} {offset}"
        );
    }
    let list = ProvenCompactCiphertextList::builder(&pk)
        .push_with_num_bits(0u32, 32)
        .unwrap()
        .build_with_proof_packed(
            &crs,
            &metadata("wide", min + 1, 32, None),
            ZkComputeLoad::Proof,
        )
        .unwrap();
    assert!(import_proven(&list, &crs, &pk, "wide", 32, min + 1, 32, None).is_err());
}
