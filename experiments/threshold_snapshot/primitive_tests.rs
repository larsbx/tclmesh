//! Native tests of pinned upstream sharing/reconstruction primitives ONLY.
//! Public fixture scalars, no FHE ciphertext, key generation or release adapter.
use aes_prng::AesRng;
use rand::SeedableRng;
use std::num::Wrapping;
use threshold_fhe::{
    algebra::{base_ring::Z128, galois_rings::degree_4::ResiduePolyF4, structure_traits::One},
    execution::sharing::{
        shamir::{
            reconstruct_w_errors_async, reconstruct_w_errors_sync, InputOp, RevealOp,
            ShamirSharings,
        },
        share::Share,
    },
};

type R = ResiduePolyF4<Z128>;

fn fixture(degree: usize) -> (R, ShamirSharings<R>) {
    let secret = R::from_scalar(Wrapping(23));
    let mut rng = AesRng::seed_from_u64(36);
    (
        secret,
        ShamirSharings::share(&mut rng, secret, 4, degree).unwrap(),
    )
}

#[test]
fn degree_one_all_six_raw_share_pairs_reconstruct() {
    // Actual raw degree-one Shamir shares have a two-share access structure.
    // These are NOT KMS user-decryption response messages or FHE partials.
    let (secret, shares) = fixture(1);
    for i in 0..4 {
        for j in (i + 1)..4 {
            let pair = ShamirSharings::create(vec![shares.shares[i], shares.shares[j]]);
            assert_eq!(pair.reconstruct(1).unwrap(), secret);
        }
    }
}

#[test]
fn degree_one_all_four_honest_triples_robust_open() {
    let (secret, shares) = fixture(1);
    for missing in 0..4 {
        let triple = ShamirSharings::create(
            shares
                .shares
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != missing)
                .map(|(_, s)| *s)
                .collect(),
        );
        assert_eq!(
            reconstruct_w_errors_async(4, 1, 1, 0, &triple).unwrap(),
            Some(secret)
        );
    }
}

#[test]
fn degree_one_two_responses_do_not_complete_robust_open() {
    let (_, shares) = fixture(1);
    let pair = ShamirSharings::create(shares.shares[..2].to_vec());
    assert!(reconstruct_w_errors_async(4, 1, 1, 0, &pair)
        .unwrap()
        .is_none());
}

#[test]
fn degree_two_all_four_raw_triples_reconstruct() {
    let (secret, shares) = fixture(2);
    for missing in 0..4 {
        let triple = ShamirSharings::create(
            shares
                .shares
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != missing)
                .map(|(_, s)| *s)
                .collect(),
        );
        assert_eq!(triple.reconstruct(2).unwrap(), secret);
    }
}

#[test]
fn degree_two_four_party_robust_open_rejects_fault_bounds() {
    // Simply increasing the sharing degree does not provide a supported MPC
    // protocol. The native robust-open bound requires degree + 2*f < n.
    let (_, shares) = fixture(2);
    for faults in 1..=2 {
        assert!(reconstruct_w_errors_async(4, 2, faults, 0, &shares).is_err());
        assert!(reconstruct_w_errors_sync(4, 2, faults, 0, &shares).is_err());
    }
}

#[test]
fn degree_one_four_responses_correct_one_corrupted_raw_share() {
    let (secret, mut shares) = fixture(1);
    let old = shares.shares[0];
    shares.shares[0] = Share::new(old.owner(), old.value() + R::ONE);
    assert_eq!(
        reconstruct_w_errors_async(4, 1, 1, 0, &shares).unwrap(),
        Some(secret)
    );
}
