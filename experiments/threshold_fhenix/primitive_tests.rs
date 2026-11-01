//! Limitation witnesses for the pinned paper benchmark, not a release backend.
//! Public scalar/MAC-sum fixtures only: no key generation or FHE decryption.
use nalgebra::DVector;
use num_bigint::BigInt;
use threshold_decryption::{
    mpc::{additive_sharing::AdditiveSecretSharing, party::Party, public_params::PublicParameters},
    network::ProtocolTransferredData,
};

fn final_phase(peer_values: &[i32]) -> Vec<u8> {
    let params = PublicParameters::init(4, 64, 1, 8, 1, 80);
    let mut party = Party::new(0, &params);
    party.set_mac_z(BigInt::from(0));
    let inputs = peer_values
        .iter()
        .map(|value| {
            let mut data = ProtocolTransferredData::empty();
            data.mac_z = Some(bitcode::serialize(&BigInt::from(*value)).unwrap());
            data
        })
        .collect();
    bincode::serialize(&party.execute_step_five(inputs)).unwrap()
}

#[test]
fn final_phase_zero_mac_sum_returns_empty() {
    assert_eq!(
        final_phase(&[0, 0, 0]),
        bincode::serialize(&ProtocolTransferredData::empty()).unwrap()
    );
}

#[test]
fn final_phase_nonzero_mac_sum_also_returns_empty() {
    // Sum = 1 modulo 2^(64+80). A final authenticated-opening check must not
    // silently treat this like the zero-sum case. This helper currently does.
    assert_eq!(final_phase(&[1, 0, 0]), final_phase(&[0, 0, 0]));
}

#[test]
fn final_phase_missing_peer_values_also_returns_empty() {
    // Scope: direct method behavior only. The network may impose additional
    // scheduling checks; this test does not demonstrate a network exploit.
    assert_eq!(final_phase(&[]), final_phase(&[0, 0, 0]));
}

#[test]
fn four_party_additive_fixture_needs_all_four_fixed_shares() {
    let fixture = [1, 2, 4, 8];
    let full = DVector::from_iterator(4, fixture.map(BigInt::from));
    assert_eq!(AdditiveSecretSharing::reveal(&full, 8), BigInt::from(15));
    for missing in 0..4 {
        let triple = DVector::from_iterator(
            3,
            fixture
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != missing)
                .map(|(_, value)| BigInt::from(*value)),
        );
        assert_ne!(AdditiveSecretSharing::reveal(&triple, 8), BigInt::from(15));
    }
}
