//! Executable correspondence checks against the exact TFHE-rs 1.8.2 pin.
//! These establish arithmetic/metadata behavior, not a statistical error bound.
use tfhe::shortint::ciphertext::{Degree, NoiseLevel};
use tfhe::shortint::gen_keys;
use tfhe::shortint::parameters::PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;
use tfhe::shortint::server_key::CiphertextNoiseDegree;

#[test]
fn degree_noise_and_torus_correspondence() {
    let params = PARAM_MESSAGE_2_CARRY_2_KS_PBS_TUNIFORM_2M128;
    assert_eq!(params.message_modulus.0, 4);
    assert_eq!(params.carry_modulus.0, 4);
    assert_eq!(params.max_noise_level.get(), 5);
    // Metadata is an upstream estimate, not a measured probability guarantee.
    assert_eq!(params.log2_p_fail, -129.581);
    let (client, server) = gen_keys(params);
    assert_eq!(server.max_degree.get(), 15);
    assert_eq!(server.max_noise_level.get(), 5);

    let zero = server.create_trivial(0);
    let edge = server.checked_scalar_add(&zero, 15).unwrap();
    assert_eq!(edge.degree.get(), 15);
    assert_eq!(client.decrypt_message_and_carry(&edge), 15);
    assert_eq!(client.decrypt(&edge), 3); // message-only API discards carry
    assert!(server.checked_scalar_add(&zero, 16).is_err());
    assert!(server.checked_scalar_add(&zero, 32).is_err());
    // Exact original counterexample: 32*delta wraps modulo 2^64 to zero.
    let wrapped = server.unchecked_scalar_add(&zero, 32);
    assert_eq!(wrapped.degree.get(), 32);
    assert_eq!(client.decrypt_message_and_carry(&wrapped), 0);

    // Isolate the noise guard from the degree guard using metadata only.
    let one = CiphertextNoiseDegree {
        degree: Degree::new(0),
        noise_level: NoiseLevel::NOMINAL,
    };
    let mut level = one;
    for _ in 1..5 {
        server.is_add_possible(level, one).unwrap();
        level.noise_level += one.noise_level;
    }
    assert!(server.is_add_possible(level, one).is_err());

    // One finite sample at each input; this is not evidence for 2^-128.
    let lut = server.generate_lookup_table(|x| (2 * x) % 4);
    for m in 0..4 {
        let input = client.encrypt(m);
        let result = server.apply_lookup_table(&input, &lut);
        assert_eq!(client.decrypt_message_and_carry(&result), (2 * m) % 4);
        assert_eq!(result.noise_level(), NoiseLevel::NOMINAL);
        assert!(result.degree.get() <= 3);
    }
}
