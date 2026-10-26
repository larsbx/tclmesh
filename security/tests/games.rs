//! The calibrated battery, exact small models, and the zero-knowledge suite.

use tclmesh_security::exact::{one_time_pad_advantage, regev_advantage, short_key_pad_advantage};
use tclmesh_security::ind_cpa::assess;
use tclmesh_security::lwe::{Flaw, Regev};
use tclmesh_security::rng::Rng;
use tclmesh_security::stats::total_variation;
use tclmesh_security::zk::{
    extract, forge, prove, real_distribution, respond, simulated_distribution, verify, verify_fs,
    Group,
};

fn sound() -> Regev {
    Regev::sound(16, 3329, 8)
}

// ---------------------------------------------------------------- IND-CPA

#[test]
fn sound_scheme_decrypts() {
    let s = sound();
    let mut rng = Rng::new(1);
    for _ in 0..500 {
        let key = s.keygen(&mut rng);
        let m = rng.bit();
        assert_eq!(s.decrypt(&key, &s.encrypt(&key, m, &mut rng)), m);
    }
}

#[test]
fn battery_finds_no_break_in_the_sound_scheme() {
    let v = assess(&sound(), 2000, 11, 1e-3);
    assert!(!v.broken, "false positive: {:?}", v.results);
}

#[test]
fn calibration_every_flaw_is_detected() {
    for flaw in [
        Flaw::NoNoise,
        Flaw::Deterministic,
        Flaw::ReusedRandomness,
        Flaw::Appended,
        Flaw::SizeLeak,
    ] {
        let v = assess(&sound().with_flaw(flaw), 2000, 13, 1e-3);
        assert!(v.broken, "{flaw:?} went undetected: {:?}", v.results);
    }
}

// ------------------------------------------------------------ exact models

#[test]
fn one_time_pad_is_perfectly_secret() {
    for q in [2, 5, 13] {
        for (m0, m1) in [(0, 1), (1, q - 1)] {
            assert_eq!(one_time_pad_advantage(q, m0, m1), 0.0);
        }
    }
}

#[test]
fn short_key_pad_is_detected_exactly() {
    assert!(short_key_pad_advantage(13, 0, 6) > 0.0);
}

#[test]
fn toy_regev_advantage_is_exactly_q_to_the_minus_n() {
    // noise supports of 0 and ⌊q/2⌋ are disjoint: the only leak is a = 0
    for (n, q, noise) in [(1, 5, 0), (1, 7, 1), (2, 5, 0), (2, 7, 1)] {
        let adv = regev_advantage(n, q, noise);
        let expected = (q as f64).powi(-(n as i32));
        assert!(
            (adv - expected).abs() < 1e-12,
            "n={n} q={q}: {adv} ≠ {expected}"
        );
    }
}

// --------------------------------------------------------- zero knowledge

#[test]
fn completeness_on_every_witness_nonce_and_challenge() {
    let g = Group::small();
    for w in 0..g.q {
        let h = g.exp(w);
        for r in 0..g.q {
            for c in 0..g.q {
                assert!(verify(&g, h, &respond(&g, w, r, c)));
            }
        }
    }
}

#[test]
fn special_soundness_extractor_recovers_every_witness() {
    let g = Group::small();
    for w in 0..g.q {
        for r in 0..g.q {
            for (c1, c2) in [(0, 1), (3, 7), (10, 2)] {
                let (a, b) = (respond(&g, w, r, c1), respond(&g, w, r, c2));
                assert_eq!(extract(&g, &a, &b), Some(w));
            }
        }
    }
}

#[test]
fn calibration_nonce_reuse_leaks_the_witness() {
    // two sessions with one nonce are a pair of public transcripts the
    // extractor needs: the leak must be reported
    let g = Group::large();
    let mut rng = Rng::new(5);
    let w = rng.below(g.q);
    let r = rng.below(g.q);
    let (a, b) = (respond(&g, w, r, 17), respond(&g, w, r, 4242));
    assert_eq!(extract(&g, &a, &b), Some(w));
}

#[test]
fn honest_verifier_zero_knowledge_is_perfect() {
    // real and simulated transcripts: identical distributions, exactly
    let g = Group::small();
    let nonces: Vec<u64> = (0..g.q).collect();
    for w in 0..g.q {
        let real = real_distribution(&g, w, &nonces);
        let simulated = simulated_distribution(&g, g.exp(w));
        assert_eq!(total_variation(&real, &simulated), 0.0, "w={w}");
    }
}

#[test]
fn calibration_biased_nonces_are_distinguishable_from_the_simulator() {
    // a prover whose nonces miss part of Z_q (here: always the same nonce)
    // produces transcripts the simulator does not
    let g = Group::small();
    let biased = real_distribution(&g, 3, &[5]);
    let simulated = simulated_distribution(&g, g.exp(3));
    assert!(total_variation(&biased, &simulated) > 0.5);
}

#[test]
fn fiat_shamir_proofs_verify_on_a_large_group() {
    let g = Group::large();
    let mut rng = Rng::new(9);
    for _ in 0..50 {
        let w = rng.below(g.q);
        let (h, tr) = prove(&g, w, &mut rng, true);
        assert!(verify_fs(&g, h, &tr, true));
        // a proof for one statement does not verify for another
        assert!(!verify_fs(&g, g.exp(w + 1), &tr, true));
    }
}

#[test]
fn calibration_weak_fiat_shamir_is_forgeable_strong_is_not() {
    let g = Group::large();
    let mut rng = Rng::new(21);
    let weak = (0..50)
        .filter(|_| forge(&g, &mut rng, false).is_some())
        .count();
    let strong = (0..50)
        .filter(|_| forge(&g, &mut rng, true).is_some())
        .count();
    assert!(weak >= 49, "weak Fiat–Shamir forgeries: {weak}/50");
    assert_eq!(strong, 0, "strong Fiat–Shamir forgeries: {strong}/50");
}
