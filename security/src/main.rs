//! `tclmesh-security`: runs the calibrated battery and prints its verdicts.

use tclmesh_security::ind_cpa::assess;
use tclmesh_security::lwe::{Flaw, Regev};

fn main() {
    let sound = Regev::sound(16, 3329, 8);
    let flaws = [
        Flaw::None,
        Flaw::NoNoise,
        Flaw::Deterministic,
        Flaw::ReusedRandomness,
        Flaw::Appended,
        Flaw::SizeLeak,
    ];
    let mut wrong = 0;
    for flaw in flaws {
        let v = assess(&sound.clone().with_flaw(flaw), 2000, 7, 1e-3);
        let expected = flaw != Flaw::None;
        let status = if v.broken == expected { "ok" } else { "WRONG" };
        if v.broken != expected {
            wrong += 1;
        }
        println!("{status:5} {:45} broken={}", v.scheme, v.broken);
        for (name, adv) in &v.results {
            println!(
                "        {name:15} advantage {:.3} in [{:.3}, {:.3}]",
                adv.estimate, adv.low, adv.high
            );
        }
    }
    std::process::exit(if wrong == 0 { 0 } else { 1 });
}
