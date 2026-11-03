#!/usr/bin/env python3
"""Generate dependency-free opening-boundary probes from pinned Primus methods."""
import argparse
import hashlib
from pathlib import Path

import threshold_primus_preprocessing_patch as patch


def method(source, signature):
    start = "    " + signature
    if source.count(start) != 1:
        raise ValueError(f"expected one method: {signature}")
    body = source.split(start, 1)[1].split("\n    }\n", 1)[0]
    return start + body + "\n    }\n"


PROBE = r"""
use std::collections::VecDeque;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::Path;

#[derive(Default)]
struct Probe {
    triplez2k_buffer: VecDeque<(u64, u64, u64)>,
    mul_count_z2k: u32,
    num_threshold: usize,
    openings: Vec<Vec<u64>>,
}

impl Probe {
    fn open_secrets_z2k(
        &mut self, _: usize, _: usize, shares: &[u64], _: bool,
    ) -> Result<Vec<u64>, ()> {
        self.openings.push(shares.to_vec());
        Ok(shares.to_vec())
    }

    fn add_z2k_const(&self, a: u64, b: u64, k: u32) -> u64 {
        (a + b) % (1 << k)
    }

__METHODS__
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<_> = std::env::args().collect();
    let scenario = args[1].as_str();
    let mut probe = Probe::default();
    let (a, b): (&[u64], &[u64]) = match scenario {
        "short-batch" => (&[7, 8], &[9, 10]),
        _ => (&[7], &[9]),
    };

    let result = catch_unwind(AssertUnwindSafe(|| {
        probe.read_z2k_triples_from_files(Path::new(&args[2]));
        if scenario == "exhausted" {
            assert_eq!(probe.mul_element_wise_z2k(&[7], &[9], 8), vec![63]);
            assert_eq!(probe.openings, [vec![5, 6]]);
            probe.openings.clear();
        }
        probe.mul_element_wise_z2k(a, b, 8)
    }));

    if scenario == "valid" {
        assert_eq!(result.ok(), Some(vec![63]));
        assert_eq!(probe.openings, [vec![5, 6]]);
    } else if result.is_ok() || !probe.openings.is_empty() {
        // Report only the classification, even though all operands are public.
        if probe.openings.last().is_some_and(|values| {
            values.ends_with(&[*a.last().unwrap(), *b.last().unwrap()])
        }) {
            eprintln!("FAIL: unmasked operands reached the opening spy");
            std::process::exit(49);
        }
        eprintln!("FAIL: unexpected opening or returned multiplication output");
        std::process::exit(50);
    } else {
        let panic = result.unwrap_err();
        let message = panic.downcast_ref::<String>().map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied()).unwrap_or("");
        let expected = match scenario {
            "missing" => "Missing Z2k preprocessing file",
            "empty" | "truncated-row" | "malformed" => "Malformed or empty Z2k preprocessing file",
            "short-batch" | "exhausted" => "Insufficient Z2k preprocessing",
            _ => unreachable!(),
        };
        assert!(message.starts_with(expected));
        let expected_remaining = if scenario == "short-batch" { 1 } else { 0 };
        assert_eq!(probe.triplez2k_buffer.len(), expected_remaining);
    }
    println!("PASS: {scenario}");
}
"""


def generate(original, mutant=False):
    git_blob = hashlib.sha1(f"blob {len(original)}\0".encode() + original).hexdigest()
    if git_blob != patch.SOURCE_BLOB:
        raise ValueError("Primus dn.rs does not match the pinned Git blob")
    source = patch.rewrite_source(original.decode("utf-8"))
    multiply = method(source, "fn mul_element_wise_z2k(&mut self,")
    guard = "        require_z2k_triples_available(self.triplez2k_buffer.len(), batch_size);"
    opening = ".open_secrets_z2k(0, self.num_threshold, &masked_values, true)"
    if multiply.count(opening) != 1 or not (
        multiply.index(guard) < multiply.index("self.next_triple_z2k()")
        < multiply.index("[a[i] - r, b[i] - s]") < multiply.index(opening)
    ):
        raise ValueError("unexpected masking or opening order")
    loader = method(source, "pub fn read_z2k_triples_from_files(")
    take = method(source, "pub fn next_triple_z2k(")
    if mutant:
        # Restore both pieces of the original exhaustion path. Keeping either
        # guard would stop the deliberate fallback before the opening spy.
        multiply = multiply.replace(guard, "", 1)
        take = patch.OLD_NEXT_TRIPLE
    return patch.HELPERS + PROBE.replace("__METHODS__", loader + take + multiply)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="original pinned dn.rs")
    parser.add_argument("out", type=Path)
    args = parser.parse_args()
    original = args.source.read_bytes()
    for name, mutant in [("fixed", False), ("zero-fallback", True)]:
        (args.out / f"{name}.rs").write_text(generate(original, mutant), encoding="utf-8")


if __name__ == "__main__":
    main()
