#!/usr/bin/env python3
"""Generate, compile and run dependency-free opening-boundary probes.

The probes embed the pinned Primus multiplication and loader methods (after
the research overlay) behind an opening spy. ``SCENARIOS`` is the only oracle:
it renders the Rust expectation table, and ``run_matrix`` checks every
variant/scenario exit status against it, so CI and the unit tests cannot
disagree about what a pass is. Research only; no cryptographic claim.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import NamedTuple

import threshold_primus_preprocessing_patch as patch

LEAK_EXIT = 49  # unmasked operands reached the opening spy or a peer


class Scenario(NamedTuple):
    file: str            # preprocessing file name (key of FILES, or absent)
    panic: str | None    # required panic prefix of the fixed probe; None = success
    remaining: int       # triples left in the aborting party's pool


FILES = {
    "valid": "a: 2, b: 3, c: 6\n",
    "empty": "",
    "truncated-row": "a: 2, b: 3, c: 6\na: 2, b: 3\n",
    "malformed": "a: 2, b: invalid, c: 6\na: 2, b: 3, c: 6\n",
}

SCENARIOS = {
    "valid": Scenario("valid", None, 0),
    "missing": Scenario("missing", patch.UNREADABLE_FILE, 0),
    "empty": Scenario("empty", patch.MALFORMED_FILE, 0),
    "truncated-row": Scenario("truncated-row", patch.MALFORMED_FILE, 0),
    "malformed": Scenario("malformed", patch.MALFORMED_FILE, 0),
    "short-batch": Scenario("valid", patch.INSUFFICIENT, 1),
    "exhausted": Scenario("valid", patch.INSUFFICIENT, 0),
    "multiparty-shortage": Scenario("valid", patch.INSUFFICIENT, 1),
}

# Scenarios where the zero-fallback mutant must be caught leaking operands.
EXHAUSTION = ("short-batch", "exhausted", "multiparty-shortage")
VARIANTS = {"fixed": False, "zero-fallback": True}


def expected_exit(variant: str) -> int:
    return LEAK_EXIT if VARIANTS[variant] else 0


def matrix() -> list[tuple[str, str]]:
    return ([("fixed", s) for s in SCENARIOS]
            + [("zero-fallback", s) for s in EXHAUSTION])


def method(source, signature):
    start = "    " + signature
    if source.count(start) != 1:
        raise ValueError(f"expected one method: {signature}")
    body = source.split(start, 1)[1].split("\n    }\n", 1)[0]
    return start + body + "\n    }\n"


def _rust_oracle() -> str:
    arms = "".join(
        f"        {json.dumps(name)} => ({json.dumps(s.panic or '')}, {s.remaining}),\n"
        for name, s in SCENARIOS.items())
    return ("fn oracle(scenario: &str) -> (&'static str, usize) {\n"
            "    match scenario {\n" + arms
            + "        _ => panic!(\"unknown scenario\"),\n    }\n}\n")


PROBE = r"""
use std::collections::VecDeque;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::Path;
use std::sync::mpsc::{channel, Receiver, Sender};
use std::time::{Duration, Instant};

type Msg = (usize, Vec<u64>);

/// Simulated broadcast transport: an opening needs every party's masked
/// shares; a missing party is a bounded timeout, never an indefinite wait.
struct Net {
    me: usize,
    peers: Vec<Sender<Msg>>,
    inbox: Receiver<Msg>,
    timeout: Duration,
}

#[derive(Default)]
struct Probe {
    triplez2k_buffer: VecDeque<(u64, u64, u64)>,
    mul_count_z2k: u32,
    num_threshold: usize,
    openings: Vec<Vec<u64>>,
    received: Vec<Msg>,
    net: Option<Net>,
}

impl Probe {
    fn open_secrets_z2k(
        &mut self, _: usize, _: usize, shares: &[u64], _: bool,
    ) -> Result<Vec<u64>, ()> {
        let Some(net) = &self.net else {
            self.openings.push(shares.to_vec());
            return Ok(shares.to_vec());
        };
        for (peer, tx) in net.peers.iter().enumerate() {
            if peer != net.me {
                let _ = tx.send((net.me, shares.to_vec()));
            }
        }
        let deadline = Instant::now() + net.timeout;
        let mut received = Vec::new();
        let complete = (1..net.peers.len()).all(|_| {
            net.inbox
                .recv_timeout(deadline.saturating_duration_since(Instant::now()))
                .map(|m| received.push(m))
                .is_ok()
        });
        self.received.extend(received);
        if !complete {
            return Err(());
        }
        let opened = self.received.iter().fold(shares.to_vec(), |acc, (_, s)| {
            acc.iter().zip(s).map(|(x, y)| x.wrapping_add(*y)).collect()
        });
        self.openings.push(opened.clone());
        Ok(opened)
    }

    fn add_z2k_const(&self, a: u64, b: u64, k: u32) -> u64 {
        (a + b) % (1 << k)
    }

__METHODS__
}

__ORACLE__

fn panic_message(p: &(dyn std::any::Any + Send)) -> String {
    p.downcast_ref::<String>().cloned()
        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_default()
}

fn fail(code: i32, why: &str) -> ! {
    eprintln!("FAIL: {why}");
    std::process::exit(code)
}

fn check_abort(scenario: &str, message: &str, remaining: usize) {
    let (prefix, expected_remaining) = oracle(scenario);
    if !message.starts_with(prefix) {
        fail(51, &format!("panic {message:?} lacks oracle prefix {prefix:?}"));
    }
    if remaining != expected_remaining {
        fail(52, &format!("{remaining} triples left, expected {expected_remaining}"));
    }
}

fn single_party(scenario: &str, file: &Path) {
    let mut probe = Probe::default();
    let (a, b): (&[u64], &[u64]) = match scenario {
        "short-batch" => (&[7, 8], &[9, 10]),
        _ => (&[7], &[9]),
    };
    let result = catch_unwind(AssertUnwindSafe(|| {
        probe.read_z2k_triples_from_files(file);
        if scenario == "exhausted" {
            assert_eq!(probe.mul_element_wise_z2k(&[7], &[9], 8), vec![63]);
            assert_eq!(probe.openings, [vec![5, 6]]);
            probe.openings.clear();
        }
        probe.mul_element_wise_z2k(a, b, 8)
    }));
    if scenario == "valid" {
        if result.ok() != Some(vec![63]) || probe.openings != [vec![5, 6]] {
            fail(50, "valid multiplication did not open masked operands once");
        }
        return;
    }
    if probe.openings.last().is_some_and(|v| {
        v.ends_with(&[*a.last().unwrap(), *b.last().unwrap()])
    }) {
        fail(49, "unmasked operands reached the opening spy");
    }
    match result {
        Ok(_) => fail(50, "unexpected returned multiplication output"),
        Err(_) if !probe.openings.is_empty() => fail(50, "unexpected opening"),
        Err(p) => check_abort(scenario, &panic_message(&*p), probe.triplez2k_buffer.len()),
    }
}

/// Three parties multiply a batch of two; party SHORT holds one triple fewer.
/// Required: the short party aborts before sending, every peer aborts within
/// the timeout bound, and nobody completes an opening or returns a product.
fn multi_party(file: &Path) {
    const N: usize = 3;
    const SHORT: usize = 2;
    const TIMEOUT: Duration = Duration::from_millis(500);
    let inputs: [([u64; 2], [u64; 2]); N] =
        [([5, 6], [7, 8]), ([11, 12], [13, 14]), ([70, 71], [90, 91])];
    let (txs, rxs): (Vec<_>, Vec<_>) = (0..N).map(|_| channel::<Msg>()).unzip();
    let started = Instant::now();
    let handles: Vec<_> = rxs.into_iter().enumerate().map(|(me, inbox)| {
        let net = Net { me, peers: txs.clone(), inbox, timeout: TIMEOUT };
        let file = file.to_path_buf();
        let (a, b) = inputs[me];
        std::thread::spawn(move || {
            let mut probe = Probe { net: Some(net), ..Probe::default() };
            let result = catch_unwind(AssertUnwindSafe(|| {
                probe.read_z2k_triples_from_files(&file);
                if me != SHORT {
                    probe.triplez2k_buffer.push_back((1, 1, 1));
                }
                probe.mul_element_wise_z2k(&a, &b, 8)
            }));
            let outcome = result.map_err(|p| panic_message(&*p));
            (outcome, probe.openings, probe.received, probe.triplez2k_buffer.len())
        })
    }).collect();
    drop(txs);
    let parties: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    let elapsed = started.elapsed();

    let (short_a, short_b) = inputs[SHORT];
    let leaked = parties.iter().flat_map(|p| &p.2).any(|(from, shares)| {
        *from == SHORT && shares.windows(2).any(|w| w == [short_a[1], short_b[1]])
    });
    if leaked {
        fail(49, "unmasked operands reached a peer");
    }
    if parties.iter().any(|p| p.0.is_ok() || !p.1.is_empty()) {
        fail(50, "a party completed an opening or returned a product");
    }
    if elapsed > TIMEOUT * (N as u32 + 1) {
        fail(53, &format!("abort was not bounded: {elapsed:?}"));
    }
    let (outcome, _, _, remaining) = &parties[SHORT];
    check_abort("multiparty-shortage", outcome.as_ref().unwrap_err(), *remaining);
}

fn main() {
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<_> = std::env::args().collect();
    let (scenario, file) = (args[1].as_str(), Path::new(&args[2]));
    match scenario {
        "multiparty-shortage" => multi_party(file),
        _ => single_party(scenario, file),
    }
    println!("PASS: {scenario}");
}
"""


def render(source: str, mutant: bool = False) -> str:
    """Probe for an already-overlaid dn.rs source (no provenance check)."""
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
    if patch.HELPERS not in source:
        raise ValueError("overlay helpers not found verbatim")
    return (patch.HELPERS + PROBE.replace("__ORACLE__", _rust_oracle())
            .replace("__METHODS__", loader + take + multiply))


def generate(original: bytes, mutant: bool = False) -> str:
    git_blob = hashlib.sha1(f"blob {len(original)}\0".encode() + original).hexdigest()
    if git_blob != patch.SOURCE_BLOB:
        raise ValueError("Primus dn.rs does not match the pinned Git blob")
    return render(patch.rewrite_source(original.decode("utf-8")), mutant)


def run_matrix(probes: dict[str, str], workdir: Path,
               rustc: list[str] = ["rustc"], timeout: int = 30) -> dict:
    """Compile each probe and check every matrix cell against SCENARIOS."""
    for name, text in FILES.items():
        (workdir / name).write_text(text, encoding="utf-8")
    for variant, text in probes.items():
        src = workdir / f"{variant}.rs"
        src.write_text(text, encoding="utf-8")
        subprocess.run([*rustc, "--edition=2021", "-A", "warnings",
                        "--crate-name", "opening_probe", str(src),
                        "-o", str(workdir / variant)],
                       check=True, capture_output=True, text=True, timeout=300)
    results = []
    for variant, scenario in matrix():
        proc = subprocess.run([str(workdir / variant), scenario,
                               str(workdir / SCENARIOS[scenario].file)],
                              capture_output=True, text=True, timeout=timeout)
        want = expected_exit(variant)
        results.append({"variant": variant, "scenario": scenario,
                        "exit": proc.returncode, "expected_exit": want,
                        "ok": proc.returncode == want,
                        "diagnostic": (proc.stdout + proc.stderr).strip().splitlines()[-1:]})
    return {"schema": "tclmesh.threshold-primus-opening-probe.v2",
            "ok": all(r["ok"] for r in results), "results": results,
            "probe_sha256": {v: hashlib.sha256(t.encode()).hexdigest()
                             for v, t in probes.items()},
            "cryptographic_release_admitted": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path, help="original pinned dn.rs")
    parser.add_argument("out", type=Path)
    parser.add_argument("--run", action="store_true", help="compile and run the matrix")
    parser.add_argument("--rustc", default="rustc", help="rustc command, e.g. 'rustc +1.85.1'")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    original = args.source.read_bytes()
    probes = {v: generate(original, m) for v, m in VARIANTS.items()}
    for variant, text in probes.items():
        (args.out / f"{variant}.rs").write_text(text, encoding="utf-8")
    if not args.run:
        return 0
    report = run_matrix(probes, args.out, args.rustc.split())
    report["source_sha256"] = hashlib.sha256(original).hexdigest()
    data = json.dumps(report, indent=2, sort_keys=True)
    if args.report:
        args.report.write_text(data + "\n", encoding="utf-8")
    print(data)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
