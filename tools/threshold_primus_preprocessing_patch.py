#!/usr/bin/env python3
"""Research-only fail-closed patch for the exact Primus ThFHE source variant.

Patches a disposable, clean checkout of primus-labs/primus-fhe at exactly
a0d075..., never TclMesh's runtime or any production system. It does not
establish any threshold-FHE cryptographic security property.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys

SOURCE_REPO = "primus-labs/primus-fhe"
SOURCE_SHA = "a0d075d9ec055fb8652925fee65768a14a627cfa"
SOURCE_BLOB = "da2e4457a9f7d8f434815d8645c4b4b1b8c0eded"
REL = "mpc/src/dn.rs"

OLD_LOADER = """    /// read z2k beaver triples from files
    pub fn read_z2k_triples_from_files(&mut self, filename: &Path) {
        //println!("read file {:?}", filename);
        use std::fs;
        use std::str::FromStr;
        //println!("read file: {:?}", filename);
        let content = fs::read_to_string(filename).expect("Failed to read file");

        for line in content.lines() {
            let parts: Vec<&str> = line.split(", ").collect();
            let values: Vec<u64> = parts
                .iter()
                .filter_map(|p| p.split(": ").nth(1))
                .filter_map(|v| u128::from_str(v).ok())
                .map(|num| num as u64)
                .collect();
            if values.len() == 3 {
                self.triplez2k_buffer
                    .push_back((values[0], values[1], values[2]));
            }
        }
        //println!("z2k triples: {}", self.triplez2k_buffer.len());
    }
"""

NEW_LOADER = """    /// A malformed, absent, or empty preprocessing file fails before any
    /// share masking or opening. Parsed rows are committed atomically.
    pub fn read_z2k_triples_from_files(&mut self, filename: &Path) {
        let content = std::fs::read_to_string(filename)
            .expect("Missing Z2k preprocessing file");
        let parsed = parse_z2k_triple_file(&content)
            .expect("Malformed or empty Z2k preprocessing file");
        self.triplez2k_buffer.extend(parsed);
    }
"""

OLD_NEXT_TRIPLE = """    pub fn next_triple_z2k(&mut self) -> (u64, u64, u64) {
        if self.triplez2k_buffer.is_empty() {
            return (0, 0, 0);
        }

        self.triplez2k_buffer.pop_front().unwrap()
    }
"""

NEW_NEXT_TRIPLE = """    pub fn next_triple_z2k(&mut self) -> (u64, u64, u64) {
        take_z2k_triple_checked(&mut self.triplez2k_buffer)
    }
"""

OLD_BATCH = """        let batch_size = a.len();

        // Get required Beaver triples
        let triples: Vec<(u64, u64, u64)> =
            (0..batch_size).map(|_| self.next_triple_z2k()).collect();
"""

NEW_BATCH = """        let batch_size = a.len();

        // Critical: fail BEFORE drawing masks or opening masked operands.
        // Do not partially consume a batch with a short triple pool.
        require_z2k_triples_available(self.triplez2k_buffer.len(), batch_size);

        // Get required Beaver triples
        let triples: Vec<(u64, u64, u64)> =
            (0..batch_size).map(|_| self.next_triple_z2k()).collect();
"""

HELPERS = """
// TclMesh #49 research-only modified-overlay hardening.
// The wire data use u128 decimal values narrowed to u64 as in the original
// importer. A u64-only parser would reject the real upstream fixture data.
fn parse_z2k_triple_line(line: &str) -> Result<(u64, u64, u64), &'static str> {
    let mut parts = line.split(", ");
    let parse = |value: Option<&str>, label: &str| -> Result<u64, &'static str> {
        let raw = value.ok_or("missing triple field")?
            .strip_prefix(label).ok_or("wrong triple field name")?
            .parse::<u128>().map_err(|_| "noncanonical triple integer")?;
        Ok(raw as u64)
    };
    let a = parse(parts.next(), "a: ")?;
    let b = parse(parts.next(), "b: ")?;
    let c = parse(parts.next(), "c: ")?;
    if parts.next().is_some() {
        return Err("extra triple fields");
    }
    Ok((a, b, c))
}

fn parse_z2k_triple_file(contents: &str)
    -> Result<Vec<(u64, u64, u64)>, &'static str>
{
    let parsed: Vec<(u64, u64, u64)> = contents
        .lines().map(parse_z2k_triple_line)
        .collect::<Result<_, _>>()?;
    if parsed.is_empty() {
        return Err("empty triple file");
    }
    Ok(parsed)
}

fn require_z2k_triples_available(available: usize, needed: usize) {
    assert!(available >= needed, "Insufficient Z2k preprocessing");
}

fn take_z2k_triple_checked(buffer: &mut VecDeque<(u64, u64, u64)>)
    -> (u64, u64, u64)
{
    buffer.pop_front().expect("Z2k preprocessing exhausted")
}
"""

NATIVE_TESTS = """
#[cfg(test)]
mod tclmesh_research_preprocessing_tests {
    use super::*;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    #[test]
    fn accepts_128_bit_file_values_with_original_cast_semantics() {
        let record = "a: 340282366920938463463374607431768211455, b: 2, c: 3";
        let parsed = parse_z2k_triple_file(record).unwrap();
        assert_eq!(parsed, vec![(u64::MAX, 2, 3)]);
    }

    #[test]
    fn rejects_empty_triple_file() {
        assert!(parse_z2k_triple_file("").is_err());
    }

    #[test]
    fn rejects_malformed_and_partial_triple_rows() {
        for data in [
            "a: 1, b: 2",
            "a: 1, b: 2, c: 3\ninvalid row",
            "a: 1, b: 2, c: 3, d: 4",
            "a: 1, b: not-a-number, c: 3",
            "a: 1, b: 2, c: 3\n",
        ] {
            // The final form is a valid single record with a newline.
            let valid = data == "a: 1, b: 2, c: 3\n";
            assert_eq!(parse_z2k_triple_file(data).is_ok(), valid);
        }
    }

    #[test]
    fn detects_exhaustion_before_masking() {
        let no_triples = catch_unwind(|| require_z2k_triples_available(0, 1));
        assert!(no_triples.is_err());
        let partial_batch = catch_unwind(|| require_z2k_triples_available(2, 3));
        assert!(partial_batch.is_err());
        require_z2k_triples_available(3, 3);
    }

    #[test]
    fn exhausted_buffer_never_supplies_a_zero_triple() {
        let mut buf = VecDeque::new();
        let result = catch_unwind(AssertUnwindSafe(|| take_z2k_triple_checked(&mut buf)));
        assert!(result.is_err());
        buf.push_back((0, 0, 0)); // Explicitly provided triple != exhaustion.
        assert_eq!(take_z2k_triple_checked(&mut buf), (0, 0, 0));
    }
}
"""

# Source-only test fixture, deliberately **not** the actual upstream file.
TEST_SOURCE_FIXTURE = ("mod matrix;\n" + OLD_LOADER + OLD_NEXT_TRIPLE
                       + OLD_BATCH
                       + "        let masked_values: Vec<u64> = vec![];\n"
                       + "        .open_secrets_z2k(0, self.num_threshold, &masked_values, true)\n")


def _replace_exact_once(source: str, old: str, new: str, description: str) -> str:
    if source.count(old) != 1:
        raise ValueError(f"expected unique unmodified {description} source signature")
    return source.replace(old, new, 1)


def rewrite_source(source: str) -> str:
    if source.count("mod matrix;\n") != 1:
        raise ValueError("expected unique matrix module insertion point")
    source = _replace_exact_once(source, OLD_LOADER, NEW_LOADER, "old loader")
    source = _replace_exact_once(source, OLD_NEXT_TRIPLE, NEW_NEXT_TRIPLE,
                                 "old triple underflow")
    source = _replace_exact_once(source, OLD_BATCH, NEW_BATCH, "old batch")
    source = source.replace("mod matrix;\n", "mod matrix;\n" + HELPERS, 1)
    if "mod tclmesh_research_preprocessing_tests" in source:
        raise ValueError("patch already present")
    return source + "\n" + NATIVE_TESTS


def assess_patch(original: str, modified: str) -> dict:
    # Source-only classification, no cryptographic release authority.
    return {
        "schema": "tclmesh.threshold-primus-preprocessing-patch.v1",
        "status": "MODIFIED_OVERLAY_SOURCE_PATCH_ONLY",
        "source": SOURCE_REPO, "expected_commit": SOURCE_SHA,
        "source_sha256": hashlib.sha256(original.encode()).hexdigest(),
        "modified_sha256": hashlib.sha256(modified.encode()).hexdigest(),
        "native_tests_executed": False, "malicious_security_established": False,
        "cryptographic_release_admitted": False,
        "limits": [
            "Modified Primus variant, NOT original Ajax reproduction",
            "Panic-based fail-before-open guard is research safety hardening, not a cryptographic security reduction",
            "Actual network, active adversary, DKG, confidentiality, and recipient-only release remain unverified",
        ],
    }


def _git(root: Path, *args: str) -> bytes:
    return subprocess.run(
        ["git", "--no-replace-objects", "-C", str(root), *args],
        capture_output=True, check=True, timeout=30,
    ).stdout


def apply_to_exact_checkout(root: Path) -> dict:
    if root.is_symlink():
        raise ValueError("symlinked research checkout")
    root = root.resolve(strict=True)
    if not root.is_dir():
        raise ValueError("missing checkout")
    top = Path(_git(root, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    if top != root:
        raise ValueError("source must be exact Git checkout root")
    head = _git(root, "rev-parse", "HEAD").decode().strip()
    if head != SOURCE_SHA:
        raise ValueError("Primus source HEAD mismatch")
    if _git(root, "status", "--porcelain", "--untracked-files=all").strip():
        raise ValueError("source must be clean before the research overlay")
    rel = root / REL
    if not rel.is_file() or rel.is_symlink():
        raise ValueError("missing or symlinked checked source")
    blob = _git(root, "rev-parse", f"HEAD:{REL}").decode().strip()
    if blob != SOURCE_BLOB:
        raise ValueError("Primus source blob mismatch")
    committed = _git(root, "show", f"HEAD:{REL}")
    if rel.read_bytes() != committed:
        raise ValueError("source bytes differ from pinned HEAD")
    original = committed.decode("utf-8")
    modified = rewrite_source(original)
    rel.write_text(modified, encoding="utf-8", newline="")
    result = assess_patch(original, modified)
    result["source_commit_verified"] = head
    result["source_git_blob_verified"] = blob
    return result


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--source", type=Path, required=True)
    p.add_argument("--require-release", action="store_true")
    p.add_argument("--report", type=Path)
    args = p.parse_args()
    if args.require_release:
        print(json.dumps({"status": "BLOCKED", "cryptographic_release_admitted": False}))
        return 2
    try:
        report = apply_to_exact_checkout(args.source)
    except (ValueError, OSError, UnicodeError, subprocess.SubprocessError) as e:
        print(json.dumps({"status": "SOURCE_INVALID", "error": str(e),
                          "cryptographic_release_admitted": False}, sort_keys=True))
        return 2
    data = json.dumps(report, sort_keys=True, indent=2)
    if args.report:
        args.report.write_text(data + "\n", encoding="utf-8")
    print(data)
    return 0


if __name__ == "__main__":
    sys.exit(main())
