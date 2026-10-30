#!/usr/bin/env python3
"""Reintroduce PR #29's second read and require both boundary tests to kill it.

Run from any directory. Restores the source even on failure and rebuilds the
normal binaries on success, so subsequent Tcl tests exercise the fixed code.
Requires the ordinary Rust suite to have passed first.
"""

from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "backends/tfhe/src/ceremony.rs"
CARGO = [
    "cargo", "test", "--release", "--locked", "--manifest-path",
    "backends/tfhe/Cargo.toml",
]
TESTS = [
    ("--test", "ceremony",
     "verification_returns_checked_snapshot_when_ceremony_files_are_replaced"),
    ("--bin", "tclmesh-tfhe",
     "tests::publish_uses_verified_snapshot_when_ceremony_files_are_replaced"),
]


def main():
    original = SOURCE.read_bytes()
    fixed = b"Ok((receipts, from_params(params)?))"
    mutant = b"Ok((receipts, crate::load(&dir.join(CRS))?))"
    if original.count(fixed) != 1:
        raise SystemExit("expected exactly one verified-object return; review the mutant")
    try:
        SOURCE.write_bytes(original.replace(fixed, mutant))
        for target, name, test in TESTS:
            result = subprocess.run(
                CARGO + [target, name, test, "--", "--exact"],
                cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            print(result.stdout, end="", flush=True)
            # A build failure, zero selected tests, or an unrelated panic is
            # not evidence that the regression detects the original defect.
            if (result.returncode == 0
                    or f"test {test} ... FAILED" not in result.stdout
                    or "CRS differs from verified snapshot" not in result.stdout):
                raise SystemExit(f"mutant was not killed by the snapshot assertion: {test}")
            print(f"MUTANT KILLED: {test}", flush=True)
    finally:
        SOURCE.write_bytes(original)
    subprocess.run(
        ["cargo", "build", "--release", "--locked", "--manifest-path",
         "backends/tfhe/Cargo.toml"], cwd=ROOT, check=True,
    )


if __name__ == "__main__":
    main()
