#!/usr/bin/env python3
"""Require the syscall regression to reject PR #35's missing-parent-sync bug."""

from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "backends/tfhe/src/main.rs"
BUILD = ["cargo", "build", "--release", "--locked", "--manifest-path",
         "backends/tfhe/Cargo.toml", "--bin", "tclmesh-tfhe"]


def main():
    original = SOURCE.read_bytes()
    fixed = b"Ok(()) => [claims.as_path(), dir]"
    if original.count(fixed) != 1:
        raise SystemExit("expected exactly one parent-sync boundary; review the mutant")
    try:
        SOURCE.write_bytes(original.replace(fixed, b"Ok(()) => [claims.as_path()]"))
        subprocess.run(BUILD, cwd=ROOT, check=True)
        p = subprocess.run(
            [sys.executable, "tools/check_claim_durability.py", "--parent-only"],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        print(p.stdout, end="", flush=True)
        if p.returncode == 0 or "AssertionError: claim sync ordering differs:" not in p.stdout:
            raise SystemExit("parent-sync mutant was not killed by the ordering assertion")
        print("MUTANT KILLED: successful import without parent-directory fsync", flush=True)
    finally:
        SOURCE.write_bytes(original)
        subprocess.run(BUILD, cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
