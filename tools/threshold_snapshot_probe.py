#!/usr/bin/env python3
"""Run pinned native sharing primitives, never threshold-decryption acceptance.

Verifies all tracked source bytes before copying them to an isolated build tree.
Only a fixed public-fixture test overlay is added. Cargo runs offline/locked;
dependency preparation is an explicit separate operation. No source pin override.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

PIN = "c668fdd32a33270fc3ad2fd92b49267b734463dd"
ROOT = Path(__file__).resolve().parents[1]
OVERLAY = ROOT / "experiments/threshold_snapshot/primitive_tests.rs"
TEST_NAME = "tclmesh_threshold_primitive_probe"
EXPECTED = {
    "degree_one_all_six_raw_share_pairs_reconstruct",
    "degree_one_all_four_honest_triples_robust_open",
    "degree_one_two_responses_do_not_complete_robust_open",
    "degree_two_all_four_raw_triples_reconstruct",
    "degree_two_four_party_robust_open_rejects_fault_bounds",
    "degree_one_four_responses_correct_one_corrupted_raw_share",
}
CANDIDATES = {
    "zama-snapshot": {
        "pin": PIN, "overlay": OVERLAY, "expected": EXPECTED,
        "tools": ("cargo", "rustc", "protoc"),
        "scope": "native_sharing_primitives_with_public_fixtures",
    },
    "fhenix-paper": {
        "pin": "19b0f0a5a71b67badb85c3c8715b3eba7e866f79",
        "overlay": ROOT / "experiments/threshold_fhenix/primitive_tests.rs",
        "expected": {
            "final_phase_zero_mac_sum_returns_empty",
            "final_phase_nonzero_mac_sum_also_returns_empty",
            "final_phase_missing_peer_values_also_returns_empty",
            "four_party_additive_fixture_needs_all_four_fixed_shares",
        },
        "tools": ("cargo", "rustc"),
        "scope": "native_benchmark_limitation_witnesses_with_public_fixtures",
    },
}


def git(root: Path, *args: str) -> bytes:
    return subprocess.run(["git", "--no-replace-objects", "-C", str(root), *args],
                          check=True, capture_output=True, timeout=30).stdout


def source_files(root: Path, expected_pin: str | None = None) -> dict[str, bytes]:
    """Check every blob, including changes hidden by skip-worktree/index flags."""
    root = root.resolve(strict=True)
    if Path(git(root, "rev-parse", "--show-toplevel").decode().strip()).resolve() != root:
        raise ValueError("not the checkout root")
    if git(root, "rev-parse", "HEAD").decode().strip() != (expected_pin or PIN):
        raise ValueError("unexpected source pin")
    if git(root, "status", "--porcelain", "--untracked-files=normal").strip():
        raise ValueError("source tree is dirty")
    files = {}
    for entry in git(root, "ls-tree", "-rz", "--full-tree", "HEAD").split(b"\0"):
        if not entry:
            continue
        metadata, name = entry.split(b"\t", 1)
        mode, kind, expected = metadata.split()
        relative = Path(name.decode())
        if mode not in (b"100644", b"100755") or kind != b"blob":
            raise ValueError("unsupported source entry")
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError("unsafe source path")
        path = root / relative
        if path.resolve() != path or path.is_symlink() or not path.is_file():
            raise ValueError(f"nonregular source: {relative}")
        data = path.read_bytes()
        actual = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if actual != expected.decode():
            raise ValueError(f"source bytes differ from pinned object: {relative}")
        files[relative.as_posix()] = data
    if not files or "Cargo.lock" not in files:
        raise ValueError("incomplete source tree")
    return files


def check_result(returncode: int, output: str, expected: set[str] | None = None) -> bool:
    """A zero-test run, ignored tests or failure must not become evidence."""
    wanted = EXPECTED if expected is None else expected
    names = re.findall(r"^test ([A-Za-z0-9_]+) \.\.\. ok$", output, re.MULTILINE)
    summaries = re.findall(
        r"test result: ok\. (\d+) passed; (\d+) failed; (\d+) ignored; (\d+) measured; (\d+) filtered out;",
        output,
    )
    return (bool(wanted) and returncode == 0 and len(names) == len(wanted) and set(names) == wanted
            and summaries == [(str(len(wanted)), "0", "0", "0", "0")])


def verify_build_files(root: Path, expected: dict[str, bytes]) -> None:
    """Do not accept a run that emitted fixtures or rewrote copied source."""
    observed = {}
    for path in root.rglob("*"):
        if path.is_symlink():
            raise ValueError("unexpected symlink in native build tree")
        if path.is_file():
            observed[path.relative_to(root).as_posix()] = path.read_bytes()
    if observed != expected:
        raise ValueError("native run changed source or emitted unexpected fixture files")


def probe(source: Path, target_dir: Path, timeout: int, candidate: str = "zama-snapshot") -> dict:
    config = CANDIDATES.get(candidate)
    report = {
        "schema": "tclmesh.threshold-native-primitive-probe.v1",
        "status": "BLOCKED", "cryptographic_release_admitted": False,
        "candidate": candidate,
        "source_pin": config["pin"] if config else None,
        "runner_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "scope": config["scope"] if config else "unknown_candidate",
        "limits": [
            "Not an FHE ciphertext decryption or an independently operated multiparty deployment",
            "Not a KMS v0.14.2 build, share-proof verifier or production security proof",
            "No distributed key custody, recipient-only release or TclMesh wire compatibility established",
            "Local build environment is not hermetic or independently attested",
        ],
    }
    try:
        if config is None:
            raise ValueError("unreviewed native probe candidate")
        files = source_files(source, config["pin"])
        digests = {name: hashlib.sha256(data).hexdigest() for name, data in sorted(files.items())}
        report["source_files"] = len(files)
        report["source_tree_sha256"] = hashlib.sha256(
            json.dumps(digests, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
        overlay = config["overlay"].read_bytes()
        report["test_overlay_sha256"] = hashlib.sha256(overlay).hexdigest()
        report["expected_tests"] = sorted(config["expected"])
        report["toolchain"] = {
            tool: subprocess.run([os.environ.get("PROTOC", tool) if tool == "protoc" else tool, "--version"], capture_output=True, text=True,
                                 check=True, timeout=15).stdout.strip()
            for tool in config["tools"]
        }
        with tempfile.TemporaryDirectory(prefix="tclmesh-native-primitives-") as tmp:
            build = Path(tmp) / "source"
            for name, data in files.items():
                path = build / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
                # Preserve executable scripts; source mode was checked by Git.
                if (source.resolve() / name).stat().st_mode & 0o111:
                    path.chmod(0o755)
            test = build / "tests" / (TEST_NAME + ".rs")
            if test.exists():
                raise ValueError("test overlay collides with pinned source")
            test.parent.mkdir(exist_ok=True)
            test.write_bytes(overlay)
            command = [
                "cargo", "--config", "profile.test.opt-level=0", "--config",
                'profile.test.package."*".opt-level=0', "--config", "profile.test.debug=0",
                "test", "--locked", "--offline", "--jobs", "2", "--target-dir",
                str(target_dir.resolve()), "--test", TEST_NAME, "--", "--test-threads=1",
            ]
            report["command"] = command
            result = subprocess.run(command, cwd=build, capture_output=True, text=True, timeout=timeout)
            verify_build_files(build, {**files, "tests/" + TEST_NAME + ".rs": overlay})
            output = result.stdout + result.stderr
            report["returncode"] = result.returncode
            report["native_output_sha256"] = hashlib.sha256(output.encode()).hexdigest()
            # Only these public-fixture tests execute. Bound diagnostics; never
            # use this runner with real keys or attach arbitrary backend logs.
            report["native_output_tail"] = output[-12000:]
            if check_result(result.returncode, result.stdout, config["expected"]):
                report["status"] = "NATIVE_PRIMITIVES_ONLY"
            else:
                report["blocker"] = "native_build_or_expected_tests_did_not_pass"
        if source_files(source, config["pin"]) != files:
            raise ValueError("source changed during probe")
    except (OSError, ValueError, subprocess.SubprocessError) as exc:
        report["status"] = "BLOCKED"
        report["blocker"] = "source_or_native_probe_unverifiable"
        report["detail"] = str(exc)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--candidate", choices=sorted(CANDIDATES), default="zama-snapshot",
                        help="reviewed source pin and public-fixture test set; never a release capability")
    parser.add_argument("--target-dir", type=Path, required=True,
                        help="build cache outside the pinned source checkout")
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    if not 1 <= args.timeout <= 1800:
        parser.error("--timeout must be between 1 and 1800 seconds")
    source, target = args.source.resolve(), args.target_dir.resolve()
    if target == source or source in target.parents:
        parser.error("--target-dir must be outside the pinned source")
    report = probe(source, target, args.timeout, args.candidate)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["status"] == "NATIVE_PRIMITIVES_ONLY" else 2


if __name__ == "__main__":
    sys.exit(main())
