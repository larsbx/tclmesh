#!/usr/bin/env python3
"""Read-only, fail-closed provenance and dependency preflight for TclMesh #36.

This does NOT verify threshold decryption, key custody, malicious security,
or TFHE ciphertext/proof compatibility. It only checks locally pinned sources
and identifies hard dependency and sample-configuration blockers.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tomllib

CANDIDATE_KMS_COMMIT = "afcc7e5a48c31f7c3772b1799c8e856c8e3166f1"
CRATES = ("tfhe", "tfhe-zk-pok")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(repo: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", "-C", str(repo), *args], check=True,
        capture_output=True, text=True, timeout=15,
    )
    return completed.stdout.strip()


def lock_versions(lock: Path) -> dict[str, list[str]]:
    data = tomllib.loads(lock.read_text(encoding="utf-8"))
    packages = data.get("package")
    if not isinstance(packages, list):
        raise ValueError(f"missing Cargo.lock package array in {lock}")
    return {
        name: sorted({p["version"] for p in packages if p.get("name") == name})
        for name in CRATES
    }


def verify_committed_file(root: Path, relative: Path) -> str:
    """Read only files tracked *at HEAD* and byte-identical to HEAD.

    Git's nearest-repository behavior and ignored files are not evidence of a
    pinned checkout. Reject both, including symlinks pointing out of the tree.
    """
    name = relative.as_posix()
    if relative.is_absolute() or ".." in relative.parts:
        raise ValueError(f"unsafe source path: {name}")
    path = root / relative
    if not path.is_file() or path.is_symlink() or path.resolve() != path:
        raise ValueError(f"non-regular or missing source: {name}")
    git(root, "ls-files", "--error-unmatch", "--", name)
    committed = subprocess.run(
        ["git", "-C", str(root), "show", "HEAD:" + name],
        check=True, capture_output=True, timeout=15,
    ).stdout
    digest = sha256(path)
    if hashlib.sha256(committed).hexdigest() != digest:
        raise ValueError(f"source does not match HEAD: {name}")
    return digest


def inspect_checkout(root: Path, lock_relative: Path, additional: tuple[Path, ...] = ()) -> dict:
    root = root.resolve(strict=True)
    actual_root = Path(git(root, "rev-parse", "--show-toplevel")).resolve(strict=True)
    if actual_root != root:
        raise ValueError(f"source directory is not Git checkout root: {root}")
    head = git(root, "rev-parse", "HEAD")
    dirty = bool(git(root, "status", "--porcelain", "--untracked-files=normal"))
    verified = {
        path.as_posix(): verify_committed_file(root, path)
        for path in (lock_relative, *additional)
    }
    return {
        "head": head,
        "tracked_dirty": dirty,
        "cargo_lock_sha256": verified[lock_relative.as_posix()],
        "verified_source_digests": verified,
        "crates": lock_versions(root / lock_relative),
    }


def evaluate(tclmesh: dict, kms: dict, expected_kms_commit: str,
             config: dict | None) -> dict:
    blockers: list[str] = []
    if kms["head"] != expected_kms_commit:
        blockers.append("kms_source_head_not_expected_pin")
    if kms["tracked_dirty"]:
        blockers.append("kms_tracked_tree_modified")
    if tclmesh["tracked_dirty"]:
        blockers.append("tclmesh_tracked_tree_modified")
    for name in CRATES:
        left, right = tclmesh["crates"].get(name, []), kms["crates"].get(name, [])
        if name == "tfhe" and (len(left) != 1 or len(right) != 1):
            blockers.append("tfhe_version_not_unique_in_both_lockfiles")
        elif left and right and left != right:
            blockers.append(f"{name}_locked_versions_differ")
    if config is None:
        blockers.append("kms_four_party_config_missing")
    else:
        if config.get("kms_type") != "threshold":
            blockers.append("kms_sample_not_threshold_mode")
        if config.get("num_parties") != 4 or config.get("num_reconstruct") != 3:
            blockers.append("kms_sample_not_three_responses_of_four")
        if config.get("fhe_params") == "Test":
            blockers.append("kms_sample_uses_insecure_test_parameters")
        elif config.get("fhe_params") != "Default":
            blockers.append("kms_sample_parameter_security_unestablished")
    return {
        "status": "BLOCKED" if blockers else "SOURCE_PREFLIGHT_ONLY",
        "blockers": blockers,
        "limits": [
            "No native TFHE/KMS ciphertext or key compatibility established",
            "No distributed key custody or security threshold established",
            "No cryptographic share verification, combination or recipient-release demonstrated",
        ],
        "tclmesh": tclmesh,
        "kms": kms,
        "kms_config": {k: config.get(k) for k in ("kms_type", "num_parties", "num_reconstruct", "num_majority", "fhe_params")} if config else None,
        "expected_kms_commit": expected_kms_commit,
    }


def preflight(tclmesh_root: Path, kms_root: Path, kms_commit: str) -> dict:
    if not re.fullmatch(r"[0-9a-f]{40}", kms_commit):
        raise ValueError("--kms-commit must be a full lowercase 40-digit SHA")
    tclmesh = inspect_checkout(tclmesh_root, Path("backends/tfhe/Cargo.lock"))
    config_relative = Path("core-client/config/client_local_threshold.toml")
    kms = inspect_checkout(kms_root, Path("Cargo.lock"), (config_relative,))
    conf_path = kms_root / config_relative
    config = tomllib.loads(conf_path.read_text(encoding="utf-8")) if conf_path.is_file() else None
    return evaluate(tclmesh, kms, kms_commit, config)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tclmesh-source", type=Path,
                        default=Path(__file__).resolve().parents[1])
    parser.add_argument("--kms-source", type=Path, required=True,
                        help="local, exact-commit Zama KMS checkout")
    parser.add_argument("--kms-commit", default=CANDIDATE_KMS_COMMIT,
                        help="full reviewed KMS commit SHA")
    args = parser.parse_args()
    try:
        report = preflight(args.tclmesh_source, args.kms_source, args.kms_commit)
    except (OSError, ValueError, KeyError, subprocess.SubprocessError, tomllib.TOMLDecodeError) as exc:
        print(json.dumps({"status": "BLOCKED", "blockers": ["source_or_lockfile_unverifiable"],
                          "detail": str(exc)}, sort_keys=True, indent=2))
        return 2
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0 if report["status"] == "SOURCE_PREFLIGHT_ONLY" else 2


if __name__ == "__main__":
    sys.exit(main())
