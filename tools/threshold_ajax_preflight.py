#!/usr/bin/env python3
"""Fail-closed source-only Ajax research preflight for TclMesh #36/#45.

A successful source review is never a threshold cryptographic acceptance result.
No network access, secret key import, decryption, or runtime capability changes.
"""

from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tomllib

PIN = "64b4f80fb90da3096e03af200d3c95abe865a987"
REQUIRED = (
    "README.md", "thfhe/Cargo.toml", "thfhe/examples/thfhe.rs",
    "thfhe/src/distdec.rs", "mpc/src/dn.rs",
)


def git(repo: Path, *args: str) -> bytes:
    return subprocess.run(
        ["git", "--no-replace-objects", "-C", str(repo), *args],
        check=True, capture_output=True, timeout=15,
    ).stdout


def assess(repo: Path, expected: str = PIN) -> dict:
    """Check tracked source identities and report only *negative* source observations."""
    repo = repo.resolve(strict=True)
    if not repo.is_dir() or repo.is_symlink():
        raise ValueError("source is not a real directory")
    root = Path(git(repo, "rev-parse", "--show-toplevel").decode().strip()).resolve()
    if root != repo:
        raise ValueError("source must be a git checkout root")
    head = git(repo, "rev-parse", "HEAD").decode().strip()
    if head != expected or len(expected) != 40:
        raise ValueError("source HEAD does not match exact audited pin")
    if git(repo, "status", "--porcelain", "--untracked-files=all").strip():
        raise ValueError("source checkout is modified or has untracked files")

    tracked = set(git(repo, "ls-tree", "-r", "--name-only", "HEAD").decode().splitlines())
    verified = {}
    for name in REQUIRED:
        if name not in tracked:
            raise ValueError("missing required tracked source: " + name)
        path = repo / name
        if path.is_symlink() or not path.is_file():
            raise ValueError("invalid tracked source type: " + name)
        committed = git(repo, "show", "HEAD:" + name)
        if path.read_bytes() != committed:
            raise ValueError("working source differs from committed bytes: " + name)
        verified[name] = committed.decode("utf-8")

    deps = tomllib.loads(verified["thfhe/Cargo.toml"]).get("dependencies", {})
    primus = [
        name for name in ("algebra", "lattice", "fhe_core")
        if isinstance(deps.get(name), dict)
        and "primus-fhe" in deps[name].get("git", "")
        and deps[name].get("branch") == "ajax"
        and not deps[name].get("rev")
    ]
    sample = verified["thfhe/examples/thfhe.rs"]
    distdec = verified["thfhe/src/distdec.rs"]
    mpc = verified["mpc/src/dn.rs"]
    blockers = [
        "active_malicious_share_verification_not_established",
        "tclmesh_tfhe_rs_1_8_2_compatibility_not_established",
        "independently_reproduced_any_subset_decryption_absent",
        "recipient_only_authentication_and_delivery_unestablished",
        "distributed_key_custody_and_epoch_fencing_unestablished",
    ]
    observations = []
    if "Cargo.lock" not in tracked:
        blockers.append("tracked_Cargo_lock_absent")
        observations.append("no_Cargo_lock_at_exact_pin")
    if primus:
        blockers.append("primus_fhe_git_branches_not_revision_pinned_in_manifest")
        observations.append("floating_manifest_git_branch_dependencies:" + ",".join(primus))
    if "if party_id <= threshold" in sample:
        blockers.append("demonstration_only_uses_first_threshold_plus_one_holders")
        observations.append("fixed_first_subset_in_example_not_protocol_proof")
    if "if backend.party_id() == 0" in distdec:
        blockers.append("plaintext_returned_to_party_zero_in_demo_protocol")
        observations.append("decryption_result_local_to_party_zero_not_authenticated_recipient")
    if "n > 2t" in mpc:
        observations.append("DN_backend_documented_honest_majority_privacy")
    return {
        "schema": "tclmesh.threshold-ajax-preflight.v1",
        "source": "primus-labs/Ajax", "pin": head,
        "status": "SOURCE_REVIEW_ONLY", "cryptographic_release_admitted": False,
        "illustrative_paper_profile": {
            "n": 5, "f_priv_semi_honest_claimed": 2, "q_release_claimed": 3,
            "active_malicious_security_verified": False,
            "note": "Any-3-of-5 is a paper-level semi-honest profile, not an accepted runtime configuration",
        },
        "verified_source_paths": sorted(verified),
        "observations": observations,
        "blockers": blockers,
        "limits": [
            "Source inspection only; no native cryptography or full dependency build",
            "Paper's main-body protocols are semi-honest; active extension not verified",
            "No per-share correctness proof, transcript verification, DKG custody, or recipient release accepted",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True, type=Path)
    parser.add_argument("--require-release", action="store_true")
    parser.add_argument("--expected-commit", default=PIN, help="source-only evaluation; never enables release")
    args = parser.parse_args()
    try:
        report = assess(args.source, args.expected_commit)
    except (ValueError, OSError, UnicodeDecodeError, subprocess.SubprocessError, tomllib.TOMLDecodeError) as err:
        print(json.dumps({"status": "SOURCE_INVALID", "cryptographic_release_admitted": False,
                          "error": str(err)}, sort_keys=True))
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 2 if args.require_release else 0


if __name__ == "__main__":
    sys.exit(main())
