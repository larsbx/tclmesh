#!/usr/bin/env python3
"""Source-only comparison of two historical threshold-FHE variants.

NO FHE is performed. A SOURCE_VARIANT_DIFFERENT report is a versioning blocker,
not a proof that either version is malicious, unsafe, or functionally equivalent.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tomllib

AJAX_REPO = "primus-labs/Ajax"
AJAX_COMMIT = "64b4f80fb90da3096e03af200d3c95abe865a987"
ALT_REPO = "primus-labs/primus-fhe"
ALT_COMMIT = "a0d075d9ec055fb8652925fee65768a14a627cfa"

# Values observed via the GitHub Git blob API at the exact commits above.
# Presence of the same source in two projects is not protocol equivalence.
BLOBS = {
    "thfhe/src/distdec.rs": (
        "5925f3a72bda07469455839d73e9f190a9dffaa9",
        "d8c5086ce58e2c869742cc77dd525ae93715053b",
    ),
    "thfhe/src/key_gen.rs": (
        "07b90b774de6ba3185886fd02961da6c749e255c",
        "a1b41a0cfb94921f283bbac77a44f3c1754eae56",
    ),
    "thfhe/src/secret_key.rs": (
        "6074e6ffe0c695878c9654188dcba554d1f7026e",
        "675d678efc61db78ba5e576e66d2ff2c89c73f55",
    ),
    "thfhe/examples/thfhe.rs": (
        "aaf545b0f8b499804f72c6fbef478b4d2f3e1ddc",
        "a27df6b1f53d2ab0148f2ff5d5c7cec6b8ccc754",
    ),
    "mpc/src/dn.rs": (
        "275ff6b11180d7e85975f654aed316ee4a46c5db",
        "da2e4457a9f7d8f434815d8645c4b4b1b8c0eded",
    ),
    "thfhe/Cargo.toml": (
        "1c9923ebd1a0bb191969ba1159bc9a0dde8f142c",
        "9060018b4e654dd42b43cc113dc6f4024b525bc6",
    ),
    "thfhe/src/lib.rs": (
        "30d8e8fabeae835054eec02e424d2ce7e973112f",
        "30d8e8fabeae835054eec02e424d2ce7e973112f",
    ),
}
ADDITIONAL_ALT = ("algebra/Cargo.toml", "fhe_core/Cargo.toml",
                  "lattice/Cargo.toml", "Cargo.toml")


def git(repo: Path, *args: str, input_bytes: bytes | None = None) -> bytes:
    return subprocess.run(
        ["git", "--no-replace-objects", "-C", str(repo), *args],
        input=input_bytes, check=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, timeout=30,
    ).stdout.strip()


def inspect_checkout(path: Path, expected_commit: str,
                     expected_blobs: dict[str, str]) -> dict:
    """Git provenance check. Public fixture helpers can use synthetic hashes."""
    if path.is_symlink():
        raise ValueError("symlinked source checkout forbidden")
    root = path.resolve(strict=True)
    if not root.is_dir():
        raise ValueError("not a source directory")
    top = Path(git(root, "rev-parse", "--show-toplevel").decode()).resolve()
    if top != root:
        raise ValueError("source path is not the checkout root")
    head = git(root, "rev-parse", "HEAD").decode()
    if head != expected_commit or len(head) != 40:
        raise ValueError("checkout does not match pinned HEAD")
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError("modified or untracked files in source checkout")
    tracked = set(git(root, "ls-tree", "-r", "--name-only", "HEAD").decode().splitlines())
    evidence = {}
    for rel, expected in expected_blobs.items():
        if rel not in tracked:
            raise ValueError("missing tracked source: " + rel)
        file = root / rel
        if not file.is_file() or file.is_symlink():
            raise ValueError("missing, non-regular or symlinked source: " + rel)
        actual_bytes = git(root, "show", "HEAD:" + rel, input_bytes=None)
        if file.read_bytes().rstrip(b"\n") != actual_bytes:
            # Above git() strips subprocess output; compare exact bytes below instead.
            # (Do not trust this preliminary match for raw files.)
            pass
        raw = subprocess.run(
            ["git", "--no-replace-objects", "-C", str(root), "show", "HEAD:" + rel],
            check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=30,
        ).stdout
        if raw != file.read_bytes():
            raise ValueError("working source differs from HEAD: " + rel)
        object_sha = git(root, "hash-object", "--stdin", input_bytes=raw).decode()
        if object_sha != expected:
            raise ValueError("unexpected pinned Git blob: " + rel)
        evidence[rel] = {
            "blob": object_sha,
            "sha256": hashlib.sha256(raw).hexdigest(),
        }
    return {
        "head": head, "tree": git(root, "rev-parse", "HEAD^{tree}").decode(),
        "tracked_count": len(tracked), "has_tracked_lock": "Cargo.lock" in tracked,
        "selected": evidence,
    }


def audit(ajax: Path, alternative: Path) -> dict:
    a = inspect_checkout(ajax, AJAX_COMMIT, {p: v[0] for p, v in BLOBS.items()})
    b = inspect_checkout(
        alternative, ALT_COMMIT,
        {**{p: v[1] for p, v in BLOBS.items()},
         **{p: _expected_blob(alternative, p) for p in ADDITIONAL_ALT}},
    )
    # The extra source blobs are bound by the exact alternate commit; their
    # source identity is read and measured, never guessed from floating refs.
    a_keygen = (ajax / "thfhe/src/key_gen.rs").read_text(encoding="utf-8")
    b_keygen = (alternative / "thfhe/src/key_gen.rs").read_text(encoding="utf-8")
    a_dec = (ajax / "thfhe/src/distdec.rs").read_text(encoding="utf-8")
    b_dec = (alternative / "thfhe/src/distdec.rs").read_text(encoding="utf-8")
    a_dep = tomllib.loads((ajax / "thfhe/Cargo.toml").read_text(encoding="utf-8"))
    b_dep = tomllib.loads((alternative / "thfhe/Cargo.toml").read_text(encoding="utf-8"))
    alt_alg = tomllib.loads((alternative / "algebra/Cargo.toml").read_text(encoding="utf-8"))
    old_manifest = a_dep.get("dependencies", {})
    new_manifest = b_dep.get("dependencies", {})
    old_git_deps = sorted(
        k for k in ("algebra", "lattice", "fhe_core")
        if isinstance(old_manifest.get(k), dict)
        and old_manifest[k].get("branch") == "ajax"
        and not old_manifest[k].get("rev")
    )
    alt_path_deps = sorted(
        k for k in ("algebra", "lattice", "fhe_core")
        if isinstance(new_manifest.get(k), dict)
        and new_manifest[k].get("path") == "../" + k
    )
    concrete = alt_alg.get("dependencies", {}).get("concrete-ntt", {})
    differences = {
        "source_blobs_differ": sorted(p for p, ids in BLOBS.items()
                                      if ids[0] != ids[1]),
        "identical_source_blobs": sorted(p for p, ids in BLOBS.items()
                                          if ids[0] == ids[1]),
        "ajax_imports_unresolved_git_ajax_branch": old_git_deps,
        "alternative_replaces_git_imports_with_workspace_paths": alt_path_deps,
        "old_keygen_noise_div_count": "noise_distribution_div_count(" in a_keygen,
        "alternative_keygen_noise_multi_party": "noise_distribution_multi_party(" in b_keygen,
        "old_decryption_opens_masked_intermediate_to_party_zero":
            "reveal_slice_z2k(&res_vec, 0, 64)" in a_dec,
        "alternative_decryption_opens_masked_intermediate_to_all":
            "reveal_slice_to_all_z2k(&res_vec, 64, true)" in b_dec,
        "alternative_concrete_ntt_floating_branch":
            concrete.get("branch") == "dev" and not concrete.get("rev"),
    }
    if len(differences["source_blobs_differ"]) < 1:
        raise ValueError("unexpected identical variant: re-review source classification")
    if len(old_git_deps) != 3 or len(alt_path_deps) != 3:
        raise ValueError("expected import topology not present")
    if not all(differences[k] is True for k in (
        "old_keygen_noise_div_count", "alternative_keygen_noise_multi_party",
        "old_decryption_opens_masked_intermediate_to_party_zero",
        "alternative_decryption_opens_masked_intermediate_to_all",
        "alternative_concrete_ntt_floating_branch",
    )):
        raise ValueError("expected semantics-relevant source difference not observed")
    return {
        "schema": "tclmesh.ajax-version-variant-audit.v1",
        "status": "SOURCE_VARIANTS_DIFFER_REVIEW_REQUIRED",
        "source": {"repository": AJAX_REPO, **a},
        "alternative": {"repository": ALT_REPO, **b},
        "differences": differences,
        "cryptographic_tests_executed": False,
        "cryptographic_release_admitted": False,
        "candidate_dependency_equivalence_established": False,
        "candidate_security_equivalence_established": False,
        "next": [
            "Authenticate historical primus-fhe/ajax revision or label alternate as a modified overlay",
            "Pin concrete-ntt and Cargo registry dependencies in an audited lockfile",
            "Compare noise parameter semantics and masked-intermediate visibility before compilation",
            "Separate semi-honest native success from malicious/recipient-aware acceptance",
        ],
    }


def _expected_blob(root: Path, rel: str) -> str:
    """Obtain *only* from committed HEAD; provenance remains bound to ALT_COMMIT."""
    # The actual source file contents are checked against HEAD in inspect_checkout.
    if root.is_symlink():
        raise ValueError("symlinked checkout not allowed")
    return git(root, "rev-parse", f"HEAD:{rel}").decode()


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--ajax", type=Path, required=True)
    p.add_argument("--alternative", type=Path, required=True)
    p.add_argument("--require-equivalence", action="store_true")
    p.add_argument("--require-cryptographic-release", action="store_true")
    args = p.parse_args()
    try:
        result = audit(args.ajax, args.alternative)
    except (OSError, ValueError, UnicodeError, subprocess.SubprocessError,
            tomllib.TOMLDecodeError) as exc:
        print(json.dumps({"status": "SOURCE_INVALID", "error": str(exc),
                          "cryptographic_release_admitted": False}, sort_keys=True))
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.require_equivalence or args.require_cryptographic_release:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
