#!/usr/bin/env python3
"""Deterministically enumerate holder subsets for later *native* threshold testing.

This tool performs NO cryptography. In particular, rejecting a 2-holder
combine at an API boundary does NOT establish IND-style 2-holder privacy.
"""
from __future__ import annotations

import argparse
from itertools import combinations
import json
from math import comb
import sys


def build_plan(participants: int, release_quorum: int, max_cases: int = 4096) -> dict:
    if (type(participants) is not int or type(release_quorum) is not int
            or not 1 <= release_quorum <= participants <= 512):
        raise ValueError("invalid participant count or release quorum (require 1 <= q <= n <= 512)")
    if type(max_cases) is not int or max_cases < 1:
        raise ValueError("case budget must be a positive integer")
    positive_count = comb(participants, release_quorum)
    negative_count = comb(participants, release_quorum - 1)
    if positive_count + negative_count > max_cases:
        raise ValueError("case budget exceeded: reduce n, q, or use a justified sampling protocol")
    holders = [f"holder-{i:03d}" for i in range(participants)]
    positive = [
        {"id": "attempt:" + ",".join(s), "holders": list(s),
         "expected": "decrypt_only_if_native_security_contract_holds"}
        for s in combinations(holders, release_quorum)
    ]
    negative = [
        {"id": "insufficient:" + ",".join(s), "holders": list(s),
         "expected": "cannot_decrypt"}
        for s in combinations(holders, release_quorum - 1)
    ]
    return {
        "schema": "tclmesh.threshold-subset-plan.v1",
        "status": "SELECTION_PLAN_ONLY",
        "participants": participants,
        "release_quorum": release_quorum,
        "holders": holders,
        "counts": {"reconstruct_attempts": positive_count,
                   "insufficient_coalitions": negative_count},
        "cases": {"reconstruct_attempts": positive,
                  "insufficient_coalitions": negative},
        "cryptographic_tests_executed": False,
        "cryptographic_release_admitted": False,
        "limits": [
            "A subset matrix is not a cryptographic proof of secrecy or correctness",
            "A refusal to combine a partial coalition is not proof that its shares leak no plaintext",
            "Success requires immutable keyset, real distributed custody, security-profile-specific verification",
            "Offline/malicious behavior, ciphertext correctness, replay, and recipient delivery remain untested",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--participants", type=int, required=True)
    parser.add_argument("--release-quorum", type=int, required=True)
    parser.add_argument("--max-cases", type=int, default=4096)
    args = parser.parse_args()
    try:
        report = build_plan(args.participants, args.release_quorum, args.max_cases)
    except ValueError as err:
        print(json.dumps({"status": "PLAN_REJECTED", "cryptographic_release_admitted": False,
                          "error": str(err)}, sort_keys=True))
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
