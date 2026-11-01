#!/usr/bin/env python3
"""Issue #36: *necessary-only* numerical audit of a claimed threshold profile.

This tool cannot authorize a cryptographic release. Its inputs are untrusted
claims, NOT authenticated security proofs or evidence of a native backend.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass


@dataclass(frozen=True)
class Claim:
    parties: int
    release_quorum: int
    privacy_corruptions: int
    byzantine_faults: int
    client_responses: int


def assess(claim: Claim) -> dict:
    errors: list[str] = []
    raw = vars(claim)
    if any(type(v) is not int for v in raw.values()):
        errors.append("integer_fields_required")
    elif claim.parties < 1:
        errors.append("nonpositive_party_count")
    else:
        if not 1 <= claim.release_quorum <= claim.parties:
            errors.append("release_quorum_out_of_range")
        if not 0 <= claim.privacy_corruptions < claim.parties:
            errors.append("privacy_corruption_bound_out_of_range")
        if not 0 <= claim.byzantine_faults < claim.parties:
            errors.append("byzantine_fault_bound_out_of_range")
        if not 1 <= claim.client_responses <= claim.parties:
            errors.append("response_count_out_of_range")
        if 1 <= claim.release_quorum <= claim.parties:
            # If up to q-1 holders can recover (or are outside the claimed
            # privacy bound), the advertised q-of-n secrecy has no proof.
            if claim.privacy_corruptions < claim.release_quorum - 1:
                errors.append("privacy_bound_below_release_quorum_minus_one")
            if claim.client_responses > claim.release_quorum:
                errors.append("requires_more_responses_than_policy_quorum")

    return {
        "status": "CLAIMS_REJECTED" if errors else "NECESSARY_CHECKS_ONLY",
        "blockers": errors,
        "claim": raw,
        "production_cryptographic_release_enabled": False,
        "unverified_obligations": [
            "source_and_binary_provenance",
            "proof_of_claimed_privacy_and_corruption_bounds",
            "every_authorized_q_subset_can_reconstruct",
            "independently_held_key_shares_no_evaluator_full_key",
            "authenticated_partial_verification_and_combination",
            "recipient_bound_delivery_and_atomic_replay_protection",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parties", type=int, required=True)
    parser.add_argument("--release-quorum", type=int, required=True)
    parser.add_argument("--privacy-corruptions", type=int, required=True)
    parser.add_argument("--byzantine-faults", type=int, required=True)
    parser.add_argument("--client-responses", type=int, required=True)
    args = parser.parse_args()
    report = assess(Claim(**vars(args)))
    print(json.dumps(report, sort_keys=True, indent=2))
    # Exit 0 means that NO OBVIOUS NUMERICAL CONTRADICTION was found.
    # It must never be treated as cryptographic, custody or output proof.
    return 2 if report["blockers"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
