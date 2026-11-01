"""Finite, synthetic checks: these do NOT validate any cryptographic scheme."""

import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "check_threshold_security_claims.py"
SPEC = importlib.util.spec_from_file_location("check_threshold_security_claims", SCRIPT)
M = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = M
SPEC.loader.exec_module(M)


class ThresholdClaimDiagnosticsTests(unittest.TestCase):
    def claim(self, n=4, q=3, privacy=1, faults=1, responses=3):
        return M.Claim(n, q, privacy, faults, responses)

    def test_documented_four_party_kms_example_cannot_certify_three_of_four(self):
        x = M.assess(self.claim())
        self.assertEqual(x["status"], "CLAIMS_REJECTED")
        self.assertIn("privacy_bound_below_release_quorum_minus_one", x["blockers"])
        self.assertFalse(x["production_cryptographic_release_enabled"])

    def test_three_responses_not_privacy_certificate(self):
        x = M.assess(self.claim(responses=3))
        self.assertEqual(x["status"], "CLAIMS_REJECTED")

    def test_two_responses_not_privacy_certificate_either(self):
        x = M.assess(self.claim(responses=2))
        self.assertEqual(x["status"], "CLAIMS_REJECTED")

    def test_conditional_numbers_are_not_cryptographic_acceptance(self):
        x = M.assess(self.claim(privacy=2))
        self.assertEqual(x["status"], "NECESSARY_CHECKS_ONLY")
        self.assertFalse(x["production_cryptographic_release_enabled"])
        self.assertIn("every_authorized_q_subset_can_reconstruct",
                      x["unverified_obligations"])

    def test_kms_sample_is_not_compatible_with_any_four_party_quorum(self):
        # With r_output=3 the release quorum must be >=3, but with
        # f_priv=1 the claimed secrecy threshold can be at most 2.
        # Thus no q in [1,4] satisfies both necessary conditions.
        for q in range(1, 5):
            with self.subTest(quorum=q):
                x = M.assess(self.claim(q=q))
                self.assertEqual(x["status"], "CLAIMS_REJECTED")

    def test_response_count_above_policy_quorum_is_rejected(self):
        x = M.assess(self.claim(privacy=2, responses=4))
        self.assertIn("requires_more_responses_than_policy_quorum", x["blockers"])

    def test_invalid_policy_and_parameter_bounds_are_rejected(self):
        for claim in [
            self.claim(n=0), self.claim(q=0), self.claim(q=5),
            self.claim(privacy=-1), self.claim(privacy=4),
            self.claim(faults=-1), self.claim(faults=4),
            self.claim(responses=0), self.claim(responses=5),
        ]:
            with self.subTest(claim=claim):
                self.assertEqual(M.assess(claim)["status"], "CLAIMS_REJECTED")

    def test_boolean_or_float_claims_are_rejected(self):
        for claim in [self.claim(privacy=True), self.claim(q=3.0)]:
            with self.subTest(claim=claim):
                self.assertIn("integer_fields_required", M.assess(claim)["blockers"])

    def test_fault_budget_is_not_substituted_for_privacy(self):
        for faults in (0, 1, 2, 3):
            self.assertIn("privacy_bound_below_release_quorum_minus_one",
                          M.assess(self.claim(faults=faults))["blockers"])

    def test_other_quorums_not_hardcoded_to_three(self):
        x = M.assess(self.claim(n=5, q=4, privacy=3, faults=1, responses=4))
        self.assertEqual(x["status"], "NECESSARY_CHECKS_ONLY")

    def test_cli_exit_code_and_json_keep_boundary(self):
        base = [sys.executable, str(SCRIPT), "--parties", "4",
                "--release-quorum", "3", "--byzantine-faults", "1",
                "--client-responses", "3"]
        bad = subprocess.run(base + ["--privacy-corruptions", "1"],
                             capture_output=True, text=True, check=False)
        self.assertEqual(bad.returncode, 2)
        self.assertEqual(json.loads(bad.stdout)["status"], "CLAIMS_REJECTED")
        possible = subprocess.run(base + ["--privacy-corruptions", "2"],
                                  capture_output=True, text=True, check=False)
        self.assertEqual(possible.returncode, 0)
        output = json.loads(possible.stdout)
        self.assertEqual(output["status"], "NECESSARY_CHECKS_ONLY")
        self.assertFalse(output["production_cryptographic_release_enabled"])


if __name__ == "__main__":
    unittest.main()
