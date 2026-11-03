"""Pure combinatorial subset-selection controls; never a cryptographic test."""
import importlib.util
import itertools
import json
import subprocess
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "threshold_subset_plan.py"
SPEC = importlib.util.spec_from_file_location("threshold_subset_plan", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class SubsetPlanTests(unittest.TestCase):
    def test_any_three_of_five_has_ten_distinct_success_candidates(self):
        plan = MODULE.build_plan(5, 3)
        subsets = plan["cases"]["reconstruct_attempts"]
        self.assertEqual(len(subsets), 10)
        self.assertEqual({tuple(case["holders"]) for case in subsets},
                         set(itertools.combinations(plan["holders"], 3)))
        self.assertEqual(len({case["id"] for case in subsets}), 10)

    def test_any_three_of_five_rejects_every_pair(self):
        plan = MODULE.build_plan(5, 3)
        insufficient = plan["cases"]["insufficient_coalitions"]
        self.assertEqual(len(insufficient), 10)
        self.assertEqual({tuple(case["holders"]) for case in insufficient},
                         set(itertools.combinations(plan["holders"], 2)))
        self.assertTrue(all(case["expected"] == "cannot_decrypt" for case in insufficient))

    def test_three_of_four_is_four_triples_and_six_pairs(self):
        p = MODULE.build_plan(4, 3)
        self.assertEqual(p["counts"], {"reconstruct_attempts": 4, "insufficient_coalitions": 6})

    def test_threshold_one_includes_empty_insufficient_coalition(self):
        p = MODULE.build_plan(2, 1)
        self.assertEqual(p["cases"]["insufficient_coalitions"][0]["holders"], [])

    def test_numerically_valid_plan_never_proves_privacy_or_correctness(self):
        p = MODULE.build_plan(5, 3)
        self.assertEqual(p["status"], "SELECTION_PLAN_ONLY")
        self.assertFalse(p["cryptographic_release_admitted"])
        self.assertFalse(p["cryptographic_tests_executed"])
        self.assertIn("not", p["limits"][0].lower())

    def test_invalid_participant_counts_rejected(self):
        for n, q in [(0, 1), (3, 0), (3, 4), (-1, 1), (True, 1), (5, True)]:
            with self.subTest(n=n, q=q), self.assertRaises(ValueError):
                MODULE.build_plan(n, q)

    def test_combinatorial_budget_protects_large_groups(self):
        with self.assertRaisesRegex(ValueError, "case budget"):
            MODULE.build_plan(512, 256, max_cases=1024)

    def test_order_and_json_deterministic(self):
        a = json.dumps(MODULE.build_plan(5, 3), sort_keys=True)
        b = json.dumps(MODULE.build_plan(5, 3), sort_keys=True)
        self.assertEqual(a, b)

    def test_cli_planner_never_runs_or_enables_crypto(self):
        c = subprocess.run([sys.executable, str(SCRIPT), "--participants", "5",
                            "--release-quorum", "3"], capture_output=True, text=True)
        self.assertEqual(c.returncode, 0, c.stderr)
        data = json.loads(c.stdout)
        self.assertEqual(data["counts"]["reconstruct_attempts"], 10)
        self.assertFalse(data["cryptographic_release_admitted"])

    def test_cli_rejects_large_matrix(self):
        c = subprocess.run([sys.executable, str(SCRIPT), "--participants", "512",
                            "--release-quorum", "256"], capture_output=True, text=True)
        self.assertEqual(c.returncode, 2)
        data = json.loads(c.stdout)
        self.assertFalse(data["cryptographic_release_admitted"])
        self.assertEqual(data["status"], "PLAN_REJECTED")


if __name__ == "__main__":
    unittest.main()
