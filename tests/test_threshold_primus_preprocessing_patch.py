"""Red-first source-transform and deny-only tests; no native FHE is executed."""

from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parents[1] / "tools"
TOOL = TOOLS / "threshold_primus_preprocessing_patch.py"
sys.path.insert(0, str(TOOLS))
import threshold_primus_preprocessing_patch as P  # noqa: E402
import threshold_primus_opening_harness as H  # noqa: E402


class PreprocessingPatchTests(unittest.TestCase):
    def setUp(self):
        self.source = P.TEST_SOURCE_FIXTURE

    def test_patch_fails_closed_on_zero_triple_underflow(self):
        patched = P.rewrite_source(self.source)
        self.assertNotIn("return (0, 0, 0);", patched)
        self.assertIn("take_z2k_triple_checked(&mut self.triplez2k_buffer)", patched)
        self.assertIn("pop_front().expect(", patched)

    def test_patch_checks_batch_before_any_mask_or_open(self):
        patched = P.rewrite_source(self.source)
        guard = patched.index("require_z2k_triples_available(self.triplez2k_buffer.len(), batch_size)")
        triple = patched.index("(0..batch_size).map(|_| self.next_triple_z2k())")
        masked = patched.index("let masked_values: Vec<u64> =")
        opened = patched.index(".open_secrets_z2k(0, self.num_threshold, &masked_values, true)")
        self.assertLess(guard, triple)
        self.assertLess(triple, masked)
        self.assertLess(masked, opened)

    def test_loader_is_strict_and_atomic(self):
        patched = P.rewrite_source(self.source)
        self.assertIn("parse_z2k_triple_file(&content)", patched)
        self.assertIn("self.triplez2k_buffer.extend(parsed);", patched)
        self.assertNotIn("filter_map(|v| u128::from_str(v).ok())", patched)
        self.assertIn("u128", patched)
        self.assertIn("as u64", patched)

    def test_native_unit_tests_injected(self):
        patched = P.rewrite_source(self.source)
        self.assertIn("fn rejects_empty_triple_file()", patched)
        self.assertIn("fn detects_exhaustion_before_masking()", patched)
        self.assertIn("fn accepts_128_bit_file_values_with_original_cast_semantics()", patched)
        self.assertIn("fn rejects_missing_preprocessing_file()", patched)
        self.assertIn("fn rejects_incomplete_preprocessing_file()", patched)
        self.assertIn("read_and_parse_z2k_triple_file(filename)", patched)

    def test_patch_rejects_missing_underflow_signature(self):
        with self.assertRaisesRegex(ValueError, "old triple"):
            P.rewrite_source(self.source.replace("return (0, 0, 0);", "panic!(\"changed\");"))

    def test_patch_rejects_duplicate_ambiguous_signatures(self):
        with self.assertRaisesRegex(ValueError, "unique"):
            P.rewrite_source(self.source + P.OLD_NEXT_TRIPLE)

    def test_patch_rejects_modified_loader(self):
        with self.assertRaisesRegex(ValueError, "unique"):
            P.rewrite_source(self.source.replace("if values.len() == 3 {", "if values.len() != 3 {"))

    def test_patch_rejects_reapplication(self):
        patched = P.rewrite_source(self.source)
        with self.assertRaises(ValueError):
            P.rewrite_source(patched)

    def test_candidate_assessment_is_never_cryptographic_acceptance(self):
        report = P.assess_patch(self.source, P.rewrite_source(self.source))
        self.assertEqual(report["status"], "MODIFIED_OVERLAY_SOURCE_PATCH_ONLY")
        self.assertFalse(report["cryptographic_release_admitted"])
        self.assertFalse(report["native_tests_executed"])
        self.assertFalse(report["malicious_security_established"])

    def test_cli_rejects_nonpinned_source_directory(self):
        with tempfile.TemporaryDirectory() as d:
            proc = subprocess.run([sys.executable, str(TOOL), "--source", d],
                                  capture_output=True, text=True)
            self.assertEqual(proc.returncode, 2)
            self.assertFalse(json.loads(proc.stdout)["cryptographic_release_admitted"])

    def test_cli_cannot_authorize_crypto(self):
        with tempfile.TemporaryDirectory() as d:
            proc = subprocess.run([sys.executable, str(TOOL),
                                   "--source", d, "--require-release"],
                                  capture_output=True, text=True)
            self.assertEqual(proc.returncode, 2)
            self.assertFalse(json.loads(proc.stdout)["cryptographic_release_admitted"])


class OpeningOracleTests(unittest.TestCase):
    """The probe oracle must match what the overlay actually panics with."""

    def setUp(self):
        self.patched = P.rewrite_source(P.TEST_SOURCE_FIXTURE)
        self.probes = {v: H.render(self.patched, m) for v, m in H.VARIANTS.items()}

    def test_every_oracle_prefix_is_emitted_by_the_overlay(self):
        for name, scenario in H.SCENARIOS.items():
            if scenario.panic:
                self.assertIn(f'"{scenario.panic}', self.patched, name)

    def test_loader_distinguishes_unreadable_from_malformed(self):
        loader = H.method(self.patched, "pub fn read_z2k_triples_from_files(")
        self.assertIn("ErrorKind::InvalidData", loader)
        self.assertIn(P.UNREADABLE_FILE, loader)
        self.assertIn(P.MALFORMED_FILE, loader)

    def test_rendered_oracle_is_the_scenario_table(self):
        for name, scenario in H.SCENARIOS.items():
            arm = f'"{name}" => ("{scenario.panic or ""}", {scenario.remaining}),'
            self.assertIn(arm, self.probes["fixed"])

    def test_matrix_covers_every_scenario_and_both_exhaustion_mutants(self):
        cells = H.matrix()
        self.assertEqual({s for v, s in cells if v == "fixed"}, set(H.SCENARIOS))
        self.assertEqual({s for v, s in cells if v == "zero-fallback"}, set(H.EXHAUSTION))
        self.assertIn("multiparty-shortage", H.EXHAUSTION)

    def test_render_rejects_source_without_overlay(self):
        with self.assertRaises(ValueError):
            H.render(P.TEST_SOURCE_FIXTURE)

    @unittest.skipUnless(shutil.which("rustc"), "rustc unavailable")
    def test_native_matrix_passes_and_mutants_leak(self):
        with tempfile.TemporaryDirectory() as d:
            report = H.run_matrix(self.probes, Path(d))
        self.assertTrue(report["ok"], json.dumps(report["results"], indent=1))
        self.assertFalse(report["cryptographic_release_admitted"])

    @unittest.skipUnless(shutil.which("rustc"), "rustc unavailable")
    def test_native_oracle_rejects_a_drifted_panic_message(self):
        # Regression for the PR #50 stale oracle: if the loader's message drifts
        # from the oracle, the matrix must fail instead of passing silently.
        drifted = dict(self.probes, fixed=self.probes["fixed"].replace(
            f'panic!("{P.UNREADABLE_FILE}', 'panic!("Missing, malformed, or empty', 1))
        self.assertNotEqual(drifted["fixed"], self.probes["fixed"])
        with tempfile.TemporaryDirectory() as d:
            report = H.run_matrix(drifted, Path(d))
        failed = {(r["variant"], r["scenario"], r["exit"]) for r in report["results"] if not r["ok"]}
        self.assertEqual(failed, {("fixed", "missing", 51)})


if __name__ == "__main__":
    unittest.main()
