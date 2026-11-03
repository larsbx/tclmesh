"""Non-cryptographic regression tests: source evidence must never enable release."""

from pathlib import Path
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "threshold_ajax_preflight.py"
SPEC = importlib.util.spec_from_file_location("threshold_ajax_preflight", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def run(*args):
    return subprocess.run(args, capture_output=True, text=True, check=True).stdout.strip()


class AjaxSourceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name) / "ajax"
        self.repo.mkdir()
        run("git", "-C", str(self.repo), "init", "-q")
        files = {
            "README.md": "# Synthetic test source, not upstream Ajax\n",
            "thfhe/Cargo.toml": '[dependencies]\nalgebra = { git = "https://github.com/serendipity-crypto/primus-fhe", branch = "ajax" }\nlattice = { git = "https://github.com/serendipity-crypto/primus-fhe", branch = "ajax" }\nfhe_core = { git = "https://github.com/serendipity-crypto/primus-fhe", branch = "ajax" }\n',
            "thfhe/examples/thfhe.rs": "if party_id <= threshold { run_decrypt(); }\n",
            "thfhe/src/distdec.rs": "if backend.party_id() == 0 { return_result(); }\n",
            "mpc/src/dn.rs": "//! DN07 requires n > 2t\n",
        }
        for name, content in files.items():
            path = self.repo / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
        run("git", "-C", str(self.repo), "add", ".")
        self.commit()

    def commit(self):
        run("git", "-C", str(self.repo), "-c", "user.name=Test",
            "-c", "user.email=test@example.invalid", "commit", "-qm", "test fixture")
        self.head = run("git", "-C", str(self.repo), "rev-parse", "HEAD")

    def test_positive_source_review_is_not_release_acceptance(self):
        result = MODULE.assess(self.repo, self.head)
        self.assertEqual(result["status"], "SOURCE_REVIEW_ONLY")
        self.assertFalse(result["cryptographic_release_admitted"])
        self.assertEqual(result["illustrative_paper_profile"]["q_release_claimed"], 3)
        self.assertIn("active_malicious_share_verification_not_established", result["blockers"])

    def test_missing_lock_and_floating_git_dependencies_flagged(self):
        blockers = MODULE.assess(self.repo, self.head)["blockers"]
        self.assertIn("tracked_Cargo_lock_absent", blockers)
        self.assertIn("primus_fhe_git_branches_not_revision_pinned_in_manifest", blockers)

    def test_fixed_subset_and_output_to_party_zero_are_not_accepted(self):
        result = MODULE.assess(self.repo, self.head)
        self.assertIn("demonstration_only_uses_first_threshold_plus_one_holders", result["blockers"])
        self.assertIn("plaintext_returned_to_party_zero_in_demo_protocol", result["blockers"])

    def test_wrong_git_pin_is_rejected(self):
        with self.assertRaisesRegex(ValueError, "exact audited pin"):
            MODULE.assess(self.repo, "f" * 40)

    def test_modified_tracked_file_is_rejected(self):
        (self.repo / "thfhe/src/distdec.rs").write_text("// different\n")
        with self.assertRaisesRegex(ValueError, "modified"):
            MODULE.assess(self.repo, self.head)

    def test_untracked_fake_lock_is_rejected(self):
        (self.repo / "Cargo.lock").write_text("# fake\n")
        with self.assertRaisesRegex(ValueError, "untracked"):
            MODULE.assess(self.repo, self.head)

    def test_missing_source_is_rejected(self):
        (self.repo / "thfhe/src/distdec.rs").unlink()
        with self.assertRaisesRegex(ValueError, "modified"):
            MODULE.assess(self.repo, self.head)

    def test_source_success_require_release_still_exit_two(self):
        cmd = [sys.executable, str(SCRIPT), "--source", str(self.repo),
               "--expected-commit", self.head]
        source = subprocess.run(cmd, capture_output=True, text=True)
        self.assertEqual(source.returncode, 0, source.stderr)
        self.assertEqual(json.loads(source.stdout)["status"], "SOURCE_REVIEW_ONLY")
        release = subprocess.run(cmd + ["--require-release"], capture_output=True, text=True)
        self.assertEqual(release.returncode, 2)
        self.assertFalse(json.loads(release.stdout)["cryptographic_release_admitted"])


if __name__ == "__main__":
    unittest.main()
