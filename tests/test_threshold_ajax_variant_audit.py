"""Synthetic Git fixtures for exact-source variant audit. No cryptography executed."""

from pathlib import Path
import importlib.util
from unittest import mock
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "threshold_ajax_variant_audit.py"
SPEC = importlib.util.spec_from_file_location("threshold_ajax_variant_audit", SCRIPT)
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)

OLD = {
    "thfhe/src/distdec.rs": "let x = reveal_slice_z2k(&res_vec, 0, 64);\n",
    "thfhe/src/key_gen.rs": "noise_distribution_div_count(noise_number);\n",
    "thfhe/src/secret_key.rs": "secret-key old\n",
    "thfhe/examples/thfhe.rs": "if party_id <= threshold { run(); }\n",
    "mpc/src/dn.rs": "//! n > 2t; semi-honest\n",
    "thfhe/Cargo.toml": (
        '[dependencies]\n'
        'algebra = { git = "https://github.com/serendipity-crypto/primus-fhe", branch = "ajax" }\n'
        'lattice = { git = "https://github.com/serendipity-crypto/primus-fhe", branch = "ajax" }\n'
        'fhe_core = { git = "https://github.com/serendipity-crypto/primus-fhe", branch = "ajax" }\n'
    ),
    "thfhe/src/lib.rs": "// shared source\n",
}
ALT = {
    **OLD,
    "thfhe/src/distdec.rs": "reveal_slice_to_all_z2k(&res_vec, 64, true);\n",
    "thfhe/src/key_gen.rs": "noise_distribution_multi_party(noise_number);\n",
    "thfhe/src/secret_key.rs": "secret-key changed\n",
    "thfhe/examples/thfhe.rs": "// changed demo\n",
    "mpc/src/dn.rs": "//! another version n > 2t; semi-honest\n",
    "thfhe/Cargo.toml": (
        '[dependencies]\n'
        'algebra = { path = "../algebra" }\n'
        'lattice = { path = "../lattice" }\n'
        'fhe_core = { path = "../fhe_core" }\n'
    ),
    "Cargo.toml": "[workspace]\nmembers = []\n",
    "algebra/Cargo.toml": (
        '[dependencies]\nconcrete-ntt = { git = "https://github.com/primus-labs/concrete-ntt", branch = "dev" }\n'
    ),
    "lattice/Cargo.toml": "[package]\nname = 'lattice'\nversion = '0.1.0'\n",
    "fhe_core/Cargo.toml": "[package]\nname = 'fhe_core'\nversion = '0.1.0'\n",
}


def git(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True,
                          capture_output=True, text=True).stdout.strip()


class VersionVariantAuditTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.a = Path(self.temp.name) / "ajax"
        self.b = Path(self.temp.name) / "alternate"
        for root, files in [(self.a, OLD), (self.b, ALT)]:
            root.mkdir()
            git(root, "init", "-q")
            for rel, data in files.items():
                target = root / rel
                target.parent.mkdir(exist_ok=True, parents=True)
                target.write_text(data)
            git(root, "add", ".")
            git(root, "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                "commit", "-qm", "synthetic")
        self.a_commit = git(self.a, "rev-parse", "HEAD")
        self.b_commit = git(self.b, "rev-parse", "HEAD")
        self.blobs = {
            rel: (git(self.a, "rev-parse", "HEAD:" + rel),
                  git(self.b, "rev-parse", "HEAD:" + rel))
            for rel in M.BLOBS
        }

    def inspect(self):
        return M.inspect_checkout(self.a, self.a_commit,
                                  {p: v[0] for p, v in self.blobs.items()})

    def audit(self):
        with mock.patch.object(M, "AJAX_COMMIT", self.a_commit), \
             mock.patch.object(M, "ALT_COMMIT", self.b_commit), \
             mock.patch.object(M, "BLOBS", self.blobs):
            return M.audit(self.a, self.b)

    def test_pinned_fixture_git_bytes_are_recognized(self):
        result = self.inspect()
        self.assertEqual(result["head"], self.a_commit)
        self.assertEqual(len(result["selected"]), 7)

    def test_wrong_head_fails(self):
        with self.assertRaisesRegex(ValueError, "pinned HEAD"):
            M.inspect_checkout(self.a, "f" * 40, {p: v[0] for p, v in self.blobs.items()})

    def test_untracked_fake_lock_fails(self):
        (self.a / "Cargo.lock").write_text("# fake registry snapshot\n")
        with self.assertRaisesRegex(ValueError, "untracked"):
            self.inspect()

    def test_changed_source_fails(self):
        (self.a / "thfhe/src/distdec.rs").write_text("forged source\n")
        with self.assertRaisesRegex(ValueError, "modified"):
            self.inspect()

    def test_missing_source_fails(self):
        (self.a / "thfhe/src/distdec.rs").unlink()
        with self.assertRaisesRegex(ValueError, "modified"):
            self.inspect()

    def test_symlinked_checkout_fails(self):
        alias = Path(self.temp.name) / "alias"
        alias.symlink_to(self.a, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, "symlinked"):
            M.inspect_checkout(alias, self.a_commit, {p: v[0] for p, v in self.blobs.items()})

    def test_source_variants_must_remain_non_equivalent_and_non_admitted(self):
        result = self.audit()
        self.assertEqual(result["status"], "SOURCE_VARIANTS_DIFFER_REVIEW_REQUIRED")
        self.assertFalse(result["candidate_security_equivalence_established"])
        self.assertFalse(result["candidate_dependency_equivalence_established"])
        self.assertFalse(result["cryptographic_tests_executed"])
        self.assertFalse(result["cryptographic_release_admitted"])
        self.assertEqual(len(result["differences"]["source_blobs_differ"]), 6)
        self.assertEqual(result["differences"]["identical_source_blobs"],
                         ["thfhe/src/lib.rs"])

    def test_source_observations_identify_changed_noise_and_visibility(self):
        differences = self.audit()["differences"]
        self.assertTrue(differences["old_keygen_noise_div_count"])
        self.assertTrue(differences["alternative_keygen_noise_multi_party"])
        self.assertTrue(differences["alternative_decryption_opens_masked_intermediate_to_all"])
        self.assertTrue(differences["alternative_concrete_ntt_floating_branch"])
        self.assertEqual(differences["ajax_imports_unresolved_git_ajax_branch"],
                         ["algebra", "fhe_core", "lattice"])

    def test_source_mutant_rejected_even_with_matching_new_blob(self):
        key = self.b / "thfhe/src/key_gen.rs"
        key.write_text("NOISE_SIGNATURE_DROPPED\n")
        git(self.b, "add", ".")
        git(self.b, "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
            "commit", "-qm", "mutant")
        self.b_commit = git(self.b, "rev-parse", "HEAD")
        self.blobs["thfhe/src/key_gen.rs"] = (
            self.blobs["thfhe/src/key_gen.rs"][0],
            git(self.b, "rev-parse", "HEAD:thfhe/src/key_gen.rs"),
        )
        with self.assertRaisesRegex(ValueError, "noise|difference"):
            self.audit()

    def test_equivalence_request_is_explicitly_rejected(self):
        report = self.audit()
        argv = ["audit", "--ajax", str(self.a), "--alternative", str(self.b),
                "--require-equivalence"]
        with mock.patch.object(sys, "argv", argv), \
             mock.patch.object(M, "audit", return_value=report), \
             mock.patch("sys.stdout", new_callable=__import__("io").StringIO):
            self.assertEqual(M.main(), 2)

    def test_cryptographic_release_request_is_explicitly_rejected(self):
        report = self.audit()
        argv = ["audit", "--ajax", str(self.a), "--alternative", str(self.b),
                "--require-cryptographic-release"]
        with mock.patch.object(sys, "argv", argv), \
             mock.patch.object(M, "audit", return_value=report), \
             mock.patch("sys.stdout", new_callable=__import__("io").StringIO):
            self.assertEqual(M.main(), 2)

    def test_public_cli_does_not_accept_synthetic_git_pin(self):
        r = subprocess.run([sys.executable, str(SCRIPT), "--ajax", str(self.a),
                            "--alternative", str(self.b)], capture_output=True, text=True)
        self.assertEqual(r.returncode, 2)
        self.assertIn('"status": "SOURCE_INVALID"', r.stdout)


if __name__ == "__main__":
    unittest.main()
