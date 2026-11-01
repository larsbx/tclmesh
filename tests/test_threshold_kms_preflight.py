"""Synthetic, non-cryptographic controls for the KMS source preflight."""

from pathlib import Path
import importlib.util
import subprocess
import tempfile
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "threshold_kms_preflight.py"
SPEC = importlib.util.spec_from_file_location("threshold_kms_preflight", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

LOCK = '''version = 3
[[package]]
name = "tfhe"
version = "{version}"
[[package]]
name = "tfhe-zk-pok"
version = "0.9.0"
'''
CONF = '''kms_type = "threshold"
num_parties = 4
num_majority = 2
num_reconstruct = 3
fhe_params = "{parameters}"
'''


def run(*argv):
    subprocess.run(argv, check=True, capture_output=True, text=True)


class SourcePreflightTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.tclmesh, self.kms = base / "tclmesh", base / "kms"
        for path in (self.tclmesh, self.kms):
            path.mkdir()
            run("git", "-C", str(path), "init", "-q")
            lock = path / ("backends/tfhe/Cargo.lock" if path == self.tclmesh else "Cargo.lock")
            lock.parent.mkdir(parents=True, exist_ok=True)
            lock.write_text(LOCK.format(version="1.8.2"))
            run("git", "-C", str(path), "add", ".")
        self._write_config("Default")
        self._commit(self.tclmesh)
        self._commit(self.kms)

    def _write_config(self, parameters):
        path = self.kms / "core-client" / "config" / "client_local_threshold.toml"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(CONF.format(parameters=parameters))
        run("git", "-C", str(self.kms), "add", ".")

    def _commit(self, path):
        run("git", "-C", str(path), "-c", "user.name=Tester", "-c",
            "user.email=test@example.invalid", "commit", "-qm", "fixture")

    def _report(self, expected=None):
        return MODULE.preflight(self.tclmesh, self.kms,
                                expected or MODULE.git(self.kms, "rev-parse", "HEAD"))

    def test_matching_pinned_sources_only_preflight_not_crypto(self):
        data = self._report()
        self.assertEqual(data["status"], "SOURCE_PREFLIGHT_ONLY")
        self.assertIn("No cryptographic share verification", data["limits"][2])

    def test_reject_mismatched_tfhe_lock(self):
        (self.kms / "Cargo.lock").write_text(LOCK.format(version="1.6.2"))
        self._commit_modified()
        data = self._report()
        self.assertIn("tfhe_locked_versions_differ", data["blockers"])

    def _commit_modified(self):
        run("git", "-C", str(self.kms), "add", ".")
        self._commit(self.kms)

    def test_reject_insecure_test_parameters(self):
        self._write_config("Test")
        self._commit_modified()
        self.assertIn("kms_sample_uses_insecure_test_parameters", self._report()["blockers"])

    def test_reject_wrong_commit(self):
        data = self._report("a" * 40)
        self.assertIn("kms_source_head_not_expected_pin", data["blockers"])

    def test_reject_modified_source(self):
        (self.kms / "Cargo.lock").write_text(LOCK.format(version="1.6.2"))
        with self.assertRaisesRegex(ValueError, "does not match HEAD"):
            self._report()

    def test_reject_missing_lockfile(self):
        (self.kms / "Cargo.lock").unlink()
        with self.assertRaisesRegex(ValueError, "missing source"):
            self._report()

    def test_reject_nested_directory_as_pretend_checkout(self):
        nested = self.kms / "nested"
        nested.mkdir()
        (nested / "Cargo.lock").write_text(LOCK.format(version="1.8.2"))
        with self.assertRaisesRegex(ValueError, "not Git checkout root"):
            MODULE.inspect_checkout(nested, Path("Cargo.lock"))

    def test_reject_ignored_untracked_lockfile(self):
        run("git", "-C", str(self.kms), "rm", "-q", "--cached", "Cargo.lock")
        (self.kms / ".gitignore").write_text("/Cargo.lock\n")
        run("git", "-C", str(self.kms), "add", ".gitignore")
        self._commit(self.kms)
        with self.assertRaises(subprocess.CalledProcessError):
            self._report()

    def test_reject_forged_configuration_even_when_ignored(self):
        path = self.kms / "core-client" / "config" / "client_local_threshold.toml"
        run("git", "-C", str(self.kms), "rm", "-q", "--cached",
            "core-client/config/client_local_threshold.toml")
        (self.kms / ".gitignore").write_text("/core-client/config/client_local_threshold.toml\n")
        run("git", "-C", str(self.kms), "add", ".gitignore")
        self._commit(self.kms)
        self.assertTrue(path.is_file())
        with self.assertRaises(subprocess.CalledProcessError):
            self._report()

    def test_reject_replaced_commit_object(self):
        # An attacker could replace the bad HEAD object with a good commit,
        # then checkout the substituted bytes while HEAD keeps the bad SHA.
        good_head = MODULE.git(self.kms, "rev-parse", "HEAD")
        (self.kms / "Cargo.lock").write_text(LOCK.format(version="1.6.2"))
        self._commit_modified()
        bad_head = MODULE.git(self.kms, "rev-parse", "HEAD")
        run("git", "-C", str(self.kms), "replace", bad_head, good_head)
        run("git", "-C", str(self.kms), "checkout", "-qf", "--detach", bad_head)

        # The pristine original commit remains the authority, regardless
        # of whether this Git version materializes the replacement checkout.
        try:
            report = self._report(bad_head)
        except ValueError as exc:
            self.assertIn("does not match HEAD", str(exc))
        else:
            self.assertEqual(report["status"], "BLOCKED")
            self.assertIn("tfhe_locked_versions_differ", report["blockers"])

    def test_report_includes_committed_file_digests(self):
        data = self._report()
        self.assertIn("backends/tfhe/Cargo.lock",
                      data["tclmesh"]["verified_source_digests"])
        self.assertIn("core-client/config/client_local_threshold.toml",
                      data["kms"]["verified_source_digests"])

    def test_reject_fake_quorum(self):
        self._write_config("Default")
        p = self.kms / "core-client" / "config" / "client_local_threshold.toml"
        p.write_text(p.read_text().replace("num_reconstruct = 3", "num_reconstruct = 2"))
        self._commit_modified()
        self.assertIn("kms_sample_not_three_responses_of_four", self._report()["blockers"])


if __name__ == "__main__":
    unittest.main()
