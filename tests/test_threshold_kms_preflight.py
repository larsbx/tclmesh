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
            (path / "Cargo.lock").write_text(LOCK.format(version="1.8.2"))
            run("git", "-C", str(path), "add", "Cargo.lock")
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
        data = self._report()
        self.assertIn("kms_tracked_tree_modified", data["blockers"])

    def test_reject_missing_lockfile(self):
        (self.kms / "Cargo.lock").unlink()
        with self.assertRaises(OSError):
            self._report()

    def test_reject_fake_quorum(self):
        self._write_config("Default")
        p = self.kms / "core-client" / "config" / "client_local_threshold.toml"
        p.write_text(p.read_text().replace("num_reconstruct = 3", "num_reconstruct = 2"))
        self._commit_modified()
        self.assertIn("kms_sample_not_three_responses_of_four", self._report()["blockers"])


if __name__ == "__main__":
    unittest.main()
