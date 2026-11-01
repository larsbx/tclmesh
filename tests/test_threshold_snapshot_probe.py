"""Synthetic runner-integrity controls; native primitive tests are separate."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

SCRIPT = Path(__file__).resolve().parents[1] / "tools/threshold_snapshot_probe.py"
SPEC = importlib.util.spec_from_file_location("threshold_snapshot_probe", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


class SourceTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        git(self.root, "init", "-q")
        (self.root / "Cargo.lock").write_text("version = 3\n")
        (self.root / "lib.rs").write_text("// fixture\n")
        (self.root / ".gitignore").write_text("ignored/\n")
        git(self.root, "add", ".")
        git(self.root, "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
            "commit", "-qm", "fixture")
        self.pin = git(self.root, "rev-parse", "HEAD")

    def read(self):
        with patch.object(MODULE, "PIN", self.pin):
            return MODULE.source_files(self.root)

    def test_exact_files(self):
        self.assertEqual(self.read()["lib.rs"], b"// fixture\n")

    def test_wrong_pin(self):
        with self.assertRaisesRegex(ValueError, "unexpected source pin"):
            MODULE.source_files(self.root)

    def test_explicit_candidate_pin_is_not_replaced_by_default(self):
        with patch.object(MODULE, "PIN", self.pin):
            with self.assertRaisesRegex(ValueError, "unexpected source pin"):
                MODULE.source_files(self.root, "a" * 40)

    def test_dirty_file(self):
        (self.root / "lib.rs").write_text("// modified\n")
        with self.assertRaises(ValueError):
            self.read()

    def test_assume_unchanged_cannot_hide_modified_build_input(self):
        git(self.root, "update-index", "--assume-unchanged", "lib.rs")
        (self.root / "lib.rs").write_text("// hidden mutation\n")
        self.assertEqual(git(self.root, "status", "--porcelain"), "")
        with self.assertRaisesRegex(ValueError, "source bytes differ"):
            self.read()

    def test_nested_root(self):
        (self.root / "nested").mkdir()
        with patch.object(MODULE, "PIN", self.pin):
            with self.assertRaisesRegex(ValueError, "not the checkout root"):
                MODULE.source_files(self.root / "nested")

    def test_untracked_source_rejected(self):
        (self.root / "untracked.rs").write_text("// fixture\n")
        with self.assertRaisesRegex(ValueError, "dirty"):
            self.read()

    def test_ignored_files_never_enter_build_tree(self):
        ignored = self.root / "ignored"
        ignored.mkdir()
        (ignored / "malicious.rs").write_text("// not a build input\n")
        self.assertNotIn("ignored/malicious.rs", self.read())

    def test_symlink_source_rejected(self):
        path = self.root / "lib.rs"
        path.unlink()
        path.symlink_to("Cargo.lock")
        with self.assertRaises(ValueError):
            self.read()

    def test_replacement_object_cannot_substitute_pinned_build_bytes(self):
        original = (self.root / "lib.rs").read_bytes()
        (self.root / "lib.rs").write_text("// different committed code\n")
        git(self.root, "add", ".")
        git(self.root, "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
            "commit", "-qm", "substitution")
        alternate = git(self.root, "rev-parse", "HEAD")
        git(self.root, "replace", self.pin, alternate)
        git(self.root, "checkout", "-qf", "--detach", self.pin)
        # Even a working tree materialized by replacement refs must be compared
        # with the actual pinned objects, never the substituted commit body.
        try:
            files = self.read()
        except ValueError:
            pass
        else:
            self.assertEqual(files["lib.rs"], original)

    def test_no_native_execution_when_source_unverifiable(self):
        with patch.object(MODULE, "source_files", side_effect=ValueError("wrong pin")), \
                patch.object(MODULE.subprocess, "run") as run:
            report = MODULE.probe(self.root, self.root.parent / "cache", 10)
        run.assert_not_called()
        self.assertEqual(report["status"], "BLOCKED")
        self.assertFalse(report["cryptographic_release_admitted"])


class ResultTests(unittest.TestCase):
    def output(self):
        return ("\n".join(f"test {name} ... ok" for name in sorted(MODULE.EXPECTED))
                + "\ntest result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out; finished in 0.01s\n")

    def test_exact_native_test_set(self):
        self.assertTrue(MODULE.check_result(0, self.output()))

    def test_candidate_results_cannot_be_cross_attributed(self):
        expected = MODULE.CANDIDATES["fhenix-paper"]["expected"]
        self.assertFalse(MODULE.check_result(0, self.output(), expected))
        fhenix_output = ("\n".join(f"test {name} ... ok" for name in sorted(expected))
                         + "\ntest result: ok. 4 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;\n")
        self.assertTrue(MODULE.check_result(0, fhenix_output, expected))
        self.assertFalse(MODULE.check_result(0, fhenix_output))

    def test_empty_expected_set_cannot_pass(self):
        self.assertFalse(MODULE.check_result(0, "test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;", set()))

    def test_unknown_candidate_never_executes(self):
        with patch.object(MODULE.subprocess, "run") as run:
            report = MODULE.probe(Path("missing"), Path("cache"), 10, "unreviewed")
        run.assert_not_called()
        self.assertEqual(report["status"], "BLOCKED")
        self.assertFalse(report["cryptographic_release_admitted"])

    def test_zero_tests_not_evidence(self):
        self.assertFalse(MODULE.check_result(0, "test result: ok. 0 passed; 0 failed; 0 ignored; 0 measured; 6 filtered out;"))

    def test_nonzero_or_missing_or_ignored_tests_rejected(self):
        self.assertFalse(MODULE.check_result(101, self.output()))
        self.assertFalse(MODULE.check_result(0, self.output().replace(" ... ok", " ... ignored", 1)))
        self.assertFalse(MODULE.check_result(0, self.output().replace("0 ignored", "1 ignored")))
        self.assertFalse(MODULE.check_result(0, self.output().replace("6 passed", "5 passed")))


class BuildTreeTests(unittest.TestCase):
    def test_unexpected_fixture_output_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "source.rs").write_bytes(b"// fixture\n")
            expected = {"source.rs": b"// fixture\n"}
            MODULE.verify_build_files(root, expected)
            (root / "unexpected-fixture-key.bin").write_bytes(b"not a real key")
            with self.assertRaisesRegex(ValueError, "unexpected fixture"):
                MODULE.verify_build_files(root, expected)

    def test_build_cannot_rewrite_verified_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "source.rs").write_bytes(b"// changed\n")
            with self.assertRaisesRegex(ValueError, "changed source"):
                MODULE.verify_build_files(root, {"source.rs": b"// original\n"})


if __name__ == "__main__":
    unittest.main()
