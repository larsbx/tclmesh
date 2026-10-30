#!/usr/bin/env python3
"""Require isolated regressions of the threshold boundary to fail Tcl tests.

This tests fail-closed gates, not cryptographic soundness. No production files
are modified. Uses the same Tcl runtime as the conformance suite.
"""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def run(root):
    result = subprocess.run(
        ["tclsh"], input="""
package require tcltest 2
namespace import ::tcltest::*
lappend auto_path [pwd]
configure -testdir [file join [pwd] tests] -file threshold-security.test -singleproc 1
exit [runAllTests]
""", cwd=root, capture_output=True, text=True, timeout=120
    )
    output = result.stdout + result.stderr
    if "threshold-security.test" not in output or "Total" not in output:
        raise RuntimeError(f"suite did not execute:\n{output}")
    return result.returncode, output


def main():
    code, output = run(ROOT)
    if code:
        raise RuntimeError(f"baseline must pass:\n{output}")
    mutants = [
        (
            "disabled mode/verification gate",
            "src/release.tcl",
            "proc ::tclmesh::release::_assert_mode {descriptor} {",
            "proc ::tclmesh::release::_assert_mode {descriptor} {\n    return",
            "TS-003-invalid-contributions",
        ),
        (
            "TFHE advertises threshold again",
            "src/tfhe.tcl",
            "return [concat {decrypt destroy authorization-quorum homomorphic proven-inputs}",
            "return [concat {decrypt destroy threshold-release authorization-quorum homomorphic proven-inputs}",
            "TS-001-capabilities",
        ),
        (
            "TFHE falls back to ordinary decrypt",
            "src/tfhe.tcl",
            "        combine-verified-release {",
            '        combine-verified-release {\n            if {$operation eq "combine-release"} {return [_call {"op":"decrypt","token":1}]}',
            "TS-005-tfhe-direct-crypto",
        ),
    ]
    for name, file, old, new, expected_test in mutants:
        with tempfile.TemporaryDirectory(prefix="tclmesh-threshold-mutant-") as tmp:
            root = Path(tmp) / "repo"
            shutil.copytree(
                ROOT, root,
                ignore=shutil.ignore_patterns(".git", ".lake", "target", "__pycache__"),
            )
            path = root / file
            source = path.read_text()
            if source.count(old) != 1:
                raise RuntimeError(f"mutation anchor must be unique: {name}")
            path.write_text(source.replace(old, new))
            code, output = run(root)
            if not code or f"==== {expected_test}" not in output or "FAILED" not in output:
                raise RuntimeError(f"mutant survived or failed unexpectedly: {name}\n{output}")
            print(f"rejected: {name} ({expected_test})")


if __name__ == "__main__":
    main()
