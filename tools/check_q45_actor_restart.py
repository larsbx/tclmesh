"""Exercise INV-Q9 against the real research actor and its SQLite authority.

Requires Erlang/OTP with Crypto and EUnit, Python 3 with SQLite, and POSIX
SIGKILL. Every listed acceptance check is mandatory. This is process-failure
evidence, not a power-loss test or a cryptographic security/refinement proof.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import sqlite3
import subprocess
import sys
import tempfile
import time
from contextlib import closing
from datetime import datetime, timezone


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "experiments/threshold_q45"
WORKER = ROOT / "tools/q45_result_store.py"
SID = b"q45-invq9-restart"
CIPHERTEXT = b"evaluated:\x01\x02\x03\x04\x05"
QUORUM = [1, 2, 3, 4]
MANDATORY = (
    "adapter_eunit",
    "whole_vm_after_commit",
    "whole_vm_after_completion",
    "actor_after_commit",
    "actor_after_completion",
    "stale_writer",
    "race_identical",
    "unavailable_store_fails_closed",
    "lost_helper_reply_recovered_after_deadline",
    "replay_notification_mutant",
)
SOURCE_PATHS = (
    "tools/check_q45_actor_restart.py",
    "tools/q45_result_store.py",
    "experiments/threshold_q45/q45_ceremony.erl",
    "experiments/threshold_q45/q45_result_store.erl",
    "experiments/threshold_q45/q45_result_store_tests.erl",
    "experiments/threshold_q45/q45_restart_tests.erl",
)


class AcceptanceFailure(Exception):
    """A required observation was absent or contradicted the contract."""


def require(condition, message):
    if not condition:
        raise AcceptanceFailure(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def source_state():
    def git(*args):
        return subprocess.check_output(
            ["git", *args], cwd=ROOT, text=True, timeout=15
        ).rstrip("\n")

    return {
        "revision": git("rev-parse", "HEAD"),
        "status": git("status", "--porcelain=v1", "--untracked-files=all"),
        "sha256": {name: sha256((ROOT / name).read_bytes()) for name in SOURCE_PATHS},
    }


def erl_path(path):
    # Paths are data, never shell or Erlang source fragments supplied by callers.
    encoded = base64.b64encode(os.fsencode(path)).decode("ascii")
    return f'binary_to_list(base64:decode("{encoded}"))'


def decode_binding(encoded):
    """Decode the small ETF subset independently of the Erlang adapter."""
    position = 0

    def take(size):
        nonlocal position
        require(position + size <= len(encoded), "truncated binding ETF")
        value = encoded[position:position + size]
        position += size
        return value

    def number(size):
        return int.from_bytes(take(size), "big")

    def term():
        tag = number(1)
        if tag == 104:  # SMALL_TUPLE_EXT
            return tuple(term() for _ in range(number(1)))
        if tag in (100, 118, 115, 119):  # Latin-1 and UTF-8 atom encodings
            size = number(2 if tag in (100, 118) else 1)
            return take(size).decode("utf-8" if tag in (118, 119) else "latin1")
        if tag == 109:  # BINARY_EXT
            return take(number(4))
        if tag == 107:  # STRING_EXT, canonical compact byte list
            return list(take(number(2)))
        if tag == 108:  # LIST_EXT
            values = [term() for _ in range(number(4))]
            require(term() == [], "improper quorum list")
            return values
        if tag == 106:  # NIL_EXT
            return []
        if tag == 97:  # SMALL_INTEGER_EXT
            return number(1)
        raise AcceptanceFailure(f"unexpected binding ETF tag {tag}")

    require(take(1) == b"\x83", "missing binding ETF version")
    decoded = term()
    require(position == len(encoded), "trailing bytes in binding ETF")
    return decoded


def snapshot(connection, expected_rows=1):
    """Read both tables directly; do not call or import the worker under test."""
    require(connection.execute("PRAGMA integrity_check").fetchall() == [("ok",)],
            "SQLite integrity check failed")
    require(connection.execute("PRAGMA foreign_key_check").fetchall() == [],
            "SQLite foreign-key check failed")
    require(connection.execute("PRAGMA journal_mode").fetchone()[0] == "wal",
            "authority is not in WAL mode")
    require(connection.execute("PRAGMA application_id").fetchone()[0] == 0x51343552,
            "unexpected SQLite application id")
    require(connection.execute("PRAGMA user_version").fetchone()[0] == 1,
            "unexpected SQLite schema version")
    results = connection.execute(
        "SELECT sid,binding,bit,receipt FROM q45_results ORDER BY sid"
    ).fetchall()
    completions = connection.execute(
        "SELECT sid,receipt FROM q45_completions ORDER BY sid"
    ).fetchall()
    require(len(results) == len(completions) == expected_rows,
            f"expected {expected_rows} result/completion rows, got "
            f"{len(results)}/{len(completions)}")
    serialized = []
    for sid, binding, bit, receipt in results:
        require(sid == SID and type(bit) is int and bit == 1,
                "durable result differs from the admitted session/bit")
        expected_binding = (
            "q45_local_binding_v1", CIPHERTEXT,
            hashlib.sha256(CIPHERTEXT).digest(), QUORUM,
        )
        require(decode_binding(binding) == expected_binding,
                "durable transcript binding differs from the independent fixture")
        expected_receipt = hashlib.sha256(
            b"tclmesh-q45-result-v1\0" + len(sid).to_bytes(8, "big") + sid
            + len(binding).to_bytes(8, "big") + binding + bytes([bit])
        ).digest()
        require(receipt == expected_receipt, "receipt hash is not bound to the result")
        require(completions == [(sid, receipt)], "completion is not bound to the receipt")
        serialized.append({"sid_hex": sid.hex(), "binding_hex": binding.hex(),
                           "bit": bit, "receipt_hex": receipt.hex()})
    return {"results": serialized,
            "completions": [{"sid_hex": sid.hex(), "receipt_hex": receipt.hex()}
                            for sid, receipt in completions]}


def observe(path):
    # mode=ro makes an accidentally missing DB fail rather than creating it.
    return sqlite3.connect(path.resolve().as_uri() + "?mode=ro",
                           uri=True, timeout=5, isolation_level=None)


class Runner:
    def __init__(self, work, evidence):
        self.work = work
        self.evidence = evidence
        self.environment = os.environ.copy()
        # The local Lean executable-discovery workaround is unrelated to OTP.
        self.environment.pop("LD_PRELOAD", None)
        self.environment.setdefault("ERL_FLAGS", "+S 2")
        self.checks = {name: {"name": name, "status": "not_run"} for name in MANDATORY}
        self.commands = []
        self.active = None

    def begin(self, name):
        self.active = name
        self.checks[name]["status"] = "running"
        print(f"Checking {name}...", flush=True)

    def passed(self, **observations):
        self.checks[self.active].update(status="passed", **observations)
        print(f"  {self.active}: passed", flush=True)
        self.active = None

    def command(self, name, command, timeout=45, expected_failure=None):
        started = time.monotonic()
        try:
            result = subprocess.run(command, cwd=self.work, env=self.environment,
                                    capture_output=True, text=True, timeout=timeout)
            output = result.stdout + result.stderr
        except subprocess.TimeoutExpired as exc:
            output = ((exc.stdout or b"") + (exc.stderr or b"")).decode("utf-8", "replace")
            (self.evidence / f"{name}.txt").write_text(output, encoding="utf-8")
            raise AcceptanceFailure(f"{name} exceeded {timeout}s") from exc
        path = self.evidence / f"{name}.txt"
        path.write_text(output, encoding="utf-8")
        self.commands.append({"name": name, "command": [str(x) for x in command],
                              "exit_code": result.returncode,
                              "seconds": round(time.monotonic() - started, 3),
                              "output_sha256": sha256(output.encode()),
                              "output_file": path.name})
        if expected_failure:
            require(result.returncode != 0 and expected_failure in output,
                    f"{name}: expected semantic failure {expected_failure!r}; "
                    f"exit={result.returncode}\n{output}")
        else:
            require(result.returncode == 0, f"{name}: exit={result.returncode}\n{output}")
        return output

    def vm_command(self, ebin, mode, database, worker=WORKER, marker=None):
        marker = marker or database.with_suffix(".marker.json")
        expression = (
            "{ok, _} = application:ensure_all_started(crypto), "
            f"ok = q45_restart_tests:run({mode}, {erl_path(database)}, "
            f"{erl_path(worker)}, {erl_path(marker)}), halt(0)."
        )
        return ["erl", "-noshell", "-pa", str(ebin), "-eval", expression]

    def run_mode(self, label, ebin, mode, database, worker=WORKER,
                 expected_failure=None):
        output = self.command(label, self.vm_command(ebin, mode, database, worker),
                              expected_failure=expected_failure)
        if expected_failure is None:
            require(f"Q45_CHECK_OK {mode}" in output,
                    f"{label}: driver completion marker is absent")
        return output

    def compile(self, name, ebin, ceremony=None):
        ebin.mkdir()
        sources = [ceremony or SOURCE / "q45_ceremony.erl",
                   SOURCE / "q45_result_store.erl", SOURCE / "q45_restart_tests.erl",
                   SOURCE / "q45_result_store_tests.erl"]
        self.command(name, ["erlc", "-Werror", "-o", str(ebin), *map(str, sources)])

    def crash_window(self, ebin, stage):
        label = f"whole_vm_{stage}"
        self.begin(label)
        database = self.work / f"{label}.sqlite"
        marker = self.work / f"{label}.marker.json"
        command = self.vm_command(ebin, f"vm_{stage}", database, marker=marker)
        log_path = self.evidence / f"{label}-writer.txt"
        started = time.monotonic()
        with log_path.open("w", encoding="utf-8") as log:
            process = subprocess.Popen(command, cwd=self.work, env=self.environment,
                                       stdout=log, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            try:
                deadline = time.monotonic() + 30
                while not marker.exists():
                    require(process.poll() is None,
                            f"{label}: writer exited before the crash marker")
                    require(time.monotonic() < deadline,
                            f"{label}: crash hook was not reached")
                    time.sleep(0.02)
                observation = json.loads(marker.read_text(encoding="utf-8"))
                require(observation.get("stage") == stage,
                        f"{label}: incorrect hook marker")
                expected_notifications = 0 if stage == "after_commit" else 1
                require(observation.get("notifications") == expected_notifications,
                        f"{label}: incorrect observed notification count")
                require(process.poll() is None, f"{label}: writer did not remain blocked")
                with closing(observe(database)) as observer:
                    before_kill = snapshot(observer)
                    # Kill the whole VM/process group, never ask OTP to stop cleanly.
                    os.killpg(process.pid, signal.SIGKILL)
                    returncode = process.wait(timeout=10)
                    require(returncode == -signal.SIGKILL,
                            f"{label}: writer was not terminated by SIGKILL")
                    after_kill = snapshot(observer)
                    require(before_kill == after_kill, f"{label}: crash changed the result")
                    version_before = observer.execute("PRAGMA data_version").fetchone()[0]
                    self.run_mode(label + "-recovery", ebin, "replay", database)
                    after_replay = snapshot(observer)
                    version_after = observer.execute("PRAGMA data_version").fetchone()[0]
                    require(after_replay == after_kill,
                            f"{label}: recovery/retries changed a durable record")
                    require(version_after == version_before,
                            f"{label}: recovery/retries performed a new SQLite write")
            finally:
                if process.poll() is None:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait(timeout=10)
        shutil.copyfile(marker, self.evidence / marker.name)
        self.commands.append({"name": label + "-writer", "command": command,
                              "exit_code": returncode, "signal": "SIGKILL",
                              "seconds": round(time.monotonic() - started, 3),
                              "output_file": log_path.name,
                              "output_sha256": sha256(log_path.read_bytes())})
        self.passed(crash_marker=observation, snapshot=after_replay,
                    data_version_before=version_before, data_version_after=version_after,
                    recovery_notifications=0, writer_exit_code=returncode)

    def execute(self):
        require(os.name == "posix" and hasattr(signal, "SIGKILL"),
                "POSIX SIGKILL is required; the process-crash checks cannot be skipped")
        for executable in ("erl", "erlc"):
            require(shutil.which(executable), f"required runtime is missing: {executable}")
        otp = self.command("otp-version", ["erl", "-noshell", "-eval",
            '{ok, _} = application:ensure_all_started(crypto), '
            'true = is_list(code:lib_dir(eunit)), '
            'io:format("OTP ~s ERTS ~s~n", [erlang:system_info(otp_release), '
            'erlang:system_info(version)]), halt(0).'])
        ebin = self.work / "baseline-ebin"
        self.compile("compile-baseline", ebin)

        self.begin("adapter_eunit")
        output = self.command("adapter_eunit", ["erl", "-noshell", "-pa", str(ebin),
            "-eval", "case eunit:test(q45_result_store_tests, [verbose]) of "
            "ok -> halt(0); _ -> halt(1) end."], timeout=90)
        require(re.search(r"(?:All [1-9][0-9]* tests passed|Test passed)", output),
                "adapter EUnit reported no executed tests")
        self.passed()

        for stage in ("after_commit", "after_completion"):
            self.crash_window(ebin, stage)

        lossy_worker = self.work / "lost_helper_response_worker.py"
        lossy_worker.write_text(
            "import importlib.util\nimport sys\n"
            f"spec = importlib.util.spec_from_file_location('q45_real_worker', {str(WORKER)!r})\n"
            "worker = importlib.util.module_from_spec(spec)\n"
            "spec.loader.exec_module(worker)\n"
            "original = worker.handle\n"
            "def lose_commit_reply(db, fields):\n"
            "    response = original(db, fields)\n"
            "    return b'lost_commit_response' if fields[0] == b'commit' else response\n"
            "worker.handle = lose_commit_reply\n"
            "raise SystemExit(worker.main())\n", encoding="utf-8")
        shutil.copyfile(lossy_worker, self.evidence / lossy_worker.name)
        cases = (
            ("actor_after_commit", "actor_after_commit", WORKER, 1),
            ("actor_after_completion", "actor_after_completion", WORKER, 1),
            ("stale_writer", "stale_writer", WORKER, 1),
            ("race_identical", "identical_race", WORKER, 1),
            ("unavailable_store_fails_closed", "unavailable_store", WORKER, 0),
            ("lost_helper_reply_recovered_after_deadline", "lost_helper_response", lossy_worker, 1),
        )
        for name, mode, worker, expected_rows in cases:
            self.begin(name)
            database = self.work / f"{name}.sqlite"
            self.run_mode(name, ebin, mode, database, worker)
            with closing(observe(database)) as observer:
                recorded = snapshot(observer, expected_rows)
            self.passed(snapshot=recorded)

        self.begin("replay_notification_mutant")
        source = (SOURCE / "q45_ceremony.erl").read_text(encoding="utf-8")
        original = ("                {replay, Receipt} ->\n"
                    "                    {{ok, Receipt}, {complete, Updated#{durable_receipt => Receipt}}};")
        replacement = ("                {replay, Receipt} ->\n"
                       "                    notify_completion(Sid, Receipt, Updated),\n"
                       "                    {{ok, Receipt}, {complete, Updated#{durable_receipt => Receipt}}};")
        require(source.count(original) == 1, "expected exactly one commit-replay mutation site")
        mutant_source = self.work / "q45_ceremony.erl"
        mutant_source.write_text(source.replace(original, replacement, 1), encoding="utf-8")
        mutant_ebin = self.work / "mutant-ebin"
        self.compile("compile-replay-notification-mutant", mutant_ebin, mutant_source)
        database = self.work / "replay_notification_mutant.sqlite"
        output = self.run_mode("replay_notification_mutant", mutant_ebin, "identical_race",
                               database, expected_failure="duplicate_completion")
        require(re.search(r"\{duplicate_completion,\s*2\}", output),
                "mutant did not report the expected two completion notifications")
        with closing(observe(database)) as observer:
            recorded = snapshot(observer)
        self.passed(expectation="compiled mutant fails with duplicate_completion",
                    mutant_source_sha256=sha256(mutant_source.read_bytes()), snapshot=recorded)
        return otp.strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--evidence-dir", type=Path)
    args = parser.parse_args()
    started = datetime.now(timezone.utc).isoformat()
    evidence = (args.evidence_dir.resolve() if args.evidence_dir else
                Path(tempfile.mkdtemp(prefix="q45-restart-evidence-")))
    evidence.mkdir(parents=True, exist_ok=True)
    before = None
    after = None
    error = None
    otp = None
    with tempfile.TemporaryDirectory(prefix="q45-actor-restart-") as directory:
        runner = Runner(Path(directory), evidence)
        try:
            before = source_state()
            otp = runner.execute()
        except (AcceptanceFailure, OSError, subprocess.SubprocessError, ValueError) as exc:
            error = str(exc)
            if runner.active:
                runner.checks[runner.active].update(status="failed", error=error)
        finally:
            try:
                after = source_state()
                if before != after:
                    error = (error + "; " if error else "") + "source or Git state changed during acceptance"
            except (OSError, subprocess.SubprocessError) as exc:
                error = (error + "; " if error else "") + f"final source guard failed: {exc}"
        passed = all(check["status"] == "passed" for check in runner.checks.values())
        receipt = {
            "schema": "q45-actor-restart-v1",
            "started_utc": started,
            "completed_utc": datetime.now(timezone.utc).isoformat(),
            "accepted": passed and error is None,
            "mandatory_checks": list(MANDATORY),
            "checks": list(runner.checks.values()),
            "commands": runner.commands,
            "versions": {"otp": otp, "python": sys.version.split()[0],
                         "sqlite": sqlite3.sqlite_version},
            "source_before": before,
            "source_after": after,
            "source_and_git_state_unchanged": before is not None and before == after,
            "runtime_environment": {"LD_PRELOAD": "unset for all Erlang/compiler/helper subprocesses",
                                    "ERL_FLAGS": runner.environment.get("ERL_FLAGS")},
            "scope": "Inert research actor; local preserved SQLite authority; process/VM crashes, "
                     "one durable result and logical completion, at-most-once notification emission. "
                     "No host power-loss, external delivery, cryptographic security, or universal refinement claim.",
            "error": error,
        }
        receipt_path = args.receipt.resolve() if args.receipt else None
        receipt["evidence_sha256"] = {
            path.name: sha256(path.read_bytes()) for path in sorted(evidence.iterdir())
            if path.is_file() and path.resolve() != receipt_path
        }
        text = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
        if receipt_path:
            receipt_path.parent.mkdir(parents=True, exist_ok=True)
            receipt_path.write_text(text, encoding="utf-8")
        else:
            print(text, end="")
        if not receipt["accepted"]:
            print(error or "one or more mandatory checks did not pass", file=sys.stderr)
            return 1
        print(f"{len(MANDATORY)}/{len(MANDATORY)} mandatory actor restart checks passed; "
              f"evidence: {evidence}", flush=True)
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
