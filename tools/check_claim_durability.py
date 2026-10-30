#!/usr/bin/env python3
"""Exercise the real TFHE import at its POSIX durability boundary (Linux CI).

Requires release binaries, cc and libc interposition. Observes actual syscalls,
not source text. EIO tests cannot simulate a power cut; they guard sync ordering
and fail-closed behavior. _exit after the real parent fsync tests interrupted
imports with no response/handle store. Independent key-directory copies below
are isolated test fixtures, never a distributed-authority claim.
"""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from threading import Barrier

ROOT = Path(__file__).resolve().parents[1]
BIN = ROOT / "backends/tfhe/target/release/tclmesh-tfhe"
PROVE = BIN.with_name("tclmesh-tfhe-prove")
CONTEXT = "ctx/durability"


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def call(keys, requests, extra=None):
    env = {**os.environ, "TCLMESH_TFHE_KEYS": str(keys), **(extra or {})}
    p = subprocess.run(
        [str(BIN)], input="".join(json.dumps(r) + "\n" for r in requests),
        capture_output=True, text=True, env=env, timeout=180,
    )
    return p, [json.loads(line) for line in p.stdout.splitlines()]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--parent-only", action="store_true")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="tclmesh-durability-") as temp:
        base = Path(temp)
        probe = base / "probe.so"
        subprocess.run([
            "cc", "-shared", "-fPIC", "-Wall", "-Wextra", "-Werror",
            str(ROOT / "tools/claim_sync_probe.c"), "-o", str(probe), "-ldl",
        ], check=True)
        keys = base / "template"
        public = base / "public"
        public.mkdir()
        p, replies = call(keys, [{"op": "publish", "dir": str(public)}])
        require(p.returncode == 0 and replies == [{"receipts": []}], p.stderr + str(replies))

        def prove(context, name, hi=None):
            proof = base / (name + ".proof")
            command = [str(PROVE), str(public), context, "0", "8", "7", str(proof)]
            if hi is not None:
                command.append(str(hi))
            subprocess.run(command, check=True, timeout=180)
            request = {"op": "import", "proof": str(proof), "context": context,
                       "lo": "0", "bits": 8, "width": 32}
            if hi is not None:
                request["hi"] = str(hi)
            return request

        request = prove(CONTEXT, "original")

        def fixture(name, existing=False):
            target = base / name
            shutil.copytree(keys, target)
            if existing:
                (target / "claims").mkdir(mode=0o700)
            return target

        def run_probe(target, fail=None, crash=False):
            log = base / (target.name + ".log")
            env = {"LD_PRELOAD": str(probe), "CLAIM_PROBE_KEYS": str(target),
                   "CLAIM_PROBE_LOG": str(log)}
            if fail:
                env["CLAIM_PROBE_FAIL"] = fail
            if crash:
                env["CLAIM_PROBE_EXIT"] = "1"
            p, replies = call(target, [request], env)
            events = log.read_text().splitlines() if log.exists() else []
            return p, replies, events

        ordered = ["before file", "synced file", "linked claim", "before claims",
                   "synced claims", "before parent", "synced parent"]
        for existing in [False, True]:
            target = fixture("existing" if existing else "first", existing)
            p, replies, events = run_probe(target)
            require(p.returncode == 0 and len(replies) == 1 and "token" in replies[0],
                    p.stderr + str(replies))
            require(events == ordered, "claim sync ordering differs: " + str(events))
        # Inspect every published field, rather than searching for one chosen
        # plaintext: only public digests, a random attempt and fixed tags exist.
        for record_path in (target / "claims").iterdir():
            record = json.loads(record_path.read_text())
            require(set(record) == {"version", "keyset", "context_digest", "statement", "attempt", "status"},
                    "unexpected claim schema")
            require(record["version"] == "tclmesh-proof-claim-v2" and record["status"] == "consumed",
                    "claim status/version differs")
            for field, size in [("keyset", 64), ("context_digest", 64), ("statement", 64), ("attempt", 16)]:
                require(len(record[field]) == size and all(c in "0123456789abcdef" for c in record[field]),
                        "claim field is not a public digest/attempt: " + field)
        print("PASS: claim schema contains only public digests, random attempt and fixed tags", flush=True)
        print("PASS: file -> link -> claims -> parent, new and pre-existing claims directory", flush=True)
        if args.parent_only:
            return

        for failure in ["file", "claims", "parent"]:
            target = fixture("fail-" + failure)
            p, replies, events = run_probe(target, fail=failure)
            require(p.returncode == 0 and len(replies) == 1 and "error" in replies[0]
                    and "token" not in replies[0], "sync failure exposed a handle: " + str(replies))
            require("fail " + failure in events, "fault did not fire: " + str(events))
            require(events == ordered[:ordered.index("before " + failure) + 1]
                    + ["fail " + failure], "continued beyond failed sync: " + str(events))
            p, retry = call(target, [request])
            require(p.returncode == 0 and len(retry) == 1, p.stderr + str(retry))
            if failure == "file":
                require("token" in retry[0], "unlinked record consumed context: " + str(retry))
            else:
                require("context claimed:" in retry[0].get("error", ""),
                        "linked claim lost after failed sync: " + str(retry))
        print("PASS: each fsync EIO prevents exposure; linked failures stay consumed on restart", flush=True)

        target = fixture("crash")
        p, replies, events = run_probe(target, crash=True)
        require(p.returncode == 86 and replies == [] and events == ordered,
                "did not terminate after durable claim before response: " + str((p.returncode, replies, events)))
        p, replies = call(target, [request])
        require(p.returncode == 0 and "context claimed:" in replies[0].get("error", ""),
                "interrupted import was accepted again: " + str(replies))
        changed = prove(CONTEXT, "changed", hi=200)
        p, replies = call(target, [changed])
        require(p.returncode == 0 and "another statement" in replies[0].get("error", ""),
                "changed verified statement was not rejected: " + str(replies))
        fresh = prove("ctx/fresh", "fresh")
        p, replies = call(target, [fresh])
        require(p.returncode == 0 and "token" in replies[0], "fresh context refused: " + str(replies))
        print("PASS: crash before expose, restart, changed valid statement and fresh context", flush=True)

        target = fixture("destroy")
        p, replies = call(target, [request, {"op": "destroy", "token": 1}, request])
        require(p.returncode == 0 and "token" in replies[0] and replies[1] == {}
                and "context claimed:" in replies[2].get("error", ""),
                "destroy released the claim: " + str(replies))
        print("PASS: destroy never releases a consumed context", flush=True)

        # Both processes finish loading the same keys before either imports.
        # Their native handle stores are separate; Tcl T-030 also covers two
        # distinct persistent handle stores through the public adapter.
        target = fixture("race")
        barrier = Barrier(2)

        def contender():
            p = subprocess.Popen([str(BIN)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE, text=True,
                                 env={**os.environ, "TCLMESH_TFHE_KEYS": str(target)})
            try:
                p.stdin.write('{"op":"keyset"}\n')
                p.stdin.flush()
                ready = json.loads(p.stdout.readline())
                require("keyset" in ready, "backend not ready: " + str(ready))
                barrier.wait(timeout=120)
                output, error = p.communicate(json.dumps(request) + "\n", timeout=180)
                require(p.returncode == 0, error)
                return json.loads(output)
            finally:
                if p.poll() is None:
                    p.kill()
                p.wait()

        with ThreadPoolExecutor(max_workers=2) as pool:
            replies = list(pool.map(lambda _: contender(), range(2)))
        require(sum("token" in r for r in replies) == 1
                and sum("context claimed:" in r.get("error", "") for r in replies) == 1,
                "concurrent import did not have exactly one winner: " + str(replies))
        print("PASS: synchronized independent processes on one filesystem admit exactly one", flush=True)


if __name__ == "__main__":
    main()
