"""Durable authority acceptance checks for the inert SPEC_4of5 experiment."""
from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
from pathlib import Path
import sqlite3
import subprocess
import sys
import tempfile
import threading
import unittest


ROOT = Path(__file__).resolve().parents[1]
WORKER = ROOT / "tools" / "q45_result_store.py"
SPEC = importlib.util.spec_from_file_location("q45_result_store", WORKER)
assert SPEC is not None and SPEC.loader is not None
store = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(store)

SID = b"q45-durable-test-session"
BINDING = b"ciphertext, digest, and frozen quorum"


class DurableResultStoreTests(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory(prefix="q45-result-store-")
        self.addCleanup(self.directory.cleanup)
        self.database = Path(self.directory.name) / "authority.sqlite3"

    def worker(self, request, database=None):
        return subprocess.run(
            [sys.executable, "-B", str(WORKER), "--db", str(database or self.database)],
            input=request, capture_output=True, timeout=15, check=False,
        )

    def request(self, command, sid=SID, binding=BINDING, bit=1, database=None):
        fields = [command.encode(), sid.hex().encode()]
        if command == "commit":
            fields += [binding.hex().encode(), str(bit).encode()]
        process = self.worker(b"\t".join(fields) + b"\n", database)
        self.assertEqual(process.returncode, 0, process.stderr or process.stdout)
        self.assertEqual(process.stderr, b"")
        self.assertTrue(process.stdout.endswith(b"\n"))
        self.assertEqual(process.stdout.count(b"\n"), 1)
        return process.stdout[:-1].split(b"\t")

    def rows(self, database=None):
        with sqlite3.connect(database or self.database) as db:
            return (
                db.execute("SELECT sid,binding,bit,receipt FROM q45_results ORDER BY sid").fetchall(),
                db.execute("SELECT sid,receipt FROM q45_completions ORDER BY sid").fetchall(),
            )

    def assert_worker_error(self, request, database=None):
        process = self.worker(request, database)
        self.assertNotEqual(process.returncode, 0)
        self.assertEqual(process.stdout, b"error\n")
        self.assertEqual(process.stderr, b"")

    def test_empty_database_initializes_versioned_authority(self):
        self.assertEqual(self.request("lookup"), [b"empty"])
        self.assertEqual(self.rows(), ([], []))
        with sqlite3.connect(self.database) as db:
            self.assertEqual(db.execute("PRAGMA application_id").fetchone()[0], store.APPLICATION_ID)
            self.assertEqual(db.execute("PRAGMA user_version").fetchone()[0], store.SCHEMA_VERSION)
            self.assertEqual(db.execute("PRAGMA journal_mode").fetchone()[0], "wal")
            store.validate_schema(db)

    def test_first_commit_has_one_result_and_one_completion(self):
        reply = self.request("commit")
        expected_id = hashlib.sha256(
            b"tclmesh-q45-result-v1\0" + len(SID).to_bytes(8, "big") + SID
            + len(BINDING).to_bytes(8, "big") + BINDING + b"\x01"
        ).digest()
        self.assertEqual(reply, [b"inserted", BINDING.hex().encode(), b"1", expected_id.hex().encode()])
        self.assertEqual(self.rows(), ([(SID, BINDING, 1, expected_id)], [(SID, expected_id)]))

    def test_identical_retries_return_receipt_without_mutation(self):
        first = self.request("commit")
        before = self.rows()
        with sqlite3.connect(self.database) as db:
            before_version = db.execute("PRAGMA data_version").fetchone()[0]
            for _ in range(3):
                self.assertEqual(self.request("commit"), [b"replay", *first[1:]])
            self.assertEqual(db.execute("PRAGMA data_version").fetchone()[0], before_version)
        self.assertEqual(self.rows(), before)

    def test_identical_and_conflicting_retries_succeed_with_all_dml_denied(self):
        first = self.request("commit")
        before = self.rows()
        denied = []

        def deny_dml(action, table, column, database, trigger):
            if action in (sqlite3.SQLITE_INSERT, sqlite3.SQLITE_UPDATE, sqlite3.SQLITE_DELETE):
                denied.append((action, table))
                return sqlite3.SQLITE_DENY
            return sqlite3.SQLITE_OK

        with sqlite3.connect(self.database, isolation_level=None) as db:
            store.initialize(db)
            db.set_authorizer(deny_dml)
            # Establish that each write operation is actually blocked, including
            # statements that would affect no rows and evade data-version checks.
            for sql in (
                "INSERT INTO q45_results SELECT * FROM q45_results WHERE 0",
                "UPDATE q45_results SET bit=bit WHERE 0",
                "DELETE FROM q45_results WHERE 0",
            ):
                with self.assertRaises(sqlite3.DatabaseError):
                    db.execute(sql)
            self.assertCountEqual([action for action, _ in denied],
                                  [sqlite3.SQLITE_INSERT, sqlite3.SQLITE_UPDATE, sqlite3.SQLITE_DELETE])
            denied.clear()
            requests = (
                ([b"commit", SID.hex().encode(), BINDING.hex().encode(), b"1"],
                 b"\t".join([b"replay", *first[1:]])),
                ([b"commit", SID.hex().encode(), BINDING.hex().encode(), b"0"], b"conflict"),
                ([b"commit", SID.hex().encode(), b"other binding".hex().encode(), b"1"], b"conflict"),
            )
            for fields, expected in requests:
                with self.subTest(fields=fields):
                    self.assertEqual(store.handle(db, fields), expected)
                    self.assertFalse(db.in_transaction)
            self.assertEqual(denied, [])
            self.assertEqual(db.total_changes, 0)
            db.set_authorizer(None)
        self.assertEqual(self.rows(), before)

    def test_denied_completion_insert_rolls_back_result_insert(self):
        self.request("lookup")
        inserts = []

        def deny_completion(action, table, column, database, trigger):
            if action == sqlite3.SQLITE_INSERT:
                inserts.append(table)
                if table == "q45_completions":
                    return sqlite3.SQLITE_DENY
            return sqlite3.SQLITE_OK

        with sqlite3.connect(self.database, isolation_level=None) as db:
            db.execute("PRAGMA foreign_keys=ON")
            store.initialize(db)
            db.set_authorizer(deny_completion)
            with self.assertRaises(sqlite3.DatabaseError):
                store.handle(db, [b"commit", SID.hex().encode(), BINDING.hex().encode(), b"1"])
            self.assertEqual(inserts, ["q45_results", "q45_completions"])
            # SQLite counts the result insertion even though it was rolled back.
            self.assertEqual(db.total_changes, 1)
            self.assertFalse(db.in_transaction)
            db.set_authorizer(None)
        self.assertEqual(self.rows(), ([], []))
        self.assertEqual(self.request("lookup"), [b"empty"])

    def test_conflicting_bit_cannot_replace_result(self):
        first = self.request("commit")
        before = self.rows()
        self.assertEqual(self.request("commit", bit=0), [b"conflict"])
        self.assertEqual(self.request("lookup"), [b"found", *first[1:]])
        self.assertEqual(self.rows(), before)

    def test_conflicting_binding_cannot_replace_result(self):
        first = self.request("commit")
        before = self.rows()
        for binding in (b"different ciphertext", b"different digest", b"different frozen quorum"):
            with self.subTest(binding=binding):
                self.assertEqual(self.request("commit", binding=binding), [b"conflict"])
        self.assertEqual(self.request("lookup"), [b"found", *first[1:]])
        self.assertEqual(self.rows(), before)

    def test_restart_reads_committed_receipt(self):
        first = self.request("commit")
        # Each request launches a new OS process and opens a new connection.
        self.assertEqual(self.request("lookup"), [b"found", *first[1:]])
        self.assertEqual(self.request("commit"), [b"replay", *first[1:]])
        self.assertEqual(tuple(map(len, self.rows())), (1, 1))

    def test_session_identifiers_define_independent_results(self):
        first = self.request("commit")
        other = self.request("commit", sid=b"another session", bit=0)
        self.assertEqual(other[0], b"inserted")
        self.assertNotEqual(first[-1], other[-1])
        self.assertEqual(self.request("lookup"), [b"found", *first[1:]])
        self.assertEqual(self.request("lookup", sid=b"another session"), [b"found", *other[1:]])
        self.assertEqual(tuple(map(len, self.rows())), (2, 2))

    def test_concurrent_identical_writers_insert_once(self):
        self.request("lookup")
        with ThreadPoolExecutor(max_workers=2) as pool:
            replies = list(pool.map(lambda _: self.request("commit"), range(2)))
        self.assertCountEqual([reply[0] for reply in replies], [b"inserted", b"replay"])
        self.assertEqual(replies[0][1:], replies[1][1:])
        self.assertEqual(tuple(map(len, self.rows())), (1, 1))

    def test_concurrent_conflicting_writers_preserve_winner(self):
        self.request("lookup")
        start = threading.Barrier(8)

        def write(bit):
            start.wait(timeout=10)
            return self.request("commit", bit=bit)

        with ThreadPoolExecutor(max_workers=8) as pool:
            replies = list(pool.map(write, (0, 1) * 4))
        self.assertCountEqual([reply[0] for reply in replies],
                              [b"inserted"] + [b"replay"] * 3 + [b"conflict"] * 4)
        winner = next(reply for reply in replies if reply[0] == b"inserted")
        for reply in replies:
            if reply[0] == b"replay":
                self.assertEqual(reply[1:], winner[1:])
        self.assertEqual(self.request("lookup"), [b"found", *winner[1:]])
        self.assertEqual(tuple(map(len, self.rows())), (1, 1))

    def test_inconsistent_result_completion_pairs_fail_closed(self):
        mutations = {
            "missing completion": "DELETE FROM q45_completions",
            "orphan completion": "DELETE FROM q45_results",
            "changed bit": "UPDATE q45_results SET bit=0",
            "changed binding": "UPDATE q45_results SET binding=x'00'",
            "changed receipt": "UPDATE q45_results SET receipt=zeroblob(32)",
            "mismatched completion": "UPDATE q45_completions SET receipt=zeroblob(32)",
        }
        for index, (name, sql) in enumerate(mutations.items()):
            with self.subTest(name=name):
                database = Path(self.directory.name) / f"inconsistent-{index}.sqlite3"
                self.request("commit", database=database)
                with sqlite3.connect(database) as db:
                    db.execute(sql)  # Deliberate corruption through a separate connection.
                before = self.rows(database)
                self.assert_worker_error(b"lookup\t" + SID.hex().encode() + b"\n", database)
                self.assert_worker_error(
                    b"commit\t" + SID.hex().encode() + b"\t" + BINDING.hex().encode() + b"\t1\n", database)
                self.assertEqual(self.rows(database), before)

    def test_unrecognized_schema_and_headers_fail_closed(self):
        mutations = {
            "version": "PRAGMA user_version=999",
            "application": "PRAGMA application_id=123",
            "table": "CREATE TABLE foreign_table(value)",
            "literal underscore": "CREATE TABLE sqliteXforeign(value)",
            "view": "CREATE VIEW foreign_view AS SELECT * FROM q45_results",
            "index": "CREATE INDEX foreign_index ON q45_results(bit)",
            "trigger": "CREATE TRIGGER foreign_trigger AFTER INSERT ON q45_results BEGIN SELECT 1; END",
        }
        for index, (name, sql) in enumerate(mutations.items()):
            with self.subTest(name=name):
                database = Path(self.directory.name) / f"schema-{index}.sqlite3"
                self.request("commit", database=database)
                with sqlite3.connect(database) as db:
                    db.execute(sql)
                before = self.rows(database)
                self.assert_worker_error(b"lookup\t" + SID.hex().encode() + b"\n", database)
                self.assertEqual(self.rows(database), before)
        unrelated = Path(self.directory.name) / "unrelated.sqlite3"
        with sqlite3.connect(unrelated) as db:
            db.execute("CREATE TABLE existing(value)")
            db.execute("INSERT INTO existing VALUES ('keep')")
        self.assert_worker_error(b"lookup\t61\n", unrelated)
        with sqlite3.connect(unrelated) as db:
            self.assertEqual(db.execute("SELECT value FROM existing").fetchall(), [("keep",)])

    def test_schema_is_rechecked_inside_request_transaction(self):
        mutations = {
            "trigger": "CREATE TRIGGER later_trigger AFTER INSERT ON q45_results BEGIN SELECT 1; END",
            "application": "PRAGMA application_id=123",
            "version": "PRAGMA user_version=999",
        }
        for index, (name, sql) in enumerate(mutations.items()):
            with self.subTest(mutation=name):
                database = Path(self.directory.name) / f"revalidation-{index}.sqlite3"
                self.request("lookup", database=database)
                with sqlite3.connect(database, isolation_level=None) as db:
                    store.initialize(db)
                    # A different connection changes the authority after its
                    # initial validation but before the request transaction.
                    with sqlite3.connect(database) as other:
                        other.execute(sql)
                    for fields in ([b"lookup", SID.hex().encode()],
                                   [b"commit", SID.hex().encode(), BINDING.hex().encode(), b"1"]):
                        with self.subTest(command=fields[0]):
                            with self.assertRaises(store.StoreError):
                                store.handle(db, fields)
                            self.assertFalse(db.in_transaction)
                self.assertEqual(self.rows(database), ([], []))

    def test_malformed_and_oversized_requests_never_mutate_authority(self):
        self.request("commit")
        before = self.rows()
        malformed = [
            b"", b"lookup\t61", b"unknown\t61\n", b"lookup\t61\textra\n",
            b"lookup\t\n", b"lookup\t0\n", b"lookup\tgg\n", b"lookup\t61  \n",
            b"lookup\t\xff\xff\n", b"lookup\t" + b"61" * 513 + b"\n",
            b"commit\t61\t62\n", b"commit\t61\t\t1\n",
            b"commit\t61\t62\t01\n", b"commit\t61\t62\t2\n",
            b"commit\t61\t" + b"62" * (store.MAX_BINDING_BYTES + 1) + b"\t1\n",
            b"x" * (store.MAX_REQUEST_BYTES + 1) + b"\n",
        ]
        for index, request in enumerate(malformed):
            with self.subTest(case=index):
                self.assert_worker_error(request)
        self.assertEqual(self.rows(), before)


if __name__ == "__main__":
    unittest.main()
