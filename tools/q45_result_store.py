"""SQLite result authority for the inert SPEC_4of5 actor experiment.

One process handles one request on stdin. The actor supplies a locally bound
opaque transcript token; this helper does not authenticate parties or verify
cryptographic shares. Keep one database namespace for the lifetime of its SIDs.
"""
from __future__ import annotations

import argparse
import hashlib
import os
import sqlite3
import sys

APPLICATION_ID = 0x51343552
SCHEMA_VERSION = 1
MAX_REQUEST_BYTES = 2 * 1024 * 1024
MAX_SID_BYTES = 512
MAX_BINDING_BYTES = 512 * 1024
DOMAIN = b"tclmesh-q45-result-v1\0"
TABLES = {
    "q45_results": """CREATE TABLE q45_results (
        sid BLOB PRIMARY KEY NOT NULL CHECK(typeof(sid)='blob'),
        binding BLOB NOT NULL CHECK(typeof(binding)='blob'),
        bit INTEGER NOT NULL CHECK(typeof(bit)='integer' AND bit IN (0,1)),
        receipt BLOB NOT NULL UNIQUE CHECK(typeof(receipt)='blob' AND length(receipt)=32),
        UNIQUE(sid, receipt)
    )""",
    "q45_completions": """CREATE TABLE q45_completions (
        sid BLOB PRIMARY KEY NOT NULL,
        receipt BLOB NOT NULL UNIQUE,
        FOREIGN KEY(sid, receipt) REFERENCES q45_results(sid, receipt)
    )""",
}


class StoreError(Exception):
    """An unrecognized or inconsistent authority must never look empty."""


def validate_schema(db: sqlite3.Connection) -> None:
    # This is a dedicated, versioned authority, not an arbitrary application DB.
    # Headers alone cannot distinguish the expected tables from empty views or
    # tables with missing uniqueness/FK constraints. Reject triggers as well.
    if (db.execute("PRAGMA user_version").fetchone()[0] != SCHEMA_VERSION
            or db.execute("PRAGMA application_id").fetchone()[0] != APPLICATION_ID):
        raise StoreError("unsupported_schema")
    actual = {
        (kind, name): " ".join(sql.split()) if sql else None
        for kind, name, sql in db.execute(
            "SELECT type, name, sql FROM sqlite_master WHERE name NOT GLOB 'sqlite_*'"
        )
    }
    expected = {("table", name): " ".join(sql.split()) for name, sql in TABLES.items()}
    if actual != expected:
        raise StoreError("unrecognized_schema")


def receipt_id(sid: bytes, binding: bytes, bit: int) -> bytes:
    return hashlib.sha256(
        DOMAIN + len(sid).to_bytes(8, "big") + sid
        + len(binding).to_bytes(8, "big") + binding + bytes([bit])
    ).digest()


def initialize(db: sqlite3.Connection) -> None:
    version = db.execute("PRAGMA user_version").fetchone()[0]
    application = db.execute("PRAGMA application_id").fetchone()[0]
    if version == SCHEMA_VERSION and application == APPLICATION_ID:
        validate_schema(db)
        return
    if version != 0 or application != 0:
        raise StoreError("unsupported_schema")
    db.execute("BEGIN IMMEDIATE")
    try:
        # A second initializer may have won while this connection waited.
        version = db.execute("PRAGMA user_version").fetchone()[0]
        application = db.execute("PRAGMA application_id").fetchone()[0]
        if version == SCHEMA_VERSION and application == APPLICATION_ID:
            validate_schema(db)
            db.commit()
            return
        if version != 0 or application != 0 or db.execute(
            "SELECT 1 FROM sqlite_master WHERE name NOT GLOB 'sqlite_*' LIMIT 1"
        ).fetchone():
            raise StoreError("unrecognized_database")
        for sql in TABLES.values():
            db.execute(sql)
        db.execute(f"PRAGMA application_id={APPLICATION_ID}")
        db.execute(f"PRAGMA user_version={SCHEMA_VERSION}")
        validate_schema(db)
        db.commit()
    except BaseException:
        db.rollback()
        raise


def read_record(db: sqlite3.Connection, sid: bytes):
    row = db.execute(
        "SELECT binding, bit, receipt FROM q45_results WHERE sid=?", (sid,)
    ).fetchone()
    event = db.execute(
        "SELECT receipt FROM q45_completions WHERE sid=?", (sid,)
    ).fetchone()
    if row is None:
        if event is not None:
            raise StoreError("orphan_completion")
        return None
    binding, bit, receipt = row
    if (not isinstance(binding, bytes) or not 0 < len(binding) <= MAX_BINDING_BYTES
            or type(bit) is not int or bit not in (0, 1)
            or not isinstance(receipt, bytes)
            or receipt != receipt_id(sid, binding, bit)
            or event != (receipt,)):
        raise StoreError("inconsistent_record")
    return binding, bit, receipt


def handle(db: sqlite3.Connection, fields: list[bytes]) -> bytes:
    if not fields or fields[0] not in (b"lookup", b"commit"):
        raise StoreError("invalid_request")
    command = fields[0]
    if len(fields) != (2 if command == b"lookup" else 4):
        raise StoreError("invalid_request")
    sid = decode_hex(fields[1], MAX_SID_BYTES)
    binding = None
    bit = None
    if command == b"commit":
        binding = decode_hex(fields[2], MAX_BINDING_BYTES)
        if fields[3] not in (b"0", b"1"):
            raise StoreError("invalid_bit")
        bit = int(fields[3])

    db.execute("BEGIN" if command == b"lookup" else "BEGIN IMMEDIATE")
    try:
        # Recheck under this transaction's snapshot/write reservation, so a
        # concurrent schema change cannot slip between validation and insertion.
        validate_schema(db)
        row = read_record(db, sid)
        if command == b"lookup":
            db.commit()
            return b"empty" if row is None else encode_record(b"found", row)
        if row is not None:
            db.commit()
            if row[:2] == (binding, bit):
                return encode_record(b"replay", row)
            return b"conflict"
        receipt = receipt_id(sid, binding, bit)
        db.execute(
            "INSERT INTO q45_results(sid,binding,bit,receipt) VALUES (?,?,?,?)",
            (sid, binding, bit, receipt),
        )
        db.execute(
            "INSERT INTO q45_completions(sid,receipt) VALUES (?,?)", (sid, receipt)
        )
        db.commit()
        # No reply is produced until FULL-synchronous SQLite COMMIT returns.
        return encode_record(b"inserted", (binding, bit, receipt))
    except BaseException:
        db.rollback()
        raise


def decode_hex(value: bytes, maximum: int) -> bytes:
    if not value or len(value) > maximum * 2 or len(value) % 2:
        raise StoreError("invalid_encoding")
    try:
        decoded = bytes.fromhex(value.decode("ascii"))
    except (ValueError, UnicodeError) as exc:
        raise StoreError("invalid_encoding") from exc
    if decoded.hex().encode() != value.lower():
        raise StoreError("noncanonical_encoding")
    return decoded


def encode_record(status: bytes, row) -> bytes:
    binding, bit, receipt = row
    return b"\t".join((status, binding.hex().encode(), str(bit).encode(), receipt.hex().encode()))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--db", required=True)
    args = parser.parse_args()
    os.umask(0o077)
    try:
        request = sys.stdin.buffer.readline(MAX_REQUEST_BYTES + 1)
        if not request.endswith(b"\n") or len(request) > MAX_REQUEST_BYTES:
            raise StoreError("oversized_or_unterminated_request")
        with sqlite3.connect(args.db, timeout=5, isolation_level=None) as db:
            db.execute("PRAGMA foreign_keys=ON")
            # WAL supports a single transactional authority across local writers.
            if db.execute("PRAGMA journal_mode=WAL").fetchone()[0] != "wal":
                raise StoreError("wal_unavailable")
            db.execute("PRAGMA synchronous=FULL")
            if db.execute("PRAGMA synchronous").fetchone()[0] != 2:
                raise StoreError("durability_unavailable")
            initialize(db)
            response = handle(db, request[:-1].split(b"\t"))
        sys.stdout.buffer.write(response + b"\n")
        sys.stdout.buffer.flush()
        return 0
    except (StoreError, sqlite3.Error, OSError, ValueError):
        # No filesystem paths, transcript bytes or Python tracebacks on the wire.
        sys.stdout.buffer.write(b"error\n")
        sys.stdout.buffer.flush()
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
