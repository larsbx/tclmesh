# Claim durability acceptance boundary

The authority is one shared POSIX filesystem containing the persistent keyset
and its claims. Copying keys to an independent host or restoring an old claims
snapshot does not preserve this authority. Administrators must preserve claims
alongside the keys; the protocol does not coordinate independently administered
hosts or resist an administrator deleting authority state.

## Keyset ownership and alternatives

Each keyset K is assigned exactly one claim authority by the deployment owner.
In this implementation that authority is the single filesystem object mounted
at `TCLMESH_TFHE_KEYS`, together with its durable, append-only `claims/` namespace.
All processes authorized to import for K MUST use that same namespace. Path
strings alone do not establish identity: replicas, copied directories, snapshot
rollbacks and separate mounts with independent storage are not this authority.
The backend's exclusive hard-link creation is its shared compare-and-claim
transaction; local handle-store persistence is not the admission authority.

| Deployment | Owner of K | Acceptance boundary |
| --- | --- | --- |
| Exclusive single-store | One service with exclusive lifetime ownership of K and its authoritative store | Only that service may import; a lock must cover all holders and survive ownership changes. A process-local lock is insufficient. |
| Shared filesystem (implemented) | One owner administers K and one shared claims namespace | Multiple processes and distinct stores transact against the same exclusive-link namespace; durable file and directory syncs precede exposure. |
| Independent hosts (not implemented) | A named shared transactional service or consensus group owns K | Every importer must use its durable unique `(K,C)` constraint, fenced authority membership and recovery protocol. Copied local claims do not implement this. |

The owner must preserve claims for as long as K may verify proofs. Cloning K
without retaining access to its existing authority is unsupported. No backend
can prevent an administrator holding secret keys from running altered code or
forking authority state. `Claims.lean` includes a two-ledger counterexample to
make this assumption explicit; its theorem quantifies over all stores sharing
the one ledger, not over independently created ledgers.

## Claim record and status

The v2 claim has exactly `version`, `keyset`, `context_digest`, `statement`,
`attempt` and `status` fields. The keyset, context and statement are public
identity/statement digests; the attempt is a random identifier. No proof bytes,
ciphertext, plaintext, raw context or secret key is recorded. `status=consumed`
means admission is permanently reserved, including when exposure or its reply
is uncertain. It does not assert that a handle was successfully returned.
Unknown versions, statuses, malformed records and statement mismatches refuse
admission. A linked claim is never deleted or downgraded by recovery.

## Runtime ordering and the Lean model

`Backend::import` verifies and expands the proof, calls `claim`, and only after
`claim` succeeds calls `keep`, which mints the exposed token. The statement
digest includes context, offset, proof width, optional upper bound and word
width. A valid proof for a changed statement cannot reuse a claimed context.

`claim` writes a private temporary record, syncs the record, and links it to the
context's digest name. Exclusive hard-link creation serializes contenders. The
winner removes the temporary name, syncs `claims/`, and then syncs its parent
key directory. Both directory syncs run on every successful claim, including
when another process created `claims/`. Any error propagates before `keep`.
Only the temporary name is removed; a linked claim is never rolled back, even
if a later sync fails. A failure before linking may leave an unreferenced temp
file, which is not an authorization or a consumed context.

`spec/TclMesh/Claims.lean` models an atomic, durable, append-only ledger. It
proves uniqueness of accepted `(keyset, context)` keys, commit-before-expose,
and permanent consumption after interruption or handle destruction. It does
not formalize POSIX syscalls, storage hardware or the Rust refinement. Mapping
a successful runtime claim to the model requires the exclusive-link semantics
and successful file/directory syncs to provide their documented durability.
An import stopped after those syncs and before `keep` maps to `interrupted`.
A lost response maps to `lostAck`; recovery reads an existing handle and is
modeled by `recover`, which cannot create another authorization.
An error after linking but before all syncs exposes no token; whether that
unacknowledged claim survives a power loss is outside the abstract model.

## Reproducible regressions

After building release binaries, run:

```sh
python3 tools/check_claim_durability.py
python3 tools/check_claim_parent_mutant.py
```

The Linux-only test interposer in `tools/claim_sync_probe.c` observes actual
`fsync` and `link` calls of the unmodified native backend. The suite checks:

- record sync before link, then claims-directory sync before parent sync,
  with both newly created and already existing `claims/` directories;
- an injected `EIO` at each sync prevents any token response;
- after linked sync failures, a normal restart still refuses that context;
- `_exit` immediately after the real parent sync, before returning to import,
  produces no response and consumes the context across restart;
- a newly proved changed statement is refused, while a fresh context imports;
- destroying a handle never releases its context;
- two backend processes ready on the same persistent keys race to import:
  exactly one wins. Tcl T-030 separately tests distinct persistent handle
  stores, and T-029 covers restart recovery and destroyed records;
- T-031 exits with status 86 after the handle store committed and before any
  handle response, recovers and decrypts the original handle after restart,
  then destroys it and refuses replay through both the old and a distinct store;
- the published record schema contains only fixed tags, public digests and a
  random attempt identifier; raw context strings cannot leak through records.

The mutation runner removes the parent sync from a temporary source mutation,
rebuilds the backend, requires the ordering assertion to fail, and restores and
rebuilds the correct source. Build failures are not accepted as mutation kills.

These tests exercise real syscalls, failure propagation and process death;
they do not emulate storage power loss or prove a filesystem's crash behavior.
They guard the ordering needed to close the P1 defect, under the stated shared
filesystem and durable-storage assumptions. No production fault-injection
environment variables or hooks are introduced.
