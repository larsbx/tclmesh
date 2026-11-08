# SPEC_4of5 INV-Q9: durable result in the research actor

This extension adds an optional SQLite result authority to the existing
`q45_ceremony` Erlang/OTP `gen_statem`. It addresses the process-crash window
after a result commits and before the actor replies. It is part of the inert
P1 experiment. It does not enable governed threshold release.

## Contract

For each session ID in one preserved database namespace, the first admitted
result commits both an immutable result record and one logical completion
record in one transaction. An identical result submission returns the
original receipt. A different bit, ciphertext, digest, or frozen quorum is
rejected. Neither retry creates a result or completion record. The actor
loads an existing result as terminal on startup, so it does not need to rerun
evaluation, collect partials, or combine again after a committed result.

The P1 admission checks still require five inputs and matching local seals,
four frozen quorum members, four locally bound opaque partials, a result
accepted by the trusted simulated combiner, and admission before the local
phase deadline. Deadline validation is at message processing, as in the
existing reducer; there is no claim that disk I/O finishes before that
deadline. The durable adapter commits only after that reducer has admitted
the result. A failed storage operation never returns a successful result or
emits a completion notification.

A worker timeout is an ambiguous commit outcome: closing its port does not
guarantee that the helper has stopped. Before a result request in an actor
that has not observed completion, the adapter rereads the authority. If the
earlier write committed, it replays that receipt before checking fresh-write
eligibility, even after the former phase deadline. Storage unavailability
is an error, never evidence that the slot is empty.

The receipt binds the session ID, the exact local binding, and the result
bit. The local binding contains the ciphertext bytes, their SHA-256 digest,
and the canonical sorted quorum. The share designation is already a
deterministic function of that quorum. This is a local P1 binding, not an
authenticated distributed setup or transcript-agreement certificate.

## Completion records and notification delivery

`q45_results` has one primary-key slot per session. `q45_completions` has one
primary-key slot per session and a composite foreign key to its result and
receipt. Both are inserted by the same `BEGIN IMMEDIATE` transaction. The
worker uses SQLite WAL with `synchronous=FULL` and returns only after COMMIT.
It validates the dedicated schema and result/receipt/completion consistency
under the transaction before treating a database as a usable authority.

The actor may send `{q45_complete, Sid, Receipt}` to an optional local process
after an inserted commit. That message is a best-effort notification. Only
the writer that inserts the result sends it. Recovery and exact replay do
not send it again.

| Crash boundary | Durable results | Logical completions | Notifications before crash | Additional notifications on replay |
|---|---:|---:|---:|---:|
| After commit, before notification/reply | 1 | 1 | 0 | 0 |
| After notification, before reply | 1 | 1 | 1 | 0 |

These are at-most-once emission tests, not an exactly-once external delivery
protocol. A future delivery service needs its own acknowledged delivery or
idempotent-consumer contract.

## API

The original `start_link/4` and pure `new/5` and `step/3` API retain their
in-memory terminal-rejection behavior. Persistent mode is explicit:

```erlang
Store = q45_result_store:new(DatabasePath, PythonWorkerPath),
{ok, Actor} = q45_ceremony:start_link(
    SessionId, BudgetMs, Evaluate, Combine,
    #{result_store => Store, completion_sink => Observer}),
{ok, Receipt} = q45_ceremony:submit(Actor, SessionId, ResultEvent).
```

`PythonWorkerPath` identifies `tools/q45_result_store.py`; Python 3 with SQLite
is required. The database parent directory must exist. This is a dedicated,
versioned database: unrelated tables, views, triggers, and indexes are rejected.
Session IDs are nonempty binaries up to 512 bytes; ciphertexts are limited to
256 KiB. Existing results return the same receipt bytes.

The test-only `hooks` option supports `after_commit` and `after_completion`
callbacks. Each receives the committed receipt. The first runs after the
SQLite helper exits successfully and before notification or reply. The second
runs after notification and before reply. Acceptance tests block at these
points and terminate the actor or entire BEAM process externally.

## Reproduce

Use Lean 4.35.0, Quint 0.33.1, Python 3 with SQLite, and Erlang/OTP with Crypto
and EUnit. The whole-process kill harness requires POSIX signals.

```sh
python3 -B tools/check_q45_actor_restart.py \
  --receipt q45-restart-results/receipt.json \
  --evidence-dir q45-restart-results
python3 -B -m unittest discover -s tests -p test_threshold_q45_result_store.py -v
python3 -B tools/check_q45_ceremony_mutants.py
python3 -B tools/check_q45_toy_replay.py
cd spec
lake build
lake env lean Audit.lean
cd ..
npm ci --ignore-scripts --no-audit --no-fund --prefix formal/quint
formal/quint/node_modules/.bin/quint test --backend=typescript formal/quint/q45_restart.qnt
formal/quint/node_modules/.bin/quint run --backend=typescript \
  --max-samples=1000 --max-steps=12 --seed=0x45 \
  --invariant=durableInvariant --verbosity=1 formal/quint/q45_restart.qnt
```

The actor runner checks source hashes, Git revision, and worktree status before
and after execution. Missing runtimes and unexecuted required checks are
failures. The ordinary `test` workflow repeats the actor gate and preserves
its receipt and logs. The pre-existing operator-server bank and manual workflow
remain separately scoped; merging this research code does not dispatch them.

## Verification boundary

`TclMesh.Q45Restart.noSecondWriteOrCompletion` proves at most one result write
and one logical completion over arbitrary finite abstract traces.
`recordedRemains` preserves the full original receipt and both counters.
`recoveredIdentical` replays the original receipt even if new eligibility is
false or a different receipt token is proposed. `recoveredConflict` rejects a
different bit or binding. Atomic storage and durable recovery are assumptions.

Quint implements these transitions separately. Its five named scenarios include
overwrite and duplicate-completion counterexamples. The 1,000-trace simulation
is bounded evidence, not exhaustive verification. The actor tests exercise
actual `gen_statem`, SQLite, receipts, crash/restart, races, and malformed helper
responses. These layers do not prove universal implementation refinement.

Every writer for a session must use the same preserved database authority.
Deleting/restoring an older database, splitting the authority across machines,
or bypassing the worker is outside that contract. Tests cover process failure,
not host power loss, disk failure, or filesystem/SQLite correctness. Incomplete
and aborted ceremonies still require their own durable lifecycle contract.

Authentication and authorization remain assumptions of this inert experiment.
Authenticated transcript agreement, verifiable partials, secure key setup,
appropriate parameters, and a malicious-security argument remain necessary.
Known P2b bit-flip and small-offset attacks retain their existing scope.
