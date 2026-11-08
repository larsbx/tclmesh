# INV-Q9 actor restart acceptance — 2026-11-08

These are fresh local execution receipts for published source commit
`b675f2bd8d33113105057869c397e0ab6772c798` and tree `ad04bf6d1fa9d17d7398f599cb9962a5a9e8b777`.
The source checkout was clean. Its revision and every tracked-file SHA-256
remained unchanged throughout the run. This directory is added afterward as
an evidence-only change; all previously validated source files remain identical.

## Results

- `acceptance.json`: all 11 required commands exited successfully.
- `actor-receipt.json`: all 10 actor checks passed, including nine adapter
  EUnit tests, two actor-kill windows, two whole-BEAM SIGKILL windows, stale
  writers, a forced identical race, unavailable storage, an actually expired
  deadline after a lost helper reply, and a compiled notification mutant.
- Both whole-BEAM writers exited with signal 9. Independent SQLite observers
  retained one original bit-1 result and one logical completion; the original
  transcript and receipt hash matched. Data version stayed 2 to 2 across
  fresh-process recovery and identical/conflicting retries.
- The compiled mutant failed specifically with `duplicate_completion,2`.
- Python threshold regression suite: 181 tests passed, no skips. This includes
  15 persistence tests, no-DML retry controls, atomic rollback, schema/header
  revalidation, and eight mixed writers yielding one insertion, three replays,
  and four conflicts.
- Lean 4.35.0 build and axiom audit passed: 2,624 declarations, 918 theorems,
  standard axioms only. The full integrated build has 24 targets.
- Quint 0.33.1 passed five restart scenarios and 1,000 bounded traces of at most
  12 steps, seed `0x45`, without a guarded invariant violation.
- Existing ceremony acceptance passed with all nine compiled transition
  mutants rejected. The 640-vector toy replay plus four malformed probes and
  P2b adversarial characterization passed.

## Runtime and evidence scope

Commands, versions, source hashes, output hashes, and timestamps are in the two
receipts. Named text files contain the corresponding unedited command output.
The actor subdirectory includes the crash markers, recovery logs, and generated
lost-response wrapper. Temporary absolute paths in these records describe the
execution environment; regenerate the wrapper by running the committed runner.

Lean/Lake used the included `proc_exe_compat.c` executable-discovery shim.
It translates only the current process's own `/proc/<pid>/exe` lookup to
`/proc/self/exe`; it does not alter proof checking. The loaded shim binary had
SHA-256 `f7556d979b6f58412145446f5452ed4ab1d07b1ca00473cad661b755c6eea8ea`.
OTP and the SQLite helpers ran without this preload. OTP 25 / ERTS 13.2.2.5
came from relocated official Ubuntu packages. Rust was available for the two
native fixture tests, so the Python suite had no runtime-related skips.

The legacy adversarial command prints a historical source revision inside its
output. The enclosing `acceptance.json` identifies the actual commit executed
here. Those counterexamples remain research-only insecurity evidence.

These checks concern local process crashes with one preserved SQLite authority.
They do not establish host power-loss tolerance, exactly-once external message
delivery, universal implementation refinement, or malicious threshold security.
No operator-server testbank was dispatched. See
[the durable-result contract](../../../../docs/threshold-q45-durable-result.md)
for assumptions and reproduction commands.
