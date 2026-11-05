# Q45 Lean and Quint server testbanks

Status: **written, awaiting execution on the operator's server**. These new
banks have had structural validation only. Previous local evidence under
`formal/quint/evidence` covers the earlier models, not these new banks.

The machine-readable inventory is [manifest.json](manifest.json). Every case
has a stable ID, a claim, and an expected outcome. There are **78 cases**
grouped into **22 execution tasks**:

| IDs | Cases | Expected outcome |
| --- | ---: | --- |
| LP001–LP020 | 20 | Lean checks the positive theorem bank and audits its axioms |
| LN001–LN008 | 8 | Lean rejects a deliberately false proposition with the specific `decide`/false diagnostic |
| QC001–QC007, QV001–QV005 | 12 | Existing ceremony/setup Quint scenarios pass |
| QB001–QB022, QS001–QS008 | 30 | New ceremony/setup Quint scenarios pass |
| QI001, QI002, QI004 | 3 | TLC finishes exhaustive safety checking with an empty queue |
| QI003, QI005, QI006 | 3 | TLC produces the specified invariant counterexamples |
| BR001 | 1 | Generated Quint trace matches 20 actual P2b/P1 snapshots; incorrect projection is rejected |
| BR002 | 1 | Existing 640-case honest and altered-partial arithmetic/actor replay matches its declared outcomes |

The new Quint cases include every omitted-holder quorum, incorrect/empty
messages, early and duplicate events, frozen membership, deadlines, terminal
states, cancelling symbolic corruptions, ideal-verifier checks, round
prerequisites, duplicate round messages, out-of-domain values and honest
agreement between both receivers. The ideal verifier is a specification
contract using ghost correctness; no cryptographic verifier is implemented.

## Prepare the server

Use a Linux server with Python 3.10+, Git, Node 22+, Java 21, the exact
`spec/lean-toolchain` version (Lean 4.35.0 via elan), and Erlang/OTP 25+ with
`erl`, `erlc` and Crypto. The service account that runs the bank needs these
executables on its own `PATH`.

Check out the exact reviewed commit of the
`research/spec-4of5-server-testbanks` branch. From that checkout, prepare the
locked Quint dependency:

```sh
npm ci --ignore-scripts --no-audit --no-fund --prefix formal/quint
```

The first Quint/TLC check obtains the pinned Apalache 0.62.4 distribution
if it is absent. For an isolated server, populate the toolchain/npm/Quint
caches before disconnecting. No runtime installation, SSH login, deployment
or test execution is performed by preparing this bank.

The runner preflights the selected suite's versions. The `lean` suite needs
Lean only; `quint` needs Node, locked Quint and Java; `all` additionally needs
Erlang for the concrete replays. The first Lean task runs `lake clean` and
`lake build` so the bank does not silently reuse the previous specification
build.

## Inspect without executing tests

These commands only parse the manifest, inspect files and print a plan:

```sh
python3 -B tools/run_q45_testbanks.py validate --suite all
python3 -B tools/run_q45_testbanks.py plan --suite all
```

They do not launch Lean, Quint, Java, Erlang, or a test subprocess. They
report `structurally_valid_not_executed`, never a proof or test result.

## Execute on your server

Choose a **new** result directory for each run. The runner refuses to
overwrite an earlier receipt. From the repository root:

```sh
python3 -B tools/run_q45_testbanks.py run --suite all --out "$HOME/q45-results/run-001"
```

Or run the two banks separately:

```sh
python3 -B tools/run_q45_testbanks.py run --suite lean --out "$HOME/q45-results/lean-001"
python3 -B tools/run_q45_testbanks.py run --suite quint --out "$HOME/q45-results/quint-001"
```

`lean` has 28 cases; `quint` has 48. `all` also runs the two concrete replay
cases, for 78 total. `--seed` defaults to `0x45` for Quint scenarios and the
generated trace; BR002 retains the original four fixed arithmetic seeds.
`--timeout` defaults to 900 seconds per subprocess and can be increased on
a slower server.

The [manual workflow](../../.github/workflows/q45-formal.yml) targets only
an operator-provisioned self-hosted runner labeled `linux`, `x64` and
`q45-formal`. It requires an exact commit SHA and a selected suite. It does
not trigger on a push or pull request, and it does not fall back to a hosted
runner. It explicitly installs the locked npm test dependency on the chosen
server, then runs the bank and uploads that run's evidence to the repository.
The direct CLI above does not require GitHub Actions or a runner registration.
The repository's other existing workflows are separate from this bank.

## Read the results

Each output directory contains an atomic `receipt.json` and separate stdout
and stderr logs for every preflight/task command. The receipt records:

- exact Git revision, dirty-checkout flag and source hashes;
- hostname, platform, Python and prerequisite version output;
- command arguments, working directory, elapsed time and log hashes;
- every selected case, its expected outcome and observed status;
- failed, interrupted and not-run cases, even if execution stops early.

Exit 0 means all selected **expectations** were satisfied. It does not mean
that the deliberately false properties hold: LN cases must fail to compile,
and the three negative QI cases must exhibit actual invariant violations.
A parse/type/import error, tool-launch failure or timeout is a failure, not
a valid counterexample. The runner stops at the first unexpected outcome,
retains incomplete cases as `not_run`, stops child model-checker processes
on timeout/interruption, and rejects a run if its source files change.

The Lean bank compiles outside the default `TclMesh` library target. Its
custom audit counts exactly 20 bank theorems and permits only the standard
Lean axioms. Each positive declaration is explicitly checked. The eight
negative fixtures compile separately after the positive prerequisite; an
arbitrary compiler error cannot satisfy their expected rejection.

Keep the server receipt and logs with the exact reviewed revision for the
next acceptance review. No result from this new bank is claimed until that
server run exists. This bank establishes acceptance-model evidence only;
cryptographic soundness, malicious-secure FHE and universal implementation
refinement remain open. It enables no governed release and merges no
protocol changes.
