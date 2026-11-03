# Primus ThFHE preprocessing fail-closed research overlay

**Date:** 2026-11-03 • **Tracking:** #49 (P1), #47 (native dependencies),
#45 (research). This is **not** a TclMesh runtime change or evidence of
production cryptographic conformance.

## Input and scope

A source-pinned, disposable **modified Primus `thfhe` variant** is used,
not the historical `serendipity-crypto/primus-fhe` `ajax` revision
required by original Ajax. The only accepted source is:

- Repository: [primus-labs/primus-fhe](https://github.com/primus-labs/primus-fhe)
- Commit: `a0d075d9ec055fb8652925fee65768a14a627cfa`
- File: `mpc/src/dn.rs`
- Expected Git blob: `da2e4457a9f7d8f434815d8645c4b4b1b8c0eded`

The author source's [`next_triple_z2k`](https://github.com/primus-labs/primus-fhe/blob/a0d075d9ec055fb8652925fee65768a14a627cfa/mpc/src/dn.rs#L1298-L1304)
returns `(0,0,0)` on a missing triple; its
[`mul_element_wise_z2k`](https://github.com/primus-labs/primus-fhe/blob/a0d075d9ec055fb8652925fee65768a14a627cfa/mpc/src/dn.rs#L1786-L1810)
uses the triple as randomness for `a-r, b-s` and then opens those
masked differences. When the pool is exhausted, the inputs to that
opening are conditionally unmasked. No running attack or actual data
loss is claimed.

## What the research patch changes

The isolated `tools/threshold_primus_preprocessing_patch.py` performs
**exact text and Git-blob checked** rewriting only of `mpc/src/dn.rs`
inside a clean checkout. It does not change TclMesh production source.

1. Replace the silent underflow fallback with a checked `VecDeque::pop_front`
   that panics on exhaustion. It can never invent a missing zero triple.
2. Require `available >= batch_size` **before** consuming any triples,
   computing masked inputs or calling `open_secrets_z2k`; refuse partially
   available batches.
3. Parse the entire preprocessing file into a temporary vector, reject
   empty/malformed/extra-field/partial lines, then **atomically** extend
   the holder's triple pool. Missing files fail immediately.
4. Preserve the original import's decimal `u128` parsing with explicit
   narrowing to `u64`. Pinned upstream fixtures contain values above
   `u64::MAX`; replacing the parser with `u64` parsing would
   inadvertently reject legitimate author fixtures and is not a valid fix.
5. Add seven Rust tests covering the empty, malformed, partial and
   128-bit fixtures, **actual missing/truncated file reads**,
   shortage-before-open, and exhausted-buffer behavior. The file-loading
   helper returns `Result` for native tests; its production-source research
   wrapper fails on errors before mutating the triple buffer.

The patch and synthetic test fixtures are **not** formal proofs of
privacy or proper Beaver triple generation. Even a fully populated file
could contain biased, repeated, adversarial, or correlated triples;
maliciously secure authenticated preprocessing is a separate obligation.

## Reproduction in CI

The dedicated [workflow](../.github/workflows/threshold-primus-preprocessing.yml)
performs three progressively stronger **non-cryptographic** checks:

- Python synthetic source-rewrite/negative tests, with an exact source-pin
  gate that refuses wrong, dirty or symlinked checkouts.
- Execute Rust unit tests **extracted from the actual patched module**
  with `rustc --test`. This tests the inserted parsing/exhaustion
  primitives without requiring the historical FHE dependencies or any
  networked participant.
- **Kill two native Rust negative mutants:** one intentionally disables the
  pre-opening batch-capacity guard, and one restores the zero-triple
  exhaustion fallback. Both altered helper binaries must compile but
  **fail their corresponding tests**. Captured failure logs are retained as
  negative-control evidence. A negative-mutant failure is not a production
  cryptographic attack or a security proof.
- Pin `primus-labs/concrete-ntt` to
  `cdeba793e46208320b30d78be19f7be78d49016a` in a separately
  archived temporary patch; generate an exact Cargo.lock; attempt
  `cargo test --package mpc --lib tclmesh_research_preprocessing_tests
  --locked` against the public modified source.

The workflow archives the research patch, complete package lock, toolchain
versions, unit-test/build logs and explicit
`cryptographic_release_admitted=false`. It does **not** run FHE
encryption, key generation, threshold decryptors, malicious networked
participants or any TclMesh release. Any failed step is a red research CI
result, not a cryptographic exploit.

Exact replay for a clean public-source checkout:

```bash
git clone --depth 1 --single-branch --branch thfhe \
  https://github.com/primus-labs/primus-fhe.git primus-research
test "$(git -C primus-research rev-parse HEAD)" = \
  a0d075d9ec055fb8652925fee65768a14a627cfa

# Commands execute from the TclMesh checkout
python3 -m unittest discover -s tests \
  -p 'test_threshold_primus_preprocessing_patch.py' -v
python3 tools/threshold_primus_preprocessing_patch.py \
  --source primus-research --report preprocessing-source-only.json
git -C primus-research diff -- mpc/src/dn.rs
```

For full native tests and dependency pinning, use the exact tracked CI
workflow; do not manually run scripts modifying host-wide `iptables` or
`tc`, and never use production secret keys or plaintexts.

## Security boundary and remaining work

A successful isolation test proves only that the **modified research
source** refuses the tested failure paths. It **does not** prove that
production Ajax or Primus is secure or that the modifier is generally
safe against malicious participants.

Before any cryptographic release claim: run actual FHE DKG and
decryption with independently held shares, check all ten three-holder
subsets under an immutable five-holder keyset, analyze two-holder
coalition confidentiality (not just API refusal), verify malicious
contributions or MPC transcripts, ensure authenticated recipient-only
delivery, and test replay, epochs, noise and corrupt preprocessing.

`cryptographic_release_admitted=false` at every source/replay stage.

## Opening-boundary regression

The workflow fetches the exact Primus commit directly. It compiles the
extracted, patched loader, triple consumer, and complete multiplication method
with Rust 1.85.1 and no Cargo dependencies. The probe substitutes an in-process
opening spy and a small-ring addition stub for the networking and field code.
Run each case in its own process with a timeout. The valid fixture must reach
the spy with masked inputs and return the expected synthetic product.

The rejection cases cover a missing file, an empty file, a truncated row
after a valid row, a malformed row before a valid row, a short batch, and an
exhausted pool after one successful multiplication. They require the expected
error, zero attempted openings for the failing operation, no returned product,
and the expected remaining pool size. Both short-batch and exhausted cases
also run against a mutant that removes the batch guard and restores the
upstream zero fallback. The same oracle must reject the mutant specifically
because the original synthetic operands reached the opening spy.

### Single oracle (fix for the stale PR #50 oracle)

At `dfe5f8e` the loader panicked with `Missing, malformed, or empty Z2k
preprocessing file`, while the probe expected `Missing Z2k preprocessing file`
or `Malformed or empty Z2k preprocessing file`. Neither prefix matched, so the
hosted step would have stopped at `missing` before the exhaustion mutants ran;
the Python tests only checked source text and passed regardless. Now:

- `threshold_primus_preprocessing_patch.py` defines each panic prefix once
  (`UNREADABLE_FILE`, `MALFORMED_FILE`, `INSUFFICIENT`, `EXHAUSTED`). The
  injected Rust interpolates them, and the loader splits
  `io::ErrorKind::InvalidData` (malformed, empty, non-UTF-8) from every other
  I/O error (missing, unreadable).
- `threshold_primus_opening_harness.py` holds the only scenario table
  (`SCENARIOS`, `EXHAUSTION`). It renders the Rust oracle from that table, and
  `--run` compiles both variants and checks every matrix cell's exit status
  (`0` fixed; `49` zero-fallback on each exhaustion scenario). CI runs that
  command and adds no expectations of its own.
- The unit tests render probes from a clean-room fixture (TclMesh-authored
  Beaver multiply with the upstream masking/opening order; no upstream code
  vendored) and, where `rustc` exists, run the whole matrix natively. An
  oracle-sensitivity test drifts the loader message back to the PR #50 text
  and requires exactly `fixed/missing` to fail with exit `51`.

### Multi-party shortage

`multiparty-shortage` runs three parties as threads over a simulated
broadcast transport. An opening needs every party's masked shares, and each
receive is bounded by a 500 ms deadline. Party 2 holds one triple fewer than
the batch of two. The fixed probe requires all of the following: party 2 aborts
with `INSUFFICIENT` before sending and keeps its triple; every peer aborts on
the timeout; no party completes an opening or returns a product; and the
whole run finishes within `(N + 1) * timeout`. The zero-fallback mutant must
instead deliver party 2's unmasked operands to a peer (exit `49`). The
transport is a simulation, not Primus networking. It shows that the patched
methods abort cleanly when composed with a deadline-bounded opening, not that
upstream networking has such a deadline.

### Local native receipt (this revision)

- Primus input SHA-256 `224241f432cf4d35d61d12fdc40a6186cb692390e619f79bac6075ad7ac0612f`
  (blob `da2e4457a9f7d8f434815d8645c4b4b1b8c0eded`).
- rustc 1.97.0: all 11 cells matched (8 fixed `PASS`; 3 mutant exit `49`).
  The isolated helper tests passed, and both helper mutants failed.
- Python: 18 patch/oracle tests passed, and 102 `test_threshold*.py` tests passed.
- The pinned 1.85.1 hosted run and its `opening-probe.json` receipt remain the
  acceptance evidence for this PR.

The spy observes calls at the opening boundary. It does not exercise peer
coordination, network delivery, plaintext decryption or the protocol's
security assumptions beyond the simulated transport above. Original Ajax additionally requires the historical
dependency pin from #47. The modified Primus Cargo stage resolves a fresh
lockfile and captures it as evidence, so its result is exploratory until a
reviewed lockfile and toolchain are replayed. Cryptographic release remains
disabled.
