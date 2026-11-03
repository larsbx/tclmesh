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
5. Add Rust tests for the empty, malformed, partial and 128-bit fixtures,
   shortage-before-open, and exhausted-buffer behavior.

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
