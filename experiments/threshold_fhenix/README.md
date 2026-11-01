# Fhenix paper implementation: native limitation witnesses

This public-fixture experiment evaluates the repository linked by the CCS 2025
paper *High-Throughput Universally Composable Threshold FHE Decryption*:
`FhenixProtocol/thresholdfhe-paper`, pinned at
`19b0f0a5a71b67badb85c3c8715b3eba7e866f79`.
It is not a TclMesh release backend and performs no FHE key generation,
ciphertext decryption or network run.

The paper supplies a promising malicious-security-with-abort framework based on
an authenticated arithmetic black box. That theorem does not by itself certify
the repository's benchmark plumbing or make an additive n-of-n setup any-q-of-n.

## Observed native behavior

| Public fixture | Actual pinned-code behavior |
| --- | --- |
| Final-step own MAC value 0 and three peer values 0 | Returns `ProtocolTransferredData::empty()` |
| Final-step own MAC value 0 and peer values 1,0,0 | Returns the same normal response, although the sum is nonzero |
| Final-step own MAC value 0 with no peer values | Returns the same normal response |
| Fixed additive shares 1,2,4,8 modulo 256 | All four reveal 15; each three-share subset reveals a different value |

The first three tests call `Party::execute_step_five` directly with correctly
bitcode-encoded public integers. The method sums MAC values but never checks the
sum, and exposes no rejection result. This is a direct-method observation: the
tests do not establish a network exploit, bypass of a deployed release gate, or
failure of the paper's ideal authenticated-MPC model. Passing these tests means
the limitation was reproduced, not that a security test approved the code.

The additive test is one deterministic functional witness, not a proof of a
privacy threshold. A three-party execution created anew is not automatically a
valid subset of an existing four-holder keyset.

Additional source-review blockers are the discovery server's centralized full-key
fixture setup and plaintext printing, local benchmark output before its separate
MAC check, absence of a reviewed q-of-n resharing protocol, and lack of a TFHE-rs
wire adapter. The network executable is deliberately not run. No source was
patched or vendored into TclMesh's production backend.

## Reproduce

```bash
git clone https://github.com/FhenixProtocol/thresholdfhe-paper.git /tmp/fhenix-source
git -C /tmp/fhenix-source --no-replace-objects checkout --detach \
  19b0f0a5a71b67badb85c3c8715b3eba7e866f79
cargo fetch --locked --manifest-path /tmp/fhenix-source/Cargo.toml

# From TclMesh; fixed candidate selects both source pin and exact test set.
python3 tools/threshold_snapshot_probe.py --candidate fhenix-paper \
  --source /tmp/fhenix-source --target-dir /tmp/fhenix-probe-build \
  > /tmp/fhenix-native-probe.json
```

The shared runner verifies every source blob, copies verified files into a
temporary tree, adds the hashed overlay and runs the four exact tests using
locked/offline Cargo. It rejects wrong source pins, cross-candidate test output,
untracked source, unexpected fixture files, incomplete runs and failed tests.
`NATIVE_PRIMITIVES_ONLY` always retains `cryptographic_release_admitted=false`.

Do not run the broad upstream test suite as a substitute: it includes an
unbounded LWE test loop and tests that generate complete fixture keys. These
integration tests build the library without executing its unit tests.

See [the receipt](../../docs/evidence/threshold-fhenix-native-probe-20261101.json)
and [the follow-up evaluation](../../docs/threshold-alternatives-followup.md).
