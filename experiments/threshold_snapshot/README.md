# Pinned native reconstruction probe

This is a research experiment for Issue #36, **not** a TclMesh backend. It uses
the official Zama threshold-fhe snapshot
`c668fdd32a33270fc3ad2fd92b49267b734463dd` and its actual Rust sharing and
reconstruction implementations. The test scalars and RNG seeds are public
fixtures. No FHE key generation or ciphertext decryption is performed.

This is the runner's default `--candidate zama-snapshot`. A separate
[`fhenix-paper` experiment](../threshold_fhenix/README.md) has its own fixed
source pin, overlay and test-name set; results cannot be cross-attributed.

| Native test | What it checks |
| --- | --- |
| All six degree-one raw-share pairs | Each pair reconstructs the fixture scalar using `RevealOp::reconstruct(1)` |
| All four degree-one honest triples | Each triple completes asynchronous robust opening at `n=4,degree=1,f_byz=1` |
| Two degree-one responses | The robust-opening API returns pending, despite raw-pair reconstruction being possible |
| All four degree-two raw-share triples | Each triple reconstructs using `RevealOp::reconstruct(2)` |
| Degree-two robust opening | Both native sync/async implementations reject `n=4,degree=2` for fault bounds one **and** two |
| One corrupted raw share among four | The degree-one asynchronous opening recovers the original fixture scalar |

This demonstrates that an API's response requirement and the underlying raw-share
access structure differ. It does not demonstrate an attack on KMS ciphertexts,
identify KMS v0.14.2's key-sharing degree, or prove confidentiality. The degree-two
failures concern these robust-opening algorithms, not every possible 3-of-4
scheme. A malicious-secure protocol with abort and verifiable contributions is
a separate candidate; it is not implemented by this probe.

Raw-share error correction is also different from independent public verification
of a cryptographic partial contribution. These tests have no participant
signatures, decryption-share proofs, recipient ciphertexts, production keys,
independent holder processes or durable release state.

## Reproduce

Install Rust/Cargo and Protocol Buffers `protoc`. Start with the exact official
snapshot; fetch its locked Cargo dependencies separately. The recorded run used
Rust/Cargo 1.93.1 and protoc 3.21.12, with unoptimized test profiles.

```bash
git clone https://github.com/zama-ai/threshold-fhe.git /tmp/threshold-fhe-source
git -C /tmp/threshold-fhe-source --no-replace-objects checkout --detach \
  c668fdd32a33270fc3ad2fd92b49267b734463dd
cargo fetch --locked --manifest-path /tmp/threshold-fhe-source/Cargo.toml

# From TclMesh. The build cache must be outside the pinned checkout.
python3 tools/threshold_snapshot_probe.py \
  --source /tmp/threshold-fhe-source \
  --target-dir /tmp/tclmesh-threshold-build \
  > /tmp/threshold-native-probe.json
```

The runner verifies **all 209 tracked files** against the pinned Git objects,
with replacement refs disabled. A wrong pin, modified/missing file, hidden index
mutation, symlink or untracked source fails before native execution. Ignored
files are never copied. The runner copies only verified files to a temporary
build tree, adds the separately hashed test overlay, and invokes locked/offline
Cargo with two build jobs. It checks source identity again afterward and refuses
runs that rewrite copied source or emit unexpected files such as fixture keys.

Only a zero exit, all six exact expected test names and a six-passed/zero-failed/
zero-ignored summary produce `NATIVE_PRIMITIVES_ONLY`. Empty or filtered runs do
not pass. The report always records `cryptographic_release_admitted=false`;
source hashes, tool versions and local test results are not binary attestations
or cryptographic security proofs. The local build environment is not hermetic.
An actual native negative control changes the expected scalar in the raw-pair
test; that test fails, Cargo returns 101, and the runner reports `BLOCKED`/exit 2.

The runner accepts Cargo's `PROTOC` environment variable when protoc is installed
at a custom path. Preparing dependencies is separate from the offline native run.

## Avoid the upstream unit-test constructor

Do **not** substitute `cargo test --lib ...` for this integration overlay.
The pinned upstream `src/tests/helper.rs` has a `#[ctor::ctor]` startup function
that calls `ensure_keys_exist` for test and real parameter fixtures. It executes
before unit-test name filtering. An initial filtered unit-test attempt compiled
but was interrupted during startup; it is **not counted as a passed test** and
its generated fixture output was discarded. The integration overlay builds the
library without `cfg(test)`, avoiding that constructor and its full-key fixture
generation. No `testing` feature is enabled by the runner.

Runner-integrity controls are synthetic and separate from native results:

```bash
python3 -m unittest discover -s tests -p 'test_threshold*.py'
```

See [the backend evaluation](../../docs/threshold-backend-evaluation.md) and
[the native run receipt](../../docs/evidence/threshold-snapshot-native-probe-20261101.json).
