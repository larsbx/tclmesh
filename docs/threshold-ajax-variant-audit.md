# Ajax versus Primus ThFHE: exact-source variant boundary

**Review:** 2026-11-03 • **Tracking:** TclMesh #45, #47 • **Cryptographic acceptance:** **BLOCKED**

This source comparison resolves a specific supply-chain question raised after
[PR #46](https://github.com/larsbx/tclmesh/pull/46): whether the extant
`primus-labs/primus-fhe` **thfhe** branch can be silently substituted for
the now-unresolved historical `serendipity-crypto/primus-fhe` **ajax** branch.
**It cannot be treated as equivalent without additional cryptographic review.**
This is a statement about missing equivalence evidence, not an allegation of
a security break in either paper or implementation.

## Exact source observations

- The separately published [Ajax source](https://github.com/primus-labs/Ajax/tree/64b4f80fb90da3096e03af200d3c95abe865a987)
  is pinned at `64b4f80fb90da3096e03af200d3c95abe865a987`.
  Its `thfhe/Cargo.toml` imports `algebra`, `lattice` and `fhe_core`
  from `serendipity-crypto/primus-fhe` Git branch `ajax`. That historical
  revision has **not** been authenticated or recovered.
- The distinct [Primus `thfhe` branch](https://github.com/primus-labs/primus-fhe/tree/a0d075d9ec055fb8652925fee65768a14a627cfa)
  is pinned at `a0d075d9ec055fb8652925fee65768a14a627cfa`.
  Its FHE crates are local workspace paths. This is a plausible
  **experimental overlay input**, not the old Ajax dependency revision.
- Six of seven selected source files have distinct Git blob IDs across
  the two pins; `thfhe/src/lib.rs` is exactly identical. Corresponding
  blob identities are fixed in `tools/threshold_ajax_variant_audit.py`.
  A shared lib.rs does not establish unchanged implementation behavior.

| File | Ajax Git blob (prefix) | Primus `thfhe` blob (prefix) | Security-relevant observation |
| --- | --- | --- | --- |
| `thfhe/src/distdec.rs` | `5925f3a7` | `d8c5086c` | Different masked-intermediate reveal paths: Ajax routes this intermediate to party 0; alternative uses `reveal_slice_to_all_z2k`. **Neither observation proves leakage or equivalence.** |
| `thfhe/src/key_gen.rs` | `07b90b77` | `a1b41a0c` | Changed noise-parameter APIs, including `noise_distribution_div_count` versus `noise_distribution_multi_party`. **Noise-security reduction and compatibility are not checked.** |
| `thfhe/src/secret_key.rs` | `6074e6ff` | `675d678e` | Slight arithmetic/code changes; correctness comparison needed. |
| `thfhe/examples/thfhe.rs` | `aaf545b0` | `a27df6b1` | Example launcher differs; both examples use only a designated `t+1` group. |
| `mpc/src/dn.rs` | `275ff6b1` | `da2e4457` | Different DN07 backend sources, requiring independent message and MAC model review. |
| `thfhe/Cargo.toml` | `1c9923eb` | `9060018b` | Git branch imports versus workspace paths; **not the same dependency graph**. |
| `thfhe/src/lib.rs` | `30d8e8fa` | `30d8e8fa` | Identical bytes at this path only. |

The alternative's `algebra/Cargo.toml` further selects
`primus-labs/concrete-ntt` branch `dev` without a manifest revision pin.
The branch's publicly observed head was
`cdeba793e46208320b30d78be19f7be78d49016a` on 2026-11-03,
which is **not** a frozen historical dependency. Commit and registry
dependencies must all be locked before native benchmark claims.

## Reproduction

The [dedicated GitHub Actions job](../.github/workflows/threshold-ajax-variant.yml)
performs a strict exact-head clone of both public sources, then executes
this audit without rebuilding or running any FHE backend.

```sh
git clone --single-branch --branch main https://github.com/primus-labs/Ajax.git ajax
git clone --single-branch --branch thfhe https://github.com/primus-labs/primus-fhe.git primus
test "$(git -C ajax rev-parse HEAD)" = 64b4f80fb90da3096e03af200d3c95abe865a987
test "$(git -C primus rev-parse HEAD)" = a0d075d9ec055fb8652925fee65768a14a627cfa

python3 tools/threshold_ajax_variant_audit.py --ajax ajax --alternative primus
# SOURCE_VARIANTS_DIFFER_REVIEW_REQUIRED, not an acceptance decision

python3 tools/threshold_ajax_variant_audit.py --ajax ajax --alternative primus \
  --require-cryptographic-release
# Must exit 2. No cryptographic release can be authorized by the source auditor.
python3 -m unittest discover -s tests -p 'test_threshold_ajax_variant_audit.py'
```

Run the Python commands from the TclMesh root. The script checks exact Git
HEAD, source cleanliness, committed bytes, and pinned Git blob hashes,
and reports full SHA-256 for the inspected files. Its negative gates can be
reproduced in isolation with **synthetic Git fixtures**. The hosted workflow's
public-source receipt can show **source identity and divergence only**;
it cannot authenticate an author signature or certify a reduction.

## Acceptance implications

1. **Historical reproduction:** locate and authenticate the actual missing
   `primus-fhe/ajax` dependency revision and produce a full transitive lock.
   This is the preferred path for reproducing original author benchmarks.
2. **Explicit alternative experiment:** if the `thfhe` branch is used, mark
   it `modified_primus_overlay` rather than Ajax's original implementation;
   compare the changed noise distributions, masked MPC opening visibility,
   transcript flow and FHE parameter fingerprints *before* any confidence claim.
3. **Separate actual cryptography:** genuinely distribute a five-holder key,
   run all ten valid 3-holder subsets and all ten insufficient 2-holder
   subsets on identical key material; test corrupt/malformed contributions,
   the exact active-adversary bounds and recipient-only release. The prior
   combinatorial planner only enumerates these sets.
4. **Fail closed:** `cryptographic_tests_executed=false`,
   `candidate_dependency_equivalence_established=false`,
   `candidate_security_equivalence_established=false` and
   `cryptographic_release_admitted=false` remain mandatory audit outcomes.
   In particular, none of these tools can satisfy TclMesh's runtime
   cryptographic-threshold conformance gate.

## Separate native build experiment: modified Primus variant only

A second [dedicated workflow](../.github/workflows/threshold-primus-native.yml)
attempts an isolated **`cargo check`** of the distinct Primus `thfhe` source
tree. It does **not** execute distributed DKG or decryption, does **not**
recover the missing Ajax dependency, and is **not** a compatibility claim.

It checks out exactly `a0d075d9ec055fb8652925fee65768a14a627cfa`,
edits *only the temporary public research checkout* to replace
`concrete-ntt`'s floating `dev` ref with observed exact commit
`cdeba793e46208320b30d78be19f7be78d49016a`, and saves the
patch. It generates and archives a complete Cargo.lock, records
`rustc -Vv`, `cargo -V` and build logs, then executes
`cargo check --package thfhe --example thfhe --locked`.

This is intentionally a **modified overlay compilation experiment**,
and must not be reported as reproduction of the original Ajax author's
benchmark or as TclMesh cryptographic acceptance. The run remains
`cryptographic_release_admitted=false` regardless of its result.
Build success would not establish semihonest confidentiality,
malicious-share verification, any-3 reconstruction, independent custody,
or recipient-only release. Its CI status must be read from the hosted
exact-head workflow before marking even compilation accepted.

## New preprocessing-safety finding: silent exhaustion fallback

Direct inspection of both independently pinned `mpc/src/dn.rs` variants
shows `next_triple_z2k` returns **`(0, 0, 0)`** when the buffered
Beaver-triple pool is empty. In both versions, the file-based loader
only appends rows that parse into three integer fields; malformed rows
can therefore reduce the usable pool without an explicit load failure.

- [Original Ajax source](https://github.com/primus-labs/Ajax/blob/64b4f80fb90da3096e03af200d3c95abe865a987/mpc/src/dn.rs#L1299-L1305)
- [Modified Primus variant](https://github.com/primus-labs/primus-fhe/blob/a0d075d9ec055fb8652925fee65768a14a627cfa/mpc/src/dn.rs#L1298-L1304)

This is a **source-level safety blocker for accepting exhausted or incomplete
preprocessing**. A zero triple satisfies the algebraic equation
`c = a*b`, but replacing unpredictable, independently generated
preprocessing with a known constant is not justified by the paper's
security proof. This review does **not** establish an exploitable break
in a deployed protocol. No native runtime exhaustion test has occurred.

**Necessary negative experiment before any native threshold acceptance:**
provide an insufficient, missing, malformed or truncated triple file and
require the experiment to fail with an explicit nonzero status *before*
opening any masked values or emitting any plaintext. Do not simply count
the number of entries loaded or substitute zeros. Source-only probes
must continue to report `cryptographic_release_admitted=false`.

The exact-source audit now checks the fallback signature in **both**
pinned variants, and the synthetic fixture includes a mutant that removes
it; passing source checks indicate a *recognized unresolved blocker*,
not a security gate that became green.
