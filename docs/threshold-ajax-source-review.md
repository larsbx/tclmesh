# Ajax (USENIX Security 2026): source-pinned threshold-FHE candidate review

**Date:** 2026-11-03. **Scope:** TclMesh issues #36 and #45. **Decision: RESEARCH ONLY; not a release backend.**

This is a source-backed supplement to the existing Zama, Tulva, Lattigo and Fhenix
reviews. The Python preflight only checks selected immutable source bytes and
reports source-level limitations. Its passing exit status is *never* a
cryptographic assertion, conformance result or runtime release permission.

## Paper-level result versus demonstrated source behavior

- [Hu et al., *Ajax: Fast Threshold Fully Homomorphic Encryption without Noise
  Flooding*, USENIX Security 2026](https://www.usenix.org/conference/usenixsecurity26/presentation/hu-zhenkai)
  describes distributed key generation for FHEW-like FHE and a mask-then-open
  threshold decryption protocol. The principal protocols are analyzed in the
  **semi-honest** setting: honest-majority key generation with corruption bound
  \`t < n/2\`, and decryption using \`t+1\` of the \`n\` holders even when this is
  a dishonest majority among *responding* parties. The paper mentions an
  active-security extension in its full version; this review has not verified
  such a protocol, a malicious-share verifier or a security reduction for
  TclMesh's target implementation.
- A meaningful **alternative** configuration to inspect is **any 3 of 5**:
  \`n=5, t=2, q_release=t+1=3, f_priv=2\` in the paper's semi-honest
  model, *subject to the exact theorems and setup assumptions*. This is a
  candidate-level numerical mapping, not a claim that the checked source
  implements every one of the ten 3-party subsets.
- Ajax's honest-majority DKG condition does **not** justify TclMesh's 3-of-4
  objective under \`t=2\`: \`4 > 2*2\` is false. Do not turn \`n=4, q=3\`
  into a deployment claim by altering a command-line participant count.
- The paper's 0.9 ms (n=3) and 4.4 ms (n=21) decryption results are **amortized
  author-reported timings**, not independently reproduced latency for a
  malicious 3-of-5 TclMesh release.

## Exact public source review

Source repository [primus-labs/Ajax](https://github.com/primus-labs/Ajax),
commit **\`64b4f80fb90da3096e03af200d3c95abe865a987\`**,
repository license **LGPL-3.0**. Public GitHub commit and recursive tree were
retrieved on 2026-11-03. The 76-entry tree contained these relevant paths:

| Source at exact pin | Observed fact | Interpretation |
| --- | --- | --- |
| [\`README.md\`](https://github.com/primus-labs/Ajax/blob/64b4f80fb90da3096e03af200d3c95abe865a987/README.md) | Documents a complete keygen/decryption example, EMP-Toolkit prerequisites, and pre-generated Beaver triples for decryption involving two or three parties (corresponding to three- or five-holder full configurations). | A reproducibility lead; bundled test triple files do not establish malicious-secure authenticated preprocessing. |
| [\`thfhe/examples/thfhe.rs:25-31\`](https://github.com/primus-labs/Ajax/blob/64b4f80fb90da3096e03af200d3c95abe865a987/thfhe/examples/thfhe.rs#L25-L31) | Sets threshold to \`(number_parties - 1)/2\`. | Not a freely configurable TclMesh release policy; test exact source-supported profiles. |
| [\`thfhe/examples/thfhe.rs:109-140\`](https://github.com/primus-labs/Ajax/blob/64b4f80fb90da3096e03af200d3c95abe865a987/thfhe/examples/thfhe.rs#L109-L140) | Demonstration invokes distributed decryption only when \`party_id <= threshold\` and prints plaintext at party zero. | Tests just one designated subset. This does **not** prove that the protocol cannot handle others, but all subsets and private recipient delivery are untested in this example. |
| [\`thfhe/src/distdec.rs:69-107\`](https://github.com/primus-labs/Ajax/blob/64b4f80fb90da3096e03af200d3c95abe865a987/thfhe/src/distdec.rs#L69-L107) | Reveals a result through the MPC backend and returns a plaintext only to party zero. | No TclMesh request/ciphertext/epoch/recipient binding or proof of accepted malicious contributions is demonstrated. |
| [\`mpc/src/dn.rs:1-3\`](https://github.com/primus-labs/Ajax/blob/64b4f80fb90da3096e03af200d3c95abe865a987/mpc/src/dn.rs#L1-L3) | DN07 backend describes \`n > 2t\` honest-majority MPC. | Supports the paper-level setup distinction; source comment is not an audited proof. |
| [\`thfhe/Cargo.toml:10-12\`](https://github.com/primus-labs/Ajax/blob/64b4f80fb90da3096e03af200d3c95abe865a987/thfhe/Cargo.toml#L10-L12) | \`algebra\`, \`lattice\`, and \`fhe_core\` select \`primus-fhe\` Git branch \`ajax\` without revision pins in the manifest. No root \`Cargo.lock\` is tracked in the 76-entry tree. | Rebuilding at the selected Ajax commit does **not** on its own freeze the transitive crypto implementation. Record each resolved Git revision, artifacts and toolchain before any native benchmark. |

No upstream executable was built during this review. The checked source is
public and identified by Git commit, **not** independently cryptographically
audited or authenticated by an author signature.

## Reproduce the limited preflight

On a machine with network access and Git:

\`\`\`sh
git clone https://github.com/primus-labs/Ajax.git
git -C Ajax checkout --detach 64b4f80fb90da3096e03af200d3c95abe865a987
python3 tools/threshold_ajax_preflight.py --source Ajax

# Deliberate no-go check, must return exit code 2 even with a clean source.
python3 tools/threshold_ajax_preflight.py --source Ajax --require-release

# Local synthetic source-integrity regression, not native FHE testing:
python3 -m unittest discover -s tests -p 'test_threshold_ajax_preflight.py'
\`\`\`

The \`tools/threshold_ajax_preflight.py\` commands are run from the TclMesh
checkout. They verify that selected working-tree source bytes equal Git's pinned
commit bytes, reject dirty/untracked files and mismatched HEAD, then return
\`SOURCE_REVIEW_ONLY\`. Do not read its ordinary exit code 0 as security
acceptance. Source inspection is intentionally conservative and based partly on
exact text patterns; missing patterns **do not** imply the absence of a flaw or
the presence of a validated feature.

## Next falsifiable protocol experiments

1. Pin \`primus-fhe\` Git dependency revisions and the EMP-Toolkit triple-generation
   source; reproduce end-to-end **5-holder DKG and 3-holder decryption** at a
   documented security parameter set. Do not substitute the checked-in triples
   for authenticated production preprocessing.
2. Holding an immutable 5-holder keyset, run **all 10 triples** and reject **all
   10 pairs**. Add participant permutations, missing/offline holders, distinct
   ciphertexts, randomized keys and a nontrivial circuit result. A
   fixed-first-three benchmark is not sufficient.
3. Demonstrate **independent custody** (no evaluator-held full FHE secret) and
   user-bound encrypted output, not the example's plaintext return to party
   zero.
4. Test invalid-but-authenticated shares, modified MPC messages, corrupted
   triples, selective abort, active corruption, replay and mixed
   keyset/ciphertext/epoch/recipient requests. Select and justify an
   **actual malicious-secure** extension or per-share proof; the main-body
   semi-honest theorem cannot discharge these tests.
5. Establish TclMesh's TFHE-rs 1.8.2 integer semantics, ciphertext
   serialization/noise bounds and lifecycle behavior against the pinned
   Primus-based implementation. Do not assume wire compatibility.
6. Capture pinned commands, build artifacts, runtime transcript digests,
   negative-mutant outcomes, resource utilization, rounds and response count.
   Report security-with-abort separately from guaranteed output delivery.

**Acceptance gate:** neither this paper, the upstream demo, nor a clean source
preflight can enable \`cryptographic-threshold-decryption\`. Existing
authorization-only paths must remain distinct and TclMesh must fail closed.
