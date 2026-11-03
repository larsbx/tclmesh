# Threshold alternatives: authenticated source versus protocol claims

Date: 2026-11-01. Follow-up to Issue #36 and the
[initial comparison](threshold-backend-evaluation.md). Production threshold
release remains unavailable. No alternative below is registered as a backend.

## Tulva: a relevant 3-of-4 design with unresolved implementation obligations

The [October 14 full paper](https://arxiv.org/abs/2610.20521) describes an
asynchronous compiler with flexible access thresholds and a TFHE-rs compatibility
layer. The 3-of-4 profile is within the advertised family, subject to a concrete
parameter/security instantiation. Its confidentiality model covers static
corruptions and honestly produced/evaluated ciphertexts; it is not a claim of
arbitrary malformed-ciphertext security.

The full paper's section 2.2 uses a trusted dealer; Remark 1 leaves distributed
key generation to future work. The
[October 5 NIST preview](https://csrc.nist.gov/csrc/media/Projects/threshold-cryptography/documents/TCall-1/Tulva-PW03.pdf)
separately proposes Tulva+ for checked output/abort. Its consistency-check option
needs `q+f_priv` responses: at `q=3,f_priv=2`, five responses exceed four holders.
Proof-carrying or authenticated-output variants need separate verification.

The paper links [osdnk/tulva](https://github.com/osdnk/tulva). Retrieved commit
`c13a15c010fc7b5dc1601fb5898bf54193f4deed` contains **only README.md**, promising
implementation publication with the proceedings. No source, concrete 3-of-4
parameters, DKG, verified partials or recipient-only delivery was obtained.
This repository snapshot cannot reproduce the paper's implementation claims.
The preview and full paper have distinct dates; a planned extension is not a
demonstrated property of the base implementation.

## Fhenix: useful malicious-secure protocol direction, benchmark not an adapter

The [CCS 2025 paper](https://web.eecs.umich.edu/~cpeikert/pubs/threshold-fhe.pdf)
proves a rounding-based decryption construction in an authenticated arithmetic
black-box model and discusses dishonest-majority security with abort. It reports
an SPDZ2k instantiation, with MP-SPDZ preprocessing and a Rust online phase.
This is a credible protocol direction to investigate beyond robust honest-majority
KMS. A proof for an ideal authenticated black box does not discharge concrete
key custody, access structure, MAC enforcement or output-delivery obligations.

The paper's repository link resolves to
[FhenixProtocol/thresholdfhe-paper](https://github.com/FhenixProtocol/thresholdfhe-paper).
The retrieved source pin is `19b0f0a5a71b67badb85c3c8715b3eba7e866f79`.
The review found the following concrete integration blockers:

| Source location at that pin | Observation and consequence |
| --- | --- |
| `src/mpc/party.rs:527-543` | `execute_step_five` computes `z_sum` and returns an empty response without checking it. Native public fixtures reproduce identical normal returns for zero/nonzero sums and missing peer values. This method is not an enforced authenticated-output boundary |
| `src/mpc/main.rs:11-29` and `src/mpc/protocol.rs:135-181` | The local benchmark obtains plaintext from `decrypt` before performing its separate MAC check. A TclMesh adapter must verify before exposing output |
| `src/network/discovery_server.rs:114-128` | Coordinator creates a complete LWE fixture key and prints its fixture plaintext before distributing shares. This is not distributed key custody; the network benchmark was not executed |
| `src/mpc/additive_sharing.rs` and `src/mpc/protocol.rs:89-106` | Setup distributes additive shares across all `n` parties. No reviewed conversion from an immutable four-holder keyset to every permitted triple is established |
| `Cargo.toml` / `Cargo.lock` / `src/mpc/lwe_scheme.rs` | Custom LWE benchmark and arithmetic/network dependencies; no TFHE-rs dependency or validated TclMesh 1.8.2 ciphertext adapter |

The native [four-test experiment](../experiments/threshold_fhenix/README.md)
uses only public scalars and calls actual pinned methods. These are limitation
witnesses, not tests of a complete network or malicious-secure FHE deployment.
They do not refute the paper's theorem or establish an exploit against production.

In this repository, `PublicParameters.k` is ciphertext bit length,
`MACSchemeParams.t` is a batch count, and `n` is participant count. None is an
implemented configurable cryptographic release quorum. Do not map them to
TclMesh's policy `q_release` merely because a benchmark runs four processes.

## Decision and next reproducible acceptance

Both source identities and the paper/preview hashes are recorded in the
[source receipt](evidence/threshold-alternatives-source-review-20261101.json).
Git object identity and HTTPS retrieval are not author-signature or binary
attestations. No claimed theorem has been silently turned into a runtime flag.

The source review narrows two possible paths:

1. **Authenticated MPC rounding:** obtain a reviewed implementation of the
   required arithmetic black box and preprocessing, enforce integrity failure
   before output, and supply a proven 3-of-4 key-sharing/setup and subset protocol.
   Removing a participant from the benchmark's additive sum is not that protocol.
2. **Tulva with checked partials/output:** obtain published pinned implementation,
   concrete four-holder parameters, malicious-secure distributed setup and a
   verified Tulva+ variant that fits the response budget. The five-response
   consistency variant cannot satisfy three-of-four availability.

For either path, require all four valid triples and all six insufficient pairs,
invalid-but-authenticated contributions, ciphertext-integrity and binding mutants,
recipient-only output, atomic consumption, rotation and safe retries. The Lean
`Release.Verified` predicates remain conditional soundness obligations. PR #42's
numerical model is complementary; it does not prove either backend correct.
Neither a trusted-dealer experiment nor a benchmark that delays integrity checks
can enable the reserved threshold capability.

Local follow-up validation: 40 synthetic Python controls, six Zama native
regression tests and four Fhenix native limitation witnesses pass. Full threshold
FHE decryption, independent holder custody and Lean builds remain unperformed.

## Final source decision: integration blocked

A bounded follow-up audit of the same Fhenix pin closes the preprocessing and
subset questions. It does not add another experimental cryptosystem or promote
the existing primitive witnesses into multiparty decryption evidence.

| Pinned source | Additional observation | Admission consequence |
| --- | --- | --- |
| [`preprocessing.rs:32-107`](https://github.com/FhenixProtocol/thresholdfhe-paper/blob/19b0f0a5a71b67badb85c3c8715b3eba7e866f79/src/mpc/preprocessing.rs#L32-L107) | `run(s,r,sk)` takes a complete secret vector and centrally builds every party's preprocessing and additive secret-key shares | Not distributed setup or a custody-preserving preprocessing adapter |
| [`mac_scheme.rs:54-111`](https://github.com/FhenixProtocol/thresholdfhe-paper/blob/19b0f0a5a71b67badb85c3c8715b3eba7e866f79/src/mpc/mac_scheme.rs#L54-L111) | The local object holds global `alpha`; `batch_open` makes MAC shares from its supplied current values | These MACs do not establish authentication of the preceding computation. `batch_check` does check its supplied MAC relation and can return `None`; that algebraic check alone does not instantiate the paper's authenticated black box |
| [`worker.rs:152-180`](https://github.com/FhenixProtocol/thresholdfhe-paper/blob/19b0f0a5a71b67badb85c3c8715b3eba7e866f79/src/network/worker.rs#L152-L180) | Each step waits for `n-1` peer messages in addition to the local party | The four-party benchmark is not an available-three protocol. Changing `n` to three creates a different setup; it does not make each triple of the original keyset usable |
| `Cargo.toml`, tracked source inventory, and setup/worker paths | No MP-SPDZ preprocessing importer or authenticated four-holder-to-three-holder conversion was identified in this snapshot | The paper's reported preprocessing instantiation remains a dependency to obtain and review, not an implemented TclMesh path |

The [decision receipt](evidence/threshold-backend-decision-20261101.json) records
the additional file hashes and the complete source-tree digest. All 251 tracked
files were checked against their pinned Git blob identities with the existing
`source_files` verifier; `git fsck --full` passed. These checks authenticate the
retrieved repository bytes to the pin, not the authors, security proof or build.
No new native run, network execution or cryptographic test is claimed here.

The integration decision for the evidence obtained on 2026-11-01 is **no-go**:

| Candidate configuration | Established boundary | Missing condition for TclMesh 3-of-4 |
| --- | --- | --- |
| Published KMS four-party example | `f_priv=1`, `f_byz=1`, `r_output=3`; exact v0.14.2 source unavailable | Secrecy against two colluding holders and authenticated compatible source |
| Old Zama four-party degree-one profile | Raw pairs reconstruct; honest triples complete the probed robust opening | Pair secrecy; raising degree to two fails the probed four-party robust constraints |
| Lattigo 3-of-4 | Passive threshold sharing is documented | Malicious contribution/output verification, safe repeated-decryption model and TFHE compatibility |
| Fhenix four-party benchmark | Additive all-party setup and public-fixture method witnesses | Distributed authenticated preprocessing, immutable-keyset subset protocol, integrity before output and TFHE adapter |
| Tulva advertised 3-of-4 family | Published design, trusted-dealer model; retrieved repository contains only a README | Concrete source/parameters, distributed setup and checked-output variant within the response budget |

OpenFHE and ATASSES remain the semi-honest leads described in the
[initial comparison](threshold-backend-evaluation.md); neither supplies an admitted
malicious-secure adapter in the inspected evidence. This decision concerns the
retrieved versions and TclMesh contract, not impossibility of threshold FHE or a
claim that any implementation is insecure.

The most defensible next engineering path is an **external, reviewed authenticated
MPC backend**, if one can supply the required distributed setup and fixed-keyset
access structure. The Fhenix paper motivates that path; its benchmark is not the
dependency to register. Do not patch in a final MAC comparison and infer that the
black-box assumptions, preprocessing, subset handling or recipient privacy follow.

For three-of-four, specify separately: secrecy against two corrupt holders;
successful output from each cooperative valid triple with the fourth offline;
and integrity against the declared malicious coalition. A protocol secure **with
abort** may refuse output when an active participant misbehaves. It must not be
advertised as tolerating that fault while guaranteeing output. Individually
verifiable partials and verified malicious-secure MPC output are alternative
contracts; neither is established by holder signatures or response counts.

Reopen adapter implementation only when an immutable dependency provides:

1. An exact protocol/security profile and reviewed setup/preprocessing with no
   complete secret at the evaluator, including a custody-preserving way to use
   every allowed triple of the same four-holder keyset and epoch.
2. A verifier or authenticated MPC output boundary that rejects corruption before
   plaintext exposure, with explicit adversary, ciphertext and retry assumptions.
3. A buildable TFHE-rs 1.8.2 key/evaluation-key/ciphertext conversion contract and
   recipient-only delivery path. Serialization resemblance is not compatibility.
4. Reproducible independent-party acceptance: all four valid triples; all six
   pairs refused; invalid-but-signed contributions; verification-bypass and
   incorrect-output controls; binding/recipient tampering; outage, revocation and
   crash/retry. Pair refusal is an implementation check, not a proof of pair
   secrecy. Refine the Lean predicates against the actual verifier while keeping
   computational soundness hypotheses explicit.

Until these dependencies exist, keep the runtime refusal and deny-only capability
assessment. Synthetic controls, primitive tests and numerical Lean checks cannot
enable release or close Issue #36.
