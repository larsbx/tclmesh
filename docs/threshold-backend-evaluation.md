# Threshold backend decision for Issue #36

Review date: 2026-11-01. Based on TclMesh main
`56b82073e1ad6d0b50123cf40197f742a8b76b49` (PR #40 is now merged).

**Decision:** no evaluated backend currently establishes TclMesh's complete
cryptographic any-3-of-4 release contract. Keep governed threshold release
unavailable. Prefer a TFHE-native, malicious-secure backend if a compatible
security profile can be established; do not adopt the documented KMS four-party
example as 3-of-4 secrecy. Lattigo is a useful arbitrary-threshold research
comparison, not an approved replacement. A signature, source hash, response count,
or passing policy arithmetic test cannot enable cryptographic release.

## Required security profile

| Quantity | Meaning | Example requirement |
| --- | --- | --- |
| `n` | Independent holders in an immutable keyset epoch | 4 |
| `q_release` | Actual cryptographic access threshold | Any 3 distinct valid holders suffice |
| `f_priv` | Colluding holders covered by the confidentiality theorem, with its exact adversary model | At least 2; passive and active guarantees must be stated separately |
| `f_byz` | Malicious deviations tolerated while preserving the specified correctness/liveness guarantee | Must be specified independently; no inference from `q_release` |
| `r_output` | Responses/transcripts needed for recipient reconstruction | Must be achievable by every permitted 3-holder subset |

The necessary secrecy condition is `f_priv >= q_release - 1`. It is not sufficient:
key setup, proof soundness, ciphertext validity, query/retry security and recipient
privacy must also hold. Any-three availability means three valid cooperating
holders can finish with the fourth offline. It does **not** require delivery when
two of those three actively sabotage a protocol. Abort on detected invalid input
is compatible with fail-closed safety; guaranteed delivery is a separate promise.
The coalition model must also cover the evaluator and any corrupted recipient.

## Compared candidates and concrete configurations

| Candidate | Configuration and security evidence | Why it is not admitted |
| --- | --- | --- |
| KMS v0.14.2 candidate | Published example: `n=4`, `f_priv=1`, `f_byz=1`, `r_output=3`; actual `q_release` not authenticated | Does not establish privacy against two holders. Exact candidate source remains unavailable. No native verification/custody/compatibility evidence |
| Official Zama threshold-fhe snapshot | Retrieved `c668fdd32a33270fc3ad2fd92b49267b734463dd`; report describes small-profile `f<n/3`, large-profile offline `f<n/4`, malicious security with static corruptions | Four-party `f=2` lies outside those profiles. Snapshot is unmaintained; its example uses centralized key generation. This is a different revision/repository from KMS |
| Lattigo | Pinned `7abb8d5dec86c6cc609e29540ddfc0c16864e14b`; arbitrary-threshold RLWE construction permits `n=4,q=3`, with privacy against up to two **passive** corruptions under the documented assumptions | No implemented active share-correctness proofs. Current security note warns retries, including changed participant sets, can expose keys. No TFHE wire compatibility |
| OpenFHE | Pinned `b59e1f291965f14fbee5172cd83a20f5b856204f`; additive multiparty examples and Shamir-based dropout-recovery APIs | Published model is semi-honest. Recovery of another party's secret share is distinct from verified partial decryption. No reviewed any-3-of-4 malicious-secure TFHE adapter |
| ATASSES / AThFHE (USENIX Security 2025) | Paper allows `N=4,T=3`, static semi-honest collusion up to `T-1=2`, nonparticipant handling and an untrusted aggregator | Paper-level candidate; malicious extension is discussion, not demonstrated TclMesh share verification. Implementation/parameters, recipient release and TFHE compatibility not validated here |

For the small Zama profile, two corruptions would require at least seven parties
just to satisfy `f<n/3`. This arithmetic does **not** establish 3-of-7 release:
the actual reconstruction, protocol participation and key-sharing rules still
need verification. Larger deployments, a different response count, or setting
`threshold=2` in a config cannot repair the four-party claim. Do not extrapolate
the example's bounds to other deployments or infer a universal impossibility.

The native follow-up now checks the snapshot's primitives directly: all six raw
degree-one share pairs reconstruct a public fixture, while the asynchronous robust
API completes for all four honest triples and remains pending for two responses.
Degree-two raw triples reconstruct, but the snapshot's robust-opening algorithms
reject four-party configurations at fault bounds one and two. These results
illustrate the access/response distinction and a specific protocol limitation;
they are not a KMS ciphertext attack or a blanket impossibility result.

## Source and proof evidence

The [source receipt](evidence/threshold-backend-source-review-20261101.json)
records commit IDs, SHA-256 digests, Git blob identity and retrieval limits.
The official threshold-fhe checkout was clean, inspected with replacement objects
disabled, and passed `git fsck`. These checks bind reviewed bytes to repository
objects; they do not verify author signatures, prove cryptographic security, or
authenticate the inaccessible KMS revision. KMS commit/tag API calls returned
404 through this connection. That is an access result, not proof of deletion or
an implementation vulnerability. No unreviewed fork substitutes for the pin.

Specific inspected evidence:

- Zama snapshot [README](https://github.com/zama-ai/threshold-fhe/blob/c668fdd32a33270fc3ad2fd92b49267b734463dd/README.md)
  identifies an unmaintained NIST snapshot. Its
  [example](https://github.com/zama-ai/threshold-fhe/blob/c668fdd32a33270fc3ad2fd92b49267b734463dd/examples/distributed_decryption.rs)
  sets four parties/threshold one and calls `gen_key_set` before sharing existing
  secrets. This test fixture is not evidence of secure distributed key generation.
  [Benchmark documentation](https://github.com/zama-ai/threshold-fhe/blob/c668fdd32a33270fc3ad2fd92b49267b734463dd/docs/threshold-benchmark.md)
  distinguishes real DKG from fake DKG and warns about test parameters.
- The snapshot's [cryptographic report](https://github.com/zama-ai/threshold-fhe/blob/c668fdd32a33270fc3ad2fd92b49267b734463dd/docs/CryptographicDocumentation.pdf),
  abstract/executive summary and section 4.3.5, separates robustness, abort and
  corruption models. Section 4.3.5.5 explicitly excludes mixed/Friends-and-Foes
  security. Its encryption ZK proofs must not be relabeled as proofs of correct
  partial decryption. A formal protocol description is not a proof that every
  implementation path meets it.
- Lattigo's pinned [multiparty README](https://github.com/tuneinsight/lattigo/blob/7abb8d5dec86c6cc609e29540ddfc0c16864e14b/multiparty/README.md)
  describes `Thresholdizer`, subset-dependent `Combiner`, public-key switching
  to an external recipient and the absence of active correctness proofs.
  Its [security note](https://github.com/tuneinsight/lattigo/blob/7abb8d5dec86c6cc609e29540ddfc0c16864e14b/SECURITY.md)
  says retry countermeasures are not implemented. Application idempotency alone
  does not prove a cryptographic retry countermeasure.
- OpenFHE's pinned [security note](https://github.com/openfheorg/openfhe-development/blob/b59e1f291965f14fbee5172cd83a20f5b856204f/docs/sphinx_rsts/intro/security.rst)
  assumes semi-honest use. [CryptoContext](https://github.com/openfheorg/openfhe-development/blob/b59e1f291965f14fbee5172cd83a20f5b856204f/src/pke/include/cryptocontext.h#L3647)
  exposes `ShareKeys` and `RecoverSharedKey`. Recovering an individual additive
  share is not necessarily reconstruction of the entire joint secret; nevertheless
  the evaluator must never collect enough material to reconstruct the joint key.
- The [ATASSES paper](https://www.usenix.org/system/files/usenixsecurity25-chang-yijia-encryption.pdf),
  section 2.3, specifies a static semi-honest model and separates malicious-security
  extensions from its main result. It establishes a research direction, not this
  repository's native acceptance.

## Compatibility with TclMesh

| Interface | TFHE-native path | RLWE alternatives |
| --- | --- | --- |
| Versions | TclMesh lock: TFHE-rs 1.8.2 / tfhe-zk-pok 0.9.0. KMS release metadata reports 1.6.2 but exact lock is unverified. Retrieved older snapshot locks 1.0.1 / 0.5.0 | Lattigo BGV/BFV/CKKS and OpenFHE multiparty formats are different schemes; not a binary-compatible TFHE upgrade |
| Ciphertexts and evaluation | Establish exact integer type, signed arithmetic, parameter fingerprint, noise squashing/flooding, tags, serialization and CRS/proof versions; test actual cross-process round trips | New backend/profile, encryption and evaluation implementation needed. Re-establish word overflow, comparison and noise semantics. CKKS approximation cannot silently replace exact integer semantics |
| Key management | Real malicious-secure DKG, isolated per-holder storage, epoch fencing, verifiable resharing and distributed backup; reject centralized/test/full-key import | Distributed threshold setup and active proofs still required; do not reconstruct the joint key in a helper/evaluator |
| Recipient release | KMS user-decryption candidate, not public output; exact recipient key and request binding verified at recipient | Collective public-key switching is a potential recipient-only mechanism in Lattigo; active correctness and retry security remain missing |
| Lean contract | Map actual native verification to `Release.Verified.validShare` and `canCombine`; MPC result verification may need a transcript/result model | Same obligations; library signatures or opaque payloads cannot instantiate `verifyProof` |

The initial source-review stage did not build a backend. The subsequent
[pinned native primitive probe](../experiments/threshold_snapshot/README.md)
compiled the older snapshot and exercised raw sharing/reconstruction only.
No actual multiparty FHE ciphertext decryption was performed.
The existing Lean theorems are conditional on named cryptographic soundness
hypotheses, not proofs of KMS, Lattigo or OpenFHE. Do not add axioms, `sorry`, or
an adapter that treats a signature as partial-decryption correctness.

Initial local validation: 21 synthetic Python provenance/policy tests pass;
the Tcl suite reports 196 passed, 29 TFHE-dependent skipped, zero failed. All
three existing threshold boundary mutants are rejected, and the release self-check
passes. An isolated Python mutant disabling the new release-policy exit gate is
also rejected. The native follow-up adds 15 runner-integrity controls (36 Python
tests total). Native TFHE/KMS integration and Lean builds were not run; no Lean
definitions changed. Native primitive results and their limits are recorded in
the experiment's separate receipt; no runtime threshold capability is enabled.

## Integration path and acceptance gates

1. **Source/security decision first.** Obtain the exact KMS candidate through an
   authenticated release/checkout or select a new explicitly reviewed pin. Verify
   its complete dependency graph, production parameter profile, corruption theorem,
   actual key-sharing degree, recipient protocol and all allowed holder subsets.
   If it cannot support 3-of-4, keep that example blocked. An alternative
   malicious-secure protocol with abort may be investigated, but no compatible
   implementation is selected here. A change of policy requires an explicit
   decision, not an automatic fallback.
2. **Isolated native spike.** Secure DKG across four independent processes with
   separate volumes; evaluator has public/evaluation keys only. Inventory storage,
   backups and crash artifacts. Ban complete client-key creation/import and test
   helpers. Recipient decrypts the delivered result; evaluator never sees plaintext.
3. **Bind and verify.** Freeze the domain-separated request, policy/manifest,
   circuit/output, ciphertext, parameters, keyset/epoch, participants, recipients,
   nonce and expiry. Verify participant role, signature and a cryptographic partial
   proof or fully verified malicious-secure MPC transcript/result before counting.
   Active-set selection and transcript identity must also be bound where required.
4. **Positive subset runs.** On a scheme proven to support it, test all four
   three-holder subsets and all six two-holder subsets. Expect every valid triple
   to reconstruct correctly and each pair to be refused. Test larger supported
   sets. API refusal is a functional test; confidentiality against a pair requires
   a security argument, not the inability of a test harness to decrypt. For schemes
   with unsafe retries, use fresh independent keysets/ciphertexts for subset tests;
   fresh request IDs alone do not make repeated partial generation safe.
5. **Adversarial and recovery runs.** Invalid-but-signed partial, invalid proof,
   noncanonical encoding, duplicate holder, mixed request/epoch/key/ciphertext/
   manifest/output/purpose/recipient, expiry, revoked holder and incorrect result
   must fail without output. Demonstrate one-party outage, durable atomic
   consumption, process crashes at each commit/exposure boundary, exact retry and
   unknown outcome. A retry must replay committed bytes or use a reviewed protocol
   mechanism; never regenerate unsafe partials for a new active set.
6. **Independent negative mutants and formal link.** Disabling share/transcript
   verification, accepting duplicate holders, allowing recipient substitution,
   bypassing epoch checks or restoring full-key fallback must break acceptance
   tests. Connect executable transitions to Lean obligations and document the
   remaining cryptographic assumptions. Only then register an immutable supported
   profile and implement `describe-threshold-keyset`/verified combine.

## Implemented checks and reproduction

`threshold_kms_preflight.py` now includes a **deny-only** policy assessment.
It keeps `q_release`, `f_priv`, `f_byz` and `r_output` separate, refuses invalid or
unreviewed participant configurations, and explicitly reports that source success
does not admit release. No caller-provided security flags are trusted. Runtime
threshold operations continue to refuse through the existing central gate.

```bash
# No source claim; prints BLOCKED, exits 2 (expected).
python3 tools/threshold_kms_preflight.py --policy-only \
  --participants 4 --release-threshold 3

# Source-only diagnostic remains backward compatible. Add this flag for an
# acceptance invocation: even synthetic matching sources must exit 2 today.
python3 tools/threshold_kms_preflight.py --kms-source /path/to/exact-kms \
  --participants 4 --release-threshold 3 --require-release-policy

# 21 synthetic provenance/policy controls; no cryptographic acceptance claim.
python3 -m unittest discover -s tests -p 'test_threshold_kms_preflight.py'
```

To reproduce the snapshot review, clone the official threshold-fhe repository,
checkout the receipt's full commit, run `git --no-replace-objects status
--porcelain` and `git fsck --full --no-dangling`, then compare SHA-256 for every
recorded path against `verified_source_digests`. For other repositories, fetch the
recorded exact commit/path and compare both Git blob identity and SHA-256. This
does not replace the missing exact KMS source gate. See the
[source preflight](threshold-kms-preflight.md) and
[runtime boundary](threshold-release-boundary.md).
