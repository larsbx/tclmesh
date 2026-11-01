# Threshold release boundary and Zama KMS compatibility investigation

Date: 2026-10-30. Tracks [issue #36](https://github.com/larsbx/tclmesh/issues/36).
This correction is independently reviewable and does not complete that issue.

Follow-up: [2026-11-01 backend evaluation](threshold-backend-evaluation.md)
compares authenticated repository bytes, security-model limits and acceptance
tests. No reviewed production threshold profile has been enabled.

## Current implemented security boundary

| Mode/capability | Accepted inputs and implementation | Claim |
| --- | --- | --- |
| `reference-release` | `release request`, reference/test backend, opaque approval values | Test state machine; plaintext may be stored |
| `authorization-quorum` | Explicit `request-authorization`, or manifest `kind authorization-quorum` with authorized APIs; opaque approvals | Trusted-adapter authorization quorum; TFHE still uses a complete client key |
| `threshold-release` policy / `cryptographic-threshold-decryption` | Reserved, always refused | No implemented cryptographic threshold release |

TFHE advertises `authorization-quorum`, never either threshold capability. Its
legacy `combine-release`, `verify-contribution`, and `combine-verified-release`
operations always refuse before process I/O. Ordinary decrypt remains available
for profiles explicitly allowing it on ungoverned handles. Governed handles reject
direct decrypt and raw release APIs even if their profile permits decryption.

The central release gate rechecks mode, backend capability and manifest policy
before counting, combining or reconciling a request as released. All pre-change
requests lacking `release_mode` are blocked. Creating a new authorization-only
manifest/request requires a deliberate operator decision; no old threshold policy
or pending request is automatically downgraded. Stored data, backend registration,
and actor authentication remain trusted-adapter inputs, not a hostile interpreter
sandbox. Access to internal Tcl procedures or registry variables is privileged.

Successful reference/authorization-only releases may expose plaintext to the
kernel and trusted operator. Neither these flows nor their receipts meet PRIVATE
threshold custody, proof validity or recipient-only release requirements.

## Reserved threshold backend interface (not enabled)

No Boolean supplied by a caller, signature alone, or advertised capability enables
this interface. A future integration must implement and validate all operations:

| Operation | Required contract before enabling |
| --- | --- |
| `describe-threshold-keyset` | Immutable scheme/version/profile, keyset/epoch, participant verification material, exact supported policy quorums, fault/collusion/availability constraints; attest distributed custody with no complete secret key at evaluator/kernel |
| `verify-contribution` | Receive canonical request binding, participant, partial and signature/proof; authenticate active participant and public share commitment, verify partial correctness or a malicious-secure MPC transcript/output; reject malformed/noncanonical inputs and every binding mismatch |
| verified contribution state | Backend-owned immutable verified reference bound to exact partial digest, request/ciphertext/keyset/epoch and participant; caller cannot set `verified=true`; durable atomic deduplication/consumption before counting |
| `combine-verified-release` | Accept only distinct verified references at a supported threshold, recheck live authority/epoch, perform authenticated combination and verify the result; no fallback to ordinary decrypt |
| release attestation/recovery | Commit consumption before exposure, bind recipients and encrypted delivery/output digest, charge leakage budget, record auditable nonsecret receipt; unknown/crash/revocation outcomes fail closed |

Canonical domain-separated request bytes must include protocol/version, manifest
and release-policy hashes, keyset and epoch, ciphertext digest, circuit hash and
output name/specification, request ID, purpose, recipients/visibility, exact context,
nonce and expiry. The authenticated message additionally binds the particular
partial/proof. All response/attestation signatures must be checked against the
request's frozen context, never a responder-selected epoch. Scheme-specific
parameter constraints are validated before request creation. The implementation
must not log raw shares or private key material.

`spec/TclMesh/Release.lean` models verification as independent authorized-holder,
signature and proof predicates over the contribution, including its binding and
payload. `cryptographicSoundness` is an explicit theorem hypothesis. The proofs
establish what follows *if* those predicates are sound; they do not prove or
instantiate a cryptographic system. The digest's canonical encoding, collision
resistance, durable consumption and distributed protocol are future obligations.

## Version-targeted KMS investigation

**Candidate source pin for the next spike:** Zama KMS **v0.14.2**, commit
`afcc7e5a48c31f7c3772b1799c8e856c8e3166f1`, as identified by the official
[release listing](https://github.com/zama-ai/kms/releases) and its
[commit link](https://github.com/zama-ai/kms/commit/afcc7e5a48c31f7c3772b1799c8e856c8e3166f1).
This is a compatibility investigation target, not an adopted dependency or an
assertion that this is the latest release. Its release notes advertise TFHE-rs
**1.6.2** and epoch/context/resharing support. TclMesh pins TFHE-rs **1.8.2** and
`tfhe-zk-pok` **0.9.0** in `backends/tfhe/Cargo.toml`; compatible ciphertext,
parameter, proof/CRS and serialization formats have not been established.

**Retrieval limitation:** the official release and documentation were accessible
through indexed web retrieval, but live GitHub API, clone/raw source, and the pinned
source file URLs returned unavailable/404 during this investigation. Consequently
this change does not authenticate a source archive, lockfile, container digest or
build, and does not claim to have inspected the pinned implementation. The source
pin above is release metadata, not a verified checkout. Obtain and hash the exact
source/lockfile/images before an integration acceptance claim. Unpinned docs below
are directional evidence; their statements must be checked against that checkout.

| Question | Evidence and compatibility consequence |
| --- | --- |
| Genuine cryptography | [Official KMS README](https://github.com/zama-ai/kms) describes malicious-secure robust MPC, distributed key generation, decryption and resharing, compatible with TFHE-rs; centralized mode also exists and must be explicitly excluded |
| Fault parameter versus quorum | [Concepts](https://github.com/zama-ai/kms/blob/main/docs/getting-started/concepts.md) uses `t` for tolerated offline/malicious parties and requires `t < n/3`. Name this `f` in TclMesh; never substitute it for policy reconstruction quorum `q` |
| Four-party example | [Client configuration](https://github.com/zama-ai/kms/blob/main/core-client/config/client_local_threshold.toml) says `n=4`, `t=1`, `num_majority=2`, `num_reconstruct=3`; [client guide](https://github.com/zama-ai/kms/blob/main/docs/guides/core_client.md) distinguishes matching responses from reconstruction. This is evidence for a candidate 3-response user-reconstruction configuration, not proof that every three-holder subset works or that two colluding key holders cannot recover secrets |
| Actual secrecy constraint | Concepts guarantees secrecy against at most `f` corrupt parties and says more than `f` can collaborate to use shares. Do not infer cryptographic 3-of-4 confidentiality from `num_reconstruct=3`: establish the actual key-sharing degree, output-sharing protocol and collusion threshold from pinned code/specification and crypto review. The candidate may not satisfy an arbitrary policy `q` |
| Verification | [Architecture](https://github.com/zama-ai/kms/blob/main/ai-docs/ARCHITECTURE.md) describes malicious-secure MPC, mTLS core peers, EIP-712 response signatures and client validation. Signatures prove authenticated origin/binding, not an independently public proof of each partial. A trusted authenticated MPC result needs its own explicit security/verification argument |
| Key custody | Threshold DKG should distribute secret shares without creating a full FHE secret at the evaluator. Exclude centralized/insecure key generation, fixture keys and complete-key import. Inspect private storage, backup/custodian restoration, resharing and revocation; independent parties must not share one full client key |
| Recipient-only release | [Official protocol architecture](https://github.com/zama-ai/fhevm/blob/8bb31fb18f373584feb213251fa6c790167075a1/docs/protocol/architecture/kms.md) distinguishes public decryption from user decryption re-encrypted for a user's key. Bind that recipient key and request context, verify/decrypt only at the authorized recipient, and ensure the kernel cannot recover plaintext |
| Noise/serialization | [Noise squashing documentation](https://github.com/zama-ai/tfhe-rs/blob/6753c2a789f887b204c72fe95324a33b2fda449a/tfhe/docs/fhe-computation/advanced-features/noise-squashing.md) explains threshold noise hiding and squashing. Plain high-level TclMesh `FheInt32`/`FheInt64` tokens are not established compatible KMS inputs; enforce parameters, ciphertext format, noise handling and chosen-ciphertext safeguards |

For a scheme proven to support the desired q-of-n boundary, test all valid
q-participant subsets, refusal at q-1, valid-signature/invalid-partial, forged proof,
malformed encoding, duplicate identity, mixed keysets/epochs/ciphertexts/manifests/
outputs/purposes/recipients, replay, revocation, partial outage and crash recovery.
Include independent negative controls that bypass verification. 3-of-4 remains an
example acceptance target. None of these cryptographic integration tests has run,
and no production threshold backend is selected by this PR.
