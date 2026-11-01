# Issue #36 — reproducible Zama KMS source preflight

**Scope:** read-only evidence gate for the *candidate* Zama KMS version. This is an initial
compatibility experiment, not the cryptographic threshold implementation, and does
not justify PRIVATE or any-`q`-of-`n` conformance.

The initial metadata candidate is KMS `v0.14.2`, commit
`afcc7e5a48c31f7c3772b1799c8e856c8e3166f1`. This pin came from release
metadata and is not yet an authenticated, successfully built source archive.
The running code must be checked against an exact checkout and lockfile.

## Execute the source/dependency gate

From an independent working directory with `git` and Python >= 3.11:

```bash
git clone https://github.com/zama-ai/kms.git kms-source
git -C kms-source checkout --detach afcc7e5a48c31f7c3772b1799c8e856c8e3166f1

# From the clean TclMesh checkout:
python3 tools/threshold_kms_preflight.py --kms-source /absolute/path/to/kms-source
```

The script **does not fetch arbitrary remote code or execute KMS**. It rejects
nested/subdirectory checkouts and untracked, ignored, symlinked or modified
evidence files. All provenance Git calls disable replacement-object resolution
(`git --no-replace-objects`), so local `git replace` refs cannot substitute a
different commit body while keeping the expected HEAD identifier.
It verifies lockfiles and sample configuration against the
actual HEAD Git objects rather than trusting bytes from the working tree.
It checks both checkouts' HEAD and cleanliness, hashes their Cargo.lock files, compares the
locked `tfhe` and `tfhe-zk-pok` package versions when present, and inspects the
four-party client sample configuration. A missing/unverifiable source, unexpected
commit, differing locked versions, insecure `Test` parameters or incorrect sample
response count yields `status: BLOCKED` and exit 2.

A zero exit means **only** `SOURCE_PREFLIGHT_ONLY`: a clean exact KMS pin,
no detected locked-version mismatch, and a sample configuration with default
rather than insecure test parameters. It is not evidence that ciphertexts or
proofs interoperate, nor of malicious security or threshold custody.
The output includes the checked commit identities, lockfile SHA-256 hashes,
diagnostic blockers and explicit non-claims. Store the JSON with experiment
provenance; do not include secret shares or plaintext in artifacts.

The candidate's documented example uses `num_parties=4`,
`num_reconstruct=3` and `fhe_params="Test"`. The *three response* setting
is a client reconstruction parameter, **not** a 3-of-4 collusion guarantee.
Similarly `t` in KMS threat model often denotes tolerated faults, while
TclMesh's policy uses a requested reconstruction threshold `q`.
They must be reconciled against the exact checked-out source and security proof.

The TclMesh lockfile currently pins TFHE-rs 1.8.2 and tfhe-zk-pok 0.9.0;
the initial KMS release investigation reported TFHE-rs 1.6.2. Version parity is
a necessary triage check for direct integration, but is not sufficient for
cryptographic, parameter, ciphertext, encoding or API compatibility. Even if
the script reports `SOURCE_PREFLIGHT_ONLY`, **Issue #36 remains open**.

## Current source-access blocker (2026-10-31)

The hosted pinned-source workflow initially failed before reaching dependency
checks: the upstream `git fetch` returned
`fatal: could not read Username for 'https://github.com'`.
That observation establishes an **unavailable source fetch in the CI runner**,
not that the repo has been deleted or that the proposed commit is valid/invalid.
A second source check through the configured GitHub connector was also not
accessible. No downloaded revision, lockfile hash, KMS build or interoperability
result is established.

The upstream retrieval workflow is now **explicitly dispatch-only** rather
than a required `pull_request` check: the GitHub-hosted runner cannot fetch
this pinned upstream source, and external source availability is not a code
regression in the TclMesh preflight implementation. Run
`kms-source-preflight` with `workflow_dispatch` on the intended branch and
record its red/blocked outcome as a **separate unresolved integration
prerequisite**. The ordinary `test` workflow continues to run all synthetic
source-integrity negative controls on every PR; a green `test` result never
means a KMS revision was fetched or authenticated.

The dispatch-only workflow intentionally stays red when source retrieval fails and writes a
nonsecret JSON report labeled `kms_source_unavailable` to preserve the exact
blocker. A preceding anonymous HTTP probe records status codes for Git smart-HTTP,
the repository metadata API and the pinned commit API as **diagnostics only**;
HTTP status by itself is not evidence of source authenticity. Never fall back to another tag, commit, mirror, unchecked archive or
centralized key without an explicit independently verified new pin.

Hosted `pull_request` evidence is tied to the exact PR head (rather than
GitHub's synthetic merge commit). The script additionally insists the supplied
directory be the Git working-tree root and the inspected files be tracked at
HEAD and byte-identical to those committed.

Proceed with an authenticated local exact checkout if the upstream repository
can be accessed. Until then the failure is a **reproducible retrieval blocker**,
not evidence supporting crypto acceptance.

## Decision gate: response count is not a cryptographic secrecy threshold

The public, unpinned KMS documentation for the four-core example describes
`n=4`, corruption/offline tolerance `f=1` (subject to `f<n/3`) and client
`num_reconstruct=3`. This is **not** a 3-of-4 collusion-resistance
certificate. To claim actual `q_release=3` secrecy, an implementation must
preserve confidentiality against `q_release-1=2` collaborating holders,
and support output reconstruction by *every* allowed three-party subset.
The candidate's documented `f_priv=1` guarantee does not cover two
corrupt parties. In particular, `f_byz<n/3` cannot certify `f_byz>=2` at
`n=4`. This is a no-go for **claiming** 3-of-4 secrecy under those
published guarantees, not an exploit proof or universal impossibility result.

Keep `q_release` (cryptographic access threshold), `f_priv` (privacy
corruption bound), `f_byz` (robust-MPC fault tolerance) and `r_output`
(client response reconstruction count) separate. Do not promote
`r_output=3` to `q_release=3` without an authenticated protocol proof,
even if three valid client responses produce a correct value. Verify
precisely which subsets, corruption patterns, recipient protections
and failure modes the pinned scheme guarantees.

The necessary secrecy-acceptance condition for policy `q_release`
is at least `f_priv >= q_release-1`; a scheme can impose additional
constraints, including a different response/reconstruction quorum.
The initial four-party target remains an example only. If a scheme
cannot satisfy the policy, reject it instead of silently downgrading.

References (directional, unpinned):
- https://github.com/zama-ai/kms/blob/main/docs/getting-started/concepts.md
- https://github.com/zama-ai/kms/blob/main/core-client/config/client_local_threshold.toml
- https://github.com/zama-ai/kms/blob/main/docs/guides/core_client.md

## Next real cryptographic validation (not performed by this script)

1. Build the exact pinned source and confirm the protocol security parameters,
   secret-share custody, per-party independent storage, actual corruption bound,
   and permitted `q` values. Do not use centralized or insecure keygen for
   security evidence.
2. Demonstrate a real four-party decryption with **no complete client key** in
   the TclMesh evaluator. Check refusal with `q-1`, all supported `q`-subsets,
   an invalid-but-signed contribution, forged/mixed binding evidence and replay.
3. Validate correctness, ciphertext/CRS/parameter compatibility, recipient-only
   output, persistence, crash/retry behavior and key rotation. Connect actual
   native verifier behavior to the `Release.Verified` Lean contract, keeping
   unsupported assumptions explicit.
4. Require independent negative mutants that disable cryptographic proof
   verification or restore full-key fallback and show that the integration
   suite catches both.

Test the preflight itself without obtaining KMS source:

```bash
python3 -m unittest discover -s tests -p 'test_threshold_kms_preflight.py'
```

These synthetic tests only cover source-provenance/compatibility diagnostics.
They must never be labeled cryptographic acceptance.

See `docs/threshold-release-boundary.md` and Issue #36 for the complete
acceptance contract.
