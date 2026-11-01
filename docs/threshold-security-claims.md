# Issue #36 — threshold claim admission: numerical obligations only

The implementation in `src/release.tcl` remains fail-closed for
`cryptographic-threshold-decryption`. This small independent diagnostic and
Lean model prevent confusing **client response counts** with **cryptographic
secrecy thresholds** before a backend is chosen.

## Four distinct parameters

- `n` = distinct independently held participant key shares;
- `q` = claimed *cryptographic* reconstruction threshold for a policy;
- `f_priv` = adversarially corrupted participants for whom an independently
  reviewed protocol establishes plaintext/secret confidentiality;
- `f_byz` = malicious/offline faults that the protocol tolerates;
- `r_output` = number of responses needed by a particular client-side
  reconstruction procedure.

The numerical **necessary** conditions for claiming any-`q`-of-`n` secrecy are:

```
1 <= q <= n
q - 1 <= f_priv
1 <= r_output <= q
```

A protocol might have stricter constraints. The last inequality is necessary
for a protocol claimed to reconstruct from **any** `q` parties, not a proof of
availability. For robust MPC schemes, constraints such as `f_byz < n/3` may
also apply, but are **scheme-specific**; one cannot substitute `f_byz` for
`f_priv`. No integer predicate proves cryptographic soundness, share-key
custody, noise correctness, malicious-secure transcript validation, or recipient
delivery.

For the publicly documented Zama KMS four-party sample, the recorded response
threshold is `r_output = 3`; the published fault/corruption profile is
`f_byz = 1` and the privacy guarantee described in the current documentation
is at most `f_priv = 1`. Thus a *claim* of `q = 3` would require
`f_priv >= 2`, which this documented guarantee does not establish. This
is **not** a proof that two-party compromise works. In fact, **no**
`q` in `1..4` passes these *necessary* checks for the particular sample
numbers: `r_output=3` requires `q>=3`, whereas `f_priv=1` can only
justify `q<=2`. The synthetic tests enumerate all four choices.
A different scheme/proof/parameter profile could behave differently. The
exact pinned KMS source is still inaccessible in the existing hosted source
experiment, so this remains a candidate-level decision gate, not source-
audited cryptography.

## Reproduce the independent checks

```bash
# Report an unsupported security claim (exit 2, CLAIMS_REJECTED).
python3 tools/check_threshold_security_claims.py \
  --parties 4 --release-quorum 3 --privacy-corruptions 1 \
  --byzantine-faults 1 --client-responses 3

# A hypothetical claim passes the arithmetic gate ONLY (exit 0).
python3 tools/check_threshold_security_claims.py \
  --parties 4 --release-quorum 3 --privacy-corruptions 2 \
  --byzantine-faults 1 --client-responses 3

python3 -m unittest discover -s tests -p 'test_threshold_security_claims.py'
(cd spec && lake build && lake env lean Audit.lean)
```

The first command produces `CLAIMS_REJECTED`; the second produces
`NECESSARY_CHECKS_ONLY`. **Neither result enables a backend or grants a
release capability.** The program contains a hard-coded
`production_cryptographic_release_enabled: false` field and cannot be used
as a runtime authorization oracle. These inputs can be forged and do not
bind an implementation to any audited primitive. The Lean definitions and
small proofs in `TclMesh.ThresholdSecurity` are similarly about finite
natural-number implications only.

## Actual acceptance remains pending

For each candidate scheme, independently validate: pinned source hashes,
exact proven `f_priv` and fault model; no evaluator-owned complete secret key;
real verification of each partial or malicious-secure MPC transcript; supported
any-`q` subsets, negative tests at `q-1`, forged share and keyset/epoch/replay
controls; recipient-bound delivery; crash/retry/rotation; and cryptographic
review. Do not re-label an authorization quorum as any-`q` threshold.
The runnable diagnostic is an early rejection filter, **not a security
certificate**.

See Issue #36 and `docs/threshold-release-boundary.md` for the acceptance
contract.
