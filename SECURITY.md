# Security

## Supported release

The v0.3.x line is the current TclMesh reference-kernel series.

## Security model

TclMesh treats installed manifests as authoritative semantics and separates declaration-time flexibility from runtime authority.

Important boundaries:

- action semantics are canonical data, not mutable procedure callbacks;
- manifest activation is versioned and hash-bound;
- action and workflow invocation require active language authority and matching holder identity;
- delegated language authority can only narrow;
- state-dependent mutation checks run inside the storage transaction or equivalent atomic guard;
- external effects are proposed separately and require explicit authorization/execution;
- effect retry after uncertain execution requires declared idempotency or explicit reconciliation;
- workflow retry after uncertain execution requires idempotent steps or explicit reconciliation;
- private backend tokens remain internal to the runtime; application code receives opaque ct:* handles;
- ciphertext handles are bound to backend, profile, and logical type;
- direct private decrypt is controlled by immutable profile policy;
- threshold release binds one handle/profile to a fixed holder set, threshold, purpose, and contribution set before backend combination.

## Private-computation warning

The built-in plaintext backend is **not encrypted and provides no confidentiality**. It exists only to validate the backend protocol and provide deterministic reference/differential execution.

Likewise, plaintext-backend threshold contributions are test acknowledgments, not cryptographic partial decryptions. A deployment that requires homomorphic encryption, threshold cryptography, function privacy, or secure key custody must provide an audited backend implementing those properties.

Opaque handles prevent application code from receiving backend tokens through the public TclMesh API; they do not by themselves make the underlying backend confidential.

## Persistence and deployment

The built-in file store is a single-process reference adapter. It refreshes before read/modify/write and uses atomic same-directory replacement, but it does not provide inter-process locking or distributed consensus.

Applications requiring multi-process or distributed authority must use an appropriate external storage/coordination boundary.

Private ciphertext handles are currently process-local runtime objects. Persisted threshold-release state can be restored, but a restarted process also needs a backend-specific strategy for reconstructing or externally resolving the bound ciphertext handle before combination. v0.4 tracks this explicitly.

Application-supplied storage, effect, workflow, and private-computation backends are trusted components. Keep them narrow, deterministic where required, authenticated, and independently tested.

## Reporting

Use the repository's private security-reporting mechanism when available. Do not include secrets, production credentials, decrypted private data, raw cryptographic key material, or confidential backend tokens in public issues.
