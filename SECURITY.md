# Security

## Supported release

The current reference-kernel API version is v0.2.0. The v0.3 private runtime
work on main is unreleased and does not claim normative PRIVATE or FULL
conformance.

## Security model

TclMesh treats the installed manifest as authoritative semantics.

Important boundaries:

- action semantics are canonical data, not mutable procedure callbacks;
- manifest activation is versioned and hash-bound;
- action invocation requires an active language, matching holder identity, granted command, and granted capability;
- state-dependent mutation checks run inside the storage transaction or equivalent atomic guard;
- external effects are proposed separately and require an explicit authorization/execution step;
- delegated language authority can only narrow;
- the private runtime uses opaque backend handles; the bundled plaintext backend
  is a reference implementation and provides no cryptographic confidentiality;
- circuit/output provenance and quorum state do not establish application release
  authorization or authenticate cryptographic shares. Those boundaries remain
  explicit v0.3 obligations in the roadmap.

## Deployment requirements

Manifest, language, effect, workflow, audit, and release registries support the
pluggable store interface. The file adapter provides a single-process reference
boundary; it does not establish multi-process or distributed consistency. Attach
stores explicitly for crash recovery and reconstruct the trusted profiles and
backend configuration before reopening release state.

Persistent private handles require backend-controlled export/restore. Protect
recovery stores according to the backend's requirements: the plaintext reference
backend writes plaintext values. Store content is trusted authority data, not an
untrusted import format. Legacy release-only stores fail closed and need explicit
migration while the original backend state remains available.

`private evaluate-bound` resolves an installed circuit from the active manifest;
it does not authorize its caller. Low-level private/release APIs are trusted
adapter entry points and must not be exposed directly to ordinary untrusted
languages. Supply application authorization, backend key/share validation, and
durable deployment boundaries before treating these APIs as production private
computation or release authorities.

Application-supplied storage and effect adapters are trusted components. Keep them narrow, deterministic where required, authenticated, and separately tested.

## Reporting

Use the repository's private security-reporting mechanism when available. Do not include secrets, production credentials, decrypted private data, or raw cryptographic key material in public issues.
