# Security

## Supported release

The v0.1.x line is the currently supported reference-kernel series.

## Security model

TclMesh v0.1.0 treats the installed manifest as authoritative semantics.

Important boundaries:

- action semantics are canonical data, not mutable procedure callbacks;
- manifest activation is versioned and hash-bound;
- action invocation requires an active language, matching holder identity, granted command, and granted capability;
- state-dependent mutation checks run inside the storage transaction or equivalent atomic guard;
- external effects are proposed separately and require an explicit authorization/execution step;
- delegated language authority can only narrow;
- private-computation support is circuit IR only; no cryptographic confidentiality is provided by v0.1.0 itself.

## Deployment requirements

The reference manifest, language, and effect registries are memory-backed. Applications requiring crash durability or multi-process consistency must place equivalent durable storage behind their deployment boundary before treating those registries as production authorities.

Application-supplied storage and effect adapters are trusted components. Keep them narrow, deterministic where required, authenticated, and separately tested.

## Reporting

Use the repository's private security-reporting mechanism when available. Do not include secrets, production credentials, decrypted private data, or raw cryptographic key material in public issues.
