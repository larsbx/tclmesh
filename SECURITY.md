# Security

## Supported release

The current reference-kernel API version is v0.2.0. The v0.3 private runtime
work on main is unreleased and does not claim normative PRIVATE or FULL
conformance.

## Security model

TclMesh treats the installed manifest as authoritative semantics.

Important boundaries:

- action semantics are canonical data, not mutable procedure callbacks;
- ordered comparisons and list membership accept only a canonical domain
  (decimal numbers, quote- and backslash-free lists), so Tcl's hex/octal number
  parsing and string substitution cannot change a policy decision;
- the Rust kernel refines the Tcl evaluator and fails closed on input whose
  meaning depends on Tcl's lack of value types;
- manifest activation is versioned and hash-bound;
- action invocation requires an active language, matching holder identity, granted command, and granted capability;
- state-dependent mutation checks run inside the storage transaction or equivalent atomic guard;
- external effects are proposed separately and require an explicit authorization/execution step;
- delegated language authority can only narrow;
- the private runtime uses opaque backend handles; the bundled plaintext backend
  is a reference implementation and provides no cryptographic confidentiality;
- under an `int<W>-checked` profile, encrypted integer results are exact: a
  circuit is evaluated only if its range certificate, checked by a checker
  proved sound in Lean, keeps every intermediate inside the `W`-bit word.
  Public inputs and handles are checked against their declared ranges. A
  ciphertext's range is established in one of three ways. It can be proved by
  the encrypting party with a TFHE-rs zero-knowledge proof of encryption
  (`tclmesh private import`); the runtime verifies the proof, bound to a
  context, offset and width, and never sees the value. It can be enforced
  inside the circuit by `tclmesh range guard`, which clamps each such input
  homomorphically, so only the ciphertext type (a `W`-bit word) is assumed;
  out-of-range values are clamped, not rejected. Or it is the encrypting
  party's claim, checked against the plaintext at `encrypt`. A proven range
  rests on the ciphertext's width and TFHE-rs's sanitizing expansion, which
  cleans every 2-bit block into `[0, 4)`, not on the CRS: even a forged proof
  yields an offset below `2^k`. What the proof adds, and what a CRS trapdoor
  would let its holder forge, is knowledge soundness: that the encrypting
  party knows its plaintext, so it cannot submit a function of another
  party's ciphertext (another bidder's bid plus one) under its own context.
  No prover may know the trapdoor. `tclmesh-tfhe-crs init|contribute|verify`
  runs a multi-party ceremony whose trapdoor is unknown unless every
  contributor colludes, and `private publish PROFILE DIR CEREMONY` verifies
  it (each contribution's proof of knowledge, the chain of contributions, and
  the CRS's power structure, by pairings) before adopting it; a ceremony
  without contributions has the public trapdoor `1` and is refused.
  The chain shows that each contribution's secret was known to someone, not
  to whom: a coordinator could make every contribution itself. So a
  contributor signs its receipt with a long-term key
  (`tclmesh-tfhe-crs keygen`, `contribute DIR SECRET`); the receipt binds
  the contribution and its place in the chain, so a signature cannot be
  moved. `private publish PROFILE DIR CEREMONY TRUSTED` adopts the ceremony
  only if one of the TRUSTED public keys signed a contribution, so trusting
  any one of those parties to discard its secret suffices. Without TRUSTED,
  unsigned ceremonies are accepted and the key holder must trust whoever ran
  them; signatures are then checked but name no one the key holder relies
  on. Alternatively `private publish PROFILE DIR CRS` adopts a CRS that
  one third party generated with `tclmesh-tfhe-crs CRS`, who must then be
  trusted; without either, the backend generates one itself, and the key
  holder must be trusted not to forge proofs. A
  proof context is single-use: a second import under it is refused while the
  first handle's record exists (destroyed handles keep theirs). A proof is
  also bound to the public key it was made under. By default each TFHE
  backend process generates fresh keys, so handles and consumed contexts last
  one process and a proof replayed into a later one fails verification. With
  `TCLMESH_TFHE_KEYS=DIR` the keys (the client key private to its owner) and
  an adopted CRS persist in DIR, and the backend gains `persistent-handles`:
  with a handle store attached (`tclmesh release use-store`), handles survive
  restarts as ciphertexts bound to their keyset, refused under any other,
  and so do the consumed contexts in their records. The persistent key
  directory must be a private, non-symlink directory (mode 0700) and its
  existing client-key.bin must be a regular, non-symlink file (mode 0600);
  insecure backup restores fail closed. DIR contains the decryption key and
  is not appropriate for an untrusted host. Context consumption is durable
  **only within the one authoritative handle store used for both imports and
  recovery**. Multiple stores sharing the same keyset do not coordinate
  context reuse. Parallel processes and distributed at-most-once import
  require an additional atomic, keyset-scoped claim protocol; this reference
  file store does not provide it. In particular, do not operate separate
  handle stores under a shared keyset while claiming global replay exclusion.
  A proven range is `[lo, lo + 2^k − 1]`, for even `k ≤ 16` or `k = 32`; for an exact `[lo, hi]`, `import`
  takes `hi` and holds `min(lo + a, hi)`, so a dishonest input is clamped to
  `hi`. To reject it instead, `range-check` computes the bit `lo ≤ x ≤ hi`
  under encryption, a release quorum decrypts that bit alone, and `admit`
  narrows the handle only if it is `1`. The release reveals exactly that bit,
  which a zero-knowledge verifier's verdict would also reveal, and the quorum
  is trusted to decrypt it honestly.
  Profiles declaring `int<W>-wrapping` make no exactness claim. The TFHE
  backend supports `W` = 32 and 64 (`FheInt32`, `FheInt64`); a handle of one
  width is never evaluated in a circuit of the other;
- governed circuits require manifest-declared release policy and role-specific
  holder/language authorization; caller identity must be authenticated by the
  trusted adapter. These checks do not authenticate cryptographic shares.

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
it does not authorize its caller. Outputs linked to a `threshold-release`
ceremony require the authorized release APIs and reject direct decryption. Outputs
without that link retain the legacy trusted-adapter path and make no governed
release claim. Low-level private/release APIs are trusted
adapter entry points and must not be exposed directly to ordinary untrusted
languages. Supply identity authentication, backend key/share validation, and
durable deployment boundaries before treating these APIs as production private
computation or release authorities.

Application-supplied storage and effect adapters are trusted components. Keep them narrow, deterministic where required, authenticated, and separately tested.

## Reporting

Use the repository's private security-reporting mechanism when available. Do not include secrets, production credentials, decrypted private data, or raw cryptographic key material in public issues.
