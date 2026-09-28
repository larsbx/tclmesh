# TclMesh v1 Normative Core

The key words MUST, MUST NOT, SHALL, SHALL NOT, SHOULD, SHOULD NOT, and MAY are normative.

## Conformance profiles

A TclMesh implementation MAY implement these independently testable profiles:

- CORE
- MACRO
- POLICY
- DEONTIC
- LANGUAGE
- WORKFLOW
- PRIVATE
- SUPERVISION
- FULL

FULL SHALL satisfy all profiles.

## Canonical execution

Authoritative execution MUST depend on a canonical installed manifest and explicit runtime state.

Installed manifests SHALL be immutable. A semantic change requires compilation of a new manifest, verification, comparison, authorization, and activation.

A registry keyed only by application identifier SHALL reject a second installation under an already-installed identifier. An implementation that supports multiple versions SHALL retain versioned/hash-bound manifest entries and use a distinct activation operation; installation SHALL NOT silently replace an installed manifest.

A versioned registry SHALL reject replacement of an already-installed application/version pair. Installation MAY add a distinct version without changing which version is active. Activation SHALL identify the exact application, version, and expected manifest hash; a hash mismatch SHALL fail activation. Authoritative execution SHALL pin the activated version and manifest hash at request start.

Canonical serialization SHALL define deterministic key ordering, scalar normalization, identifier normalization, and semantic list ordering. It SHALL NOT depend on ambient hash iteration order, undeclared timestamps, or undeclared randomness.

The reference registry SHALL compute a SHA-256 digest over the canonical manifest byte sequence. Hashing SHALL use an explicit byte encoding. A change to the canonical manifest SHALL produce a distinct manifest identity except for the ordinary collision bound of the selected digest.

## Action lifecycle

An authoritative action SHALL execute in this order:

1. resolve manifest;
2. resolve language instance;
3. resolve canonical action;
4. verify capability;
5. bind actor;
6. bind context;
7. cast arguments;
8. construct query or changeset;
9. establish the transaction boundary, or establish an equivalent atomic version/predicate guard, before any state-dependent authorization, deontic evaluation, validation, or change calculation that can affect a mutation;
10. load or reload the authoritative current state inside that boundary;
11. evaluate state-dependent authorization preconditions;
12. evaluate state-dependent deontic rules;
13. execute state-dependent validations;
14. calculate changes from the guarded state;
15. calculate effect proposals;
16. persist state changes using the same transaction or atomic guard;
17. commit;
18. authorize post-commit effects;
19. execute effects;
20. emit outcome events;
21. return a structured result.

A mutating read-modify-write action SHALL NOT rely solely on state observed before the transaction boundary. If any state-dependent check is performed as a preflight optimization, it MUST be repeated against the authoritative state inside the transaction, or persistence MUST atomically compare the exact version or predicate assumed by that check.

## Structured errors

Operational code SHALL NOT parse error prose.

Errors SHALL contain at least:

```tcl
{
    class validation
    code missing-required-field
    message "Required field is missing"
    details {}
}
```

Core classes include invalid-input, type, validation, authorization, deontic-conflict, capability, state, not-found, conflict, deadline, quota, transaction, effect, circuit, ciphertext, release, language-expired, language-consumed, manifest, compiler, and internal.

## Macros

All macros SHALL fully expand before manifest installation.

Pure macros MUST NOT access network, filesystem, clock, environment, external processes, undeclared randomness, or mutable global application state.

The compiler SHALL enforce expansion depth, emitted-node limits, cycle detection, deterministic ordering, and declared emission contracts.

Every generated semantic node SHALL retain expansion lineage.

## Capabilities

No interpreter receives ambient sensitive authority by default.

Capabilities SHALL be explicit, scoped, expiring, revocable objects.

A delegated capability MUST satisfy:

```text
child authority subset-of parent authority
```

A child MAY narrow scope, shorten expiry, lower usage count, add restrictions, remove commands, remove delegation, and lower delegation depth. It SHALL NOT broaden authority.

Delegation SHALL preserve every parent context binding. A child MAY add context bindings that make the context strictly narrower, or repeat an inherited binding with the same value. It SHALL NOT remove or replace an inherited binding with a different value. Implementations with richer context predicates MUST establish that the child context denotes a subset of the parent context before delegation succeeds.

One-use capabilities SHALL transition through durable active/reserved/consumed or active/reserved/released states.

## Language lifecycle

Language states are:

```text
provisioning
active
suspended
expired
consumed
revoked
destroyed
```

Only active instances MAY issue authoritative commands.

Any semantic change to an active language SHALL create a new generation.

Aliases MAY alter vocabulary but SHALL NOT alter canonical authority.

A conforming LANGUAGE implementation SHOULD expose `language why-not`.

## Fivefold deontic semantics

Canonical verdict symbols are W, N, M, K, H.

Rule applicability SHALL distinguish applicable, inapplicable, unknown, and invalid.

The resolver SHALL preserve hard admissibility conflicts, preference conflicts, priority conflicts, authority conflicts, temporal conflicts, jurisdiction conflicts, and unresolved conflicts.

Unknown SHALL NOT be silently treated as false unless a declared logic explicitly requires it.

Deontic judgment, authorization decision, and execution decision SHALL remain separate.

## Effects

External effects SHALL originate from validated canonical operations.

Effect lifecycle:

```text
proposed -> authorized -> executing -> succeeded
proposed -> denied
authorized -> executing -> failed
```

Externally meaningful transitions SHALL be durably recorded.

Effects SHOULD support idempotency identifiers.

Simulation environments SHALL possess no irreversible-effect capabilities.

## Workflows

Authoritative workflow state SHALL NOT depend solely on an interpreter stack, coroutine stack, process memory, or global variables.

Retries SHALL preserve capability checks, manifest checks, deadlines, and idempotency.

Compensation SHALL be represented by explicit actions or effects and its outcome SHALL be recorded.

## Private computation

Encrypted values SHALL NOT influence ordinary TCL control flow.

Every encrypted input SHALL bind to a declared logical type, keyset, cryptographic context, parameter profile, and where relevant packing layout.

Every private circuit SHALL have a canonical hash.

The compiler SHOULD perform range analysis for all intermediate nodes. Unsafe overflow SHALL be rejected unless an explicit checked overflow semantic is declared.

Packing layout is part of circuit identity.

Private output SHALL remain opaque until an authorized release procedure succeeds.

Application manifests SHALL contain key metadata but SHALL NOT contain raw secret decryption material.

Ordinary language instances SHALL never receive raw secret-key access.

## Threshold release

Release states are:

```text
pending
collecting
quorum-reached
combining
released
rejected
expired
failed
```

Partial release contributions SHALL bind to one request, ciphertext, circuit, output specification, and purpose.

Replay of a consumed release contribution SHALL fail.

## Supervision

Supervised units SHALL declare restart policy, shutdown timeout, and health semantics.

Supported restart strategies are one-for-one, one-for-all, and rest-for-one.

Restart intensity SHALL be bounded. Exceeding the bound SHALL escalate failure instead of restarting indefinitely.

Crash reports SHALL be structured and SHALL redact protected plaintext.

## Security invariants

- INV-S1: no ambient effect authority.
- INV-S2: external effects originate from validated canonical operations.
- INV-S3: delegated authority never exceeds ancestor authority.
- INV-S4: encrypted output becomes plaintext only through authorized release.
- INV-S5: authoritative actions, judgments, circuits, and effects bind to a manifest hash.
- INV-S6: one-shot actions and ceremonies are replay-resistant.
- INV-S7: ordinary scripts never access raw decryption keys.
- INV-S8: decision authority does not imply effect authority.
- INV-S9: simulation cannot execute irreversible effects.
- INV-S10: every active language can report its authority and provenance.

## Compiler invariants

- INV-C1: all macros fully expand before installation.
- INV-C2: unknown canonical node types are rejected.
- INV-C3: every field and action reference resolves.
- INV-C4: every expression type-checks.
- INV-C5: private operations use compatible cryptographic types.
- INV-C6: extension capabilities are declared.
- INV-C7: macro expansion cycles fail compilation.
- INV-C8: rule defeat relations reference valid rules.

## Private-computation invariants

- INV-H1: encrypted values do not control ordinary interpreter branching.
- INV-H2: circuit structure is fixed before private execution.
- INV-H3: every encrypted input binds to declared type and keyset.
- INV-H4: every circuit has a manifest-bound circuit hash.
- INV-H5: every release declares an output policy.
- INV-H6: production circuits SHOULD have plaintext reference tests.
- INV-H7: cryptographic parameters come from approved parameter profiles.

## Conformance suites

CORE covers determinism, resources, types, actions, changesets, query rejection, manifest hashing, required-field rejection, and structured errors.

MACRO covers declaration, expression, semantic expansion, hygiene, provenance, limits, cycles, emission contracts, determinism, and declared build inputs.

POLICY covers permit, deny, conditional decisions, filter authorization, expiry, one-use consumption, attenuation, anti-amplification, context binding, and explanation.

DEONTIC covers W/N/M/K/H, hard conflict, preference conflict, exception, specificity, unresolved conflict, unknown applicability, and certificate reproducibility.

LANGUAGE covers instantiation, aliases, capability absence, context binding, generation replacement, expiry, revocation, one-shot consumption, delegation, attenuation, collision handling, why-not, lineage, and terminal destruction.

WORKFLOW covers dependency ordering, durable restart, retry, deadlines, compensation, manifest pinning, terminal state, idempotency, and effect replay prevention.

PRIVATE covers type compatibility, keyset mismatch, branch rejection, circuit canonicalization, circuit hashing, overflow, packing identity, reference equivalence, opaque output, release authorization, quorum, insufficient quorum, replay rejection, circuit binding, and secret-key opacity.

SUPERVISION covers crash detection, restart strategies, intensity limits, structured reports, shutdown timeout, timer expiry, isolation, and reconstruction.

## Definition of done

Version 1 is complete when one integrated executable acceptance scenario can:

1. define a resource;
2. generate resource elements through a macro;
3. define a state-transition action;
4. attach authorization;
5. attach a fivefold rule;
6. compile a canonical manifest;
7. instantiate a user-specific language;
8. delegate a strictly narrower agent language;
9. invoke an action through that language;
10. produce a judgment certificate;
11. produce authorization and execution decisions;
12. create an effect proposal;
13. execute or reject the effect;
14. evaluate a private aggregate;
15. request threshold release;
16. complete release;
17. consume a one-shot capability;
18. revoke the language;
19. restart a failed runtime worker;
20. reconstruct complete operation provenance.

If authoritative behavior in this scenario depends on hidden mutable semantics outside canonical manifest data and explicit runtime state, v1 is not complete.

## Central invariant

```text
maximum expressiveness before compilation
minimum ambiguity after compilation
```

New domain abstractions SHOULD normally be introduced by TCL macros and extensions that compile to existing canonical nodes, rather than by widening the trusted runtime kernel.
