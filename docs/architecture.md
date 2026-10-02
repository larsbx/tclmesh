# TclMesh Architecture

## System model

TclMesh treats an application as a compiled TCL language environment rather than a collection of opaque callbacks. Resources, actions, policies, deontic rules, workflows, private circuits, and language capabilities compile into one canonical manifest.

```text
TCL declarations and macros
    -> capture and expansion
    -> symbol/type/capability resolution
    -> policy and deontic verification
    -> private-circuit lowering
    -> canonical manifest
    -> runtime execution
```

## Canonical manifest

The installed manifest is authoritative. It contains no unexpanded macros and no arbitrary opaque runtime script bodies.

```tcl
{
    manifest_version 1
    application {id private-operations version 1}
    types {}
    resources {}
    actions {}
    policies {}
    rules {}
    circuits {}
    workflows {}
    ceremonies {}
    languages {}
    capabilities {}
    provenance {}
    manifest_hash {}
}
```

Two semantically identical manifests must serialize identically.

## Resources and actions

A resource describes an application entity. Actions are the canonical means of reading or transforming state.

```tcl
resource Shipment {
    attributes {
        attribute id uuid -primary true -generated true
        attribute owner_id uuid -required true
        attribute state enum -values {
            proposed accepted collected delivered cancelled
        }
    }

    actions {
        action accept update {
            validate {
                transition state {proposed} accepted
            }
            change {
                set state accepted
            }
        }
    }
}
```

Changes are represented as values, not hidden mutation.

## Macro model

TclMesh supports declaration, expression, semantic, resource-pattern, workflow, language, and private-computation macros.

Generated semantic nodes retain source location, macro definition, macro invocation, expansion lineage, and stable generated-symbol identity.

Pure macros may not depend on network, clock, environment, filesystem, undeclared randomness, or mutable global application state.

## Fivefold deontic semantics

TclMesh supports five action verdicts:

- W — obligatory
- N — recommended
- M — permissible
- K — discouraged
- H — forbidden

The five verdicts are not a numeric scale. Their internal semantics separate admissibility from preference.

```text
W  perform-required  perform
N  both-allowed      perform
M  both-allowed      neutral
K  both-allowed      omit
H  omit-required     omit
```

Resolution also records whether a judgment is determinate, conflicted, underdetermined, inapplicable, invalid-context, or indeterminate. A conflict is never silently converted into permissibility.

## Language instances

A language instance is a first-class runtime object:

```text
L = <V,G,S,C,X,P,T>

V vocabulary
G grammar and macros
S canonical semantics
C capabilities
X context bindings
P provenance
T lifecycle
```

A language instance may belong to a user, agent, task, contract, session, object, workflow, ceremony, incident, appeal, negotiation, device, or location.

Delegation is capability attenuation: a child language cannot acquire authority absent from its parent.

## Policy, deontic, and execution are separate

```tcl
{
    deontic {status determinate verdict K}
    authorization {decision permit}
    execution {decision require-confirmation}
}
```

The software therefore does not confuse normative judgment with operational permission.

## Private computation

Private computations are expressed as typed circuit ASTs.

```tcl
encrypted-application PrivateEligibility {
    input age       {cipher uint8}
    input income    {cipher uint32}
    input threshold {public uint32}

    output eligible {cipher bool}

    circuit {
        set adult [he ge $age 18]
        set qualified [he le $income $threshold]
        return [he and $adult $qualified]
    }
}
```

Encrypted values may not control ordinary TCL branching. Conditional selection over protected values must be represented explicitly in the private circuit.

Every production circuit should have canonical circuit identity, range analysis, packing identity, a parameter profile, a plaintext reference evaluator, encrypted simulation, and a release policy.

## Threshold release

Private output release is an explicit governed operation.

```tcl
decrypt-ceremony AggregateRelease {
    threshold 3-of-5
    requires {
        circuit-hash-approved
        output-type aggregate
        purpose quarterly-report
    }
    release {total average}
}
```

## Effects

Decisions and effects are separate.

```text
action evaluation
    -> effect proposal
    -> policy check
    -> effect authorization
    -> durable ledger entry
    -> effect execution
    -> outcome entry
```

A script that proposes an effect does not automatically possess authority to execute it.

## Workflows, ceremonies, and supervision

Authoritative workflow state is serializable and reconstructable. It must not depend solely on a coroutine stack, interpreter stack, or process memory.

Ceremonies add participants, phases, quorum conditions, and phase-specific languages.

Long-running compiler workers, language instances, private workers, workflow runners, ceremony coordinators, and effect executors are supervised fault domains.

## Central invariant

```text
maximum expressiveness before compilation
minimum ambiguity after compilation
```

New domain abstractions should normally be introduced by TCL macros and extensions that compile to existing canonical nodes, rather than by widening the trusted runtime kernel.


### Threshold release process recovery

Attaching a release store also attaches the private handle registry to that store
under `private.handles`. Backend recovery material is stored separately from the
public release descriptors. Handle IDs, allocation counter, profile binding, and
destroyed tombstones survive a process restart. Configure the same profiles and
register their backends before reopening the release store. Existing stores with
only `release.registry` do not contain enough information for fresh-process
recovery and are rejected on reopen. Migrate such stores explicitly while the
original private registry and backend state are available. Lost backend state
cannot be reconstructed from a `ct:*` ID alone.

Persistence requires the backend capability `persistent-handles`. The backend
implements `export-handle profile type token` and
`restore-handle profile type recovery-material`. Export must return durable,
serializable recovery material; restore must validate it and return a usable
backend token or fail closed. For real backends, use an authenticated ciphertext
or a stable backend-owned object reference, with revocation and authorization
checked by the backend. Tclmesh does not reinterpret recovery material as a token.
Public `handle describe` and release descriptors never expose it. Unsupported
backends cannot attach their active handles to a persistent registry. Restoring
with a changed profile is rejected. Store and backend access remain trusted,
single-writer configuration, as with the existing pluggable registry stores.

The plaintext reference backend serializes its value and provides no confidentiality;
its recovery files contain plaintext. This is a test contract, not a cryptographic
threshold backend. Applications must protect recovery stores appropriately for
the selected backend. The existing `idempotent-release` requirement still governs
retrying an uncertain `combining` state.

R-010 through R-014 launch independent Tcl processes, including a process that
exits inside the combination callback after the `combining` commit. They cover
quorum restart, uncertain retry, destroyed handles, backend restoration rejection,
profile changes, ID allocation, opaque descriptors, and direct-decrypt prohibition.


### Circuit identity and manifest-bound evaluation

`private canonical circuit` sorts named input/output/node maps and the declared
metadata maps `output_nodes` and `packing`, preserving ordered type descriptors
and operations. Other metadata values are opaque; callers must use stable scalar
representations for them. `private digest circuit` hashes the UTF-8 Tcl list
`{tclmesh-private-circuit-v1 <canonical-circuit>}` with SHA-256. The domain tag
separates this identity from manifest identity. Packing identity is included;
packing validity, type inference, and overflow proofs remain separate obligations.

`private evaluate-bound profile application circuit-id inputs` reads the active
manifest, verifies its hash, and resolves the named installed circuit. An optional
circuit `metadata profile` must match the supplied profile. Each returned opaque
handle records a public `binding` containing application ID, manifest version/hash,
circuit ID/hash, output name, and ordered output specification. The caller cannot
provide this provenance through request context. Changing the active manifest
later does not relabel an existing output. Ordinary `private evaluate` records
circuit/output identity without asserting a manifest pin; encrypted input handles
have an empty binding.

A release copies the handle's binding and rechecks it before combination or retry.
The backend receives it as `combine-release` context field `binding`, alongside
purpose, release ID, and application context. Persistence carries the binding with
the handle and request; PB-008 verifies the backend receives the original manifest
pin after a fresh process. Older requests/handles with no binding retain an empty
binding and gain no retroactive provenance.

This API establishes provenance, not authorization. The next slice must enforce
manifest-declared release policy and holder/language authority. Backends must still
verify cryptographic contribution scope and consumption; the plaintext reference
backend checks only the reference quorum lifecycle.

The [estate authority-first contract](https://github.com/larsbx/estate-governance/blob/main/docs/architecture/estate-repository-template-v2.md)
was consulted for this slice. `src/` remains
the sole runtime implementation; `tests/` supplies conformance evidence and
`docs/spec-v1.md` the normative target. TclMesh is not an estate-template adopter,
and this change introduces no new layout or authority migration.
