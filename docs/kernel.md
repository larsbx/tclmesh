# Tier A kernel

TclMesh separates the **meta-language** from the **kernel**:

| Tier | Form | Role |
|---|---|---|
| Meta-language | Tcl declarations, macros, compiler | writes languages; compiles them to canonical data |
| A: kernel | canonical action descriptors (data) | authoritative evaluation: authorization, deontic judgment, validation, changes, effect proposals |

Authoritative semantics never run as Tcl procedures. They are canonical
descriptors interpreted by three evaluators:

- `TclMesh.Kernel.evaluate` in `spec/`: the executable Lean specification, and
  the oracle. Its building blocks carry proofs (`docs/proofs.md`);
- `tclmesh-kernel` in `kernel/`: the Rust kernel, intended to become the
  authoritative executor. It must equal the specification on every input;
- `::tclmesh::action::evaluate` in `src/action.tcl`: the Tcl reference. It is
  untyped, so it agrees with the specification only up to kernel refusals.

Both are pure functions:

```text
evaluate(action_id, descriptor, state, request)
    -> {verdict, changed fields, proposed effects} | fault
```

No registry, store, clock, or other ambient input is consulted. `action run`
does the registry, language, and transaction work around the Tcl evaluator.

## Canonical comparison domain

A Tcl value has no type, which makes several Tcl behaviours unsafe in policy:
`expr` reads `0x10` as 16, `010` as octal 8, and `" 1"` as 1, and `in` applies
backslash and quote substitution to any string. Both evaluators therefore
restrict ordered comparisons and membership to a canonical domain:

- **Numbers** (`lt lte gt gte`) match
  `-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?`, with the written exponent at
  most 1000 in magnitude. Any other operand, including `Inf`, `NaN`, hex,
  octal, signs, and padding, raises `TCLMESH ACTION PREDICATE NON_NUMERIC op`,
  and `not` cannot invert that error. Numbers are **exact decimals**:
  `1e3 = 1000`, `0.10 = 0.1`, `-0 = 0`, and `0.1 < 0.10000000000000000001`.
  There is no floating-point rounding, and the order is a total preorder,
  proved in `spec/TclMesh/Decimal.lean`.
- **Lists** (`in`) contain only bare words and brace groups: no backslash, no
  double quote, braces balanced. Anything else raises
  `TCLMESH ACTION PREDICATE NON_CANONICAL_LIST`.
- `eq`, `neq`, and `contains` compare strings exactly. `contains` with an empty
  needle is false.

## Data model and refinement

Kernel inputs are JSON: strings are scalars, arrays are lists, objects are dicts.
Numbers, booleans, and null have no meaning. The kernel enforces types that Tcl
cannot see:

- reading a list or dict where a scalar is needed;
- following a path through a scalar;
- descriptor parts spelled as strings instead of lists.

In each case the kernel fails closed with `TCLMESH KERNEL NON_CANONICAL reason`.

The relations checked are:

- kernel `=` specification on **every** vector, refusals included
  (`conform --exact`);
- between the kernel `k` and the Tcl reference `t`: `k = t` on vectors marked
  `canonical`, and otherwise `k = t` or `k` is a `KERNEL NON_CANONICAL` refusal.

So the kernel computes exactly what the specification says. It never permits,
changes, or emits anything the Tcl reference would not, and on typed input it
agrees with the reference exactly.

## Conformance

```sh
tclsh tools/conformance.tcl check                    # recorded outcomes current
cargo test --manifest-path kernel/Cargo.toml         # unit + committed vectors
(cd spec && lake build spec-eval)                    # executable specification
tclsh tools/conformance.tcl generate 7 2000 3 > v.json
spec/.lake/build/bin/spec-eval v.json > s.json
kernel/target/debug/tclmesh-kernel conform v.json s.json --exact
tclsh tools/conformance.tcl run v.json > o.json
kernel/target/debug/tclmesh-kernel conform v.json o.json --min-agreement 0.6
```

- `conformance/vectors.json` holds curated cases.
- `conformance/expected.json` holds the outcomes the Tcl reference recorded for
  them, one per line. It is regenerated with `tools/conformance.tcl update`.
- The generator is a seeded 64-bit LCG, so a failing seed reproduces exactly.
  `NOISE` is the percentage of malformed choices.
- CI runs fixed seeds plus one seed per run.
- `conform` prints refusal counts by reason, so you can see what the kernel
  declined rather than only that it agreed.
- `tclmesh-kernel evaluate` reads `{action_id, descriptor, state, request}` on
  stdin and prints the outcome.

## Toward encrypted languages

The kernel is where ciphertext becomes a type, not a string. See
[roadmap](roadmap.md#encrypted-languages). The invariant is that the kernel can
route opaque ciphertext through declared circuits and attach provenance to it,
but holds no decryption capability. Release happens only through threshold
ceremonies whose key holders sit outside the kernel.
