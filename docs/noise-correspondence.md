# Noise model correspondence and limits

Audited against **TFHE-rs 1.8.2**, tag `tfhe-rs-1.8.2`, source commit
`e8f3926bb53d7eea95e8a7f581f60aae1c7aba16`. The runtime pins `=1.8.2`
and its lockfile; this audit does not cover other versions.

## Repaired claims

The previous checker accepted `[.lin [] 32]` with output 0, because it only
validated output noise. The integer decoder returned 32 although the native
phase wraps. `checkedStep` now validates **every wire**, including dead
intermediates, fresh inputs and PBS results: `0 ≤ lo ≤ hi ≤ maxDeg` and
`level ≤ maxLevel`. `analyze_admissible` and
`bootstrapped_representable` prove the resulting representability property.
This is deliberately conservative. The IR's linear combination is one atomic
modeled gate; no arbitrary signed linear expression's native lowering is
proved. A native lowering must also justify its intermediate operations.

`bootstrapped_sound` requires `CallsGood` on the actual evolving execution.
`CallGood` names one LUT and one ciphertext and includes both the correct
message and a hard bound on output noise. There is no universal success claim
about a sampled function on unused inputs. Boot functions and input noise may
share randomness; independence is never assumed.

`NoiseProbability` gives an exact finite weighted model of complete joint
random tapes. Positive integer weights represent rational probabilities;
normalization divides by positive total mass. `ConditionalBound fresh num den`
requires, at each reached PBS after all previous calls succeeded,

    den * firstFailureMass ≤ num * successfulPrefixMass.

For positive `den`, this is a conditional failure probability bound `num/den`.
A bound for each finer reachable history implies this aggregate prefix bound.
`failureMass_eq` identifies first-failure mass with actual failed execution
tapes. `output_failure_bound` proves

    den * incorrectOutputMass ≤ pbsCount * num * totalMass.

Taking `num = 1`, `den = 2^128` gives the familiar union bound **only if the
conditional premise for the full `CallGood` event is independently justified**.
Neither the TFHE-rs parameter label nor isolated per-fixed-input estimates
prove that premise under adaptive, correlated key/ciphertext reuse. A decode
failure estimate also does not by itself bound the stronger event that output
noise exceeds the model's absolute fresh bound while still decoding correctly.
There is no unconditional native `pbsCount * 2^-128` theorem here. Bad input
noise must be excluded by `Fresh` on the sample population or charged as a
separate failure event. Arbitrary non-rational probability spaces are not
formalized by this finite model.

## Versioned source evidence

All source links below are pinned to the audited commit.

| Library behavior | Evidence | Status of correspondence |
| --- | --- | --- |
| Default computation parameters select message 4 / carry 4 TUniform parameters | [aliases](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/parameters/aliases.rs); [default config](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/high_level_api/keys/inner.rs) | Runtime `config()` uses the default computation parameters plus dedicated compact-PKE parameters. This audit's native test explicitly selects the aliased computation parameter. |
| V1_8 aliases V1_4; moduli 4/4, max noise level 5, `log2_p_fail = -129.581` | [V1_8](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/parameters/v1_8/classic/tuniform/p_fail_2_minus_128/ks_pbs.rs); [V1_4](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/parameters/v1_4/classic/tuniform/p_fail_2_minus_128/ks_pbs.rs) | Values are inspectable and asserted by the native test. The numerical error estimate remains upstream cryptographic analysis, not a Lean proof or a statistical test result. |
| Degree bound 15; noise metadata is summed/scaled and reset to nominal after nontrivial PBS | [metadata](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/ciphertext/common.rs); [server](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/server_key/mod.rs) | Metadata supports a target PBS error rate; nominal does not mean a proved absolute phase bound. Trivial PBS can have zero noise. Lean's hard `fresh` bound is an additional assumption. |
| Checked add checks degree and noise; checked scalar add checks degree; unchecked operations bypass checks | [add](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/server_key/add.rs); [scalar add](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/server_key/scalar_add.rs) | The static checker is a conservative discipline, not an assertion that all library APIs enforce it. |
| Native encoding has `delta = 2^59`, padded cleartext modulus 32, and wrapping u64 phase arithmetic | [encoding](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/encoding.rs) | `torus_decode_tfhe22` proves rounded modular decoding equals the represented message under the explicit absolute-noise premise; `bootstrapped_torus_sound` applies this to every checked output. The integer phase is a lift; negative noise at zero can wrap, so “no phase reduction ever occurs” is false. |
| `decrypt_message_and_carry` retains carry; `decrypt` additionally reduces modulo message modulus 4 | [client](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/client_key/mod.rs) | The block theorem corresponds to message-and-carry decoding. A value 15 decodes as 3 with message-only `decrypt`. |
| PBS uses a generated LUT; native result degree is the LUT degree and noise metadata becomes nominal | [server](https://github.com/zama-ai/tfhe-rs/blob/e8f3926bb53d7eea95e8a7f581f60aae1c7aba16/tfhe/src/shortint/server_key/mod.rs) | Lean zero-extends its list LUT; a refinement must generate the same function over the whole block domain. Native PBS correctness and the joint conditional error/noise bound remain assumptions. |

## Reproducible checks

- `cd spec && lake build && lake env lean Audit.lean`: all proofs, exact
  counterexamples, negative controls, and standard-axiom audit. Regression
  theorems cover constants 32/16/−1, degree 15, unused overflow, PBS result
  overflow, isolated noise levels 5/6, malformed disciplines and references,
  unused bad arguments and a correlated execution violating the conditional
  premise.
- `cargo test --release --locked --manifest-path backends/tfhe/Cargo.toml --test noise`:
  native parameter values, checked degree boundary, exact 32-to-zero wrap,
  message-only versus carry decoding, isolated metadata noise checks, and
  nontrivial PBS samples. These finite samples do not estimate rare failures.
- The existing TFHE workflow is now triggered by `Noise*.lean` changes and
  runs all native backend tests and the Tcl TFHE acceptance corpus.

The Range model still assumes TFHE-rs integer functional correctness. Neither
native integer-to-block refinement, native PBS implementation correctness,
nor the probabilistic premises above are discharged by this follow-up.
