# P2b dishonest-participant acceptance characterization

Date: 2026-11-05. Source: [draft PR #55](https://github.com/larsbx/tclmesh/pull/55),
revision `b5507710d9a1d2d81e8643803dcb7e3dfd7f1f1d`, stacked on #54 and #53.
This change adds research fixtures, tests, replay and documentation. It changes
no setup, relinearization, partial-generation, ceremony or governed-release
implementation. It is separate from Ajax native reproduction in issue #47.

**Result:** the honest 640-case P2b replay is preserved. A single canonical
partial alteration also flips the result in all 640 cases, including through
the P1 actor. Passing this characterization suite records that missing
verification; it does not establish malicious security or authorize release.

## Reproduce

From the repository root, with Python 3 and Erlang/OTP (compiler, Crypto, EUnit):

```sh
python3 -B tools/check_q45_adversarial.py --receipt /tmp/q45-adversarial.json
python3 -B -m unittest discover -s tests -p 'test_threshold*.py'
python3 -B tools/check_q45_ceremony_mutants.py
python3 -B tools/check_q45_toy_replay.py
```

The first command runs 18 Python adversarial tests, generates exact P2b
transcripts using the original RNG labels/order, compiles the unchanged P1
actor and the test replay module with `-Werror`, and independently decodes
their admitted shares in Erlang. Missing OTP or a failing replay is an error.
`--python-only` explicitly requests a reduced check and records that actor
replay did not execute. The JSON receipt includes source hashes, Python
version, measured counts and actor outcomes. A local full-run receipt is
committed at [q45-p2b-adversarial-receipt.json](../experiments/threshold_q45/q45-p2b-adversarial-receipt.json).

CI discovers the Python tests through the existing threshold suite, and the
`q45-ceremony` job runs the full independent P2b replay. The previously green
[PR #55 workflow](https://github.com/larsbx/tclmesh/actions/runs/41787764643)
predates these additions and is not evidence for their hosted acceptance.

Local verification on Python 3.12.14 and OTP 25 passed all 131 Python threshold
tests, all 12 ceremony EUnit tests and all 9 compiled ceremony mutants. The
unchanged P0/P1 actor replay also passed its 640 cases and 4 malformed probes.
All three existing governed-release boundary mutants were rejected. This is
local research evidence; it does not establish hosted or native-FHE acceptance.

## Observed outcomes

These are deterministic toy observations, not attack probabilities or security
estimates. No adversary in these tests accesses production keys or a release
endpoint. The single-process fixture can inspect every toy secret; tests that
use that ability are identified below.

| Experiment | Local result |
| --- | --- |
| Original P2b full-key inputs/seeds | 128/128 correct |
| Original P2b threshold inputs/seeds/quorums | 640/640 correct in Python and the P1 actor |
| 72-bit setting, required 40-bit margin | 61/128 ciphertexts miss the margin |
| 80-bit setting, margin and four-partial decoding bound | 0/128 failures of either check |
| Add `DELTA = floor(q/2)` to one partial's constant coefficient, modulo `q` | 640/640 canonical altered partial sets decode to the opposite bit, with all other coefficients zero; P1 records that opposite result |
| Add `2^80` to one partial's constant coefficient | 640/640 altered sets still decode correctly and complete in P1 |
| Oracle constructs one partial with actual residual `2^80 + 1` | 640/640 decode correctly despite violating the assumed per-holder bound; Python combiner does not check it |
| Alter one second-round contribution's first gadget term by `DELTA` | Accepted as canonical; all 128 ciphertexts fail full-key correctness and both 80-bit assumptions; all 640 threshold decodings fail equality with the expected plaintext |
| P2b/P1 malformed one-byte partial | Admitted as opaque payload, then aborts in the independent decoding callback in 4/4 seed probes |
| Ceremony transition suite | 12 EUnit tests pass; all 9 existing compiled transition mutants are rejected |

The altered-relinearization experiment has its own fixed ciphertext RNG labels;
it is a counterexample corpus, not a paired statistical comparison with the
honest noise corpus. A failed plaintext equality can include trailing nonzero
coefficients. Unlike the targeted partial bit flip, it is not claimed to yield
a well-formed opposite Boolean result in the P1 actor.

## Interface and failure matrix

Test names below are in
[test_threshold_q45_adversarial.py](../tests/test_threshold_q45_adversarial.py),
except the named EUnit cases in
[q45_ceremony_tests.erl](../experiments/threshold_q45/q45_ceremony_tests.erl).
“Rejected” means a local call or callback rejects, not that a malicious holder
is publicly identified or that other participants share the same view.

| Surface / attack | Current detection | Executable witness / remaining obligation |
| --- | --- | --- |
| Public shares, fragments, first- and second-round messages: missing, extra, or duplicate labels | Exact expected cardinality and sender sets reject | `test_withholding_and_duplicate_messages_are_rejected_at_each_setup_round`; no setup recovery or blame protocol |
| Noncanonical coefficients, wrong polynomial length | Public-share, holder and round aggregation ingress reject tested values, including bool coefficients | `test_noncanonical_coefficients_are_rejected_at_public_fragment_and_relin_ingress`; enforce canonical bytes and strict types at every untrusted entry point |
| Directly supplied truncated `FirstAggregate` | `second_round` accepts and emits a short share; relabeled full-length second shares let `evaluation_key` silently truncate the key through `zip` | `test_direct_aggregate_objects_bypass_aggregation_shape_checks`; do not assume dataclass construction authenticated a received aggregate |
| Sender impersonation using five distinct labels on one party's values | Accepted | `test_sender_labels_can_be_forged_without_authentication`; labels are not credentials |
| Same setup/session with changed public contribution / aggregate public key | Both evaluator keys accepted with the same relinearization transcript; altered key produces incorrect fresh decryptions | `test_inconsistent_public_keys_are_locally_accepted`; public-key agreement and a bound setup transcript are absent |
| Last public contributor cancels the other public values to select a key with an attacker-known secret | Aggregation accepts; all 16 tested fresh input ciphertexts decrypt under the attacker's chosen secret | `test_last_public_contributor_can_choose_aggregate_with_known_secret`; assumes visibility of the other public contributions before choosing its own, and needs no oracle secret. No proof ties that contribution to private fragments or relinearization state. |
| One replica of a private fragment changed | Each recipient inbox accepted; replicas disagree and selected quorums can reconstruct differently | `test_fragment_equivocation_is_accepted_and_quorums_can_disagree`; controlled algebraic witness uses `c1 = DELTA`, not a claimed honest nonlinear ciphertext |
| Both replicas changed equally | Local equality still holds while pooled key differs from public-key secret | `test_equal_replica_corruption_still_has_no_public_secret_consistency_check`; oracle sees the discrepancy, recipients have no public consistency proof |
| Canonical first- or second-round polynomial altered | Accepted; secret-key oracle finds gadget residual beyond the honest bound | `test_canonical_first_round_corruption_is_accepted_oracle_detects_bad_gadget` and second-round counterpart; oracle residual is not a public verifier |
| Second round explicitly names a different aggregate | Rejected | `test_conflicting_round_transcript_rejected_but_relabeling_is_accepted`; changing the aggregate field back admits incorrect terms |
| Two internally consistent local aggregate views | Both local computations accept and yield different evaluation keys | `test_two_consistent_local_round_views_both_pass_without_global_agreement`; one reducer has no evidence about another reducer's view |
| Missing, duplicate, unknown or malformed raw partials | `q45_oracle.combine` checks none of these; dict keys are ignored, `zip` can truncate polynomials | `test_partial_combiner_has_no_membership_count_or_value_validation`; only the ceremony envelope supplies local count/membership and the replay callback supplies canonical decoding checks |
| Incorrect canonical partial with correct ceremony binding | Accepted and can produce a valid opposite Boolean result | `test_640_honest_cases_and_canonical_corruption_with_80_bit_smudging` and `run_p2b/1`; arithmetic contribution verification is absent |
| No smudging, or smudging residual beyond the configured bound | Can still decode correctly; no public rejection | `test_holder_can_omit_smudging_without_public_rejection`, plus the 640-case residual probe; honest randomness/bound assumptions are not enforced |
| Duplicate/conflicting partial in one ceremony state | Later event rejected | Existing `freeze_before_any_partial_test`; this is first-message-wins local deduplication, not authenticated origin or global equivocation detection |
| Same participant sends different opaque partials to two receiver states | Each state accepts its first value | EUnit `equivocation_is_only_locally_detected_test`; authenticated agreement is absent |
| Frozen holder withholds | Actor times out without a result; fifth holder cannot replace it | EUnit `withheld_frozen_holder_cannot_be_replaced_in_session_test`; Python raw combiner meanwhile computes without waiting, so it is not a safe protocol combiner |

P1 checks session, exact ciphertext bytes and digest, sorted frozen quorum,
one message per label, phases and deadlines. Its `digest` is only SHA-256 of
the evaluated ciphertext. Setup identity, participant credentials, aggregate
public key, relinearization transcript, keyset epoch, circuit identity and
parameter profile are not part of that digest. A local mismatch can be rejected
without providing agreement or origin authentication. The raw Python partial
is just a polynomial: it carries none of these bindings.

## What 80-bit smudging establishes here

For honest setup and evaluation, let `E` be the oracle's measured ciphertext
noise and `B = 2^80`. The corpus checks both

```text
bit_length(E) + 40 <= 80
E + 4 B < DELTA / 2
```

Each honest holder samples its residual in `[-B, B]` coefficientwise. The
observed maximum ciphertext noise widths are 33, 33, 33 and 34 bits for seeds
69, 4660, 7 and 99 respectively. Those measurements explain why 72 bits
misses some 40-bit margins and 80 bits passes this corpus.

The checks assume an honest ciphertext noise estimate and bounded holder
residuals. They do not verify either assumption against an adversary. Adding
`DELTA` to a partial alters the decoded message while leaving its canonical
encoding intact. Adding a smaller offset, or omitting smudging, can leave
correctness unchanged. Correct decoding therefore cannot certify partial
integrity, correct randomness sampling or privacy. Changing a relinearization
contribution also invalidates the honest noise estimate before partial
generation; sampling 80-bit smudging afterwards does not repair it.

The per-share out-of-bound test uses the oracle's local secret pieces to
measure the residual; a public observer cannot extract that residual from a
masked partial. No conclusion about statistical hiding, adaptive corruptions,
collusion, repeated requests or production parameters follows from these tests.

## Remaining protocol obligations (proposals, not implemented)

| Layer | Required work and next acceptance condition |
| --- | --- |
| Local admission hardening | Validate all received aggregates, digit counts, polynomials, exact holder identities and complete partial sets; reject before arithmetic. Remove truncation behavior from any future untrusted combiner path. Mutation tests must fail on each omitted check. These checks can be added without changing the algebra, but do not prove contribution correctness. |
| Authenticated confidential delivery | Bind every message to a credentialed participant, recipient, session, protocol/version, round, keyset/epoch, parameter and CRS identifiers, and exact predecessor transcript. Private fragment delivery must be confidential as well as authenticated. Test forged identities, valid signatures on wrong contexts, replay and recipient substitution. Signatures authenticate the signer, not the arithmetic. |
| Agreement and equivocation handling | Agree on the participant set, public shares/key, first aggregate and complete round transcript using an explicit authenticated broadcast/agreement protocol. Commit to canonical bytes and round order. Test one signer sending two valid but conflicting messages to honest recipients, not just mixed metadata at one combiner. Define complaint evidence, abort and blame without exposing secret fragments. |
| Verifiable setup and relinearization | Replace honest-dealer replication with a specified verifiable sharing/consistency protocol; establish a common witness tying public key, replicated fragments, CRS and both relinearization rounds together. Prove the required witness relations and bounds, or use a suitable malicious-secure MPC protocol. Equal replicas or signed contributions alone are insufficient. This extends the cryptographic protocol, not just the transport envelope. |
| Verifiable partials and bounded noise | Adopt a specified proof/commitment protocol or malicious-secure MPC that establishes the correct designated key-share contribution for the exact request, with the required bounded masking and privacy argument. Tests must reject validly authenticated incorrect shares and proofs, excessive/correlated/cancelled masks, mixed ciphertexts, old epochs and forged predecessor transcripts. Merely asserting a proof Boolean or checking canonical coefficients is insufficient. |
| Availability, recovery and output policy | State tolerated faults, synchrony assumptions, setup/reconstruction thresholds and whether security allows abort or requires robustness/fairness. Current setup and sealing need all five, while a frozen four-party quorum can be blocked by one holder. Any alternative-quorum retry needs a new bound transcript and safe leakage/replay accounting; shares from different designations must not be mixed. A signature cannot force a participant to send. |
| Construction and implementation evidence | Select and review a construction whose confidentiality, integrity and fault model actually meet any-4-of-5 requirements. Supply secure parameters, cryptographic RNG, key custody, transcript proof soundness and implementation conformance. The insecure degree-32 toy ring, public test seeds, in-memory secrets and raw replicated partials cannot acquire production malicious security through acceptance tests or an increase to 80 bits. |

The next reviewable milestone is a written malicious-participant protocol and
binding/verification contract, with the above counterexamples mapped to concrete
verification relations and an explicit fault/abort model. Implementation of
those protocol changes requires approval. Governed cryptographic release stays
disabled under the [existing release boundary](threshold-release-boundary.md).
No protocol changes are merged by this research extension.

Four-of-five reconstruction and confidentiality against three passive holders
do not by themselves establish security or availability against three actively
malicious holders. Specify the active-corruption threshold separately; do not
inherit it from the access-structure label.
