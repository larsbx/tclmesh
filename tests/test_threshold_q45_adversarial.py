"""Acceptance characterization of dishonest P2b holders, not security proofs.

Some tests deliberately assert acceptance of an attack: these lock down a
known limitation so a protocol proposal has concrete counterexamples to fix.
"""
import importlib.util
import random
import sys
import unittest
from dataclasses import replace

from test_threshold_q45_collective_relin import P, Q, R, SCRIPT

SPEC = importlib.util.spec_from_file_location(
    "q45_adversarial_probe", SCRIPT.with_name("q45_adversarial_probe.py")
)
A = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = A
SPEC.loader.exec_module(A)
MEASUREMENTS = {}


def changed(poly, delta=Q.DELTA):
    return Q.padd(poly, Q.const(delta))


class DishonestParticipants(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.f = A.fixture(Q.SEEDS[0])

    def test_fixture_matches_original_p2b_rng_and_keys(self):
        from test_threshold_q45_collective_relin import fixture
        plan, members, public, packets, first, aggregate, second = fixture(Q.SEEDS[0])
        self.assertEqual((self.f.plan, self.f.contributors, self.f.public, self.f.packets,
                          self.f.first, self.f.aggregate, self.f.second),
                         (plan, members, public, packets, first, aggregate, tuple(second)))

    def test_withholding_and_duplicate_messages_are_rejected_at_each_setup_round(self):
        f = self.f
        inbox = [p for batch in f.packets for p in batch if p.recipient == 1]
        calls = [
            (lambda xs: P.public_key(f.plan.setup, xs), list(f.public)),
            (lambda xs: P.holder(f.plan.setup, 1, xs), inbox),
            (lambda xs: R.aggregate_first(f.plan, xs), list(f.first)),
            (lambda xs: R.evaluation_key(f.aggregate, f.public, xs), list(f.second)),
        ]
        for call, messages in calls:
            for bad in (messages[:-1], messages + messages[:1], messages[:-1] + messages[:1]):
                with self.subTest(call=call, length=len(bad)), self.assertRaises(ValueError):
                    call(bad)

    def test_noncanonical_coefficients_are_rejected_at_public_fragment_and_relin_ingress(self):
        f = self.f
        inbox = [p for batch in f.packets for p in batch if p.recipient == 1]
        for poly in (Q.zero()[:-1], (Q.Q_MOD,) + Q.zero()[1:], (-1,) + Q.zero()[1:],
                     (True,) + Q.zero()[1:]):
            with self.subTest(poly=poly[0]):
                with self.assertRaises(ValueError):
                    P.public_key(f.plan.setup, (replace(f.public[0], value=poly),) + f.public[1:])
                with self.assertRaises(ValueError):
                    P.holder(f.plan.setup, 1, [replace(inbox[0], value=poly)] + inbox[1:])
                pair = (poly, f.first[0].pairs[0][1])
                bad = replace(f.first[0], pairs=(pair,) + f.first[0].pairs[1:])
                with self.assertRaises(ValueError):
                    R.aggregate_first(f.plan, (bad,) + f.first[1:])
                bad = replace(f.second[0], terms=(poly,) + f.second[0].terms[1:])
                with self.assertRaises(ValueError):
                    R.evaluation_key(f.aggregate, f.public, (bad,) + f.second[1:])

    def test_inconsistent_public_keys_are_locally_accepted(self):
        f = self.f
        public = (replace(f.public[0], value=changed(f.public[0].value)),) + f.public[1:]
        other = R.evaluation_key(f.aggregate, public, f.second)
        self.assertNotEqual(other.pk, f.evaluator.pk)
        self.assertEqual(other.rlk, f.evaluator.rlk)
        # No public-share transcript is bound into FirstAggregate/SecondShare.
        self.assertTrue(all(s.aggregate == f.aggregate for s in f.second))
        failures = 0
        rng = random.Random("inconsistent public key")
        for bit in (0, 1):
            for _ in range(8):
                ct = Q.encrypt(other, bit, rng)
                failures += Q.decrypt(f.secret, ct) != (bit,) + (0,) * (Q.N - 1)
        self.assertGreater(failures, 0)

    def test_fragment_equivocation_is_accepted_and_quorums_can_disagree(self):
        f = self.f
        coalition = Q.UNQUALIFIED[0]
        a, b = sorted(Q.holders(coalition))
        fragments = [p for batch in f.packets for p in batch]
        target = next(p for p in fragments if p.sender == 1 and
                      p.recipient == a and p.coalition == coalition)
        altered = [replace(p, value=changed(p.value, 1)) if p == target else p for p in fragments]
        bad_holder = P.holder(f.plan.setup, a, [p for p in altered if p.recipient == a])
        self.assertNotEqual(bad_holder.pieces[coalition], f.holders[b].pieces[coalition])
        # A small ciphertext multiplier makes the one-unit replica discrepancy
        # cross the decoding boundary only when the altered holder is designated.
        ct = (Q.zero(), Q.const(Q.DELTA))
        good_holder_quorum = frozenset(Q.PARTIES) - {a}
        bad_holder_quorum = frozenset(Q.PARTIES) - {b}
        outputs = []
        for quorum in (good_holder_quorum, bad_holder_quorum):
            good = A.partials(f, quorum, ct, {i: random.Random(i) for i in quorum})
            corrupted = dict(good)
            if a in quorum:
                corrupted[a] = P.partial(bad_holder, quorum, ct[1], random.Random(a),
                                         smudge_bits=R.SMUDGE_BITS)
            outputs.append((Q.combine(ct, good), Q.combine(ct, corrupted)))
        self.assertEqual(*outputs[0])
        self.assertNotEqual(*outputs[1])

    def test_last_public_contributor_can_choose_aggregate_with_known_secret(self):
        f = self.f
        rng = random.Random('dishonest last public contributor')
        known_secret = Q.ternary(rng)  # attacker-owned, not the oracle's key
        chosen_public = Q.padd(Q.pneg(Q.pmul(f.plan.setup.a, known_secret)), Q.cbd(rng))
        cancellation = Q.padd(chosen_public, Q.pneg(Q.padd(*(s.value for s in f.public[1:]))))
        forged = (replace(f.public[0], value=cancellation),) + f.public[1:]
        public = P.public_key(f.plan.setup, forged)
        self.assertEqual(public.pk[0], chosen_public)
        for bit in (0, 1):
            for _ in range(8):
                self.assertEqual(Q.decrypt(known_secret, Q.encrypt(public, bit, rng)), Q.const(bit))
        # No relation between this public contribution and its replicated
        # private fragments or first-round secret was verified. This witness
        # assumes the attacker can see the other public contributions first.

    def test_equal_replica_corruption_still_has_no_public_secret_consistency_check(self):
        f = self.f
        coalition = Q.UNQUALIFIED[0]
        fragments = [p for batch in f.packets for p in batch]
        altered = [replace(p, value=changed(p.value, 1))
                   if p.sender == 1 and p.coalition == coalition else p for p in fragments]
        local = {i: P.holder(f.plan.setup, i, [p for p in altered if p.recipient == i])
                 for i in Q.PARTIES}
        a, b = sorted(Q.holders(coalition))
        self.assertEqual(local[a].pieces[coalition], local[b].pieces[coalition])
        pooled = {c: value for holder in local.values() for c, value in holder.pieces.items()}
        self.assertEqual(Q.padd(*pooled.values()), changed(f.secret, 1))
        self.assertNotEqual(Q.padd(*pooled.values()), f.secret)

    def test_canonical_first_round_corruption_is_accepted_oracle_detects_bad_gadget(self):
        f = self.f
        pair = (changed(f.first[0].pairs[0][0]), f.first[0].pairs[0][1])
        bad = replace(f.first[0], pairs=(pair,) + f.first[0].pairs[1:])
        aggregate = R.aggregate_first(f.plan, (bad,) + f.first[1:])
        second = [R.second_round(aggregate, state, random.Random(i))
                  for i, state in enumerate(f.locals)]
        evaluator = R.evaluation_key(aggregate, f.public, second)
        self.assertGreater(max(A.gadget_residuals(evaluator, f.secret)), A.gadget_bound())

    def test_canonical_second_round_corruption_is_accepted_oracle_detects_bad_gadget(self):
        f = self.f
        bad = replace(f.second[0], terms=(changed(f.second[0].terms[0]),) + f.second[0].terms[1:])
        evaluator = R.evaluation_key(f.aggregate, f.public, (bad,) + f.second[1:])
        self.assertGreater(A.gadget_residuals(evaluator, f.secret)[0], A.gadget_bound())

    def test_conflicting_round_transcript_rejected_but_relabeling_is_accepted(self):
        f = self.f
        pair = (changed(f.aggregate.pairs[0][0]), f.aggregate.pairs[0][1])
        other = replace(f.aggregate, pairs=(pair,) + f.aggregate.pairs[1:])
        dishonest = R.second_round(other, f.locals[0], random.Random("split view"))
        with self.assertRaises(ValueError):
            R.evaluation_key(f.aggregate, f.public, (dishonest,) + f.second[1:])
        # The aggregate field is an unauthenticated Python value, not a proof.
        rebound = replace(dishonest, aggregate=f.aggregate)
        evaluator = R.evaluation_key(f.aggregate, f.public, (rebound,) + f.second[1:])
        self.assertGreater(max(A.gadget_residuals(evaluator, f.secret)), A.gadget_bound())

    def test_two_consistent_local_round_views_both_pass_without_global_agreement(self):
        f = self.f
        pair = (changed(f.first[0].pairs[0][0]), f.first[0].pairs[0][1])
        bad = replace(f.first[0], pairs=(pair,) + f.first[0].pairs[1:])
        other = R.aggregate_first(f.plan, (bad,) + f.first[1:])
        second = [R.second_round(other, state, random.Random(i))
                  for i, state in enumerate(f.locals)]
        key = R.evaluation_key(other, f.public, second)
        self.assertNotEqual(other, f.aggregate)
        self.assertNotEqual(key.rlk, f.evaluator.rlk)

    def test_sender_labels_can_be_forged_without_authentication(self):
        f = self.f
        forged = [replace(f.public[0], sender=i) for i in Q.PARTIES]
        key = P.public_key(f.plan.setup, forged)
        self.assertNotEqual(key.pk, f.evaluator.pk)
        # Cardinality checks alone accept one contribution relabeled as five.
        first = [replace(f.first[0], sender=i) for i in Q.PARTIES]
        R.aggregate_first(f.plan, first)
        second = [replace(f.second[0], sender=i) for i in Q.PARTIES]
        R.evaluation_key(f.aggregate, forged, second)

    def test_direct_aggregate_objects_bypass_aggregation_shape_checks(self):
        f = self.f
        short = replace(f.aggregate, pairs=f.aggregate.pairs[:1])
        # second_round checks the plan, but not a received aggregate's shape.
        partial_round = R.second_round(short, f.locals[0], random.Random(1))
        self.assertEqual(len(partial_round.terms), 1)
        # A dishonest caller can rebind full-length terms to the malformed
        # aggregate. evaluation_key's zip then silently drops gadget digits.
        forged = [replace(s, aggregate=short) for s in f.second]
        evaluator = R.evaluation_key(short, f.public, forged)
        self.assertEqual(len(evaluator.rlk), 1)

    def test_altered_relin_contributions_invalidate_80_bit_noise_assumptions(self):
        counts = dict(altered_relin_full_key_cases=0, altered_relin_decode_failures=0,
                      altered_relin_margin_80_failures=0, altered_relin_bound_80_failures=0,
                      altered_relin_threshold_cases=0, altered_relin_threshold_failures=0)
        for seed in Q.SEEDS:
            f = A.fixture(seed)
            bad = replace(f.second[0], terms=(changed(f.second[0].terms[0]),) + f.second[0].terms[1:])
            f.evaluator = R.evaluation_key(f.aggregate, f.public, (bad,) + f.second[1:])
            rng = random.Random(f"altered relin ciphertexts:{seed}")
            streams = {i: random.Random(f"altered relin partial:{seed}:{i}") for i in Q.PARTIES}
            for bits in Q.INPUTS:
                _, ct = A.ciphertext(f, bits, rng)
                expected = Q.const(Q.reference(bits))
                noise = Q.noise(ct, f.secret, Q.reference(bits))
                counts['altered_relin_full_key_cases'] += 1
                counts['altered_relin_decode_failures'] += Q.decrypt(f.secret, ct) != expected
                counts['altered_relin_margin_80_failures'] += noise.bit_length() + Q.KAPPA > R.SMUDGE_BITS
                counts['altered_relin_bound_80_failures'] += noise + Q.QUORUM * (1 << R.SMUDGE_BITS) >= Q.DELTA // 2
                for quorum in Q.QUORUMS:
                    parts = A.partials(f, quorum, ct, streams)
                    self.assertTrue(all(P.canonical_polynomial(p) for p in parts.values()))
                    counts['altered_relin_threshold_cases'] += 1
                    counts['altered_relin_threshold_failures'] += Q.combine(ct, parts) != expected
        self.assertEqual(counts['altered_relin_full_key_cases'], 128)
        self.assertEqual(counts['altered_relin_threshold_cases'], 640)
        for key, count in counts.items():
            self.assertGreater(count, 0, key)
        MEASUREMENTS.update(counts)

    def test_partial_combiner_has_no_membership_count_or_value_validation(self):
        ct = (Q.zero(), Q.zero())
        self.assertEqual(Q.combine(ct, {}), Q.zero())
        self.assertEqual(Q.combine(ct, {99: Q.const(Q.DELTA)}), Q.const(1))
        self.assertEqual(Q.combine(ct, {i: Q.const(Q.DELTA) for i in range(3)}), Q.const(1))
        self.assertEqual(Q.combine(ct, {99: (Q.Q_MOD,) + Q.zero()[1:]}), Q.zero())
        self.assertEqual(len(Q.combine(ct, {99: (0,)})), 1)  # zip silently truncates

    def test_holder_can_omit_smudging_without_public_rejection(self):
        f = self.f
        quorum = Q.QUORUMS[0]
        _, ct = A.ciphertext(f, Q.INPUTS[-1], random.Random("no smudge"))
        parts = A.partials(f, quorum, ct, {i: random.Random(i) for i in quorum}, bits=0)
        self.assertEqual(Q.combine(ct, parts), Q.const(1))
        self.assertTrue(all(P.canonical_polynomial(p) for p in parts.values()))
        # Correct decoding cannot certify that 80-bit randomness was sampled.

    def test_partial_withholding_does_not_automatically_redesignate(self):
        f = self.f
        quorum = Q.QUORUMS[0]
        _, ct = A.ciphertext(f, Q.INPUTS[-1], random.Random("withholding"))
        parts = A.partials(f, quorum, ct, {i: random.Random(i) for i in quorum})
        del parts[min(quorum)]
        self.assertNotEqual(Q.combine(ct, parts), Q.const(1))
        # Another four-party quorum works only with fresh designation/partials.
        other = Q.QUORUMS[-1]
        fresh = A.partials(f, other, ct, {i: random.Random(i) for i in other})
        self.assertEqual(Q.combine(ct, fresh), Q.const(1))

    def test_640_honest_cases_and_canonical_corruption_with_80_bit_smudging(self):
        counts = dict(full_key_cases=0, threshold_cases=0, margin_72_failures=0,
                      margin_80_failures=0, decode_bound_80_failures=0,
                      delta_bit_flips_accepted=0, small_offsets_decode_correctly=0,
                      over_bound_partials_decode_correctly=0)
        widths = {}
        for seed, mask, bits, f, _, ct, quorum, parts, noise in A.replay_cases():
            expected = Q.const(Q.reference(bits))
            self.assertEqual(Q.combine(ct, parts), expected, (seed, mask, quorum))
            self.assertTrue(all(P.canonical_polynomial(p) for p in parts.values()))
            counts['threshold_cases'] += 1
            widths[str(seed)] = max(widths.get(str(seed), 0), noise.bit_length())
            if quorum == Q.QUORUMS[0]:
                self.assertEqual(Q.decrypt(f.secret, ct), expected)
                counts['full_key_cases'] += 1
                counts['margin_72_failures'] += noise.bit_length() + Q.KAPPA > 72
                counts['margin_80_failures'] += noise.bit_length() + Q.KAPPA > R.SMUDGE_BITS
                counts['decode_bound_80_failures'] += noise + Q.QUORUM * (1 << R.SMUDGE_BITS) >= Q.DELTA // 2
            attacker = min(quorum)
            flipped = {**parts, attacker: changed(parts[attacker])}
            self.assertTrue(P.canonical_polynomial(flipped[attacker]))
            self.assertEqual(Q.combine(ct, flipped), Q.const(1 - Q.reference(bits)))
            counts['delta_bit_flips_accepted'] += 1
            # A small canonical alteration hides beneath the correctness budget.
            small = {**parts, attacker: changed(parts[attacker], 1 << R.SMUDGE_BITS)}
            self.assertEqual(Q.combine(ct, small), expected)
            counts['small_offsets_decode_correctly'] += 1
            # Oracle-only construction of an invalid smudging residual; neither
            # the holder interface nor combine checks its actual bound.
            d = Q.designation(quorum)
            sigma = Q.padd(Q.zero(), *(v for c, v in f.holders[attacker].pieces.items() if d[c] == attacker))
            raw = Q.pmul(ct[1], sigma)
            out_of_bound = changed(raw, (1 << R.SMUDGE_BITS) + 1)
            self.assertEqual(Q.inf_norm(Q.padd(out_of_bound, Q.pneg(raw))), (1 << R.SMUDGE_BITS) + 1)
            self.assertEqual(Q.combine(ct, {**parts, attacker: out_of_bound}), expected)
            counts['over_bound_partials_decode_correctly'] += 1
        self.assertEqual(counts, dict(full_key_cases=128, threshold_cases=640,
            margin_72_failures=61, margin_80_failures=0, decode_bound_80_failures=0,
            delta_bit_flips_accepted=640, small_offsets_decode_correctly=640,
            over_bound_partials_decode_correctly=640))
        MEASUREMENTS.update(counts, noise_widths_by_seed=widths, smudge_bits=R.SMUDGE_BITS,
                            required_margin_bits=Q.KAPPA)


if __name__ == '__main__':
    unittest.main()
