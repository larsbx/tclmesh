"""P2b toy relinearization and nonlinear SPEC_4of5 differential checks."""
import importlib.util
import random
import sys
import unittest
from dataclasses import replace
from fractions import Fraction

from test_threshold_q45_collective_setup import P, Q, SCRIPT

SPEC = importlib.util.spec_from_file_location(
    "q45_collective_relin", SCRIPT.with_name("q45_collective_relin.py")
)
R = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = R
SPEC.loader.exec_module(R)


def fixture(seed):
    rng = random.Random(f"P2b common:{seed}")
    setup = P.Setup(f"P2b:{seed}", Q.uniform(rng))
    plan = R.RelinSetup(setup, tuple(Q.uniform(rng) for _ in range(Q.RELIN_DIGITS)))
    party_rngs = {i: random.Random(f"P2b party:{seed}:{i}") for i in Q.PARTIES}
    contributors, public_shares, packets = zip(*[
        P.begin_contribution(setup, i, party_rngs[i]) for i in Q.PARTIES
    ])
    locals_, first = zip(*[
        R.first_round(plan, member, party_rngs[member.party]) for member in contributors
    ])
    aggregate = R.aggregate_first(plan, reversed(first))
    second = [
        R.second_round(aggregate, state, party_rngs[state.member.party]) for state in locals_
    ]
    return plan, contributors, public_shares, packets, first, aggregate, second


def balanced_subquorum_hit_rate(holders, ciphertexts):
    hits, counts = [0, 0], [0, 0]
    for coalition in Q.UNQUALIFIED:
        known = {c: value for i in coalition for c, value in holders[i].pieces.items()}
        pooled = Q.padd(*known.values())
        for bits, ciphertext in ciphertexts.items():
            bit = Q.reference(bits)
            hits[bit] += Q.decrypt(pooled, ciphertext)[0] == bit
            counts[bit] += 1
    return (Fraction(hits[0], counts[0]) + Fraction(hits[1], counts[1])) / 2


class CollectiveRelinearization(unittest.TestCase):
    def test_collective_keys_reconstruct_every_nonlinear_case(self):
        cases = 0
        for seed in Q.SEEDS:
            plan, contributors, public, packets, _, aggregate, second = fixture(seed)
            evaluator = R.evaluation_key(aggregate, reversed(public), reversed(second))
            holders = {
                i: P.holder(plan.setup, i, (p for batch in packets for p in batch if p.recipient == i))
                for i in Q.PARTIES
            }
            # Test oracle only. The evaluator and combiner never receive this key.
            secret = Q.padd(*(member.secret for member in contributors))
            secret_squared = Q.pmul(secret, secret)
            coefficient_bound = len(Q.PARTIES)
            error_bound = Q.ETA * coefficient_bound
            relin_bound = 2 * Q.N * coefficient_bound * error_bound + error_bound
            for j, key in enumerate(evaluator.rlk):
                message = Q.reduce(c << (Q.RELIN_BASE_BITS * j) for c in secret_squared)
                residual = Q.padd(Q.phase(key, secret), Q.pneg(message))
                self.assertLessEqual(Q.inf_norm(residual), relin_bound, (seed, j))

            rng = random.Random(f"P2b ciphertexts:{seed}")
            partial_rngs = {i: random.Random(f"P2b partial:{seed}:{i}") for i in Q.PARTIES}
            ciphertexts = {}
            for bits in Q.INPUTS:
                inputs = [Q.encrypt(evaluator, bit, rng) for bit in bits]
                ciphertext = Q.e4(Q.ct_add, lambda a, b: Q.ct_mul(evaluator, a, b), inputs)
                ciphertexts[bits] = ciphertext
                bit = Q.reference(bits)
                expected = (bit,) + (0,) * (Q.N - 1)
                self.assertEqual(Q.decrypt(secret, ciphertext), expected, (seed, bits))
                noise = Q.noise(ciphertext, secret, bit)
                self.assertLessEqual(noise.bit_length() + Q.KAPPA, R.SMUDGE_BITS, (seed, bits))
                self.assertLess(noise + Q.QUORUM * (1 << R.SMUDGE_BITS), Q.DELTA // 2)
                for quorum in Q.QUORUMS:
                    parts = {
                        i: P.partial(holders[i], quorum, ciphertext[1], partial_rngs[i],
                                     smudge_bits=R.SMUDGE_BITS)
                        for i in sorted(quorum)
                    }
                    self.assertEqual(Q.combine(ciphertext, parts), expected, (seed, bits, quorum))
                    if bits == Q.INPUTS[-1]:
                        designation = Q.designation(quorum)
                        for i, part in parts.items():
                            sigma = Q.padd(Q.zero(), *(value for c, value in holders[i].pieces.items()
                                                       if designation[c] == i))
                            residual = Q.padd(part, Q.pneg(Q.pmul(ciphertext[1], sigma)))
                            self.assertGreaterEqual(Q.inf_norm(residual), 1 << (R.SMUDGE_BITS - 4))
                    cases += 1
            # Descriptive O6 check on each fixed toy setup. The scores within
            # one setup are correlated and say nothing about security.
            rate = balanced_subquorum_hit_rate(holders, ciphertexts)
            self.assertTrue(Fraction(3, 10) <= rate <= Fraction(7, 10), (seed, rate))
        self.assertEqual(cases, 640)

    def test_first_round_rejects_missing_duplicate_foreign_and_malformed_shares(self):
        plan, _, _, _, first, _, _ = fixture(Q.SEEDS[0])
        foreign = replace(plan, setup=replace(plan.setup, session="foreign"))
        for invalid in (
            first[:-1],
            first[:-1] + first[:1],
            first[:-1] + (replace(first[-1], plan=foreign),),
            first[:-1] + (replace(first[-1], pairs=first[-1].pairs[:-1]),),
        ):
            with self.assertRaises(ValueError):
                R.aggregate_first(plan, invalid)

    def test_second_round_rejects_missing_duplicate_and_conflicting_transcript(self):
        _, _, public, _, _, aggregate, second = fixture(Q.SEEDS[0])
        first_pair = (Q.zero(), aggregate.pairs[0][1])
        conflicting = replace(aggregate, pairs=(first_pair,) + aggregate.pairs[1:])
        for invalid in (
            second[:-1],
            second[:-1] + second[:1],
            second[:-1] + [replace(second[-1], aggregate=conflicting)],
            second[:-1] + [replace(second[-1], terms=second[-1].terms[:-1])],
        ):
            with self.assertRaises(ValueError):
                R.evaluation_key(aggregate, public, invalid)

    def test_crs_rejects_reused_or_malformed_polynomials(self):
        plan, _, _, _, _, _, _ = fixture(Q.SEEDS[0])
        for invalid in (
            plan.a[:-1],
            (plan.setup.a,) + plan.a[1:],
            (plan.a[1],) + plan.a[1:],
            (Q.zero()[:-1],) + plan.a[1:],
        ):
            with self.assertRaises(ValueError):
                replace(plan, a=invalid)
