"""P2a toy collective-key and holder-local reconstruction checks."""
import importlib.util
import random
import sys
import unittest
from dataclasses import replace
from functools import reduce
from itertools import combinations

from test_threshold_q45_oracle import Q, SCRIPT

SPEC = importlib.util.spec_from_file_location(
    "q45_collective_setup", SCRIPT.with_name("q45_collective_setup.py")
)
P = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = P
SPEC.loader.exec_module(P)


def fixture(seed):
    setup = P.Setup(f"P2a:{seed}", Q.uniform(random.Random(f"public:{seed}")))
    contributions = [
        P.contribute(setup, i, random.Random(f"party:{seed}:{i}")) for i in Q.PARTIES
    ]
    public = [key_share for key_share, _ in contributions]
    fragments = [fragment for _, packets in contributions for fragment in packets]
    return setup, public, fragments


class CollectiveSetup(unittest.TestCase):
    def test_four_seeds_every_input_and_quorum_reconstructs_encrypted_parity(self):
        cases = 0
        for seed in Q.SEEDS:
            setup, public, fragments = fixture(seed)
            public_key = P.public_key(setup, reversed(public))
            self.assertEqual(public_key.pk[1], setup.a)
            holders = {
                i: P.holder(setup, i, (p for p in reversed(fragments) if p.recipient == i))
                for i in Q.PARTIES
            }
            rng = random.Random(f"evaluation:{seed}")
            partial_rngs = {i: random.Random(f"partial:{seed}:{i}") for i in Q.PARTIES}
            for bits in Q.INPUTS:
                inputs = [Q.encrypt(public_key, bit, rng) for bit in bits]
                ciphertext = reduce(Q.ct_add, inputs)
                expected = (sum(bits) % 2,) + (0,) * (Q.N - 1)
                for quorum in Q.QUORUMS:
                    parts = {i: P.partial(holders[i], quorum, ciphertext[1], partial_rngs[i])
                             for i in sorted(quorum)}
                    self.assertEqual(Q.combine(ciphertext, parts), expected, (seed, bits, quorum))
                    cases += 1
        self.assertEqual(cases, 640)

    def test_routing_preserves_replication_and_local_visibility(self):
        setup, _, fragments = fixture(Q.SEEDS[0])
        inboxes = {i: [p for p in fragments if p.recipient == i] for i in Q.PARTIES}
        self.assertEqual([len(inboxes[i]) for i in Q.PARTIES], [20] * 5)
        local = {i: P.holder(setup, i, packets).pieces for i, packets in inboxes.items()}
        for coalition in Q.UNQUALIFIED:
            for sender in Q.PARTIES:
                copies = [p for p in fragments if (p.sender, p.coalition) == (sender, coalition)]
                self.assertEqual(len(copies), 2)
                self.assertEqual({p.recipient for p in copies}, set(Q.PARTIES) - coalition)
                self.assertEqual(copies[0].value, copies[1].value)
            self.assertEqual({i for i in Q.PARTIES if coalition not in local[i]}, coalition)
            a, b = sorted(set(Q.PARTIES) - coalition)
            self.assertEqual(local[a][coalition], local[b][coalition])

    def test_public_key_rejects_incomplete_foreign_or_malformed_contributions(self):
        setup, public, _ = fixture(Q.SEEDS[0])
        foreign = replace(setup, session="different")
        for invalid in (public[:-1], public[:-1] + public[:1],
                        public[:-1] + [replace(public[-1], setup=foreign)],
                        public[:-1] + [replace(public[-1], sender=6)],
                        public[:-1] + [replace(public[-1], value=Q.zero()[:-1])]):
            with self.subTest(invalid=invalid[-1].sender), self.assertRaises(ValueError):
                P.public_key(setup, invalid)

    def test_holder_rejects_incomplete_foreign_misrouted_or_malformed_fragments(self):
        setup, _, fragments = fixture(Q.SEEDS[0])
        inbox = [p for p in fragments if p.recipient == 1]
        foreign = replace(setup, session="different")
        for invalid in (inbox[:-1], inbox[:-1] + inbox[:1],
                        inbox[:-1] + [replace(inbox[-1], setup=foreign)],
                        inbox[:-1] + [replace(inbox[-1], recipient=2)],
                        inbox[:-1] + [replace(inbox[-1], coalition=frozenset((1, 2, 3)))],
                        inbox[:-1] + [replace(inbox[-1], value=(Q.Q_MOD,) + Q.zero()[1:])]):
            with self.subTest(length=len(invalid)), self.assertRaises(ValueError):
                P.holder(setup, 1, invalid)

    def test_partial_refuses_small_quorums_and_nonmembers(self):
        setup, _, fragments = fixture(Q.SEEDS[0])
        local = P.holder(setup, 1, (p for p in fragments if p.recipient == 1))
        rng = random.Random(42)
        for size in range(4):
            for parties in combinations(Q.PARTIES, size):
                with self.assertRaises(ValueError):
                    P.partial(local, frozenset(parties), Q.zero(), rng)
        for invalid in (frozenset((2, 3, 4, 5)), frozenset((1, 2, 3, 6)), frozenset(Q.PARTIES)):
            with self.assertRaises(ValueError):
                P.partial(local, invalid, Q.zero(), rng)
