"""SPEC_4of5 P0 oracle: kernel algebra, access structure, toy BFV, obligations.

The toy BFV parameters are insecure by construction; nothing here is a
cryptographic claim, only a Dec∘Eval differential reference.
"""
import importlib.util
import itertools
import math
import subprocess
import sys
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "q45_oracle.py"
SPEC = importlib.util.spec_from_file_location("q45_oracle", SCRIPT)
Q = importlib.util.module_from_spec(SPEC)
sys.modules["q45_oracle"] = Q
SPEC.loader.exec_module(Q)

INPUTS = tuple(itertools.product((0, 1), repeat=5))


def cost_semantics():
    """Values are (depth, frozenset of distinct mul nodes): shared terms count once."""
    leaf = lambda i: (0, frozenset(), ("x", i))
    add = lambda a, b: (max(a[0], b[0]), a[1] | b[1], ("+", a[2], b[2]))

    def mul(a, b):
        node = ("*", a[2], b[2])
        return (max(a[0], b[0]) + 1, a[1] | b[1] | {node}, node)

    return add, mul, tuple(leaf(i) for i in range(5))


class KernelAlgebra(unittest.TestCase):
    def test_threshold_identity_holds_for_all_n_le_11(self):
        for n in range(1, 12):
            for k in range(1, n + 1):
                for w in range(n + 1):
                    self.assertEqual(Q.threshold_via_elementary(n, k, w), int(w >= k), (n, k, w))

    def test_e4_over_f2_is_threshold_on_all_inputs(self):
        for x in INPUTS:
            self.assertEqual(Q.e4(*Q.F2, x), Q.reference(x))

    def test_e4_is_bit2_of_popcount(self):
        for x in INPUTS:
            self.assertEqual(Q.e4(*Q.F2, x), (sum(x) >> 2) & 1)

    def test_e4_costs_seven_multiplications_at_depth_two(self):
        add, mul, x = cost_semantics()
        depth, muls, _ = Q.e4(add, mul, x)
        self.assertEqual((depth, len(muls)), (2, 7))

    def test_m1_mutant_witnesses_are_exactly_x2345_all_one(self):
        self.assertEqual(Q.witnesses(Q.e4_mutant_m1, Q.reference),
                         ((0, 1, 1, 1, 1), (1, 1, 1, 1, 1)))

    def test_m2_threshold_three_mutant_has_ten_witnesses(self):
        ws = Q.witnesses(Q.e4, lambda x: int(sum(x) >= 3))
        self.assertEqual(len(ws), math.comb(5, 3))
        self.assertTrue(all(sum(w) == 3 for w in ws))


class AccessStructure(unittest.TestCase):
    def test_ten_maximal_unqualified_sets_each_with_two_holders(self):
        self.assertEqual(len(Q.UNQUALIFIED), 10)
        self.assertTrue(all(len(Q.holders(a)) == 2 for a in Q.UNQUALIFIED))

    def test_each_party_holds_four_shares(self):
        self.assertEqual(Q.load(), (4, 4, 4, 4, 4))

    def test_designation_total_iff_quorum(self):
        for r in range(6):
            for s in itertools.combinations(Q.PARTIES, r):
                self.assertEqual(Q.designation(frozenset(s)) is not None, r >= 4, s)

    def test_designation_assigns_each_share_to_a_holder_inside_s(self):
        for s in map(frozenset, itertools.combinations(Q.PARTIES, 4)):
            d = Q.designation(s)
            self.assertTrue(all(i in s and i in Q.holders(a) for a, i in d.items()))

    def test_shamir_lagrange_integral_only_for_two_quorums(self):
        integral = {s for s in itertools.combinations(Q.PARTIES, 4)
                    if all(l.denominator == 1 for l in Q.lagrange(s).values())}
        self.assertEqual(integral, {(1, 2, 3, 4), (2, 3, 4, 5)})
        self.assertTrue(all(abs(l) <= 20 for s in integral for l in Q.lagrange(s).values()))


class ToyBFV(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.ctx = Q.keygen(Q.random.Random(1))

    def test_fresh_roundtrip(self):
        rng = Q.random.Random(2)
        for m in (0, 1):
            ct = Q.encrypt(self.ctx, m, rng)
            self.assertEqual(Q.decrypt(self.ctx.s, ct), (m,) + (0,) * (Q.N - 1))

    def test_homomorphic_product_and_sum(self):
        rng = Q.random.Random(3)
        for a, b in itertools.product((0, 1), repeat=2):
            ca, cb = Q.encrypt(self.ctx, a, rng), Q.encrypt(self.ctx, b, rng)
            self.assertEqual(Q.decrypt(self.ctx.s, Q.ct_mul(self.ctx, ca, cb))[0], a & b)
            self.assertEqual(Q.decrypt(self.ctx.s, Q.ct_add(ca, cb))[0], a ^ b)

    def test_replicated_shares_sum_to_secret(self):
        shares = Q.replicate(self.ctx.s, Q.random.Random(4))
        total = Q.zero()
        for r in shares.values():
            total = Q.padd(total, r)
        self.assertEqual(total, tuple(c % Q.Q_MOD for c in self.ctx.s))


class Obligations(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = Q.run(0x45)

    def test_all_ten_obligations_pass(self):
        self.assertEqual(tuple(self.report), Q.OBLIGATION_IDS)
        failed = {k: v for k, v in self.report.items() if not v.ok}
        self.assertEqual(failed, {})

    def test_o3_covers_160_cases(self):
        self.assertIn("160/160", self.report["O3"].detail)

    def test_raising_obligation_counts_as_failure(self):
        def boom(_):
            raise RuntimeError("x")
        self.assertFalse(Q.discharge(boom, None).ok)

    def test_removing_smudging_is_caught_by_o7(self):
        st = Q.State.build(0x45, smudge_bits=0)
        self.assertFalse(Q.o7_smudging_present(st).ok)

    def test_cli_exits_zero(self):
        out = subprocess.run([sys.executable, "-I", str(SCRIPT), "0x7"],
                             capture_output=True, text=True, timeout=300)
        self.assertEqual(out.returncode, 0, out.stdout + out.stderr)
        self.assertIn("10/10", out.stdout)


if __name__ == "__main__":
    unittest.main()
