"""Expanded P1 sampling of the unchanged P0 toy sub-quorum experiment."""
import unittest

from test_threshold_q45_oracle import Q


class ExpandedSubquorumExperiment(unittest.TestCase):
    def test_ten_thousand_trials_with_fresh_sharings(self):
        # Sample the plaintext bit uniformly so a constant guess does not
        # benefit from the imbalance in the 32 Boolean inputs.
        inputs = {bit: [x for x in Q.INPUTS if Q.reference(x) == bit] for bit in (0, 1)}
        trials_per_seed = 10_000 // len(Q.SEEDS)
        for seed in Q.SEEDS:
            with self.subTest(seed=hex(seed)):
                state = Q.State.build(seed)
                rng = state.rng("P1/O6")
                hits = 0
                for _ in range(trials_per_seed):
                    bit = rng.randrange(2)
                    x = rng.choice(inputs[bit])
                    coalition = rng.choice(Q.UNQUALIFIED)
                    shares = Q.replicate(state.ctx.s, rng)
                    pooled = Q.padd(*(share for a, share in shares.items() if a != coalition))
                    hits += Q.decrypt(pooled, state.c_t[x])[0] == bit
                rate = hits / trials_per_seed
                self.assertTrue(0.45 <= rate <= 0.55, (hex(seed), hits, trials_per_seed))
                print(f"P1 O6 seed {seed:#x}: {hits}/{trials_per_seed} ({rate:.3f})")
