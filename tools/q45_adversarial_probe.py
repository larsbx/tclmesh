"""Test-only P2b fixtures and counterexamples. No protocol or release API.

All secrets are visible to this single-process oracle. Accepted corruption is
a recorded limitation, never a successful cryptographic verification.
"""
from dataclasses import dataclass
from random import Random

import q45_oracle as Q
import q45_collective_setup as P
import q45_collective_relin as R


@dataclass
class Fixture:
    plan: R.RelinSetup
    contributors: tuple
    public: tuple
    packets: tuple
    locals: tuple
    first: tuple
    aggregate: R.FirstAggregate
    second: tuple
    evaluator: R.EvaluationKey
    holders: dict
    secret: Q.Poly


def fixture(seed):
    # Exact RNG labels/order used by the original P2b acceptance fixture.
    rng = Random(f"P2b common:{seed}")
    setup = P.Setup(f"P2b:{seed}", Q.uniform(rng))
    plan = R.RelinSetup(setup, tuple(Q.uniform(rng) for _ in range(Q.RELIN_DIGITS)))
    streams = {i: Random(f"P2b party:{seed}:{i}") for i in Q.PARTIES}
    contributors, public, packets = zip(*[
        P.begin_contribution(setup, i, streams[i]) for i in Q.PARTIES
    ])
    locals_, first = zip(*[
        R.first_round(plan, member, streams[member.party]) for member in contributors
    ])
    aggregate = R.aggregate_first(plan, reversed(first))
    second = tuple(R.second_round(aggregate, state, streams[state.member.party]) for state in locals_)
    evaluator = R.evaluation_key(aggregate, reversed(public), reversed(second))
    holders = {
        i: P.holder(setup, i, (p for batch in packets for p in batch if p.recipient == i))
        for i in Q.PARTIES
    }
    secret = Q.padd(*(member.secret for member in contributors))  # oracle only
    return Fixture(plan, contributors, public, packets, locals_, first, aggregate,
                   second, evaluator, holders, secret)


def ciphertext(f, bits, rng):
    inputs = [Q.encrypt(f.evaluator, bit, rng) for bit in bits]
    return inputs, Q.e4(Q.ct_add, lambda a, b: Q.ct_mul(f.evaluator, a, b), inputs)


def partials(f, quorum, ct, streams, bits=R.SMUDGE_BITS):
    return {i: P.partial(f.holders[i], quorum, ct[1], streams[i], smudge_bits=bits)
            for i in sorted(quorum)}


def gadget_residuals(evaluator, secret):
    squared = Q.pmul(secret, secret)
    return tuple(Q.inf_norm(Q.padd(Q.phase(key, secret), Q.pneg(
        Q.reduce(c << (Q.RELIN_BASE_BITS * j) for c in squared))))
        for j, key in enumerate(evaluator.rlk))


def gadget_bound():
    return 2 * Q.N * len(Q.PARTIES) * (Q.ETA * len(Q.PARTIES)) + Q.ETA * len(Q.PARTIES)


def replay_cases():
    """Yield original 640 cases, preserving the original RNG consumption."""
    for seed in Q.SEEDS:
        f = fixture(seed)
        rng = Random(f"P2b ciphertexts:{seed}")
        streams = {i: Random(f"P2b partial:{seed}:{i}") for i in Q.PARTIES}
        for mask, bits in enumerate(Q.INPUTS):
            inputs, ct = ciphertext(f, bits, rng)
            noise = Q.noise(ct, f.secret, Q.reference(bits))
            for quorum in Q.QUORUMS:
                yield seed, mask, bits, f, inputs, ct, quorum, partials(f, quorum, ct, streams), noise
