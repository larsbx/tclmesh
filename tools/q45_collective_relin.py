"""Honest-party collective relinearization in the insecure P0 toy ring."""
from dataclasses import dataclass, field
from random import Random
from typing import Iterable

import q45_collective_setup as setup
import q45_oracle as q45

# The collective nonlinear path has a larger measured noise budget than P0.
SMUDGE_BITS = 80

Poly = q45.Poly
Pairs = tuple[tuple[Poly, Poly], ...]


@dataclass(frozen=True)
class RelinSetup:
    setup: setup.Setup
    a: tuple[Poly, ...]

    def __post_init__(self):
        if (
            len(self.a) != q45.RELIN_DIGITS
            or any(not setup.canonical_polynomial(poly) for poly in self.a)
            or len(set(self.a)) != q45.RELIN_DIGITS
            or self.setup.a in self.a
        ):
            raise ValueError("expected one distinct common polynomial per gadget digit")


@dataclass(frozen=True)
class FirstLocal:
    plan: RelinSetup
    member: setup.Contributor = field(repr=False)
    ephemeral: Poly = field(repr=False)


@dataclass(frozen=True)
class FirstShare:
    plan: RelinSetup
    sender: int
    pairs: Pairs


@dataclass(frozen=True)
class FirstAggregate:
    plan: RelinSetup
    pairs: Pairs


@dataclass(frozen=True)
class SecondShare:
    aggregate: FirstAggregate
    sender: int
    terms: tuple[Poly, ...]


@dataclass(frozen=True)
class EvaluationKey(setup.PublicKey):
    rlk: Pairs


def first_round(
    plan: RelinSetup, member: setup.Contributor, rng: Random
) -> tuple[FirstLocal, FirstShare]:
    if member.setup != plan.setup:
        raise ValueError("contributor belongs to a different public-key setup")
    secret = member.secret
    ephemeral = q45.ternary(rng)
    pairs = []
    for j, a in enumerate(plan.a):
        gadget_secret = q45.reduce(c << (q45.RELIN_BASE_BITS * j) for c in secret)
        h0 = q45.padd(q45.pneg(q45.pmul(ephemeral, a)), gadget_secret, q45.cbd(rng))
        h1 = q45.padd(q45.pmul(secret, a), q45.cbd(rng))
        pairs.append((h0, h1))
    return FirstLocal(plan, member, ephemeral), FirstShare(plan, member.party, tuple(pairs))


def aggregate_first(plan: RelinSetup, shares: Iterable[FirstShare]) -> FirstAggregate:
    shares = tuple(shares)
    if (
        len(shares) != len(setup.PARTIES)
        or {s.sender for s in shares} != setup.PARTIES
        or any(
            s.plan != plan or len(s.pairs) != q45.RELIN_DIGITS
            or any(len(pair) != 2 or not all(map(setup.canonical_polynomial, pair)) for pair in s.pairs)
            for s in shares
        )
    ):
        raise ValueError("expected one complete first-round share per contributor")
    pairs = tuple(
        (q45.padd(*(p[0] for p in digit)), q45.padd(*(p[1] for p in digit)))
        for digit in zip(*(s.pairs for s in shares))
    )
    return FirstAggregate(plan, pairs)


def second_round(aggregate: FirstAggregate, local: FirstLocal, rng: Random) -> SecondShare:
    if local.plan != aggregate.plan:
        raise ValueError("first-round aggregate belongs to a different setup")
    secret = local.member.secret
    difference = q45.padd(local.ephemeral, q45.pneg(secret))
    terms = tuple(
        q45.padd(q45.pmul(secret, h0), q45.pmul(difference, h1), q45.cbd(rng))
        for h0, h1 in aggregate.pairs
    )
    return SecondShare(aggregate, local.member.party, terms)


def evaluation_key(
    aggregate: FirstAggregate,
    public_shares: Iterable[setup.PublicShare],
    second: Iterable[SecondShare],
) -> EvaluationKey:
    second = tuple(second)
    if (
        len(second) != len(setup.PARTIES)
        or {s.sender for s in second} != setup.PARTIES
        or any(
            s.aggregate != aggregate or len(s.terms) != q45.RELIN_DIGITS
            or not all(map(setup.canonical_polynomial, s.terms))
            for s in second
        )
    ):
        raise ValueError("expected one complete second-round share bound to this aggregate")
    public = setup.public_key(aggregate.plan.setup, public_shares)
    rlk = tuple(
        (q45.padd(*terms), h1)
        for terms, (_, h1) in zip(zip(*(s.terms for s in second)), aggregate.pairs)
    )
    return EvaluationKey(public.pk, rlk)
