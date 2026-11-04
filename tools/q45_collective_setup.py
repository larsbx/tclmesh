"""In-memory, honest-party P2a experiment using the insecure P0 toy ring.

Each party samples one additive key contribution and replicates its pieces to
the corresponding pairs of holders. The public key contains only the sum of
public contributions and the common polynomial. No production protocol is
implemented here.
"""
from dataclasses import dataclass
from random import Random
from typing import Iterable

import q45_oracle as q45

Coalition = frozenset[int]
PARTIES = frozenset(q45.PARTIES)


def _canonical(poly: q45.Poly) -> bool:
    return len(poly) == q45.N and all(type(c) is int and 0 <= c < q45.Q_MOD for c in poly)


@dataclass(frozen=True)
class Setup:
    session: str
    a: q45.Poly

    def __post_init__(self):
        if not self.session or not _canonical(self.a):
            raise ValueError("expected a session ID and a canonical common polynomial")


@dataclass(frozen=True)
class PublicShare:
    setup: Setup
    sender: int
    value: q45.Poly


@dataclass(frozen=True)
class Fragment:
    setup: Setup
    sender: int
    recipient: int
    coalition: Coalition
    value: q45.Poly


@dataclass(frozen=True)
class PublicKey:
    # The .pk shape is the only part of the P0 context needed by encrypt().
    pk: tuple[q45.Poly, q45.Poly]


@dataclass(frozen=True)
class Holder:
    party: int
    pieces: dict[Coalition, q45.Poly]


def contribute(setup: Setup, sender: int, rng: Random) -> tuple[PublicShare, tuple[Fragment, ...]]:
    if sender not in PARTIES:
        raise ValueError("unknown sender")
    secret = q45.ternary(rng)
    public = q45.padd(q45.pneg(q45.pmul(setup.a, secret)), q45.cbd(rng))
    fragments = tuple(
        Fragment(setup, sender, recipient, coalition, value)
        for coalition, value in q45.replicate(secret, rng).items()
        for recipient in sorted(q45.holders(coalition))
    )
    return PublicShare(setup, sender, public), fragments


def public_key(setup: Setup, shares: Iterable[PublicShare]) -> PublicKey:
    shares = tuple(shares)
    if (
        len(shares) != len(PARTIES)
        or {p.sender for p in shares} != PARTIES
        or any(p.setup != setup or not _canonical(p.value) for p in shares)
    ):
        raise ValueError("expected one public share from each setup participant")
    return PublicKey((q45.padd(*(p.value for p in shares)), setup.a))


def holder(setup: Setup, recipient: int, inbox: Iterable[Fragment]) -> Holder:
    if recipient not in PARTIES:
        raise ValueError("unknown recipient")
    coalitions = [c for c in q45.UNQUALIFIED if recipient in q45.holders(c)]
    expected = {(sender, c) for sender in PARTIES for c in coalitions}
    inbox = tuple(inbox)
    if (
        len(inbox) != len(expected)
        or {(p.sender, p.coalition) for p in inbox} != expected
        or any(p.setup != setup or p.recipient != recipient or not _canonical(p.value) for p in inbox)
    ):
        raise ValueError("expected the recipient's complete, distinct setup fragments")
    return Holder(recipient, {
        c: q45.padd(*(p.value for p in inbox if p.coalition == c)) for c in coalitions
    })


def partial(local: Holder, quorum: Coalition, c1: q45.Poly, rng: Random) -> q45.Poly:
    if len(quorum) != q45.QUORUM or not quorum <= PARTIES or local.party not in quorum:
        raise ValueError("expected a four-party quorum containing the local holder")
    if not _canonical(c1):
        raise ValueError("expected a canonical ciphertext polynomial")
    designation = q45.designation(quorum)
    designated = [piece for c, piece in local.pieces.items() if designation[c] == local.party]
    sigma = q45.padd(q45.zero(), *designated)
    return q45.padd(q45.pmul(c1, sigma), q45.smudge(rng, q45.SMUDGE_BITS))
