#!/usr/bin/env python3
"""SPEC_4of5 P0 Dec∘Eval differential oracle for the 4-of-5 quorum kernel.

T(x) = [x1+...+x5 >= 4] = e4(x) over F2, evaluated by one kernel term under two
semantics (F2 plaintext, toy BFV ciphertext) and decrypted by any 4 of 5
replicated key holders.

THESE PARAMETERS ARE NOT SECURE. Pure Python, exact integer arithmetic, a
reference only: N = 32, t = 2, q = 2^127 - 1, relin base 2^16 with 8 digits,
CBD(3) errors, ternary s and u, kappa = 40, varsigma = 72.

Usage: python3 -I tools/q45_oracle.py [seed]   (exit 0 iff 10/10 pass)
"""
from __future__ import annotations

import itertools
import math
import random
import sys
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Mapping

# ---------------------------------------------------------------- parameters
N, T_MOD, Q_MOD = 32, 2, (1 << 127) - 1
DELTA = Q_MOD // T_MOD
RELIN_BASE_BITS, RELIN_DIGITS = 16, 8
ETA, KAPPA, SMUDGE_BITS = 3, 40, 72
PARTIES = (1, 2, 3, 4, 5)
QUORUM = 4
SEEDS = (0x45, 0x1234, 0x7, 0x63)
O6_TRIALS, O6_BAND = 128, (0.3, 0.7)
INPUTS = tuple(itertools.product((0, 1), repeat=len(PARTIES)))

Poly = tuple  # N integers


# ---------------------------------------------------------------- reference
def reference(x) -> int:
    return int(sum(x) >= QUORUM)


def threshold_via_elementary(n: int, k: int, w: int) -> int:
    """[w >= k] = sum_{j=k}^{n} (-1)^{j-k} C(j-1,k-1) e_j, with e_j(x) = C(w,j)."""
    return sum((-1) ** (j - k) * math.comb(j - 1, k - 1) * math.comb(w, j)
               for j in range(k, n + 1))


# ---------------------------------------------------------------- the kernel, written once
def _kernel(add, mul, x, rho_left):
    x1, x2, x3, x4, x5 = x
    p12, p45 = mul(x1, x2), mul(x4, x5)
    pi = add(add(mul(x3, x4), mul(x3, x5)), p45)
    rho = mul(rho_left(add, x1, x2), x3)
    return add(mul(p12, pi), mul(p45, rho))


def e4(add, mul, x):
    """T = p12*pi + p45*rho: 7 multiplications, depth 2."""
    return _kernel(add, mul, x, lambda add, a, b: add(a, b))


def e4_mutant_m1(add, mul, x):
    """Plausible wrong kernel: rho = x1*x3 drops the x2x3x4x5 monomial."""
    return _kernel(add, mul, x, lambda add, a, b: a)


F2 = (lambda a, b: a ^ b, lambda a, b: a & b)


def witnesses(kernel, ref) -> tuple:
    return tuple(x for x in INPUTS if kernel(*F2, x) != ref(x))


# ---------------------------------------------------------------- access structure
UNQUALIFIED = tuple(frozenset(a) for a in itertools.combinations(PARTIES, QUORUM - 1))


def holders(a: frozenset) -> frozenset:
    return frozenset(PARTIES) - a


def load() -> tuple:
    return tuple(sum(p in holders(a) for a in UNQUALIFIED) for p in PARTIES)


def designation(s: frozenset) -> Mapping[frozenset, int] | None:
    """delta_S(A) = min(H(A) ∩ S); None unless total over every A."""
    picks = {a: holders(a) & s for a in UNQUALIFIED}
    return None if any(not h for h in picks.values()) else {a: min(h) for a, h in picks.items()}


def lagrange(s) -> Mapping[int, Fraction]:
    return {j: math.prod((Fraction(m, m - j) for m in s if m != j), start=Fraction(1)) for j in s}


# ---------------------------------------------------------------- ring Z_q[X]/(X^N + 1)
def zero() -> Poly:
    return (0,) * N


def const(c: int) -> Poly:
    return (c,) + (0,) * (N - 1)


def center(c: int) -> int:
    c %= Q_MOD
    return c - Q_MOD if c > Q_MOD // 2 else c


def reduce(p) -> Poly:
    return tuple(c % Q_MOD for c in p)


def padd(*ps) -> Poly:
    return reduce(map(sum, zip(*ps)))


def pneg(p) -> Poly:
    return reduce(-c for c in p)


def pmul_z(a, b) -> Poly:
    """Negacyclic product over Z (no reduction mod q)."""
    r = [0] * (2 * N)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                r[i + j] += ai * bj
    return tuple(r[i] - r[i + N] for i in range(N))


def pmul(a, b) -> Poly:
    return reduce(pmul_z(a, b))


def scale_round(p) -> Poly:
    """round(t/q · p) over Z, then mod q."""
    return reduce((2 * T_MOD * c + Q_MOD) // (2 * Q_MOD) for c in p)


def inf_norm(p) -> int:
    return max(abs(center(c)) for c in p)


# ---------------------------------------------------------------- sampling
def ternary(rng) -> Poly:
    return tuple(rng.choice((-1, 0, 1)) for _ in range(N))


def cbd(rng) -> Poly:
    return tuple(sum(rng.getrandbits(1) - rng.getrandbits(1) for _ in range(ETA)) for _ in range(N))


def uniform(rng) -> Poly:
    return tuple(rng.randrange(Q_MOD) for _ in range(N))


def smudge(rng, bits: int) -> Poly:
    return tuple(rng.randint(-(1 << bits), 1 << bits) for _ in range(N)) if bits else zero()


# ---------------------------------------------------------------- toy BFV
@dataclass(frozen=True)
class Context:
    s: Poly
    pk: tuple
    rlk: tuple


def _rlwe(s, rng, payload=zero()) -> tuple:
    a = uniform(rng)
    return padd(pneg(padd(pmul(a, s), cbd(rng))), payload), a


def keygen(rng) -> Context:
    s = ternary(rng)
    s2 = pmul(s, s)
    rlk = tuple(_rlwe(s, rng, reduce(c << (RELIN_BASE_BITS * j) for c in s2))
                for j in range(RELIN_DIGITS))
    return Context(s, _rlwe(s, rng), rlk)


def encrypt(ctx: Context, m: int, rng) -> tuple:
    b, a = ctx.pk
    u = ternary(rng)
    return padd(pmul(b, u), cbd(rng), const(DELTA * m)), padd(pmul(a, u), cbd(rng))


def ct_add(x, y) -> tuple:
    return padd(x[0], y[0]), padd(x[1], y[1])


def _digits(p) -> tuple:
    mask = (1 << RELIN_BASE_BITS) - 1
    return tuple(tuple((c >> (RELIN_BASE_BITS * j)) & mask for c in p) for j in range(RELIN_DIGITS))


def ct_mul(ctx: Context, x, y) -> tuple:
    (a0, a1), (b0, b1) = (tuple(tuple(map(center, c)) for c in ct) for ct in (x, y))
    d0 = scale_round(pmul_z(a0, b0))
    d1 = scale_round(map(sum, zip(pmul_z(a0, b1), pmul_z(a1, b0))))
    d2 = scale_round(pmul_z(a1, b1))
    parts = tuple((pmul(dj, r0), pmul(dj, r1)) for dj, (r0, r1) in zip(_digits(d2), ctx.rlk))
    return padd(d0, *(p[0] for p in parts)), padd(d1, *(p[1] for p in parts))


def phase(ct, key) -> Poly:
    return padd(ct[0], pmul(ct[1], key))


def decode(p) -> tuple:
    return tuple(((T_MOD * center(c) * 2 + Q_MOD) // (2 * Q_MOD)) % T_MOD for c in p)


def decrypt(key, ct) -> tuple:
    return decode(phase(ct, key))


def noise(ct, key, m: int) -> int:
    return inf_norm(padd(phase(ct, key), pneg(const(DELTA * m))))


# ---------------------------------------------------------------- threshold decryption
def replicate(s, rng) -> Mapping[frozenset, Poly]:
    head = {a: uniform(rng) for a in UNQUALIFIED[:-1]}
    return {**head, UNQUALIFIED[-1]: padd(s, pneg(padd(*head.values())))}


def partials(shares, quorum: frozenset, c1, rng, smudge_bits) -> Mapping[int, Poly]:
    d = designation(quorum)
    sigma = {i: padd(zero(), *(r for a, r in shares.items() if d[a] == i)) for i in sorted(quorum)}
    return {i: padd(pmul(c1, si), smudge(rng, smudge_bits)) for i, si in sigma.items()}


def combine(ct, parts) -> tuple:
    return decode(padd(ct[0], *parts.values()))


def shamir(s, rng) -> Mapping[int, Poly]:
    coeffs = (s,) + tuple(uniform(rng) for _ in range(QUORUM - 1))
    return {j: padd(*(reduce(j ** k * c for c in f) for k, f in enumerate(coeffs))) for j in PARTIES}


def lambda_mod_q(l: Fraction) -> int:
    return l.numerator * pow(l.denominator, -1, Q_MOD) % Q_MOD


def shamir_combine(ct, shares, quorum, rng, local: bool, smudge_bits) -> tuple:
    lam = {j: lambda_mod_q(l) for j, l in lagrange(quorum).items()}
    scaled = lambda p, c: reduce(c * v for v in p)
    if local:
        parts = (padd(scaled(pmul(ct[1], shares[j]), lam[j]), smudge(rng, smudge_bits)) for j in quorum)
    else:
        parts = (scaled(padd(pmul(ct[1], shares[j]), smudge(rng, smudge_bits)), lam[j]) for j in quorum)
    return decode(padd(ct[0], *parts))


# ---------------------------------------------------------------- one run
QUORUMS = tuple(frozenset(s) for s in itertools.combinations(PARTIES, QUORUM))
EXPECT = {x: (reference(x),) + (0,) * (N - 1) for x in INPUTS}


@dataclass(frozen=True)
class State:
    seed: int
    smudge_bits: int
    ctx: Context
    shares: Mapping
    c_t: Mapping

    @classmethod
    def build(cls, seed: int, smudge_bits: int = SMUDGE_BITS) -> "State":
        rng = random.Random(seed)
        ctx = keygen(rng)
        bfv = (ct_add, lambda a, b: ct_mul(ctx, a, b))
        c_t = {x: e4(*bfv, tuple(encrypt(ctx, xi, rng) for xi in x)) for x in INPUTS}
        return cls(seed, smudge_bits, ctx, replicate(ctx.s, rng), c_t)

    def rng(self, tag: str):
        return random.Random(f"{self.seed}:{tag}")


@dataclass(frozen=True)
class Result:
    ok: bool
    detail: str


def check(ok: bool, detail: str) -> Result:
    return Result(bool(ok), detail)


def o1_circuit_fidelity(_):
    bad = witnesses(e4, reference)
    return check(not bad, f"{len(INPUTS) - len(bad)}/{len(INPUTS)} inputs")


def o2_full_key(st: State):
    good = sum(decrypt(st.ctx.s, st.c_t[x]) == EXPECT[x] for x in INPUTS)
    return check(good == len(INPUTS), f"{good}/{len(INPUTS)}")


def o3_quorum_decrypt(st: State):
    rng = st.rng("O3")
    cases = [(x, s) for x in INPUTS for s in QUORUMS]
    good = sum(combine(st.c_t[x], partials(st.shares, s, st.c_t[x][1], rng, st.smudge_bits)) == EXPECT[x]
               for x, s in cases)
    return check(good == len(cases), f"{good}/{len(cases)} (input, quorum) cases")


def o4_access(_):
    subsets = [frozenset(s) for r in range(len(PARTIES) + 1) for s in itertools.combinations(PARTIES, r)]
    ok = all((designation(s) is not None) == (len(s) >= QUORUM) for s in subsets)
    return check(ok and load() == (4,) * 5, f"{len(subsets)} subsets; load {set(load())}")


def o5_noise_margin(st: State):
    e = max(noise(st.c_t[x], st.ctx.s, reference(x)) for x in INPUTS)
    lg = e.bit_length()
    ok = lg + KAPPA <= SMUDGE_BITS and e + len(PARTIES) * (1 << SMUDGE_BITS) < DELTA // 2
    return check(ok, f"log2‖e‖ = {lg}; {lg} + {KAPPA} ≤ {SMUDGE_BITS}; Δ/2 ≈ 2^{round(math.log2(DELTA // 2))}")


def o6_subquorum_blind(st: State):
    hits = 0
    for k in range(O6_TRIALS):
        x, a = INPUTS[k % len(INPUTS)], UNQUALIFIED[k % len(UNQUALIFIED)]
        pooled = padd(zero(), *(r for b, r in st.shares.items() if holders(b) & a))
        hits += decrypt(pooled, st.c_t[x])[0] == reference(x)
    rate = hits / O6_TRIALS
    return check(O6_BAND[0] <= rate <= O6_BAND[1], f"hit rate {rate:.3f} over {O6_TRIALS} trials")


def o7_smudging_present(st: State):
    rng = st.rng("O7")
    s = QUORUMS[0]
    c1 = st.c_t[INPUTS[-1]][1]
    d = designation(s)
    sigma = {i: padd(zero(), *(r for a, r in st.shares.items() if d[a] == i)) for i in sorted(s)}
    parts = partials(st.shares, s, c1, rng, st.smudge_bits)
    bits = tuple(inf_norm(padd(parts[i], pneg(pmul(c1, sigma[i])))).bit_length() for i in sorted(s))
    return check(all(b >= SMUDGE_BITS - 4 for b in bits), ", ".join(map(str, bits)) + " bits")


def m1_mutant_kernel(_):
    ws = witnesses(e4_mutant_m1, reference)
    return check(bool(ws), "witnesses " + ", ".join(map(str, ws)))


def m2_mutant_threshold(_):
    ws = witnesses(e4, lambda x: int(sum(x) >= QUORUM - 1))
    return check(bool(ws), f"{len(ws)} witnesses")


def m3_shamir_lambda_placement(st: State):
    rng = st.rng("M3")
    sh = shamir(st.ctx.s, rng)
    survives = lambda local: tuple(
        tuple(sorted(q)) for q in QUORUMS
        if all(shamir_combine(st.c_t[x], sh, q, rng, local, st.smudge_bits) == EXPECT[x] for x in INPUTS))
    loc, late = survives(True), survives(False)
    ok = len(loc) == len(QUORUMS) and set(late) == {(1, 2, 3, 4), (2, 3, 4, 5)}
    return check(ok, f"{len(loc)}/{len(QUORUMS)} vs. survives only {', '.join(map(str, late))}")


OBLIGATIONS: Mapping[str, Callable] = {
    "O1": o1_circuit_fidelity, "O2": o2_full_key, "O3": o3_quorum_decrypt,
    "O4": o4_access, "O5": o5_noise_margin, "O6": o6_subquorum_blind,
    "O7": o7_smudging_present, "M1": m1_mutant_kernel, "M2": m2_mutant_threshold,
    "M3": m3_shamir_lambda_placement,
}
OBLIGATION_IDS = tuple(OBLIGATIONS)


def discharge(obligation, st) -> Result:
    """An obligation that raises is a failure, never a pass."""
    try:
        return obligation(st)
    except Exception as exc:  # noqa: BLE001 - fail closed
        return Result(False, f"raised {type(exc).__name__}: {exc}")


def run(seed: int) -> Mapping[str, Result]:
    st = State.build(seed)
    return {k: discharge(f, st) for k, f in OBLIGATIONS.items()}


def main(argv) -> int:
    seed = int(argv[1], 0) if len(argv) > 1 else SEEDS[0]
    report = run(seed)
    for k, r in report.items():
        print(f"{k:<3} {'PASS' if r.ok else 'FAIL'}  {r.detail}")
    passed = sum(r.ok for r in report.values())
    print(f"seed {seed:#x}: {passed}/{len(report)} obligations")
    return 0 if passed == len(report) else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
