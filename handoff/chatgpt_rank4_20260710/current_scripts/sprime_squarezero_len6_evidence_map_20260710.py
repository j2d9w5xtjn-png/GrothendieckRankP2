#!/usr/bin/env python3
r"""Exact S' sweep on the mixed-characteristic square-zero length-six ring.

  G1 = Z/4[z1,z2,z3,z4] / (2 zi, zi zj for all i,j).

The ring has 64 elements, m=(2,z1,z2,z3,z4), m^2=0, and Soc(R)=m.
All six F2-rational xy Hopf fibers and all four t^4 normal forms are tested.

The full generator syzygy is gated without iterating 64^5 tuples.  Every
coefficient is exhaustively checked to split uniquely as a residue bit plus
a socle element; every generator annihilates the socle; and the 2^5 residue
patterns are exhaustively checked to map bijectively to m.  Consequently

  Syz(2,z1,z2,z3,z4) = Soc(R)^5

exactly, of cardinality 32^5=2^25, and its residual quotient is zero.  Thus
each S'-failure formula has one division representative modulo irrelevant
socle shifts and contains no quantifier or approximation.
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time

from z3 import (
    And, BitVec, BitVecVal, Extract, Or, Solver, is_true, sat, set_param,
    simplify, unsat,
)

sys.path.insert(0, __file__.rsplit("/", 1)[0])

from order4sat import fresh  # noqa: E402
from order4sat_ramified_towers_20260709 import value  # noqa: E402
from s2check import build_blocks, phi_of_coords  # noqa: E402


class G1:
    name = "G1=Z/4[z1,z2,z3,z4]/(2zi,zi*zj)"
    characteristic = 4

    def zero(self):
        return (BitVecVal(0, 2),) + tuple(BitVecVal(0, 1) for _ in range(4))

    def one(self):
        return (BitVecVal(1, 2),) + tuple(BitVecVal(0, 1) for _ in range(4))

    def var(self, tag):
        n = fresh(tag)
        return (BitVec(n + "_a", 2),) + tuple(
            BitVec(f"{n}_z{i}", 1) for i in range(1, 5))

    def add(self, a, b):
        return (a[0] + b[0],) + tuple(x ^ y for x, y in zip(a[1:], b[1:]))

    def sub(self, a, b):
        return (a[0] - b[0],) + tuple(x ^ y for x, y in zip(a[1:], b[1:]))

    def mul(self, a, b):
        a0, b0 = Extract(0, 0, a[0]), Extract(0, 0, b[0])
        return (a[0] * b[0],) + tuple(
            (a0 & y) ^ (x & b0) for x, y in zip(a[1:], b[1:]))

    def eq0(self, a):
        return And(*[x == 0 for x in a])

    def neq0(self, a):
        return Or(*[x != 0 for x in a])

    def lowzero(self, a):
        return Extract(0, 0, a[0]) == 0

    def deform(self, tag):
        v = self.var(tag)
        return (BitVecVal(2, 2) * v[0],) + v[1:]

    def concrete(self, a, z1, z2, z3, z4):
        return (BitVecVal(a, 2), BitVecVal(z1, 1), BitVecVal(z2, 1),
                BitVecVal(z3, 1), BitVecVal(z4, 1))

    def elements(self):
        return [self.concrete(a, *zs) for a in range(4)
                for zs in itertools.product((0, 1), repeat=4)]

    def named(self):
        return {
            "two": self.concrete(2, 0, 0, 0, 0),
            "z1": self.concrete(0, 1, 0, 0, 0),
            "z2": self.concrete(0, 0, 1, 0, 0),
            "z3": self.concrete(0, 0, 0, 1, 0),
            "z4": self.concrete(0, 0, 0, 0, 1),
        }

    def generators(self):
        n = self.named()
        return [n["two"], n["z1"], n["z2"], n["z3"], n["z4"]]


XY_MULT = {(1, 2, 3): 1}
T4_MULT = {(1, 1, 2): 1, (1, 2, 3): 1}

XY_PINS = {
    "a2a2": {(3, 1, 2): 1, (3, 2, 1): 1},
    "W2F": {(2, 1, 1): 1, (3, 1, 2): 1, (3, 2, 1): 1},
    "mu2mu2": {
        (1, 1, 1): 1, (2, 2, 2): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
    "mu2a2": {
        (1, 1, 1): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
    },
    "mu2mu2_unipotent": {
        (1, 1, 1): 1, (1, 2, 2): 1, (1, 2, 3): 1,
        (1, 3, 2): 1, (1, 3, 3): 1,
        (2, 2, 2): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
    "mu2mu2_irreducible": {
        (1, 2, 2): 1, (1, 1, 3): 1, (1, 3, 1): 1, (1, 3, 3): 1,
        (2, 1, 1): 1, (2, 2, 2): 1,
        (2, 1, 3): 1, (2, 3, 1): 1,
        (2, 2, 3): 1, (2, 3, 2): 1, (2, 3, 3): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
}


def t4_pins(c1, c4):
    out = {(3, 1, 2): 1, (3, 2, 1): 1}
    if c1:
        for key in ((1, 1, 2), (1, 2, 1), (1, 2, 3), (1, 3, 2),
                    (3, 2, 3), (3, 3, 2)):
            out[key] = 1
    if c4:
        out[(1, 2, 2)] = 1
    return out


class PinnedRing:
    def __init__(self, base, pins, label):
        self.R, self.pins = base, pins
        self.name = base.name + " [" + label + "]"

    def __getattr__(self, key):
        return getattr(self.R, key)

    def var(self, tag):
        if len(tag) == 4 and tag[0] == "c" and tag[1:].isdigit():
            i, j, k = map(int, tag[1:])
            residue = self.R.one() if self.pins.get((i, j, k), 0) else self.R.zero()
            return self.R.add(residue, self.R.deform(tag))
        return self.R.var(tag)


def key(a):
    return value(a)


def elt(R, a):
    return R.concrete(*a)


def additive_closure(R, generators):
    span = {key(R.zero())}
    genkeys = [key(g) for g in generators]
    changed = True
    while changed:
        changed = False
        for a in list(span):
            for b in genkeys:
                c = key(R.add(elt(R, a), elt(R, b)))
                if c not in span:
                    span.add(c)
                    changed = True
    return span


def ring_gate(R):
    started = time.monotonic()
    els = R.elements()
    val_list = [key(a) for a in els]
    vals = set(val_list)
    assert len(els) == len(vals) == 64
    zero, one = key(R.zero()), key(R.one())
    n = R.named()

    # Independent concrete implementation of the displayed presentation.
    # Checking the Z3 operations against these tables on every input pair
    # proves that the later pure-integer 64^3 audit is also an exhaustive
    # audit of the operations used by the solver.
    def padd(a, b):
        return ((a[0] + b[0]) % 4,) + tuple(x ^ y for x, y in zip(a[1:], b[1:]))

    def psub(a, b):
        return ((a[0] - b[0]) % 4,) + tuple(x ^ y for x, y in zip(a[1:], b[1:]))

    def pmul(a, b):
        return ((a[0] * b[0]) % 4,) + tuple(
            ((a[0] & 1) & y) ^ (x & (b[0] & 1))
            for x, y in zip(a[1:], b[1:])
        )

    # Presentation relations.
    for g in R.generators():
        for h in R.generators():
            assert key(R.mul(g, h)) == zero

    # Exhaustively cross-check all binary Z3 operations against the
    # independent truth tables.
    for a, ak in zip(els, val_list):
        assert key(R.add(a, R.zero())) == padd(ak, zero) == ak
        assert key(R.mul(a, R.one())) == pmul(ak, one) == ak
        for b, bk in zip(els, val_list):
            assert key(R.add(a, b)) == padd(ak, bk)
            assert key(R.sub(a, b)) == psub(ak, bk)
            assert key(R.mul(a, b)) == pmul(ak, bk)

    # Exhaustive ring axioms on the verified tables; the genuinely ternary
    # laws run on all 64^3 triples.
    for a in val_list:
        assert padd(a, zero) == a
        assert padd(a, psub(zero, a)) == zero
        assert pmul(a, one) == a
    for a, b in itertools.product(val_list, repeat=2):
        assert padd(a, b) in vals and padd(a, b) == padd(b, a)
        assert pmul(a, b) in vals and pmul(a, b) == pmul(b, a)
    for a, b, c in itertools.product(val_list, repeat=3):
        assert padd(padd(a, b), c) == padd(a, padd(b, c))
        assert pmul(pmul(a, b), c) == pmul(a, pmul(b, c))
        assert pmul(a, padd(b, c)) == padd(pmul(a, b), pmul(a, c))

    m = {key(a) for a in els if is_true(simplify(R.lowzero(a)))}
    assert len(m) == 32 and zero in m and one not in m
    assert all(key(R.mul(elt(R, a), elt(R, b))) == zero for a in m for b in m)

    soc = {key(a) for a in els
           if all(key(R.mul(a, elt(R, b))) == zero for b in m)}
    assert soc == m and len(soc) == 32

    # The five displayed generators span all of m over F2.
    residue_span = {
        key(sum_ring(R, [g for bit, g in zip(bits, R.generators()) if bit]))
        for bits in itertools.product((0, 1), repeat=5)
    }
    assert residue_span == m

    units = {key(a) for a in els
             if any(key(R.mul(a, b)) == one for b in els)}
    assert units == vals - m
    print(f"[ring gate] |R|=64, char=4, |m|=|Soc|=32, m^2=0, "
          f"five generators span m -> PASS ({time.monotonic()-started:.2f}s)",
          flush=True)
    return m, soc


def sum_ring(R, xs):
    out = R.zero()
    for x in xs:
        out = R.add(out, x)
    return out


def full_syzygy_gate(R, m, soc):
    started = time.monotonic()
    gens = R.generators()
    one, zero = R.one(), key(R.zero())

    # Exhaust every element's unique residue-bit + socle decomposition.
    seen = set()
    for bit in (0, 1):
        for s in soc:
            a = R.add(one, elt(R, s)) if bit else elt(R, s)
            seen.add(key(a))
            assert int(not is_true(simplify(R.lowzero(a)))) == bit
    assert seen == {key(a) for a in R.elements()}

    # Exhaustively prove every generator annihilates every socle element.
    assert all(key(R.mul(g, elt(R, s))) == zero for g in gens for s in soc)

    # Exhaust the 2^5 residue coefficient patterns.  Their images are all of
    # m, so a residue tuple is a syzygy iff every residue bit is zero.
    images = {}
    for bits in itertools.product((0, 1), repeat=5):
        image = sum_ring(R, [g for bit, g in zip(bits, gens) if bit])
        images[bits] = key(image)
    assert len(set(images.values())) == 32
    assert {v for v in images.values()} == m
    assert [bits for bits, image in images.items() if image == zero] == [(0, 0, 0, 0, 0)]

    syz_size = len(soc) ** 5
    assert syz_size == 1 << 25
    print(f"[full syzygy gate] Syz=Soc^5 exactly, |Syz|={syz_size}, "
          f"residual dimension=0 -> PASS ({time.monotonic()-started:.2f}s)",
          flush=True)


def in_kernel(R, phi, vec):
    return And(*[R.eq0(a) for a in phi_of_coords(R, phi, vec)])


def division_constraints(R, phi_i, gens, vecs):
    rows = []
    for r in range(3):
        total = R.zero()
        for g, vec in zip(gens, vecs):
            total = R.add(total, R.mul(g, vec[r]))
        rows.append(R.eq0(R.sub(total, phi_i[r + 1])))
    return rows


def sprime_holds(R, phi, gens, tag):
    rows = []
    for i in range(1, 4):
        vecs = [[R.var(f"{tag}_h_{i}_{j}_{r}") for r in range(3)]
                for j in range(5)]
        rows.append(And(*division_constraints(R, phi[i], gens, vecs),
                        *[in_kernel(R, phi, vec) for vec in vecs]))
    return And(*rows)


def sprime_fail_i(R, phi, gens, tag, i):
    vecs = [[R.var(f"{tag}_f_{i}_{j}_{r}") for r in range(3)]
            for j in range(5)]
    division = And(*division_constraints(R, phi[i], gens, vecs))
    # Syz/Soc^5=0, and socle shifts do not alter kernel membership because
    # fiber2 puts every phi coefficient in m and Soc*m=0.
    some_nonkernel = Or(*[
        Or(*[R.neq0(a) for a in phi_of_coords(R, phi, vec)]) for vec in vecs
    ])
    return And(division, some_nonkernel)


def solve(label, constraints, timeout):
    s = Solver()
    s.set("timeout", timeout * 1000)
    s.add(*constraints)
    t0 = time.monotonic()
    ans = s.check()
    print(f"  [{label}] -> {ans} ({time.monotonic()-t0:.2f}s)", flush=True)
    return ans


def run_stratum(base, fib, pins, label, timeout):
    print(f"--- {label} ---", flush=True)
    R = PinnedRing(base, pins, label)
    A, M, C, F, phi, _, _ = build_blocks(R, fib)
    core = A + M + C + F
    h0 = solve("H0 full bialgebra+fiber2", core, timeout)
    if h0 == unsat:
        print("  [VACUOUS] no bialgebra lift in this exact stratum", flush=True)
        return ("vacuous",)
    if h0 != sat:
        return ("open-H0", str(h0))

    gens = base.generators()
    s1 = solve("S1 explicit S'-HOLDS witness",
               core + [sprime_holds(R, phi, gens, "sq6")], timeout)
    if s1 != sat:
        return ("invalid-S1", str(s1))

    out = []
    for i in range(1, 4):
        out.append(solve(f"S2.{i} exact S'-FAIL_i",
                         core + [sprime_fail_i(R, phi, gens, "sq6", i)], timeout))
    return tuple(map(str, out))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--fibers", choices=("xy", "t4", "all"), default="all")
    ap.add_argument("--gates-only", action="store_true")
    args = ap.parse_args()
    set_param("parallel.enable", True)

    base = G1()
    print("EXACT S' MIXED SQUARE-ZERO LENGTH-SIX SWEEP", flush=True)
    m, soc = ring_gate(base)
    full_syzygy_gate(base, m, soc)
    if args.gates_only:
        print("DONE gates-only sprime_squarezero_len6_evidence_map_20260710", flush=True)
        return

    results = []
    if args.fibers in ("xy", "all"):
        for name, pins in XY_PINS.items():
            label = "xy/" + name
            results.append((label, run_stratum(base, XY_MULT, pins, label, args.timeout)))
    if args.fibers in ("t4", "all"):
        for c1, c4 in itertools.product((0, 1), repeat=2):
            label = f"t4/c1={c1},c4={c4}"
            results.append((label, run_stratum(
                base, T4_MULT, t4_pins(c1, c4), label, args.timeout)))

    print("===== SUMMARY =====", flush=True)
    for label, ans in results:
        print(f"  {label}: {','.join(ans)}", flush=True)
    print("DONE sprime_squarezero_len6_evidence_map_20260710", flush=True)


if __name__ == "__main__":
    main()
