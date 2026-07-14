#!/usr/bin/env python3
r"""Exact rank-four searches over all basic unit-carry chain rings of length 5.

For c,d in F_2, the ring R(c,d) has additive group

    (Z/8){1} + (Z/4){p}

and relation

    p^2 = 2 + 2c*p + 4d.

Each is a residue-F_2 chain ring of length five with p^5=0.  R(0,0) is the
pure Eisenstein truncation; R(1,0) extends the omitted length-four twist
p^2=2+2p.  The d term records the remaining valuation-four unit carry in
this fixed coordinate presentation.
"""

from __future__ import annotations

import itertools
import sys
import time

from z3 import And, BitVec, BitVecVal, Extract, Or, ZeroExt, is_true, simplify

from order4sat import fresh
from order4sat_ramified_towers_20260709 import (
    FIBERS, resize_unsigned, solve_ring_fiber, value,
)


class TwistedChainLen5:
    def __init__(self, c, d):
        self.c, self.d = c, d
        self.K = 2 + 4 * d
        self.L = 2 * c
        self.name = f"chain5(c={c},d={d}): p^2={self.K}+{self.L}p"

    def zero(self):
        return BitVecVal(0, 3), BitVecVal(0, 2)

    def one(self):
        return BitVecVal(1, 3), BitVecVal(0, 2)

    def var(self, tag):
        name = fresh(tag)
        return BitVec(name + "_a", 3), BitVec(name + "_p", 2)

    def add(self, x, z):
        return x[0] + z[0], x[1] + z[1]

    def sub(self, x, z):
        return x[0] - z[0], x[1] - z[1]

    def mul(self, x, z):
        a, b = x
        A, B = z
        bB3 = ZeroExt(1, b * B)
        scalar = a * A + BitVecVal(self.K, 3) * bB3
        pcoef = (resize_unsigned(a, 2) * B + b * resize_unsigned(A, 2)
                 + BitVecVal(self.L, 2) * b * B)
        return scalar, pcoef

    def eq0(self, x):
        return And(x[0] == 0, x[1] == 0)

    def neq0(self, x):
        return Or(x[0] != 0, x[1] != 0)

    def lowzero(self, x):
        return Extract(0, 0, x[0]) == 0

    def deform(self, tag):
        v = self.var(tag)
        return BitVecVal(2, 3) * v[0], v[1]

    def concrete(self, a, b):
        return BitVecVal(a, 3), BitVecVal(b, 2)

    def elements(self):
        return [self.concrete(a, b) for a in range(8) for b in range(4)]


def ring_gates(R):
    started = time.monotonic()
    els = R.elements()
    zero, one = R.zero(), R.one()
    p = R.concrete(0, 1)
    rhs = R.concrete(R.K, R.L)
    assert len({value(x) for x in els}) == 32
    assert value(R.mul(p, p)) == value(rhs)

    for x, z, w in itertools.product(els, repeat=3):
        assert value(R.add(x, zero)) == value(x)
        assert value(R.mul(x, one)) == value(x)
        assert value(R.mul(x, z)) == value(R.mul(z, x))
        assert value(R.mul(R.mul(x, z), w)) == value(R.mul(x, R.mul(z, w)))
        assert value(R.mul(x, R.add(z, w))) == value(
            R.add(R.mul(x, z), R.mul(x, w)))

    m = [x for x in els if is_true(simplify(R.lowzero(x)))]
    pk = one
    sizes = []
    for _ in range(1, 6):
        pk = R.mul(pk, p)
        sizes.append(len({value(R.mul(pk, x)) for x in els}))
    assert sizes == [16, 8, 4, 2, 1]
    assert {value(R.mul(p, x)) for x in els} == {value(x) for x in m}
    print(f"  [ring gates] |R|=32, m=(p), |(p^k)|={sizes} -> PASS "
          f"({time.monotonic()-started:.2f}s)", flush=True)


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 7200
    print("EXACT LENGTH-5 CHAIN-TWIST RANK-4 SEARCH", flush=True)
    summary = []
    for c, d in itertools.product((0, 1), repeat=2):
        R = TwistedChainLen5(c, d)
        print(f"===== base {R.name} =====", flush=True)
        ring_gates(R)
        for name, fiber in FIBERS:
            verdict = solve_ring_fiber(R, name, fiber, timeout)
            summary.append((c, d, name, verdict))
    print("===== SUMMARY =====", flush=True)
    for c, d, name, verdict in summary:
        print(f"R({c},{d}) | {name} | {verdict}", flush=True)
    print("DONE order4sat_ramified_chain_twists_len5_20260709", flush=True)


if __name__ == "__main__":
    main()
