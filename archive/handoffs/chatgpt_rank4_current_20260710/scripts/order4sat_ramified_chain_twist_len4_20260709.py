#!/usr/bin/env python3
r"""Exact rank-four Hopf search over the omitted twisted length-four chain ring.

The base is

    R_tw = (Z/4)[p] / (p^2 - 2p - 2).

It has additive group (Z/4)^2, maximal ideal (p), and
p^2=2+2p, p^3=2p, p^4=0.  This is the unit-twisted ramification-index-two
chain ring not represented by the earlier family p^2=2.
"""

from __future__ import annotations

import itertools
import sys
import time

from z3 import And, BitVec, BitVecVal, Extract, Or, is_true, simplify

from order4sat import fresh
from order4sat_ramified_towers_20260709 import FIBERS, solve_ring_fiber, value


class TwistedChainLen4:
    name = "Z/4[p]/(p^2-2p-2)"

    def zero(self):
        return BitVecVal(0, 2), BitVecVal(0, 2)

    def one(self):
        return BitVecVal(1, 2), BitVecVal(0, 2)

    def var(self, tag):
        name = fresh(tag)
        return BitVec(name + "_a", 2), BitVec(name + "_p", 2)

    def add(self, x, z):
        return x[0] + z[0], x[1] + z[1]

    def sub(self, x, z):
        return x[0] - z[0], x[1] - z[1]

    def mul(self, x, z):
        a, b = x
        c, d = z
        # bd*p^2 = 2bd + 2bd*p.
        return (a * c + BitVecVal(2, 2) * b * d,
                a * d + b * c + BitVecVal(2, 2) * b * d)

    def eq0(self, x):
        return And(x[0] == 0, x[1] == 0)

    def neq0(self, x):
        return Or(x[0] != 0, x[1] != 0)

    def lowzero(self, x):
        return Extract(0, 0, x[0]) == 0

    def deform(self, tag):
        v = self.var(tag)
        return BitVecVal(2, 2) * v[0], v[1]

    def concrete(self, a, b):
        return BitVecVal(a, 2), BitVecVal(b, 2)

    def elements(self):
        return [self.concrete(a, b) for a in range(4) for b in range(4)]


def ring_gates(R):
    started = time.monotonic()
    els = R.elements()
    zero, one = R.zero(), R.one()
    p = R.concrete(0, 1)
    two = R.concrete(2, 0)
    two_p = R.concrete(0, 2)
    assert len({value(x) for x in els}) == 16
    assert value(R.mul(p, p)) == value(R.add(two, two_p))
    assert value(R.mul(R.mul(p, p), p)) == value(two_p)
    assert value(R.mul(R.mul(R.mul(p, p), p), p)) == value(zero)

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
    for _ in range(1, 5):
        pk = R.mul(pk, p)
        sizes.append(len({value(R.mul(pk, x)) for x in els}))
    assert sizes == [8, 4, 2, 1]
    assert {value(R.mul(p, x)) for x in els} == {value(x) for x in m}
    print(f"  [ring gates] |R|=16, m=(p), |(p^k)|={sizes} -> PASS "
          f"({time.monotonic()-started:.2f}s)", flush=True)


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 7200
    R = TwistedChainLen4()
    print("EXACT TWISTED CHAIN RANK-4 SEARCH", flush=True)
    print(f"===== base {R.name} =====", flush=True)
    ring_gates(R)
    summary = []
    for name, fiber in FIBERS:
        verdict = solve_ring_fiber(R, name, fiber, timeout)
        summary.append((name, verdict))
    print("===== SUMMARY =====", flush=True)
    for name, verdict in summary:
        print(f"{R.name} | {name} | {verdict}", flush=True)
    print("DONE order4sat_ramified_chain_twist_len4_20260709", flush=True)


if __name__ == "__main__":
    main()
