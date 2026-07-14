#!/usr/bin/env python3
r"""Full rank-four Hopf search over a non-curvilinear length-five base.

The corrected associative presentation is

  R = (Z/4)[x,y]/(2x,2y,xy,y^2-2,x^3-2).

Its additive basis is Z/4{1} + F_2{x,x^2,y}.  It is local Gorenstein with
m=(x,y), m^2=(x^2), m^3=(2), m^4=0 and socle (2).  In particular it is not
detected by merely testing curvilinear projections.
"""

from __future__ import annotations

import itertools
import sys
import time

from z3 import And, BitVec, BitVecVal, Extract, Or, ZeroExt, is_true, simplify

from order4sat import fresh
from order4sat_ramified_towers_20260709 import FIBERS, solve_ring_fiber, value


class RamifiedXYGorensteinLen5:
    name = "Z/4[x,y]/(2x,2y,xy,y^2-2,x^3-2)"

    def zero(self):
        return (BitVecVal(0, 2), BitVecVal(0, 1), BitVecVal(0, 1),
                BitVecVal(0, 1))

    def one(self):
        return (BitVecVal(1, 2), BitVecVal(0, 1), BitVecVal(0, 1),
                BitVecVal(0, 1))

    def var(self, tag):
        name = fresh(tag)
        return (BitVec(name + "_a", 2), BitVec(name + "_x", 1),
                BitVec(name + "_x2", 1), BitVec(name + "_y", 1))

    def add(self, u, v):
        return (u[0] + v[0], u[1] ^ v[1], u[2] ^ v[2], u[3] ^ v[3])

    def sub(self, u, v):
        return (u[0] - v[0], u[1] ^ v[1], u[2] ^ v[2], u[3] ^ v[3])

    def mul(self, u, v):
        a, b, c, d = u
        A, B, C, D = v
        # x*x^2=x^3=2 and y^2=2 give the only non-scalar carries.
        carry = (b & C) ^ (c & B) ^ (d & D)
        scalar = a * A + BitVecVal(2, 2) * ZeroExt(1, carry)
        xcoef = (Extract(0, 0, a) & B) ^ (b & Extract(0, 0, A))
        x2coef = ((Extract(0, 0, a) & C) ^ (c & Extract(0, 0, A))
                  ^ (b & B))
        ycoef = (Extract(0, 0, a) & D) ^ (d & Extract(0, 0, A))
        return scalar, xcoef, x2coef, ycoef

    def eq0(self, u):
        return And(*[z == 0 for z in u])

    def neq0(self, u):
        return Or(*[z != 0 for z in u])

    def lowzero(self, u):
        return Extract(0, 0, u[0]) == 0

    def deform(self, tag):
        v = self.var(tag)
        return (BitVecVal(2, 2) * v[0], v[1], v[2], v[3])

    def concrete(self, a, b, c, d):
        return (BitVecVal(a, 2), BitVecVal(b, 1), BitVecVal(c, 1),
                BitVecVal(d, 1))

    def elements(self):
        return [self.concrete(a, b, c, d) for a in range(4)
                for b in range(2) for c in range(2) for d in range(2)]


def ring_gates(R):
    started = time.monotonic()
    els = R.elements()
    zero, one = R.zero(), R.one()
    two = R.concrete(2, 0, 0, 0)
    x = R.concrete(0, 1, 0, 0)
    x2 = R.concrete(0, 0, 1, 0)
    y = R.concrete(0, 0, 0, 1)
    assert len({value(z) for z in els}) == 32
    assert value(R.mul(two, x)) == value(zero)
    assert value(R.mul(two, y)) == value(zero)
    assert value(R.mul(x, y)) == value(zero)
    assert value(R.mul(y, y)) == value(two)
    assert value(R.mul(x, x)) == value(x2)
    assert value(R.mul(x2, x)) == value(two)

    for u, v, w in itertools.product(els, repeat=3):
        assert value(R.add(u, zero)) == value(u)
        assert value(R.mul(u, one)) == value(u)
        assert value(R.mul(u, v)) == value(R.mul(v, u))
        assert value(R.mul(R.mul(u, v), w)) == value(R.mul(u, R.mul(v, w)))
        assert value(R.mul(u, R.add(v, w))) == value(
            R.add(R.mul(u, v), R.mul(u, w)))

    m = [z for z in els if is_true(simplify(R.lowzero(z)))]
    mv = {value(z) for z in m}
    m2 = {value(R.mul(u, v)) for u in m for v in m}
    m3 = {value(R.mul(R.concrete(*u), v)) for u in m2 for v in m}
    m4 = {value(R.mul(R.concrete(*u), v)) for u in m3 for v in m}
    assert [len(mv), len(m2), len(m3), len(m4)] == [16, 4, 2, 1]
    assert m2 == {value(zero), value(x2), value(two), value(R.add(x2, two))}
    assert m3 == {value(zero), value(two)}
    assert m4 == {value(zero)}
    socle = {value(z) for z in els
             if all(value(R.mul(z, u)) == value(zero) for u in m)}
    assert socle == {value(zero), value(two)}
    print(f"  [ring gates] |R|=32, |m^k|=[16,4,2,1], socle=(2) "
          f"-> PASS ({time.monotonic()-started:.2f}s)", flush=True)


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 7200
    R = RamifiedXYGorensteinLen5()
    print("EXACT RAMIFIED XY-GORENSTEIN RANK-4 SEARCH", flush=True)
    print(f"===== base {R.name} =====", flush=True)
    ring_gates(R)
    summary = []
    for name, fiber in FIBERS:
        verdict = solve_ring_fiber(R, name, fiber, timeout)
        summary.append((name, verdict))
    print("===== SUMMARY =====", flush=True)
    for name, verdict in summary:
        print(f"{R.name} | {name} | {verdict}", flush=True)
    print("DONE order4sat_ramified_xy_gorenstein_len5_20260709", flush=True)


if __name__ == "__main__":
    main()
