#!/usr/bin/env python3
r"""Full rank-four Hopf search on a small non-principal ramified base.

The ring is

    R_u = (Z/8)[y] / (2y, y^2-4).

It has 16 elements, maximal ideal m=(2,y), m^2=(4), m^3=0, residue field
F_2, and one-dimensional socle (4).  Unlike the previously searched
curvilinear rings, it has embedding dimension two and a mixed-characteristic
quadratic carry y^2=4.  Its quotient by the socle is

    (Z/4)[y] / (2y,y^2),

one of the mixed-characteristic square-zero bases not covered by the
equal-characteristic symbol theorem.

The Hopf equation builder is the audited ring-generic builder in order4sat.py.
All bialgebra axioms and the killed-by-2 fiber condition are imposed.  A SAT
bialgebra with [4]^# nonzero is followed by a separate full antipode query.
"""

from __future__ import annotations

import itertools
import sys
import time

from z3 import And, BitVec, BitVecVal, Extract, Or, ZeroExt, is_true, simplify

from order4sat import fresh
from order4sat_ramified_towers_20260709 import FIBERS, solve_ring_fiber, value


class Ru:
    """(Z/8)[y]/(2y,y^2-4), represented by a+b*y, a mod 8, b mod 2."""

    name = "Z/8[y]/(2y,y^2-4)"

    def zero(self):
        return BitVecVal(0, 3), BitVecVal(0, 1)

    def one(self):
        return BitVecVal(1, 3), BitVecVal(0, 1)

    def var(self, tag):
        name = fresh(tag)
        return BitVec(name + "_a", 3), BitVec(name + "_b", 1)

    def add(self, x, z):
        return x[0] + z[0], x[1] ^ z[1]

    def sub(self, x, z):
        return x[0] - z[0], x[1] ^ z[1]

    def mul(self, x, z):
        a, b = x
        c, d = z
        # ac + bd*y^2 = ac+4bd; (ad+bc)y only sees a,c modulo 2.
        bd = ZeroExt(2, b & d)
        ycoef = (Extract(0, 0, a) & d) ^ (b & Extract(0, 0, c))
        return a * c + BitVecVal(4, 3) * bd, ycoef

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
        return BitVecVal(a, 3), BitVecVal(b, 1)

    def elements(self):
        return [self.concrete(a, b) for a in range(8) for b in range(2)]


def ring_gates(R):
    started = time.monotonic()
    els = R.elements()
    vals = {value(x) for x in els}
    assert len(vals) == 16
    zero, one = R.zero(), R.one()
    y = R.concrete(0, 1)
    two = R.concrete(2, 0)
    four = R.concrete(4, 0)
    assert value(R.mul(two, y)) == value(zero)
    assert value(R.mul(y, y)) == value(four)

    for x, z, w in itertools.product(els, repeat=3):
        assert value(R.add(x, zero)) == value(x)
        assert value(R.mul(x, one)) == value(x)
        assert value(R.mul(x, z)) == value(R.mul(z, x))
        assert value(R.mul(R.mul(x, z), w)) == value(R.mul(x, R.mul(z, w)))
        assert value(R.mul(x, R.add(z, w))) == value(
            R.add(R.mul(x, z), R.mul(x, w)))

    m = [x for x in els if is_true(simplify(R.lowzero(x)))]
    m2 = {value(R.mul(x, z)) for x in m for z in m}
    m3 = {value(R.mul(R.mul(x, z), w)) for x in m for z in m for w in m}
    assert len(m) == 8
    assert m2 == {value(zero), value(four)}
    assert m3 == {value(zero)}
    socle = {value(x) for x in els
             if all(value(R.mul(x, z)) == value(zero) for z in m)}
    assert socle == {value(zero), value(four)}
    print(f"  [ring gates] |R|=16, |m|=8, m^2=(4), m^3=0, socle=(4) "
          f"-> PASS ({time.monotonic()-started:.2f}s)", flush=True)


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 7200
    R = Ru()
    print("EXACT NON-PRINCIPAL RAMIFIED RANK-4 SEARCH", flush=True)
    print(f"===== base {R.name} =====", flush=True)
    ring_gates(R)
    summary = []
    for name, fiber in FIBERS:
        verdict = solve_ring_fiber(R, name, fiber, timeout)
        summary.append((name, verdict))
    print("===== SUMMARY =====", flush=True)
    for name, verdict in summary:
        print(f"{R.name} | {name} | {verdict}", flush=True)
    print("DONE order4sat_ramified_ru_len4_20260709", flush=True)


if __name__ == "__main__":
    main()
