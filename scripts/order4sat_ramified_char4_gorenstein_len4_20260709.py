#!/usr/bin/env python3
r"""Full rank-four Hopf searches on the two omitted char-4 Gorenstein bases.

For c=0,1, test

    R_c = (Z/4)[y] / (y^2 - 2*c*y).

Both rings have 16 elements, m=(2,y), m^2=(2y), m^3=0, residue F_2,
and one-dimensional socle (2y).  Their quotient by the socle is the
mixed-characteristic square-zero ring (Z/4)[y]/(2y,y^2).  These are the
alternating/nonalternating characteristic-four Gorenstein extensions that
are not represented by the earlier principal-ring search.
"""

from __future__ import annotations

import itertools
import sys
import time

from z3 import And, BitVec, BitVecVal, Extract, Or, is_true, simplify

from order4sat import fresh
from order4sat_ramified_towers_20260709 import FIBERS, solve_ring_fiber, value


class Char4Gorenstein:
    def __init__(self, c):
        if c not in (0, 1):
            raise ValueError(c)
        self.c = c
        relation = "y^2" if c == 0 else "y^2-2y"
        self.name = f"Z/4[y]/({relation})"

    def zero(self):
        return BitVecVal(0, 2), BitVecVal(0, 2)

    def one(self):
        return BitVecVal(1, 2), BitVecVal(0, 2)

    def var(self, tag):
        name = fresh(tag)
        return BitVec(name + "_a", 2), BitVec(name + "_b", 2)

    def add(self, x, z):
        return x[0] + z[0], x[1] + z[1]

    def sub(self, x, z):
        return x[0] - z[0], x[1] - z[1]

    def mul(self, x, z):
        a, b = x
        d, f = z
        return a * d, a * f + b * d + BitVecVal(2 * self.c, 2) * b * f

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
    vals = {value(x) for x in els}
    assert len(vals) == 16
    zero, one = R.zero(), R.one()
    y = R.concrete(0, 1)
    two_y = R.concrete(0, 2)
    assert value(R.mul(y, y)) == value(R.concrete(0, 2 * R.c))

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
    assert m2 == {value(zero), value(two_y)}
    assert m3 == {value(zero)}
    socle = {value(x) for x in els
             if all(value(R.mul(x, z)) == value(zero) for z in m)}
    assert socle == {value(zero), value(two_y)}
    print(f"  [ring gates] |R|=16, |m|=8, m^2=(2y), m^3=0, "
          f"socle=(2y) -> PASS ({time.monotonic()-started:.2f}s)", flush=True)


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 7200
    print("EXACT CHAR-4 GORENSTEIN RANK-4 SEARCH", flush=True)
    summary = []
    for c in (0, 1):
        R = Char4Gorenstein(c)
        print(f"===== base {R.name} =====", flush=True)
        ring_gates(R)
        for name, fiber in FIBERS:
            verdict = solve_ring_fiber(R, name, fiber, timeout)
            summary.append((R.name, name, verdict))
    print("===== SUMMARY =====", flush=True)
    for ring, name, verdict in summary:
        print(f"{ring} | {name} | {verdict}", flush=True)
    print("DONE order4sat_ramified_char4_gorenstein_len4_20260709", flush=True)


if __name__ == "__main__":
    main()
