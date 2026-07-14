#!/usr/bin/env python3
r"""Full rank-four Hopf search over a ramified length-five Gorenstein base.

The exact ring is

  R = (Z/4)[pi,y] /
      (pi^2-2, 2y, pi*y-2pi, y^2-2pi).

Its additive group is Z/4{1} + Z/4{pi} + F_2{y}, hence |R|=32.  It is a
non-principal mixed-characteristic local ring with

  m=(pi,y), m^2=(2,2pi), m^3=(2pi), m^4=0,

and socle (2pi).  This is deeper than the three length-four Gorenstein bases
tested in the companion scripts and has genuinely mixed pi/y carries.
"""

from __future__ import annotations

import itertools
import sys
import time

from z3 import And, BitVec, BitVecVal, Extract, Or, ZeroExt, is_true, simplify

from order4sat import fresh
from order4sat_ramified_towers_20260709 import FIBERS, solve_ring_fiber, value


class RamifiedGorensteinLen5:
    name = "Z/4[pi,y]/(pi^2-2,2y,pi*y-2pi,y^2-2pi)"

    def zero(self):
        return BitVecVal(0, 2), BitVecVal(0, 2), BitVecVal(0, 1)

    def one(self):
        return BitVecVal(1, 2), BitVecVal(0, 2), BitVecVal(0, 1)

    def var(self, tag):
        name = fresh(tag)
        return (BitVec(name + "_a", 2), BitVec(name + "_p", 2),
                BitVec(name + "_y", 1))

    def add(self, x, z):
        return x[0] + z[0], x[1] + z[1], x[2] ^ z[2]

    def sub(self, x, z):
        return x[0] - z[0], x[1] - z[1], x[2] ^ z[2]

    def mul(self, x, z):
        a, b, c = x
        d, f, g = z
        # pi^2=2 contributes to the scalar coordinate.  Each of pi*y and
        # y^2 is 2pi, contributing twice its coefficient to the pi coordinate.
        bf = b * f
        scalar = a * d + BitVecVal(2, 2) * bf
        bg = b * ZeroExt(1, g)
        cf = ZeroExt(1, c) * f
        cg = ZeroExt(1, c & g)
        picoef = a * f + b * d + BitVecVal(2, 2) * (bg + cf + cg)
        ycoef = (Extract(0, 0, a) & g) ^ (c & Extract(0, 0, d))
        return scalar, picoef, ycoef

    def eq0(self, x):
        return And(x[0] == 0, x[1] == 0, x[2] == 0)

    def neq0(self, x):
        return Or(x[0] != 0, x[1] != 0, x[2] != 0)

    def lowzero(self, x):
        return Extract(0, 0, x[0]) == 0

    def deform(self, tag):
        v = self.var(tag)
        return BitVecVal(2, 2) * v[0], v[1], v[2]

    def concrete(self, a, b, c):
        return BitVecVal(a, 2), BitVecVal(b, 2), BitVecVal(c, 1)

    def elements(self):
        return [self.concrete(a, b, c)
                for a in range(4) for b in range(4) for c in range(2)]


def ring_gates(R):
    started = time.monotonic()
    els = R.elements()
    vals = {value(x) for x in els}
    assert len(vals) == 32
    zero, one = R.zero(), R.one()
    two = R.concrete(2, 0, 0)
    pi = R.concrete(0, 1, 0)
    two_pi = R.concrete(0, 2, 0)
    y = R.concrete(0, 0, 1)
    assert value(R.mul(pi, pi)) == value(two)
    assert value(R.mul(pi, y)) == value(two_pi)
    assert value(R.mul(y, y)) == value(two_pi)
    assert value(R.mul(two, y)) == value(zero)

    for x, z, w in itertools.product(els, repeat=3):
        assert value(R.add(x, zero)) == value(x)
        assert value(R.mul(x, one)) == value(x)
        assert value(R.mul(x, z)) == value(R.mul(z, x))
        assert value(R.mul(R.mul(x, z), w)) == value(R.mul(x, R.mul(z, w)))
        assert value(R.mul(x, R.add(z, w))) == value(
            R.add(R.mul(x, z), R.mul(x, w)))

    m = [x for x in els if is_true(simplify(R.lowzero(x)))]
    powers = [{value(x) for x in m}]
    for _ in range(3):
        prev = powers[-1]
        nxt = {value(R.mul(R.concrete(*a), z)) for a in prev for z in m}
        powers.append(nxt)
    assert [len(s) for s in powers] == [16, 4, 2, 1]
    assert powers[1] == {
        value(zero), value(two), value(two_pi), value(R.add(two, two_pi))}
    assert powers[2] == {value(zero), value(two_pi)}
    assert powers[3] == {value(zero)}
    socle = {value(x) for x in els
             if all(value(R.mul(x, z)) == value(zero) for z in m)}
    assert socle == {value(zero), value(two_pi)}
    print(f"  [ring gates] |R|=32, |m^k|=[16,4,2,1], socle=(2pi) "
          f"-> PASS ({time.monotonic()-started:.2f}s)", flush=True)


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 7200
    R = RamifiedGorensteinLen5()
    print("EXACT RAMIFIED LENGTH-5 GORENSTEIN RANK-4 SEARCH", flush=True)
    print(f"===== base {R.name} =====", flush=True)
    ring_gates(R)
    summary = []
    for name, fiber in FIBERS:
        verdict = solve_ring_fiber(R, name, fiber, timeout)
        summary.append((name, verdict))
    print("===== SUMMARY =====", flush=True)
    for name, verdict in summary:
        print(f"{R.name} | {name} | {verdict}", flush=True)
    print("DONE order4sat_ramified_gorenstein_len5_20260709", flush=True)


if __name__ == "__main__":
    main()
