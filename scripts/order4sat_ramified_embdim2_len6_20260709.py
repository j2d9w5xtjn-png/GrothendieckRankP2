#!/usr/bin/env python3
r"""Direct rank-four search on ramified, nonprincipal two-parameter bases.

The configurable family is

  R_{N,L,theta} = O_N[u]/(pi^L u, u^2-theta),
  O_N = Z_2[pi]/(pi^2-2, pi^N).

It has residue field F_2 and length N+L.  The default N=4,L=2 gives the
64-element length-six bases theta=0,pi^2,pi^3; deeper N,L values are accepted.
The special Hopf fiber is pinned to alpha_2 x mu_2, but every higher base-ring
digit of both multiplication and coproduct remains free.  The final query is
the full bialgebra system together with [4]^# != eta epsilon; failure of the
stronger auxiliary invariant S' is never treated as a counterexample.
"""

from __future__ import annotations

import argparse
import itertools
import sys

from z3 import And, BitVec, BitVecVal, Extract, Or, ZeroExt

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat import fresh, run  # noqa: E402


def cast(x, width):
    old = x.size()
    if old == width:
        return x
    if old < width:
        return ZeroExt(width - old, x)
    return Extract(width - 1, 0, x)


class EisensteinDVR:
    """Z_2[pi]/(pi^e-2,pi^N) in its Z_2-basis 1,...,pi^(e-1)."""

    def __init__(self, e, N):
        self.e, self.N = e, N
        self.widths = tuple((N - r + e - 1) // e for r in range(min(e, N)))

    def zero(self):
        return tuple(BitVecVal(0, w) for w in self.widths)

    def one(self):
        return tuple(BitVecVal(int(r == 0), w) for r, w in enumerate(self.widths))

    def var(self, tag):
        nm = fresh(tag)
        return tuple(BitVec(nm + f"_{r}", w) for r, w in enumerate(self.widths))

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def mul(self, a, b):
        out = [BitVecVal(0, w) for w in self.widths]
        for r, x in enumerate(a):
            for s, y in enumerate(b):
                degree = r + s
                carry = int(degree >= self.e)
                target = degree - carry * self.e
                if target >= len(out):
                    continue
                w = self.widths[target]
                term = cast(x, w) * cast(y, w)
                out[target] = out[target] + ((term << 1) if carry else term)
        return tuple(out)

    def eq0(self, a):
        return And(*[x == 0 for x in a])

    def neq0(self, a):
        return Or(*[x != 0 for x in a])

    def lowzero(self, a):
        return (a[0] & 1) == 0

    def deform(self, tag):
        v = self.var(tag)
        return (2 * v[0],) + v[1:]

    def monomial(self, degree):
        if degree >= self.N:
            return self.zero()
        r, q = degree % self.e, degree // self.e
        out = list(self.zero())
        out[r] = BitVecVal(1 << q, self.widths[r])
        return tuple(out)

    def reduce_to(self, a, target):
        assert self.e == target.e and target.N <= self.N
        return tuple(cast(a[r], target.widths[r]) for r in range(len(target.widths)))

    def lift_from(self, a, source):
        assert self.e == source.e and source.N <= self.N
        out = list(self.zero())
        for r, x in enumerate(a):
            out[r] = cast(x, self.widths[r])
        return tuple(out)

    def elements(self):
        return [tuple(BitVecVal(v, w) for v, w in zip(vals, self.widths))
                for vals in itertools.product(*[range(1 << w) for w in self.widths])]


class RamifiedThickening:
    """O_{2,N} + (O_{2,L})u with u^2=theta and pi^L u=0."""

    def __init__(self, N=4, L=2, theta_degree=None):
        if not (0 < L < N):
            raise ValueError("need 0 < L < N")
        if theta_degree is not None and (theta_degree >= N or L + theta_degree < N):
            raise ValueError("theta must be nonzero mod pi^N and annihilated by pi^L")
        self.N, self.L = N, L
        self.O = EisensteinDVR(2, N)
        self.M = EisensteinDVR(2, L)
        self.theta_degree = theta_degree
        self.theta = self.O.zero() if theta_degree is None else self.O.monomial(theta_degree)
        th = "0" if theta_degree is None else f"pi^{theta_degree}"
        self.name = f"Z_2[pi,u]/(pi^2-2,pi^{N},pi^{L}u,u^2-{th})"

    def zero(self):
        return self.O.zero(), self.M.zero()

    def one(self):
        return self.O.one(), self.M.zero()

    def var(self, tag):
        return self.O.var(tag + "o"), self.M.var(tag + "u")

    def add(self, x, y):
        return self.O.add(x[0], y[0]), self.M.add(x[1], y[1])

    def sub(self, x, y):
        return self.O.sub(x[0], y[0]), self.M.sub(x[1], y[1])

    def mul(self, x, y):
        a, b = x
        c, d = y
        ac = self.O.mul(a, c)
        if self.theta_degree is not None:
            bd = self.M.mul(b, d)
            ac = self.O.add(ac, self.O.mul(self.theta, self.O.lift_from(bd, self.M)))
        ad = self.M.mul(self.O.reduce_to(a, self.M), d)
        bc = self.M.mul(b, self.O.reduce_to(c, self.M))
        return ac, self.M.add(ad, bc)

    def eq0(self, x):
        return And(self.O.eq0(x[0]), self.M.eq0(x[1]))

    def neq0(self, x):
        return Or(self.O.neq0(x[0]), self.M.neq0(x[1]))

    def lowzero(self, x):
        return self.O.lowzero(x[0])

    def deform(self, tag):
        return self.O.deform(tag + "o"), self.M.var(tag + "u")

    def elements(self):
        return [(a, b) for a in self.O.elements() for b in self.M.elements()]


class PinCoproductResidue:
    """Proxy which fixes c_{ijk} modulo m and delegates all ring operations."""

    def __init__(self, ring, residue_c):
        self.R, self.residue_c = ring, residue_c
        self.name = ring.name + " [residue Delta pinned]"

    def __getattr__(self, key):
        return getattr(self.R, key)

    def var(self, tag):
        if len(tag) == 4 and tag[0] == "c" and tag[1:].isdigit():
            i, j, k = map(int, tag[1:])
            z = self.R.one() if self.residue_c.get((i, j, k), 0) else self.R.zero()
            return self.R.add(z, self.R.deform(tag))
        return self.R.var(tag)


# Basis 1,x,y,xy.  x is primitive; 1+y is the multiplicative coordinate.
XY_MULT = {(1, 2, 3): 1}
ALPHA2_MU2_DELTA = {
    (2, 2, 2): 1,
    (3, 1, 2): 1,
    (3, 2, 1): 1,
    (3, 3, 2): 1,
    (3, 2, 3): 1,
}


def validate(R):
    """Exhaustive ring axioms/locality/deformation-range checks."""
    from ringcheck import Tab, check_axioms, check_locality, ev

    els = R.elements()
    T = Tab(R, els)
    check_axioms(T, [ev(x) for x in els], triple_cap=24)
    nm, q, powers = check_locality(T, expect_residue_deg=1)

    pi = R.O.monomial(1), R.M.zero()
    u = R.O.zero(), R.M.one()
    pi2 = R.O.monomial(2), R.M.zero()
    piL = R.O.monomial(R.L), R.M.zero()
    assert ev(R.mul(pi, pi)) == ev(pi2)
    p = R.one()
    for _ in range(R.N):
        p = R.mul(p, pi)
    assert ev(p) == ev(R.zero())
    assert ev(R.mul(piL, u)) == ev(R.zero())
    assert ev(R.mul(u, u)) == ev((R.theta, R.M.zero()))
    print(f"VALIDATED {R.name}")
    print(f"  |R|={len(els)}, |m|={nm}, residue F_{q}, |m^k|={powers}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--N", type=int, default=4, help="truncate the ramified DVR at pi^N")
    ap.add_argument("--L", type=int, default=2, help="annihilator relation pi^L u=0")
    ap.add_argument("--theta", default="0", help="0, piK, or all admissible pi-powers")
    ap.add_argument("--validate", action="store_true")
    ap.add_argument("--unpin-delta", action="store_true")
    args = ap.parse_args()

    if args.theta == "all":
        degrees = [None] + list(range(max(2, args.N - args.L), args.N))
    elif args.theta == "0":
        degrees = [None]
    elif args.theta.startswith("pi") and args.theta[2:].isdigit():
        degrees = [int(args.theta[2:])]
    else:
        raise SystemExit("--theta must be 0, piK, or all")
    for degree in degrees:
        base = RamifiedThickening(args.N, args.L, degree)
        if args.validate:
            validate(base)
            continue
        R = base if args.unpin_delta else PinCoproductResidue(base, ALPHA2_MU2_DELTA)
        run(R, "alpha_2 x mu_2 (xy algebra)", XY_MULT, use_fiber2=True)


if __name__ == "__main__":
    main()
