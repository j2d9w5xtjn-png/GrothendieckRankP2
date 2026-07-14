#!/usr/bin/env python3
"""Residue field F_8 = F_2[w]/(w^3+w+1): cubic unramified extensions.
Covers W(F_8)/8 and F_8[eps]/eps^3."""
from z3 import And, Or, set_param
from order4sat import Z8, F2eps3, build, run


class Ext3:
    """R[w]/(w^3 - w - 1): the unramified cubic extension of R.

    The reduction below uses w^3 = w + 1 (all `add`, no sign), i.e. the relation
    w^3 - w - 1 = 0.  Over a characteristic-2 base that polynomial *is* w^3+w+1;
    over Z/8 it is a different monic lift of it.  Either way the reduction mod
    m_R is w^3+w+1, which is irreducible over F_2, so R[w]/(w^3-w-1) is free of
    rank 3, local, with residue field F_8 -- and the unramified cubic extension
    is unique up to isomorphism, so this ring is W(F_8)/8 when R = Z/8.
    (Machine-verified: see `ringcheck.py`, which recomputes the minimal
    polynomial of w and certifies its reduction mod m is irreducible.)
    """
    def __init__(self, base):
        self.R = base
        self.name = base.name + "[w]/(w^3-w-1)"
    def zero(self): return (self.R.zero(),)*3
    def one(self):  return (self.R.one(), self.R.zero(), self.R.zero())
    def var(self, tag): return tuple(self.R.var(tag+f"e{i}") for i in range(3))
    def add(self, x, y): return tuple(self.R.add(a,b) for a,b in zip(x,y))
    def sub(self, x, y): return tuple(self.R.sub(a,b) for a,b in zip(x,y))
    def mul(self, x, y):
        R = self.R
        u1,v1,z1 = x; u2,v2,z2 = y
        s = R.add(R.mul(v1,z2), R.mul(z1,v2))
        t = R.mul(z1,z2)
        c0 = R.add(R.mul(u1,u2), s)
        c1 = R.add(R.add(R.add(R.mul(u1,v2), R.mul(v1,u2)), s), t)
        c2 = R.add(R.add(R.add(R.mul(u1,z2), R.mul(v1,v2)), R.mul(z1,u2)), t)
        return (c0, c1, c2)
    def eq0(self, x):  return And(*[self.R.eq0(a) for a in x])
    def neq0(self, x): return Or(*[self.R.neq0(a) for a in x])
    def lowzero(self, x): return And(*[self.R.lowzero(a) for a in x])
    def deform(self, tag): return tuple(self.R.deform(tag+f"e{i}") for i in range(3))


if __name__ == "__main__":
    set_param("parallel.enable", True)
    fibs = [("F_q[x,y]/(x^2,y^2)", {(1,2,3):1}),
            ("F_q[t]/t^4", {(1,1,2):1, (1,2,3):1})]
    # sanity of the extension arithmetic: (w)(w)(w) = w+1 in F_8 checked implicitly
    for R in [Ext3(Z8()), Ext3(F2eps3())]:
        for fn, fib in fibs:
            run(R, fn, fib, use_fiber2=True)
    print("DONE order4sat_f8", flush=True)
