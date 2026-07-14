#!/usr/bin/env python3
"""
order4sat_beyond.py -- push the order-4 search to deeper/wider Artin local bases:

  equal char, principal m:      F_2[eps]/eps^N, N = 4, 5, 6
  equal char, NON-principal m:  F_2[x,y]/(x,y)^3   (length 6, m^2 != 0 -- outside
                                 all known results and outside the curvilinear class)
                                F_2[x,y]/(x^2,y^2) (length 4, non-curvilinear)
  mixed char, unramified:       Z/16, Z/32
  mixed char, ramified:         Z[pi]/(pi^2-2, pi^4)  (length 4)
  residue field F_4:            quadratic unramified extensions of a few of the above

For each: does a free rank-4 bialgebra with local fiber shape, fiber killed by 2,
and [4]^# != 0 exist?  (UNSAT = no counterexample over that exact ring.)
"""
from z3 import BitVec, BitVecVal, ZeroExt, Extract, And, Or, set_param
from order4sat import Ext, build, run, fresh


class F2Quot:
    """Quotient F_2-algebra with basis e_0 = 1, e_1..e_{n-1} spanning m,
    given by a multiplication table mt[(i,j)] = list of basis indices in e_i e_j."""
    def __init__(self, name, n, mt):
        self.name, self.n = name, n
        self.T = {}
        for i in range(n):
            for j in range(n):
                if i == 0: prods = [j]
                elif j == 0: prods = [i]
                else: prods = mt.get((min(i,j), max(i,j)), [])
                self.T[(i,j)] = prods
    def zero(self): return tuple(BitVecVal(0,1) for _ in range(self.n))
    def one(self):  return tuple(BitVecVal(1 if i==0 else 0,1) for i in range(self.n))
    def var(self, tag):
        nm = fresh(tag)
        return tuple(BitVec(nm+f"_{i}",1) for i in range(self.n))
    def add(self, a, b): return tuple(x ^ y for x,y in zip(a,b))
    def sub(self, a, b): return self.add(a,b)
    def mul(self, a, b):
        out = [BitVecVal(0,1)]*self.n
        for i in range(self.n):
            for j in range(self.n):
                t = a[i] & b[j]
                for k in self.T[(i,j)]:
                    out[k] = out[k] ^ t
        return tuple(out)
    def eq0(self, a):  return And(*[x == 0 for x in a])
    def neq0(self, a): return Or(*[x != 0 for x in a])
    def lowzero(self, a): return a[0] == 0
    def deform(self, tag):
        v = self.var(tag)
        return (BitVecVal(0,1),) + v[1:]


def F2epsN(N):
    mt = {(i,j): ([i+j] if i+j < N else []) for i in range(1,N) for j in range(i,N)}
    return F2Quot(f"F2[eps]/eps^{N}", N, mt)

# F2[x,y]/(x,y)^3 : basis 1, x, y, x^2, xy, y^2
FatPoint3 = F2Quot("F2[x,y]/(x,y)^3", 6,
    {(1,1):[3], (1,2):[4], (2,2):[5],
     (1,3):[], (1,4):[], (1,5):[], (2,3):[], (2,4):[], (2,5):[],
     (3,3):[], (3,4):[], (3,5):[], (4,4):[], (4,5):[], (5,5):[]})

# F2[x,y]/(x^2,y^2) : basis 1, x, y, xy
BiDual = F2Quot("F2[x,y]/(x^2,y^2)", 4,
    {(1,1):[], (1,2):[3], (2,2):[], (1,3):[], (2,3):[], (3,3):[]})

# F2[u,v]/(u,v)^2 : basis 1, u, v  (square-zero m, embdim 2; session 13 --
# Theorem N gates in s5gates.py; ringcheck CASES entry added same session)
FatPoint2 = F2Quot("F2[u,v]/(u,v)^2", 3,
    {(1,1):[], (1,2):[], (2,2):[]})


class Z2N:
    def __init__(self, N):
        self.N = N; self.name = f"Z/{2**N}"
    def zero(self): return BitVecVal(0,self.N)
    def one(self):  return BitVecVal(1,self.N)
    def var(self, tag): return BitVec(fresh(tag), self.N)
    def add(self, a, b): return a + b
    def sub(self, a, b): return a - b
    def mul(self, a, b): return a * b
    def eq0(self, a):  return a == 0
    def neq0(self, a): return a != 0
    def lowzero(self, a): return (a & 1) == 0
    def deform(self, tag): return 2*self.var(tag)


class Rram4:
    """Z[pi]/(pi^2-2, pi^4): elements a + b pi with a, b in Z/4 (pi^4 = 4 = 0)."""
    name = "Z[pi]/(pi^2-2,pi^4)"
    def zero(self): return (BitVecVal(0,2), BitVecVal(0,2))
    def one(self):  return (BitVecVal(1,2), BitVecVal(0,2))
    def var(self, tag):
        n = fresh(tag)
        return (BitVec(n+"_a",2), BitVec(n+"_b",2))
    def add(self, x, y): return (x[0]+y[0], x[1]+y[1])
    def sub(self, x, y): return (x[0]-y[0], x[1]-y[1])
    def mul(self, x, y):
        a,b = x; c,d = y
        return (a*c + 2*(b*d), a*d + b*c)
    def eq0(self, x):  return And(x[0]==0, x[1]==0)
    def neq0(self, x): return Or(x[0]!=0, x[1]!=0)
    def lowzero(self, x): return (x[0] & 1) == 0
    def deform(self, tag):
        v = self.var(tag)                    # pi*(a+b pi) = 2b + a pi
        return (2*v[1], v[0])


if __name__ == "__main__":
    set_param("parallel.enable", True)
    fibs = [("F_q[x,y]/(x^2,y^2)", {(1,2,3):1}),
            ("F_q[t]/t^4", {(1,1,2):1, (1,2,3):1})]
    # Sessions 6-7 completed (all UNSAT, see log): eps^4..eps^6, BiDual,
    # FatPoint3, Z/16, Z/32, Z[pi]/(pi^2-2,pi^4), all fiber2=True, both fibers.
    # Session 8 restart: the process died mid-solve on F4[eps]/eps^4 xy.
    # Resume there.  Ext(FatPoint3) (4096 elements, slowest) is moved LAST:
    # its equal-char m^3=0 content is now implied by THEORY section 12
    # (first-order symbol theorem + polarization), so it is audit-only.
    jobs = []
    for R in [Ext(F2epsN(4)), Ext(Z2N(4))]:
        for fp in fibs:
            jobs.append((R, fp))
    for R, (fn, fib) in jobs:
        run(R, fn, fib, use_fiber2=True)
    # without the fiber condition on the most important new ones
    for R in [F2epsN(4), FatPoint3, BiDual, Z2N(4), Rram4()]:
        for fn, fib in fibs:
            run(R, fn, fib, use_fiber2=False)
    # audit-only tail (subsumed by THEORY section 12 once its gates passed)
    for fn, fib in fibs:
        run(Ext(FatPoint3), fn, fib, use_fiber2=True)
    print("DONE order4sat_beyond", flush=True)
