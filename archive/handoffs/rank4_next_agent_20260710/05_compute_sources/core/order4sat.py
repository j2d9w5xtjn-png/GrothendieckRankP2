#!/usr/bin/env python3
"""
order4sat.py -- Ring-generic exact decision procedure for order-4
counterexamples to Grothendieck's "killed by the order" question, over the
small Artin local base rings where the question was open.

Base rings implemented (all local, length <= 3):
  * F2eps3  = F_2[eps]/(eps^3)           (equal char; cross-checks the M2 result)
  * Z8      = Z/8                        (mixed char, unramified)
  * Rram    = Z[pi]/(pi^2 - 2, pi^3)     (mixed char, ramified e=2, length 3;
                                          outside Schoof: m^2 != 0 there)
  * ext(R)  = R[w]/(w^2+w+1)             (residue field F_4 version of any R)

For each base ring R we ask: does there exist a free rank-4 bialgebra
(optionally Hopf) A over R, with special fiber the given local algebra shape
(F_q[x,y]/(x^2,y^2) or F_q[t]/t^4) and special fiber killed by 2, such that
[4]^# != 0?  UNSAT = no counterexample over that exact base ring.

Elements are tuples of Z3 bitvectors; all arithmetic is exact.
"""
from z3 import (BitVec, BitVecVal, Solver, Or, And, sat, unsat, set_param,
                Extract, ZeroExt)

FRESH = [0]
def fresh(tag):
    FRESH[0] += 1
    return f"{tag}__{FRESH[0]}"


class F2eps3:
    """F_2[eps]/eps^3: element = tuple of three 1-bit vectors (digits)."""
    name = "F2[eps]/eps^3"
    def zero(self): return (BitVecVal(0,1),)*3
    def one(self):  return (BitVecVal(1,1), BitVecVal(0,1), BitVecVal(0,1))
    def var(self, tag):
        n = fresh(tag)
        return tuple(BitVec(n+f"_{i}",1) for i in range(3))
    def add(self, a, b): return tuple(x ^ y for x, y in zip(a, b))
    def sub(self, a, b): return self.add(a, b)
    def mul(self, a, b):
        return (a[0]&b[0], (a[0]&b[1])^(a[1]&b[0]),
                (a[0]&b[2])^(a[1]&b[1])^(a[2]&b[0]))
    def eq0(self, a):  return And(*[x == 0 for x in a])
    def neq0(self, a): return Or(*[x != 0 for x in a])
    def lowzero(self, a): return a[0] == 0           # a in m = (eps)
    def deform(self, tag):                            # generic element of m
        v = self.var(tag)
        return (BitVecVal(0,1), v[0], v[1])


class Z8:
    """Z/8: element = one 3-bit vector."""
    name = "Z/8"
    def zero(self): return BitVecVal(0,3)
    def one(self):  return BitVecVal(1,3)
    def var(self, tag): return BitVec(fresh(tag), 3)
    def add(self, a, b): return a + b
    def sub(self, a, b): return a - b
    def mul(self, a, b): return a * b
    def eq0(self, a):  return a == 0
    def neq0(self, a): return a != 0
    def lowzero(self, a): return (a & 1) == 0        # a in m = (2)
    def deform(self, tag): return 2 * self.var(tag)


class Rram:
    """Z[pi]/(pi^2-2, pi^3): elements a + b*pi, a in Z/4, b in Z/2.
    (pi^3 = 2*pi = 0, pi^2 = 2, 4 = 0.)"""
    name = "Z[pi]/(pi^2-2,pi^3)"
    def zero(self): return (BitVecVal(0,2), BitVecVal(0,1))
    def one(self):  return (BitVecVal(1,2), BitVecVal(0,1))
    def var(self, tag):
        n = fresh(tag)
        return (BitVec(n+"_a",2), BitVec(n+"_b",1))
    def add(self, x, y): return (x[0]+y[0], x[1]^y[1])
    def sub(self, x, y): return (x[0]-y[0], x[1]^y[1])
    def mul(self, x, y):
        a, b = x; c, d = y
        # (a+b pi)(c+d pi) = ac + 2bd + (ad+bc) pi ;  2bd computed in Z/4,
        # ad+bc in Z/2 (2pi = 0 kills carries into pi-component)
        ac = a*c
        bd = ZeroExt(1, b & d)          # 0 or 1 in Z/4
        newa = ac + 2*bd
        newb = (Extract(0,0,a) & d) ^ (b & Extract(0,0,c))
        return (newa, newb)
    def eq0(self, x):  return And(x[0] == 0, x[1] == 0)
    def neq0(self, x): return Or(x[0] != 0, x[1] != 0)
    def lowzero(self, x): return (x[0] & 1) == 0     # m = (pi) = {even + b pi}
    def deform(self, tag):
        # pi * (a + b pi) = 2b + a pi  -> generic element of m
        v = self.var(tag)
        return (2*ZeroExt(1, v[1]), Extract(0,0,v[0]))


class Ext:
    """R[w]/(w^2+w+1): quadratic unramified extension (residue field F_4)."""
    def __init__(self, base):
        self.R = base
        self.name = base.name + "[w]/(w^2+w+1)"
    def zero(self): return (self.R.zero(), self.R.zero())
    def one(self):  return (self.R.one(),  self.R.zero())
    def var(self, tag): return (self.R.var(tag+"u"), self.R.var(tag+"v"))
    def add(self, x, y): return (self.R.add(x[0],y[0]), self.R.add(x[1],y[1]))
    def sub(self, x, y): return (self.R.sub(x[0],y[0]), self.R.sub(x[1],y[1]))
    def mul(self, x, y):
        u1, v1 = x; u2, v2 = y
        R = self.R
        a = R.mul(u1,u2); b = R.mul(v1,v2)
        m = R.add(R.mul(u1,v2), R.mul(u2,v1))
        # (u1+v1 w)(u2+v2 w) = u1u2 - v1v2 + (u1v2+u2v1-v1v2) w
        return (R.sub(a,b), R.sub(m,b))
    def eq0(self, x):  return And(self.R.eq0(x[0]), self.R.eq0(x[1]))
    def neq0(self, x): return Or(self.R.neq0(x[0]), self.R.neq0(x[1]))
    def lowzero(self, x): return And(self.R.lowzero(x[0]), self.R.lowzero(x[1]))
    def deform(self, tag): return (self.R.deform(tag+"u"), self.R.deform(tag+"v"))


def build(R, fib, with_antipode):
    Z, One = R.zero(), R.one()
    add, mul, sub = R.add, R.mul, R.sub

    c = {(i,j,k): R.var(f"c{i}{j}{k}")
         for i in range(1,4) for j in range(1,4) for k in range(1,4)}
    Mtab = {}
    for i in range(1,4):
        for j in range(i,4):
            for r in range(1,4):
                base = One if fib.get((i,j,r),0) else Z
                Mtab[(i,j,r)] = add(base, R.deform(f"d{i}{j}{r}"))
    def M(i,j,r):
        ii, jj = min(i,j), max(i,j)
        return Mtab[(ii,jj,r)]
    def ebas(i): return [One if t==i else Z for t in range(4)]

    S = [[None]*4 for _ in range(4)]
    for a in range(4):
        for b in range(4):
            if a==0: S[a][b] = ebas(b)
            elif b==0: S[a][b] = ebas(a)
            else: S[a][b] = [Z, M(a,b,1), M(a,b,2), M(a,b,3)]

    def mulA(u,v):
        out = [Z]*4
        for i in range(4):
            for j in range(4):
                co = mul(u[i], v[j])
                for r in range(4):
                    out[r] = add(out[r], mul(co, S[i][j][r]))
        return out

    idx2 = lambda a,b: 4*a+b
    idx3 = lambda a,b,cc: 16*a+4*b+cc

    DE = [[One if t==0 else Z for t in range(16)]]
    for i in range(1,4):
        v = [Z]*16
        v[idx2(i,0)] = add(v[idx2(i,0)], One)
        v[idx2(0,i)] = add(v[idx2(0,i)], One)
        for j in range(1,4):
            for k in range(1,4):
                v[idx2(j,k)] = add(v[idx2(j,k)], c[(i,j,k)])
        DE.append(v)

    eqs = []
    # associativity
    for i in range(1,4):
        for j in range(1,4):
            for k in range(1,4):
                u = mulA(mulA(ebas(i),ebas(j)),ebas(k))
                w = mulA(ebas(i),mulA(ebas(j),ebas(k)))
                eqs += [sub(u[t],w[t]) for t in range(4)]
    # Delta multiplicative
    def DofVec(v4):
        out = [Z]*16
        for r in range(4):
            for t in range(16):
                out[t] = add(out[t], mul(v4[r], DE[r][t]))
        return out
    def mulT2(u,v):
        out = [Z]*16
        for a in range(4):
            for b in range(4):
                for a2 in range(4):
                    for b2 in range(4):
                        co = mul(u[idx2(a,b)], v[idx2(a2,b2)])
                        for k in range(4):
                            t1 = mul(co, S[a][a2][k])
                            for l in range(4):
                                out[idx2(k,l)] = add(out[idx2(k,l)],
                                                     mul(t1, S[b][b2][l]))
        return out
    for i in range(1,4):
        for j in range(i,4):
            lhs = DofVec(S[i][j]); rhs = mulT2(DE[i], DE[j])
            eqs += [sub(lhs[t],rhs[t]) for t in range(16)]
    # coassociativity
    for i in range(1,4):
        out = [Z]*64
        for r in range(4):
            for s in range(4):
                u = DE[i][idx2(r,s)]
                for a in range(4):
                    for b in range(4):
                        out[idx3(a,b,s)] = add(out[idx3(a,b,s)],
                                               mul(u, DE[r][idx2(a,b)]))
                for b in range(4):
                    for cc in range(4):
                        out[idx3(r,b,cc)] = sub(out[idx3(r,b,cc)],
                                                mul(u, DE[s][idx2(b,cc)]))
        eqs += out

    # phi = [2]^#, P4 = [4]^#
    phi = [ebas(0)]
    for i in range(1,4):
        out = [Z]*4
        for j in range(4):
            for k in range(4):
                co = DE[i][idx2(j,k)]
                for r in range(4):
                    out[r] = add(out[r], mul(co, S[j][k][r]))
        phi.append(out)
    P4 = []
    for i in range(1,4):
        out = [Z]*4
        for r in range(4):
            for t in range(4):
                out[t] = add(out[t], mul(phi[i][r], phi[r][t]))
        P4.append(out)

    fiber2 = [R.lowzero(phi[i][r]) for i in range(1,4) for r in range(4)]

    anti = []
    if with_antipode:
        svar = {(i,r): R.var(f"s{i}{r}") for i in range(1,4) for r in range(1,4)}
        SL = [ebas(0)] + [[Z]+[svar[(i,r)] for r in range(1,4)] for i in range(1,4)]
        def SofVec(v4):
            out = [Z]*4
            for r in range(4):
                for t in range(4):
                    out[t] = add(out[t], mul(v4[r], SL[r][t]))
            return out
        for i in range(1,4):
            for j in range(i,4):
                lhs = SofVec(S[i][j]); rhs = mulA(SL[i],SL[j])
                anti += [R.eq0(sub(lhs[t],rhs[t])) for t in range(4)]
        for i in range(1,4):
            out1, out2 = [Z]*4, [Z]*4
            for j in range(4):
                for k in range(4):
                    co = DE[i][idx2(j,k)]
                    u1 = mulA(SL[j], ebas(k)); u2 = mulA(ebas(j), SL[k])
                    for t in range(4):
                        out1[t] = add(out1[t], mul(co,u1[t]))
                        out2[t] = add(out2[t], mul(co,u2[t]))
            anti += [R.eq0(out1[t]) for t in range(4)]
            anti += [R.eq0(out2[t]) for t in range(4)]

    ncc = Or(*[R.neq0(sub(c[(i,j,k)], c[(i,k,j)]))
               for i in range(1,4) for j in range(1,4) for k in range(1,4) if j<k])
    p4nz = Or(*[R.neq0(P4[i][t]) for i in range(3) for t in range(4)])
    base = [R.eq0(e) for e in eqs] + fiber2
    return base, anti, p4nz, ncc


def run(R, fibname, fib, use_fiber2=True):
    print(f"===== base {R.name}, fiber {fibname}, fiber2={use_fiber2} =====", flush=True)
    base, anti, p4nz, ncc = build(R, fib, with_antipode=True)
    if not use_fiber2:
        nb = len([1 for i in range(1,4) for r in range(4)])
        base = base[:-nb]     # drop the fiber2 constraints (appended last)
    def check(label, extra):
        s = Solver()
        s.set("timeout", 7200*1000)
        for a in base: s.add(a)
        for a in extra: s.add(a)
        res = s.check()
        print(f"  [{label}] -> {res}", flush=True)
        if res == sat and extra:
            m = s.model()
            nz = sorted((str(d), m[d].as_long()) for d in m.decls()
                        if m[d].as_long() != 0)
            print(f"    nonzero: {nz}", flush=True)
        return res
    r1 = check("1: bialgebra(+fiber2) sanity (expect sat)", [])
    r2 = check("2: + [4]^# != 0", [p4nz])
    if r2 == sat:
        check("3: + antipode", [p4nz] + anti)
        check("4: + antipode + noncocomm", [p4nz, ncc] + anti)


if __name__ == "__main__":
    import sys
    set_param("parallel.enable", True)
    nofib = "--nofiber2" in sys.argv
    fibs = [("F_q[x,y]/(x^2,y^2)", {(1,2,3):1}),
            ("F_q[t]/t^4", {(1,1,2):1, (1,2,3):1})]
    if nofib:
        rings = [F2eps3(), Z8(), Rram(), Ext(F2eps3()), Ext(Z8()), Ext(Rram())]
        for R in rings:
            for fn, fib in fibs:
                run(R, fn, fib, use_fiber2=False)
    else:
        rings = [F2eps3(), Rram(), Ext(F2eps3()), Ext(Z8()), Ext(Rram())]
        for R in rings:
            for fn, fib in fibs:
                run(R, fn, fib)
    print("DONE order4sat", flush=True)
