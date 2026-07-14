#!/usr/bin/env python3
"""
ablate.py -- Axiom-ablation experiment over F_2[eps]/eps^3 (session 3).

Purpose (theory-guiding, not theorem-producing): the M2/SAT results show that
the bialgebra axioms + "fiber killed by 2" force [4]^# = 0 at length 3.  A
human proof of the underlying identity ("psi^2 = 0", see THEORY_order4.md)
must use *some* of the axioms.  This script determines WHICH axiom blocks are
load-bearing, by dropping one block at a time and asking Z3 whether
[4]^# != 0 becomes satisfiable.

  block A = associativity of the deformed multiplication
  block M = Delta multiplicative (compatibility)
  block C = coassociativity
  block F = fiber killed by 2

Queries (per fiber shape), over the ringcheck-validated F2eps3 class:
  gate0:  A+M+C+F                 -> expect sat   (mu_2 x mu_2 exists)
  gate1:  A+M+C+F + [4]^# != 0    -> expect unsat (reproduces Theorem B; if
                                     this fails, the block bookkeeping is
                                     wrong -- STOP)
  ablC:   A+M  +F + [4]^# != 0    -> ? (is coassociativity needed?)
  ablM:   A+C  +F + [4]^# != 0    -> ? (is Delta-multiplicativity needed?)
  ablA:   M+C  +F + [4]^# != 0    -> ? (is associativity needed?)

A `sat` on an ablation line means: that axiom is essential -- there is a
"pseudo-bialgebra" violating only it and having [4]^# != 0.  The model is
printed (it is NOT a counterexample to anything; it fails the dropped axiom).

The ring class F2eps3 is copied verbatim from order4sat.py (validated by
ringcheck.py).  The equation builder is the same code as order4sat.build()
with the single change that the three equation blocks are returned separately.
"""
from z3 import BitVec, BitVecVal, Solver, Or, And, sat, unsat, set_param

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


def build_blocks(R, fib):
    """Same construction as order4sat.build(), but the equation blocks
    (associativity / Delta-multiplicativity / coassociativity) are returned
    separately, along with the fiber2 constraints and the [4]^# != 0 witness."""
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

    # --- block A: associativity ---
    eqsA = []
    for i in range(1,4):
        for j in range(1,4):
            for k in range(1,4):
                u = mulA(mulA(ebas(i),ebas(j)),ebas(k))
                w = mulA(ebas(i),mulA(ebas(j),ebas(k)))
                eqsA += [sub(u[t],w[t]) for t in range(4)]

    # --- block M: Delta multiplicative ---
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
    eqsM = []
    for i in range(1,4):
        for j in range(i,4):
            lhs = DofVec(S[i][j]); rhs = mulT2(DE[i], DE[j])
            eqsM += [sub(lhs[t],rhs[t]) for t in range(16)]

    # --- block C: coassociativity ---
    eqsC = []
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
        eqsC += out

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
    p4nz = Or(*[R.neq0(P4[i][t]) for i in range(3) for t in range(4)])

    A = [R.eq0(e) for e in eqsA]
    Mb = [R.eq0(e) for e in eqsM]
    C = [R.eq0(e) for e in eqsC]
    return A, Mb, C, fiber2, p4nz


def check(label, constraints, expect=None):
    s = Solver()
    s.set("timeout", 7200*1000)
    for a in constraints: s.add(a)
    res = s.check()
    tag = ""
    if expect is not None:
        tag = "  [GATE OK]" if str(res) == expect else f"  [GATE FAILED: expected {expect} -- STOP, bookkeeping wrong]"
    print(f"  [{label}] -> {res}{tag}", flush=True)
    if res == sat and expect is None:
        m = s.model()
        nz = sorted((str(d), m[d].as_long()) for d in m.decls()
                    if m[d].as_long() != 0)
        print(f"    nonzero (pseudo-bialgebra witness, NOT a counterexample): {nz}",
              flush=True)
    return res


if __name__ == "__main__":
    set_param("parallel.enable", True)
    R = F2eps3()
    fibs = [("F_q[x,y]/(x^2,y^2)", {(1,2,3):1}),
            ("F_q[t]/t^4", {(1,1,2):1, (1,2,3):1})]
    for fn, fib in fibs:
        print(f"===== base {R.name}, fiber {fn} =====", flush=True)
        A, Mb, C, F, p4nz = build_blocks(R, fib)
        check("gate0: A+M+C+F sanity", A+Mb+C+F, expect="sat")
        check("gate1: A+M+C+F + [4]!=0", A+Mb+C+F+[p4nz], expect="unsat")
        check("ablC : A+M+F   + [4]!=0 (coassoc dropped)", A+Mb+F+[p4nz])
        check("ablM : A+C+F   + [4]!=0 (Delta-mult dropped)", A+C+F+[p4nz])
        check("ablA : M+C+F   + [4]!=0 (assoc dropped)", Mb+C+F+[p4nz])
        check("ablF : A+M+C   + [4]!=0 (fiber2 dropped; = B' base, known unsat)",
              A+Mb+C+[p4nz], expect="unsat")
    print("DONE ablate", flush=True)
