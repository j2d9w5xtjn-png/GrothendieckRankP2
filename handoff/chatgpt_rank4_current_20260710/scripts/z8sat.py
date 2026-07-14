#!/usr/bin/env python3
"""
z8sat.py -- Exact decision procedure for order-4 counterexamples over R = Z/8Z.

Every structure constant is a Z3 bitvector of width 3 (= element of Z/8);
all Hopf-algebra equations are exact mod-8 bitvector arithmetic. This decides
(for the base ring Z/8 itself, residue field F_2):

  Does there exist a free rank-4 Hopf algebra A over Z/8 whose special fiber
  is the given local F_2-algebra, with special fiber killed by 2, such that
  [4]^# != 0 ?

Layers of conditions (each run reports SAT/UNSAT):
  (1) bialgebra + fiber killed by 2                        [sanity: SAT expected]
  (2) (1) + [4]^# != 0                                     [counterexample, bialgebra level]
  (3) (2) + antipode exists                                [counterexample, Hopf level]
  (4) (3) + noncocommutative                               [handoff's target branch]

Conventions as in z8search.m2:
  A = R.1 + R.e1 + R.e2 + R.e3,  e_i e_j = sum_r M_(i,j,r) e_r,
  M_(i,j,r) = fib_(i,j,r) + 2*d_(i,j,r)  (fiber = standard algebra),
  Delta(e_i) = e_i x 1 + 1 x e_i + sum_{j,k>=1} c_(i,j,k) e_j x e_k,
  phi = [2]^# = mu o Delta,  P4_i = phi(phi(e_i)).
"""
import sys
from z3 import (BitVec, BitVecVal, Solver, Or, And, sat, unsat, set_param)

W = 3  # bit width: arithmetic mod 8


def build(fib, with_antipode):
    Z = BitVecVal(0, W)
    One = BitVecVal(1, W)

    c = {(i, j, k): BitVec(f"c_{i}_{j}_{k}", W)
         for i in range(1, 4) for j in range(1, 4) for k in range(1, 4)}
    dvar = {(i, j, r): BitVec(f"d_{i}_{j}_{r}", W)
            for i in range(1, 4) for j in range(i, 4) for r in range(1, 4)}

    def M(i, j, r):
        ii, jj = min(i, j), max(i, j)
        base = One if fib.get((ii, jj, r), 0) else Z
        return base + 2 * dvar[(ii, jj, r)]

    def ebas(i):
        return [One if t == i else Z for t in range(4)]

    # product table S[a][b] = 4-vector of e_a * e_b
    S = [[None] * 4 for _ in range(4)]
    for a in range(4):
        for b in range(4):
            if a == 0:
                S[a][b] = ebas(b)
            elif b == 0:
                S[a][b] = ebas(a)
            else:
                S[a][b] = [Z, M(a, b, 1), M(a, b, 2), M(a, b, 3)]

    def mulA(u, v):
        out = [Z, Z, Z, Z]
        for i in range(4):
            for j in range(4):
                for r in range(4):
                    out[r] = out[r] + u[i] * v[j] * S[i][j][r]
        return out

    idx2 = lambda a, b: 4 * a + b
    idx3 = lambda a, b, cc: 16 * a + 4 * b + cc

    # Delta images
    DE = []
    DE.append([One if t == 0 else Z for t in range(16)])
    for i in range(1, 4):
        v = [Z] * 16
        v[idx2(i, 0)] = v[idx2(i, 0)] + One
        v[idx2(0, i)] = v[idx2(0, i)] + One
        for j in range(1, 4):
            for k in range(1, 4):
                v[idx2(j, k)] = v[idx2(j, k)] + c[(i, j, k)]
        DE.append(v)

    eqs = []  # bitvector expressions required to be 0 mod 8

    # associativity
    for i in range(1, 4):
        for j in range(1, 4):
            for k in range(1, 4):
                u = mulA(mulA(ebas(i), ebas(j)), ebas(k))
                w = mulA(ebas(i), mulA(ebas(j), ebas(k)))
                eqs += [u[t] - w[t] for t in range(4)]

    def DofVec(v4):
        out = [Z] * 16
        for r in range(4):
            for t in range(16):
                out[t] = out[t] + v4[r] * DE[r][t]
        return out

    def mulT2(u, v):
        out = [Z] * 16
        for a in range(4):
            for b in range(4):
                for a2 in range(4):
                    for b2 in range(4):
                        co = u[idx2(a, b)] * v[idx2(a2, b2)]
                        SA, SB = S[a][a2], S[b][b2]
                        for k in range(4):
                            for l in range(4):
                                out[idx2(k, l)] = out[idx2(k, l)] + co * SA[k] * SB[l]
        return out

    # Delta multiplicative
    for i in range(1, 4):
        for j in range(i, 4):
            lhs = DofVec(S[i][j])
            rhs = mulT2(DE[i], DE[j])
            eqs += [lhs[t] - rhs[t] for t in range(16)]

    # coassociativity
    for i in range(1, 4):
        out = [Z] * 64
        for r in range(4):
            for s in range(4):
                u = DE[i][idx2(r, s)]
                for a in range(4):
                    for b in range(4):
                        out[idx3(a, b, s)] = out[idx3(a, b, s)] + u * DE[r][idx2(a, b)]
                for b in range(4):
                    for cc in range(4):
                        out[idx3(r, b, cc)] = out[idx3(r, b, cc)] - u * DE[s][idx2(b, cc)]
        eqs += out

    # phi and P4
    phi = [ebas(0)]
    for i in range(1, 4):
        out = [Z] * 4
        for j in range(4):
            for k in range(4):
                co = DE[i][idx2(j, k)]
                for r in range(4):
                    out[r] = out[r] + co * S[j][k][r]
        phi.append(out)
    P4 = []
    for i in range(1, 4):
        out = [Z] * 4
        for r in range(4):
            for t in range(4):
                out[t] = out[t] + phi[i][r] * phi[r][t]
        P4.append(out)

    # fiber killed by 2: phi(e_i) == 0 mod 2  (low bit of each coordinate is 0)
    fiber2 = []
    for i in range(1, 4):
        for r in range(4):
            fiber2.append((phi[i][r] & 1) == 0)

    # antipode (optional): S(e_i) = sum_r s_(i,r) e_r, algebra map + convolution ids
    anti = []
    if with_antipode:
        svar = {(i, r): BitVec(f"s_{i}_{r}", W)
                for i in range(1, 4) for r in range(1, 4)}
        SL = [ebas(0)] + [[Z] + [svar[(i, r)] for r in range(1, 4)] for i in range(1, 4)]

        def SofVec(v4):
            out = [Z] * 4
            for r in range(4):
                for t in range(4):
                    out[t] = out[t] + v4[r] * SL[r][t]
            return out

        for i in range(1, 4):
            for j in range(i, 4):
                lhs = SofVec(S[i][j])
                rhs = mulA(SL[i], SL[j])
                anti += [lhs[t] == rhs[t] for t in range(4)]
        for i in range(1, 4):
            out1, out2 = [Z] * 4, [Z] * 4
            for j in range(4):
                for k in range(4):
                    co = DE[i][idx2(j, k)]
                    u1 = mulA(SL[j], ebas(k))
                    u2 = mulA(ebas(j), SL[k])
                    for t in range(4):
                        out1[t] = out1[t] + co * u1[t]
                        out2[t] = out2[t] + co * u2[t]
            anti += [out1[t] == 0 for t in range(4)]
            anti += [out2[t] == 0 for t in range(4)]

    # noncocommutativity: some c_(i,j,k) != c_(i,k,j)
    noncocomm = Or([c[(i, j, k)] != c[(i, k, j)]
                    for i in range(1, 4) for j in range(1, 4) for k in range(1, 4) if j < k])

    p4nonzero = Or([P4[i][t] != 0 for i in range(3) for t in range(4)])

    base = [e == 0 for e in eqs] + fiber2
    return base, anti, p4nonzero, noncocomm


def run(fibname, fib):
    print(f"===== Z/8, fiber {fibname} =====", flush=True)
    base, anti, p4nz, ncc = build(fib, with_antipode=True)

    def check(label, extra):
        s = Solver()
        s.set("timeout", 3600 * 1000)
        for a in base:
            s.add(a)
        for a in extra:
            s.add(a)
        res = s.check()
        print(f"  [{label}] -> {res}", flush=True)
        if res == sat:
            m = s.model()
            vals = sorted((str(d), m[d].as_long()) for d in m.decls())
            nz = [(n, v) for (n, v) in vals if v != 0]
            print(f"    nonzero assignments: {nz}", flush=True)
        return res

    check("1: bialgebra + fiber2 (sanity, expect sat)", [])
    check("2: + [4]^# != 0 (bialgebra counterexample?)", [p4nz])
    check("3: + antipode (Hopf counterexample?)", [p4nz] + anti)
    check("4: + noncocommutative", [p4nz, ncc] + anti)


if __name__ == "__main__":
    set_param("parallel.enable", True)
    run("F2[x,y]/(x^2,y^2)", {(1, 2, 3): 1})
    run("F2[t]/(t^4)", {(1, 1, 2): 1, (1, 2, 3): 1})
    print("DONE z8sat", flush=True)
