#!/usr/bin/env python3
"""rank16_leading_z3.py — HONEST full-axiom test of the leading rank-16
obstruction  Psi_1^4 = 0  (and Psi_1^2, Psi_1^3) for arbitrary rank-16
killed-by-2 monomial fibers, incl. the length-4 ALTERNATING ZIGZAGS.

WHY.  The linear cotangent scanners (ours: rank16_altzigzag_firstorder.py;
ChatGPT's: hopf_firstorder_scanner.py) can only produce the generator-entry
block L of Psi_1 and then take MATRIX powers.  That is unsound:

    L^k (matrix) = Psi_1^k mod I^2   ONLY IF  Psi_1(I^2) subset I^2,

which FAILS because Psi_1 = mu_0.Delta_1 + mu_1.Delta_0 contains the Hochschild
cochain mu_1, which lowers degree (mu_1(a^2,a^2) = a).  Composing Psi_1 with
itself is BILINEAR in the unknowns, so no linear scanner can decide it.  That is
how ChatGPT's rank-16 "quartic seed" (idempotent L, single_power_nonzero[4])
arose: the entry matrix is genuinely realizable, but its power is a mirage.

This script does the honest thing: it builds the FULL first-order bialgebra
deformation over F2[e]/e^2 (assoc + Delta-mult + coassoc, both mu and Delta
deformed) and asks Z3 whether the true composite Psi_1^K is nonzero -- both as a
full map on I and restricted to generator (degree-1) outputs, the latter being
the honest meaning of "L^K mod I^2".

Fibers are imported from rank16_altzigzag_firstorder.build_fiber (gates run
there: counit, coassoc, phi0 = 0), so the two tools always agree on the model.

Reading: Psi_1^4 != 0 `unsat` => leading rank-16 route DEAD for that fiber (over
F2; the equations are F2-linear-coefficiented but the query is bilinear, so this
is an exact-F2 statement, not an arbitrary-k' theorem).  `sat` => genuine
leading counterexample SEED; escalate to NE=3,4,5 lifts.

Run:  ~/.venvs/z3env/bin/python rank16_leading_z3.py [fiber ...] [--powers 1,2,3,4]
"""
import sys, time, itertools, argparse
from z3 import Solver, BitVec, BitVecVal, Or, set_param
from rank16_altzigzag_firstorder import build_fiber, gen_index

T0 = time.time()


def run(name, powers, timeout_ms):
    nm, caps, DIM, idx_of, exps_of, MUL, DELTA0_GEN = build_fiber(name)
    NE = 2                                     # first order: F2[e]/e^2
    I = list(range(1, DIM))
    G = [gen_index(caps, i) for i in range(len(caps))]
    GEN = set(G)

    def mul(a, b):
        m = MUL[a][b]
        return None if m < 0 else m
    def t2(a, b): return a * DIM + b
    def u2(i): return divmod(i, DIM)
    def t3(a, b, c): return (a * DIM + b) * DIM + c
    def band(x, y):
        if isinstance(x, int): return y if x else 0
        if isinstance(y, int): return x if y else 0
        return x & y
    def bnot(x):
        if isinstance(x, int): return 1 - x
        return x ^ BitVecVal(1, 1)
    def bxor(x, y):
        if isinstance(x, int): return y if x == 0 else bnot(y)
        if isinstance(y, int): return x if y == 0 else bnot(x)
        return x ^ y
    def isz(x): return isinstance(x, int) and x == 0

    # ---- Delta0 (constant bitsets over T2) ----
    def vmul_t2(u, v):
        out = 0; uu = u
        while uu:
            l = uu & -uu; i = l.bit_length() - 1; uu ^= l
            x, y = u2(i); vv = v
            while vv:
                l2 = vv & -vv; j = l2.bit_length() - 1; vv ^= l2
                p, q = u2(j); xp = mul(x, p); yq = mul(y, q)
                if xp is not None and yq is not None: out ^= 1 << t2(xp, yq)
        return out
    DG = {}
    for g, terms in DELTA0_GEN.items():
        v = 0
        for (p, q) in terms: v ^= 1 << t2(p, q)
        DG[g] = v
    def dmono(m):
        out = 1 << t2(0, 0)
        for slot, e in enumerate(exps_of(m)):
            g = gen_index(caps, slot)
            for _ in range(e): out = vmul_t2(out, DG[g])
        return out
    D0 = [dmono(m) for m in range(DIM)]
    # ---- fiber gates: counit, coassoc, phi0 = 0 (build_fiber does NOT gate) ----
    for m in range(DIM):
        left = right = 0; vv = D0[m]
        while vv:
            l = vv & -vv; i = l.bit_length() - 1; vv ^= l
            p, q = u2(i)
            if p == 0: left ^= 1 << q
            if q == 0: right ^= 1 << p
        assert left == (1 << m) and right == (1 << m), f'{nm}: counit FAIL at {exps_of(m)}'
    for m in range(DIM):
        lhs = rhs = 0; vv = D0[m]
        while vv:
            l = vv & -vv; i = l.bit_length() - 1; vv ^= l
            p, q = u2(i); dp = D0[p]
            while dp:
                l2 = dp & -dp; j = l2.bit_length() - 1; dp ^= l2
                p1, p2 = u2(j); lhs ^= 1 << t3(p1, p2, q)
            dq = D0[q]
            while dq:
                l2 = dq & -dq; j = l2.bit_length() - 1; dq ^= l2
                q1, q2 = u2(j); rhs ^= 1 << t3(p, q1, q2)
        assert lhs == rhs, f'{nm}: coassoc FAIL at {exps_of(m)}'
    for x in I:
        acc = 0; vv = D0[x]
        while vv:
            l = vv & -vv; i = l.bit_length() - 1; vv ^= l
            p, q = u2(i); m = mul(p, q)
            if m is not None: acc ^= 1 << m
        assert acc == 0, f'{nm}: phi0 != 0 (not killed by 2)'
    print(f'  gates OK (counit/coassoc/phi0=0)  DIM={DIM} c={len(G)}', flush=True)

    # ---- first-order variables ----
    MU = {}; WV = {}
    for ii, x in enumerate(I):
        for y in I[ii:]:
            MU[(1, x, y)] = [0] + [BitVec(f'{nm}_m1_{x}_{y}_{o}', 1) for o in I]
    for x in I:
        v = [0] * (DIM * DIM)
        for p in I:
            for q in I: v[t2(p, q)] = BitVec(f'{nm}_w1_{x}_{p}_{q}', 1)
        WV[(1, x)] = v
    def muvar(l, x, y):
        if x > y: x, y = y, x
        return MU[(l, x, y)]
    def leg_mul(l, p, q):
        if l == 0:
            m = mul(p, q)
            return [] if m is None else [(m, 1)]
        if p == 0 or q == 0: return []
        mv = muvar(l, p, q)
        return [(o, mv[o]) for o in I]
    def basis(x):
        X = [[0] * DIM for _ in range(NE)]; X[0][x] = 1; return X
    def A_mul(X, Y):
        Z = [[0] * DIM for _ in range(NE)]
        for i in range(NE):
            for j in range(NE - i):
                r0 = i + j
                x0, y0 = X[i][0], Y[j][0]
                if not isz(x0):
                    for c in range(DIM): Z[r0][c] = bxor(Z[r0][c], band(x0, Y[j][c]))
                if not isz(y0):
                    for c in range(DIM): Z[r0][c] = bxor(Z[r0][c], band(y0, X[i][c]))
                if not (isz(x0) or isz(y0)): Z[r0][0] = bxor(Z[r0][0], band(x0, y0))
                for x in I:
                    xx = X[i][x]
                    if isz(xx): continue
                    for y in I:
                        yy = Y[j][y]
                        if isz(yy): continue
                        xy = band(xx, yy); m = mul(x, y)
                        if m is not None: Z[r0][m] = bxor(Z[r0][m], xy)
                        for l in range(1, NE - i - j):
                            mv = muvar(l, x, y)
                            for o in I: Z[r0 + l][o] = bxor(Z[r0 + l][o], band(xy, mv[o]))
        return Z
    def Delta_apply(X):
        R = [[0] * (DIM * DIM) for _ in range(NE)]
        for i in range(NE):
            if not isz(X[i][0]): R[i][t2(0, 0)] = bxor(R[i][t2(0, 0)], X[i][0])
            for x in I:
                xx = X[i][x]
                if isz(xx): continue
                vv = D0[x]
                while vv:
                    lb = vv & -vv; k = lb.bit_length() - 1; vv ^= lb
                    R[i][k] = bxor(R[i][k], xx)
                for l in range(1, NE - i):
                    for k, e in enumerate(WV[(l, x)]):
                        if not isz(e): R[i + l][k] = bxor(R[i + l][k], band(xx, e))
        return R
    def T2_mul(U, V):
        Z = [[0] * (DIM * DIM) for _ in range(NE)]
        for i in range(NE):
            for iu, f in enumerate(U[i]):
                if isz(f): continue
                p, q = u2(iu)
                for j in range(NE - i):
                    for iv, g0 in enumerate(V[j]):
                        if isz(g0): continue
                        pp, qq = u2(iv); fg = band(f, g0)
                        for l1 in range(NE - i - j):
                            L = leg_mul(l1, p, pp)
                            if not L: continue
                            for l2 in range(NE - i - j - l1):
                                Rl = leg_mul(l2, q, qq)
                                if not Rl: continue
                                rr = i + j + l1 + l2
                                for c1, e1 in L:
                                    fe = band(fg, e1)
                                    if isz(fe): continue
                                    for c2, e2 in Rl:
                                        tt = band(fe, e2)
                                        if isz(tt): continue
                                        Z[rr][t2(c1, c2)] = bxor(Z[rr][t2(c1, c2)], tt)
        return Z
    def coassoc_defect(x):
        U = Delta_apply(basis(x))
        L = [[0] * (DIM ** 3) for _ in range(NE)]; R = [[0] * (DIM ** 3) for _ in range(NE)]
        for i in range(NE):
            for idx2, f in enumerate(U[i]):
                if isz(f): continue
                p, q = u2(idx2)
                if p == 0: L[i][t3(0, 0, q)] = bxor(L[i][t3(0, 0, q)], f)
                else:
                    vv = D0[p]
                    while vv:
                        lb = vv & -vv; k = lb.bit_length() - 1; vv ^= lb
                        p1, p2 = u2(k); L[i][t3(p1, p2, q)] = bxor(L[i][t3(p1, p2, q)], f)
                    for l in range(1, NE - i):
                        for k, e in enumerate(WV[(l, p)]):
                            if not isz(e):
                                p1, p2 = u2(k)
                                L[i + l][t3(p1, p2, q)] = bxor(L[i + l][t3(p1, p2, q)], band(f, e))
                if q == 0: R[i][t3(p, 0, 0)] = bxor(R[i][t3(p, 0, 0)], f)
                else:
                    vv = D0[q]
                    while vv:
                        lb = vv & -vv; k = lb.bit_length() - 1; vv ^= lb
                        q1, q2 = u2(k); R[i][t3(p, q1, q2)] = bxor(R[i][t3(p, q1, q2)], f)
                    for l in range(1, NE - i):
                        for k, e in enumerate(WV[(l, q)]):
                            if not isz(e):
                                q1, q2 = u2(k)
                                R[i + l][t3(p, q1, q2)] = bxor(R[i + l][t3(p, q1, q2)], band(f, e))
        return [[bxor(L[r][c], R[r][c]) for c in range(DIM ** 3)] for r in range(NE)]

    S = Solver()
    if timeout_ms: S.set('timeout', timeout_ms)
    neq = [0]
    def assert0(x):
        if isinstance(x, int):
            assert x == 0, 'constant axiom violation — encoding bug'
            return
        S.add(x == 0); neq[0] += 1
    PR = {(x, y): A_mul(basis(x), basis(y)) for x in I for y in I}
    for x, y, z in itertools.product(I, repeat=3):
        A1 = A_mul(PR[(x, y)], basis(z)); A2 = A_mul(basis(x), PR[(y, z)])
        for r in range(1, NE):
            for o in range(DIM): assert0(bxor(A1[r][o], A2[r][o]))
    for ii, x in enumerate(I):
        for y in I[ii:]:
            LHS = Delta_apply(A_mul(basis(x), basis(y)))
            RHS = T2_mul(Delta_apply(basis(x)), Delta_apply(basis(y)))
            for r in range(1, NE):
                for o in range(DIM * DIM): assert0(bxor(LHS[r][o], RHS[r][o]))
    for x in I:
        C = coassoc_defect(x)
        for r in range(1, NE):
            for o in range(DIM ** 3): assert0(C[r][o])
    print(f'  axioms: {neq[0]} eqs  ({time.time()-T0:.0f}s)', flush=True)

    PSI = {n: {} for n in range(NE)}
    for x in I:
        Dr = Delta_apply(basis(x)); Ph = [[0] * DIM for _ in range(NE)]
        for i in range(NE):
            for idx2, f in enumerate(Dr[i]):
                if isz(f): continue
                p, q = u2(idx2)
                for l in range(NE - i):
                    for cc, e in leg_mul(l, p, q): Ph[i + l][cc] = bxor(Ph[i + l][cc], band(f, e))
        for n in range(NE): PSI[n][x] = Ph[n]
    def psi_apply(n, vec):
        out = [0] * DIM
        for x in I:
            vx = vec[x]
            if isz(vx): continue
            Px = PSI[n][x]
            for c in range(DIM):
                if not isz(Px[c]): out[c] = bxor(out[c], band(vx, Px[c]))
        return out
    def psi_pow(x, K):
        v = [1 if c == x else 0 for c in range(DIM)]
        for _ in range(K): v = psi_apply(1, v)
        return v
    def cond(K, gen_only):
        lits = []
        outs = GEN if gen_only else range(DIM)
        for x in I:
            v = psi_pow(x, K)
            for c in outs:
                if isz(v[c]): continue
                if isinstance(v[c], int): return True
                lits.append(v[c] == BitVecVal(1, 1))
        return Or(lits) if lits else False
    def ask(label, cnd):
        if cnd is True: print(f'    {label}: trivially sat', flush=True); return 'sat'
        if cnd is False: print(f'    {label}: trivially unsat (identically 0)', flush=True); return 'unsat'
        S.push(); S.add(cnd); t = time.time(); r = S.check(); S.pop()
        print(f'    {label}: {r}   ({time.time()-t:.1f}s)', flush=True)
        return str(r)

    print(f'  [S0 axioms only]: {S.check()}  (must be sat)', flush=True)
    res = {}
    for K in powers:
        res[(K, 'full')] = ask(f'Psi_1^{K} != 0  (full map)', cond(K, False))
        res[(K, 'gen')] = ask(f'Psi_1^{K} != 0  (gen output = honest L^{K} mod I^2)', cond(K, True))
    seed = res.get((4, 'full')) == 'sat'
    print(f'  ==> {nm}: {"*** LEADING SEED (Psi_1^4 realizable) ***" if seed else "no leading seed (Psi_1^4 = 0)"}',
          flush=True)
    return nm, res


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('fibers', nargs='*')
    ap.add_argument('--powers', default='2,3,4')
    ap.add_argument('--timeout-ms', type=int, default=300000)
    a = ap.parse_args()
    fibers = a.fibers or ['W4F', 'AZ_X8Y2', 'AZ_X4Y4_a', 'AZ_X4Y4_b',
                          'AZ_X4Y2Z2_star', 'W2F_W2F', 'W3F_a2', 'c44_ca1_cb1']
    powers = [int(x) for x in a.powers.split(',')]
    rows = []
    for f in fibers:
        print(f'----- fiber {f} -----', flush=True)
        try:
            nm, res = run(f, powers, a.timeout_ms)
            rows.append((nm, res))
        except AssertionError as ex:
            print(f'  [REJECTED by gates] {ex}', flush=True)
    print('\n=== SUMMARY (honest full-axiom first-order, exact F2) ===', flush=True)
    hdr = f'{"fiber":18}' + ''.join(f'  P^{K}full P^{K}gen' for K in powers)
    print(hdr, flush=True)
    for nm, res in rows:
        line = f'{nm:18}'
        for K in powers:
            line += f'  {res[(K,"full")]:>7} {res[(K,"gen")]:>6}'
        print(line, flush=True)
    print(f'DONE rank16_leading_z3 ({time.time()-T0:.0f}s)', flush=True)
