#!/usr/bin/env python3
"""rank8_td4.py — the rank-8 s = 4 Massey probe (session 15).

Context (see THEORY_rank8.md; ChatGPT larger-rank handoff at
scripts/larger_rank_bundle/).  For a free rank-8 bialgebra A over
R = F2[e]/e^N with killed-by-2 fiber H, the comorphism of squaring
Phi = [2]^# = mu Delta is an R-algebra endomorphism with digit expansion
Phi = sum_r e^r Psi_r, Psi_0 = phi_0 = 0, and [8]^# = Phi^3.  Hence

  [8]^# = sum_s e^s TD_s,   TD_s = sum_{i+j+k=s, i,j,k>=1} Psi_i Psi_j Psi_k.

TD_3 = Psi_1^3 = 0 for all tested fibers (Theorem R8-1: handoff L^2 = 0
+ automatic product-kill Psi_1(I^2) = 0).  The FIRST live layer is

  TD_4 = Psi_1 Psi_1 Psi_2 + Psi_1 Psi_2 Psi_1 + Psi_2 Psi_1 Psi_1,

which needs only the e<=2 deformation data (mu_1, mu_2, w_1, w_2).  This
script imposes the FULL bialgebra axioms at digits 1 and 2 (associativity,
Delta-multiplicativity, coassociativity; mu commutative — any
counterexample group scheme has commutative function algebra, and Deligne
covers cocommutative Delta, so w is unconstrained) over F2[e]/e^3 and asks

  MAIN:  can TD_4 != 0 ?

RELAXATION LOGIC (why unsat is strong): a counterexample over ANY
F2[e]/e^N truncates to a deformation over F2[e]/e^3 with the same
(Psi_1, Psi_2), and the e^4-digit of its true Phi^3 is exactly the TD_4
computed here.  So `unsat` closes the s = 4 layer for the given fiber over
EVERY curvilinear base at exact-F2 strength.  `sat` = a counterexample
SEED whose lift obstructions must then be checked (it is NOT yet a
counterexample).  Higher layers (s = 5 needs Psi_3, etc.) remain open
either way — same layer bookkeeping as the order-4 program (THEORY 12.6.1).

Gates per fiber:
  S0 axioms-only        -> expect sat  (encoding non-vacuous)
  S1 Psi_1^3 != 0       -> expect unsat (cross-checks Theorem R8-1 and
                           this encoding against the handoff's independent
                           linear-algebra computation)
  S2 Psi_1 != 0         -> discovery (sat for fibers with L-space != 0)
  S3 Psi_2 != 0         -> expect sat (layer-2 non-vacuity)
  MAIN TD_4 != 0        -> THE question

Fibers: W3F and the eight exterior masks (bit i of mask = generator x_i is
mu_2-type: Delta0 x_i += x_i (x) x_i; else alpha_2-type primitive).
Delta0 tables identical to scripts/rank8_gates.py (ALL RANK8 GATES PASSED:
coassociative, counital, multiplicative, phi_0 = 0).

Run:  ~/.venvs/z3env/bin/python rank8_td4.py [fiber ...]
      default order: W3F mask6 mask3 mask5 mask1 mask2 mask4 mask0 mask7
"""
import sys, time
from z3 import Solver, BitVec, BitVecVal, Or, sat, unsat

D = 3
DIM = 1 << D
NE = 3                      # digits 0,1,2  (e^3 = 0)
I_BASIS = list(range(1, DIM))
GENS = [1 << i for i in range(D)]
Z0 = 0                      # python int constants where possible
T0 = time.time()

def mul_monom(a, b):
    return None if (a & b) else (a | b)

def t2i(a, b): return a * DIM + b
def t2u(i): return divmod(i, DIM)
def t3i(a, b, c): return (a * DIM + b) * DIM + c

def band(x, y):
    if isinstance(x, int): return y if x else 0
    if isinstance(y, int): return x if y else 0
    return x & y

def bxor(x, y):
    if isinstance(x, int): return y if x == 0 else bnot(y)
    if isinstance(y, int): return x if y == 0 else bnot(x)
    return x ^ y

def bnot(x):
    if isinstance(x, int): return 1 - x
    return x ^ BitVecVal(1, 1)

def is_znum(x): return isinstance(x, int) and x == 0

def delta0_table(fiber):
    if fiber == 'W3F':
        def dgen(g):
            n = g.bit_length() - 1
            terms = [(g, 0), (0, g)]
            N = 1 << n
            for a in range(1, N): terms.append((a, N - a))
            v = 0
            for a, b in terms: v ^= 1 << t2i(a, b)
            return v
        DG = {g: dgen(g) for g in GENS}
    elif fiber.startswith('mask'):
        mask = int(fiber[4:])
        DG = {}
        for i, g in enumerate(GENS):
            v = (1 << t2i(g, 0)) ^ (1 << t2i(0, g))
            if (mask >> i) & 1: v ^= 1 << t2i(g, g)
            DG[g] = v
    else:
        raise ValueError(fiber)
    def vmul(u, v):
        res = 0; uu = u
        while uu:
            l = uu & -uu; i = l.bit_length() - 1; uu ^= l
            a, b = t2u(i); vv = v
            while vv:
                l2 = vv & -vv; j = l2.bit_length() - 1; vv ^= l2
                c, e = t2u(j)
                ac = mul_monom(a, c); be = mul_monom(b, e)
                if ac is not None and be is not None:
                    res ^= 1 << t2i(ac, be)
        return res
    def dmono(m):
        res = 1 << t2i(0, 0)
        for g in GENS:
            if m & g: res = vmul(res, DG[g])
        return res
    return [dmono(m) for m in range(DIM)]

def run_fiber(fiber):
    print(f'===== rank8_td4: fiber {fiber} =====', flush=True)
    DELTA0 = delta0_table(fiber)
    # phi0 = 0 sanity (independent of rank8_gates)
    for m in I_BASIS:
        res = 0; vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2u(idx)
            c = mul_monom(a, b)
            if c is not None: res ^= 1 << c
        assert res == 0, f'fiber {fiber} not killed by 2'
    # ---- variables ----
    MU = {}   # MU[(l,a,b)] -> 8-list (a <= b, entries: coord 0 fixed 0)
    WV = {}   # WV[(l,a)]   -> 64-list (I (x) I coords only, rest 0)
    for l in (1, 2):
        for ii, a in enumerate(I_BASIS):
            for b in I_BASIS[ii:]:
                v = [0] * DIM
                for out in I_BASIS:
                    v[out] = BitVec(f'{fiber}_m{l}_{a}_{b}_{out}', 1)
                MU[(l, a, b)] = v
        for a in I_BASIS:
            v = [0] * (DIM * DIM)
            for p in I_BASIS:
                for q in I_BASIS:
                    v[t2i(p, q)] = BitVec(f'{fiber}_w{l}_{a}_{p}_{q}', 1)
            WV[(l, a)] = v

    def muvar(l, a, b):
        if a > b: a, b = b, a
        return MU[(l, a, b)]

    def A_mul(X, Y):
        """X, Y: NE x DIM digit arrays. Deformed product, e^NE = 0."""
        Zr = [[0] * DIM for _ in range(NE)]
        for i in range(NE):
            for j in range(NE - i):
                r0 = i + j
                x0, y0 = X[i][0], Y[j][0]
                if not is_znum(x0):
                    for c in range(DIM):
                        Zr[r0][c] = bxor(Zr[r0][c], band(x0, Y[j][c]))
                if not is_znum(y0):
                    for c in range(DIM):
                        Zr[r0][c] = bxor(Zr[r0][c], band(y0, X[i][c]))
                if not (is_znum(x0) or is_znum(y0)):
                    Zr[r0][0] = bxor(Zr[r0][0], band(x0, y0))
                for a in I_BASIS:
                    xa = X[i][a]
                    if is_znum(xa): continue
                    for b in I_BASIS:
                        yb = Y[j][b]
                        if is_znum(yb): continue
                        xy = band(xa, yb)
                        m = mul_monom(a, b)
                        if m is not None:
                            Zr[r0][m] = bxor(Zr[r0][m], xy)
                        for l in range(1, NE - i - j):
                            mv = muvar(l, a, b)
                            for c in I_BASIS:
                                Zr[r0 + l][c] = bxor(Zr[r0 + l][c],
                                                     band(xy, mv[c]))
        return Zr

    def Delta_apply(X):
        Dr = [[0] * (DIM * DIM) for _ in range(NE)]
        for i in range(NE):
            if not is_znum(X[i][0]):
                Dr[i][t2i(0, 0)] = bxor(Dr[i][t2i(0, 0)], X[i][0])
            for a in I_BASIS:
                xa = X[i][a]
                if is_znum(xa): continue
                vv = DELTA0[a]
                while vv:
                    lb = vv & -vv; idx = lb.bit_length() - 1; vv ^= lb
                    Dr[i][idx] = bxor(Dr[i][idx], xa)
                for l in range(1, NE - i):
                    wv = WV[(l, a)]
                    for idx in range(DIM * DIM):
                        if is_znum(wv[idx]): continue
                        Dr[i + l][idx] = bxor(Dr[i + l][idx],
                                              band(xa, wv[idx]))
        return Dr

    def leg_mul(l, p, q):
        """mu_l applied to basis pair (p,q); returns (coord,expr) list."""
        if l == 0:
            m = mul_monom(p, q)
            return [] if m is None else [(m, 1)]
        if p == 0 or q == 0:
            return []
        mv = muvar(l, p, q)
        return [(c, mv[c]) for c in I_BASIS]

    def T2_mul(U, V):
        Zr = [[0] * (DIM * DIM) for _ in range(NE)]
        for i in range(NE):
            for iu in range(DIM * DIM):
                f = U[i][iu]
                if is_znum(f): continue
                p, q = t2u(iu)
                for j in range(NE - i):
                    for iv in range(DIM * DIM):
                        g = V[j][iv]
                        if is_znum(g): continue
                        pp, qq = t2u(iv)
                        fg = band(f, g)
                        for l1 in range(NE - i - j):
                            L = leg_mul(l1, p, pp)
                            if not L: continue
                            for l2 in range(NE - i - j - l1):
                                Rl = leg_mul(l2, q, qq)
                                if not Rl: continue
                                r = i + j + l1 + l2
                                for (c1, e1) in L:
                                    fe = band(fg, e1)
                                    if is_znum(fe): continue
                                    for (c2, e2) in Rl:
                                        t = band(fe, e2)
                                        if is_znum(t): continue
                                        cc = t2i(c1, c2)
                                        Zr[r][cc] = bxor(Zr[r][cc], t)
        return Zr

    def basis_elt(a):
        X = [[0] * DIM for _ in range(NE)]
        X[0][a] = 1
        return X

    def coassoc_defect(a):
        """digits of (Delta (x) id) Delta(e_a) + (id (x) Delta) Delta(e_a)."""
        U = Delta_apply(basis_elt(a))
        L = [[0] * (DIM ** 3) for _ in range(NE)]
        R = [[0] * (DIM ** 3) for _ in range(NE)]
        for i in range(NE):
            for idx in range(DIM * DIM):
                f = U[i][idx]
                if is_znum(f): continue
                p, q = t2u(idx)
                # Delta on first leg
                if p == 0:
                    L[i][t3i(0, 0, q)] = bxor(L[i][t3i(0, 0, q)], f)
                else:
                    vv = DELTA0[p]
                    while vv:
                        lb = vv & -vv; k = lb.bit_length() - 1; vv ^= lb
                        p1, p2 = t2u(k)
                        L[i][t3i(p1, p2, q)] = bxor(L[i][t3i(p1, p2, q)], f)
                    for l in range(1, NE - i):
                        wv = WV[(l, p)]
                        for k in range(DIM * DIM):
                            if is_znum(wv[k]): continue
                            p1, p2 = t2u(k)
                            L[i + l][t3i(p1, p2, q)] = bxor(
                                L[i + l][t3i(p1, p2, q)], band(f, wv[k]))
                # Delta on second leg
                if q == 0:
                    R[i][t3i(p, 0, 0)] = bxor(R[i][t3i(p, 0, 0)], f)
                else:
                    vv = DELTA0[q]
                    while vv:
                        lb = vv & -vv; k = lb.bit_length() - 1; vv ^= lb
                        q1, q2 = t2u(k)
                        R[i][t3i(p, q1, q2)] = bxor(R[i][t3i(p, q1, q2)], f)
                    for l in range(1, NE - i):
                        wv = WV[(l, q)]
                        for k in range(DIM * DIM):
                            if is_znum(wv[k]): continue
                            q1, q2 = t2u(k)
                            R[i + l][t3i(p, q1, q2)] = bxor(
                                R[i + l][t3i(p, q1, q2)], band(f, wv[k]))
        return [[bxor(L[r][c], R[r][c]) for c in range(DIM ** 3)]
                for r in range(NE)]

    # ---- build axioms ----
    S = Solver()
    neq = 0
    def assert_zero(x):
        nonlocal neq
        if isinstance(x, int):
            assert x == 0, 'constant axiom violation — encoding bug'
            return
        S.add(x == 0); neq += 1

    print(f'[{time.time()-T0:8.1f}s] building associativity...', flush=True)
    PRODS = {}
    for a in I_BASIS:
        for b in I_BASIS:
            PRODS[(a, b)] = A_mul(basis_elt(a), basis_elt(b))
    for a in I_BASIS:
        for b in I_BASIS:
            AB = PRODS[(a, b)]
            for c in I_BASIS:
                ABC = A_mul(AB, basis_elt(c))
                ABC2 = A_mul(basis_elt(a), PRODS[(b, c)])
                for r in (1, 2):
                    for co in range(DIM):
                        assert_zero(bxor(ABC[r][co], ABC2[r][co]))
    print(f'[{time.time()-T0:8.1f}s] building Delta-multiplicativity...',
          flush=True)
    for ii, a in enumerate(I_BASIS):
        for b in I_BASIS[ii:]:
            LHS = Delta_apply(A_mul(basis_elt(a), basis_elt(b)))
            RHS = T2_mul(Delta_apply(basis_elt(a)), Delta_apply(basis_elt(b)))
            for r in (1, 2):
                for co in range(DIM * DIM):
                    assert_zero(bxor(LHS[r][co], RHS[r][co]))
    print(f'[{time.time()-T0:8.1f}s] building coassociativity...', flush=True)
    for a in I_BASIS:
        Cd = coassoc_defect(a)
        for r in (1, 2):
            for co in range(DIM ** 3):
                assert_zero(Cd[r][co])
    print(f'[{time.time()-T0:8.1f}s] axioms built: {neq} equations',
          flush=True)

    # ---- Psi maps ----
    PSI = {1: {}, 2: {}}
    for a in I_BASIS:
        Dr = Delta_apply(basis_elt(a))
        Ph = [[0] * DIM for _ in range(NE)]
        for i in range(NE):
            for idx in range(DIM * DIM):
                f = Dr[i][idx]
                if is_znum(f): continue
                p, q = t2u(idx)
                for l in range(NE - i):
                    for (cc, e) in leg_mul(l, p, q):
                        Ph[i + l][cc] = bxor(Ph[i + l][cc], band(f, e))
        PSI[1][a] = Ph[1]
        PSI[2][a] = Ph[2]
        # digit 0 must be identically 0 on I (killed-by-2 fiber)
        for co in range(DIM):
            assert is_znum(Ph[0][co]) or not isinstance(Ph[0][co], int), \
                'phi0 nonzero'
            if isinstance(Ph[0][co], int):
                assert Ph[0][co] == 0

    def psi_apply(n, vec):
        out = [0] * DIM
        for a in I_BASIS:
            va = vec[a]
            if is_znum(va): continue
            Pa = PSI[n][a]
            for c in range(DIM):
                if is_znum(Pa[c]): continue
                out[c] = bxor(out[c], band(va, Pa[c]))
        return out

    def triple(n1, n2, n3, a):
        return psi_apply(n1, psi_apply(n2, psi_apply(n3,
                         [1 if c == a else 0 for c in range(DIM)])))

    def nonzero_disj(vecs):
        lits = []
        for v in vecs:
            for c in range(DIM):
                if is_znum(v[c]): continue
                if isinstance(v[c], int):
                    return True  # constant 1: identically nonzero
                lits.append(v[c] == BitVecVal(1, 1))
        return Or(lits) if lits else False

    def query(label, cond, expect):
        t = time.time()
        S.push()
        if cond is True:
            print(f'  [{label}] -> trivially sat', flush=True); S.pop(); return
        if cond is False:
            print(f'  [{label}] -> trivially unsat', flush=True); S.pop(); return
        S.add(cond)
        r = S.check()
        S.pop()
        tag = ''
        if expect is not None:
            tag = '  [GATE OK]' if str(r) == expect else '  [GATE **FAIL**]'
        print(f'  [{label}] -> {r}{tag}   ({time.time()-t:.1f}s)', flush=True)
        return str(r)

    t = time.time()
    r0 = S.check()
    print(f'  [S0 axioms only] -> {r0}'
          f'{"  [GATE OK]" if r0 == sat else "  [GATE **FAIL**]"}'
          f'   ({time.time()-t:.1f}s)', flush=True)
    query('S1 Psi1^3 != 0 (expect unsat, Thm R8-1 cross-check)',
          nonzero_disj([triple(1, 1, 1, a) for a in I_BASIS]), 'unsat')
    query('S2 Psi1 != 0 (discovery)',
          nonzero_disj([PSI[1][a] for a in I_BASIS]), None)
    query('S3 Psi2 != 0 (expect sat)',
          nonzero_disj([PSI[2][a] for a in I_BASIS]), 'sat')
    td4 = []
    for a in I_BASIS:
        t1 = triple(1, 1, 2, a)
        t2_ = triple(1, 2, 1, a)
        t3_ = triple(2, 1, 1, a)
        td4.append([bxor(bxor(t1[c], t2_[c]), t3_[c]) for c in range(DIM)])
    query('MAIN TD4 != 0', nonzero_disj(td4), None)
    print(f'===== fiber {fiber} done ({time.time()-T0:.1f}s total) =====',
          flush=True)

FIBERS = sys.argv[1:] if len(sys.argv) > 1 else \
    ['W3F', 'mask6', 'mask3', 'mask5', 'mask1', 'mask2', 'mask4',
     'mask0', 'mask7']
for fb in FIBERS:
    run_fiber(fb)
print('DONE rank8_td4', flush=True)
