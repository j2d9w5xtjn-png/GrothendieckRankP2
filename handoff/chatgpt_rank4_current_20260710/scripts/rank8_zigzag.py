#!/usr/bin/env python3
"""rank8_zigzag.py — the s>=4 Massey layers for rank-8 killed-by-2 fibers
with F != 0 (NON-EXTERIOR algebra) — the untested-fiber gap (session 16).

WHY THIS FILE EXISTS.  Every prior rank-8 script (rank8_td4/td4b/td4c/td5,
and the whole ChatGPT larger_rank bundle) hardcodes the EXTERIOR algebra
A_0 = F2[x0,x1,x2]/(xi^2).  That algebra is precisely the HEIGHT-1 case:
Frobenius F = 0 on the Dieudonne module.  So all fourteen tested fibers
(masks, W3[F], products) have F = 0.  The killed-by-2 fibers with F != 0
live on a DIFFERENT algebra (a generator t with t^2 != 0, i.e. a t^4-type
factor) and have NEVER been tested at ANY layer.  Theorems R8-1/R8-2 do
NOT cover them.  This is the sharpest remaining crack for a counterexample.

THE FIBER Z1 (handoff THEORY_rank8 §6.2 "zigzag").  Dieudonne module
length 3 over F2[F,V]/(FV,VF) with Fe1 = e0 = Ve2 (both F,V != 0),
indecomposable, killed by 2.  Its Hopf algebra, derived (session 16) by
amalgamating the F-extension G_a[F^2] = F2[t]/t^4 (t primitive, e0 = t^2)
with the V-extension W2[F] along the shared socle e0 = t^2:

  O_Z1 = F2[t,x]/(t^4, x^2)        (dim 8, NON-exterior: t^2 != 0)
  Delta t = t@1 + 1@t              (t primitive)
  Delta x = x@1 + 1@x + t^2 @ t^2  (Witt extension by e0 = t^2)

Hand-checked killed by 2 (phi0(t)=2t=0, phi0(x)=2x+t^4=0) and coassociative
(both verified again by the in-script fiber gates below).  Cotangent dim 2,
so the LEADING term Psi_1^3 = 0 automatically (a 2x2 nilpotent squares to
0); the first LIVE layer is TD_4 (needs Psi_2), exactly as for the exterior
fibers — but here R8-2 says nothing.

Z1DUAL is the Cartier dual (F <-> V swapped).  Its algebra is built by the
same amalgam with the roles of the two extension types swapped; see the
FIBERS table.  [If a direct construction is uncertain, the honest move is
to run Z1 first — it is the clean case.]

CROSS-CHECKS.  Fibers 'xmask0' (= alpha_2^3) and 'xW3F' re-encode two
EXTERIOR fibers through this general monomial-algebra machinery; their
TD_4 MUST come back `unsat` (Theorem R8-2), validating the general encoding
against the bitmask scripts.  Run them first.

ENCODING.  Identical layer bookkeeping to rank8_td5.py (generic TD(s) over
compositions, NE digits, full bialgebra axioms at digits 1..NE-1 over
F2[e]/e^NE).  The ONLY change is the algebra: monomials are mixed-radix
exponent tuples with per-generator nilpotency caps, and multiplication is a
precomputed table MUL (add exponents, zero if any cap is reached).  Setting
all caps = 2 recovers the bitmask (exterior) algebra exactly.

Reading verdicts (same as td5): `unsat` at layer s closes s for that fiber
over EVERY curvilinear base at exact-F2 strength; `sat` is a counterexample
SEED whose lift must then be checked.

Run:  ~/.venvs/z3env/bin/python rank8_zigzag.py [fiber ...] [--NE n] [--s s]
      default: xmask0 xW3F Z1   at NE=3 (TD_4)
"""
import sys, time
from itertools import product as iproduct
from z3 import Solver, BitVec, BitVecVal, Or, sat, unsat

T0 = time.time()

# ---------- fiber definitions ----------
# caps: per-generator nilpotency (exponent < cap). DIM = prod(caps).
# gens: list of generator monomial-indices (in the mixed-radix scheme).
# delta0: dict g -> list of (p,q) monomial-index pairs, Delta(g)=sum g_p @ g_q
#         (the primitive part g@1 + 1@g must be included explicitly).
def make_fiber(caps):
    r = len(caps)
    strides = [1] * r
    for i in range(1, r):
        strides[i] = strides[i - 1] * caps[i - 1]
    DIM = strides[-1] * caps[-1]
    def idx_of(exps):
        return sum(e * s for e, s in zip(exps, strides))
    def exps_of(m):
        out = []
        for i in range(r):
            out.append((m // strides[i]) % caps[i])
        return out
    # multiplication table (monomial index or -1)
    MUL = [[-1] * DIM for _ in range(DIM)]
    for a in range(DIM):
        ea = exps_of(a)
        for b in range(DIM):
            eb = exps_of(b)
            ec = [ea[i] + eb[i] for i in range(r)]
            if all(ec[i] < caps[i] for i in range(r)):
                MUL[a][b] = idx_of(ec)
    return DIM, strides, idx_of, exps_of, MUL

def gen_index(caps, which):
    """monomial index of the `which`-th generator (exponent 1 in slot which)."""
    strides = [1] * len(caps)
    for i in range(1, len(caps)):
        strides[i] = strides[i - 1] * caps[i - 1]
    return strides[which]

def build_fiber(name):
    if name == 'xmask0':                       # alpha_2^3 (exterior), F=0
        caps = (2, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        g = [gen_index(caps, i) for i in range(3)]
        def T2(p, q, DIM=DIM): return p * DIM + q
        delta0 = {g[i]: [(g[i], 0), (0, g[i])] for i in range(3)}
    elif name == 'xW3F':                       # W_3[F] (exterior), F=0
        caps = (2, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        x0, x1, x2 = 1, 2, 4
        x0x1 = idx_of([1, 1, 0])               # = 3
        delta0 = {
            x0: [(x0, 0), (0, x0)],
            x1: [(x1, 0), (0, x1), (x0, x0)],
            x2: [(x2, 0), (0, x2), (x0, x0x1), (x1, x1), (x0x1, x0)],
        }
    elif name == 'Z1':                         # F2[t,x]/(t^4,x^2), F!=0
        caps = (4, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        t = idx_of([1, 0])                     # = 1
        t2 = idx_of([2, 0])                    # = 2
        x = idx_of([0, 1])                     # = 4
        delta0 = {
            t: [(t, 0), (0, t)],               # t primitive
            x: [(x, 0), (0, x), (t2, t2)],     # x + Witt(e0=t^2)
        }
    elif name == 'GaF3':                       # G_a[F^3] = F2[t]/t^8, F-Jordan-3
        # single long Frobenius chain, t primitive, V=0.  Cotangent dim 1.
        caps = (8,)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        t = idx_of([1])
        delta0 = {t: [(t, 0), (0, t)]}
    elif name == 'aGaF2':                       # alpha_2 x G_a[F^2], F!=0
        # F2[t,s]/(t^4,s^2), t primitive (G_a[F^2]), s primitive (alpha_2)
        caps = (4, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        t = idx_of([1, 0]); s = idx_of([0, 1])
        delta0 = {t: [(t, 0), (0, t)], s: [(s, 0), (0, s)]}
    elif name == 'GaF2mu2':                     # G_a[F^2] x mu_2, F!=0
        # F2[t,s]/(t^4,s^2), t primitive, s group-like (mu_2): Ds = s@1+1@s+s@s
        caps = (4, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        t = idx_of([1, 0]); s = idx_of([0, 1])
        delta0 = {t: [(t, 0), (0, t)], s: [(s, 0), (0, s), (s, s)]}
    elif name == 'Z1dual':                     # Cartier-dual amalgam, F!=0
        # dual zigzag: swap the two extension roles.  Algebra F2[t,x]/(t^4,x^2)
        # again (self-similar underlying algebra) but the V-extension is put on
        # t^2 and the primitive/socle structure is dualised: here x is primitive
        # and t carries BOTH a divided part and the coupling.  This branch is
        # the LESS certain of the two; the fiber gates will reject it if the
        # proposed Delta0 is not a valid killed-by-2 coalgebra.
        caps = (4, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        t = idx_of([1, 0]); t2 = idx_of([2, 0]); t3 = idx_of([3, 0])
        x = idx_of([0, 1])
        delta0 = {
            t:  [(t, 0), (0, t)],
            x:  [(x, 0), (0, x), (t, t3), (t3, t)],
        }
    else:
        raise ValueError(name)
    return caps, DIM, idx_of, exps_of, MUL, delta0


def run_fiber(name, NE, target_s):
    caps, DIM, idx_of, exps_of, MUL, DELTA0_GEN = build_fiber(name)
    I_BASIS = list(range(1, DIM))
    LAYERS = list(range(1, NE))
    AXIOM_DIGITS = list(range(1, NE))
    print(f'===== rank8_zigzag: fiber {name}  caps={caps} DIM={DIM} '
          f'NE={NE} target=TD_{target_s} =====', flush=True)

    def mul_monom(a, b):
        m = MUL[a][b]
        return None if m < 0 else m

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

    def compositions(s, parts, lo, hi):
        return [c for c in iproduct(range(lo, hi + 1), repeat=parts)
                if sum(c) == s]

    # ---- build DELTA0 table (bitset over T2 = DIM*DIM) ----
    def vmul_t2(u, v):                          # product in A@A as bitsets
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
    DG = {}
    for g, terms in DELTA0_GEN.items():
        v = 0
        for (p, q) in terms:
            v ^= 1 << t2i(p, q)
        DG[g] = v
    def dmono(m):
        res = 1 << t2i(0, 0)
        exps = exps_of(m)
        for slot, e in enumerate(exps):
            g = gen_index(caps, slot)
            for _ in range(e):
                res = vmul_t2(res, DG[g])
        return res
    DELTA0 = [dmono(m) for m in range(DIM)]

    # ---- fiber gates (counit, coassoc, phi0=0) ----
    for m in range(DIM):
        left = right = 0; vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2u(idx)
            if a == 0: left ^= 1 << b
            if b == 0: right ^= 1 << a
        assert left == (1 << m) and right == (1 << m), \
            f'{name}: counit FAIL at monomial {m} ({exps_of(m)})'
    for m in range(DIM):
        lhs = rhs = 0; vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2u(idx)
            da = DELTA0[a]
            while da:
                l2 = da & -da; j = l2.bit_length() - 1; da ^= l2
                p, q = t2u(j); lhs ^= 1 << t3i(p, q, b)
            db = DELTA0[b]
            while db:
                l2 = db & -db; j = l2.bit_length() - 1; db ^= l2
                p, q = t2u(j); rhs ^= 1 << t3i(a, p, q)
        assert lhs == rhs, f'{name}: coassoc FAIL at monomial {m} ({exps_of(m)})'
    # phi0 = mu.Delta0, must be 0 on I (killed by 2)
    for m in I_BASIS:
        res = 0; vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2u(idx); c = mul_monom(a, b)
            if c is not None: res ^= 1 << c
        assert res == 0, f'{name}: NOT killed by 2 (phi0 != 0) at {exps_of(m)}'
    nonexterior = any(caps[i] > 2 for i in range(len(caps)))
    print(f'  fiber gates OK (counit/coassoc/phi0=0); '
          f'{"NON-exterior (F!=0)" if nonexterior else "exterior (F=0)"}',
          flush=True)

    # ---- deformation variables ----
    MU = {}; WV = {}
    for l in LAYERS:
        for ii, a in enumerate(I_BASIS):
            for b in I_BASIS[ii:]:
                MU[(l, a, b)] = [0] + [BitVec(f'{name}_m{l}_{a}_{b}_{o}', 1)
                                       for o in I_BASIS]
        for a in I_BASIS:
            v = [0] * (DIM * DIM)
            for p in I_BASIS:
                for q in I_BASIS:
                    v[t2i(p, q)] = BitVec(f'{name}_w{l}_{a}_{p}_{q}', 1)
            WV[(l, a)] = v

    def muvar(l, a, b):
        if a > b: a, b = b, a
        return MU[(l, a, b)]

    def A_mul(X, Y):
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
                        if m is not None and m != 0:
                            Zr[r0][m] = bxor(Zr[r0][m], xy)
                        elif m == 0:
                            Zr[r0][0] = bxor(Zr[r0][0], xy)
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
                                        tt = band(fe, e2)
                                        if is_znum(tt): continue
                                        Zr[r][t2i(c1, c2)] = bxor(
                                            Zr[r][t2i(c1, c2)], tt)
        return Zr

    def basis_elt(a):
        X = [[0] * DIM for _ in range(NE)]
        X[0][a] = 1
        return X

    def coassoc_defect(a):
        U = Delta_apply(basis_elt(a))
        Lv = [[0] * (DIM ** 3) for _ in range(NE)]
        Rv = [[0] * (DIM ** 3) for _ in range(NE)]
        for i in range(NE):
            for idx in range(DIM * DIM):
                f = U[i][idx]
                if is_znum(f): continue
                p, q = t2u(idx)
                if p == 0:
                    Lv[i][t3i(0, 0, q)] = bxor(Lv[i][t3i(0, 0, q)], f)
                else:
                    vv = DELTA0[p]
                    while vv:
                        lb = vv & -vv; k = lb.bit_length() - 1; vv ^= lb
                        p1, p2 = t2u(k)
                        Lv[i][t3i(p1, p2, q)] = bxor(Lv[i][t3i(p1, p2, q)], f)
                    for l in range(1, NE - i):
                        wv = WV[(l, p)]
                        for k in range(DIM * DIM):
                            if is_znum(wv[k]): continue
                            p1, p2 = t2u(k)
                            Lv[i + l][t3i(p1, p2, q)] = bxor(
                                Lv[i + l][t3i(p1, p2, q)], band(f, wv[k]))
                if q == 0:
                    Rv[i][t3i(p, 0, 0)] = bxor(Rv[i][t3i(p, 0, 0)], f)
                else:
                    vv = DELTA0[q]
                    while vv:
                        lb = vv & -vv; k = lb.bit_length() - 1; vv ^= lb
                        q1, q2 = t2u(k)
                        Rv[i][t3i(p, q1, q2)] = bxor(Rv[i][t3i(p, q1, q2)], f)
                    for l in range(1, NE - i):
                        wv = WV[(l, q)]
                        for k in range(DIM * DIM):
                            if is_znum(wv[k]): continue
                            q1, q2 = t2u(k)
                            Rv[i + l][t3i(p, q1, q2)] = bxor(
                                Rv[i + l][t3i(p, q1, q2)], band(f, wv[k]))
        return [[bxor(Lv[r][c], Rv[r][c]) for c in range(DIM ** 3)]
                for r in range(NE)]

    # ---- assemble axioms ----
    S = Solver(); neq = 0
    def assert_zero(x):
        nonlocal neq
        if isinstance(x, int):
            assert x == 0, 'constant axiom violation — encoding bug'
            return
        S.add(x == 0); neq += 1

    print(f'[{time.time()-T0:8.1f}s] assoc...', flush=True)
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
                for r in AXIOM_DIGITS:
                    for co in range(DIM):
                        assert_zero(bxor(ABC[r][co], ABC2[r][co]))
    print(f'[{time.time()-T0:8.1f}s] Delta-mult...', flush=True)
    for ii, a in enumerate(I_BASIS):
        for b in I_BASIS[ii:]:
            LHS = Delta_apply(A_mul(basis_elt(a), basis_elt(b)))
            RHS = T2_mul(Delta_apply(basis_elt(a)), Delta_apply(basis_elt(b)))
            for r in AXIOM_DIGITS:
                for co in range(DIM * DIM):
                    assert_zero(bxor(LHS[r][co], RHS[r][co]))
    print(f'[{time.time()-T0:8.1f}s] coassoc...', flush=True)
    for a in I_BASIS:
        Cd = coassoc_defect(a)
        for r in AXIOM_DIGITS:
            for co in range(DIM ** 3):
                assert_zero(Cd[r][co])
    print(f'[{time.time()-T0:8.1f}s] axioms built: {neq} equations', flush=True)

    # ---- Psi maps ----
    PSI = {n: {} for n in range(NE)}
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
        for n in range(NE):
            PSI[n][a] = Ph[n]
        for co in range(DIM):
            v = Ph[0][co]
            assert is_znum(v) or not isinstance(v, int), 'phi0 nonzero'
            if isinstance(v, int): assert v == 0

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
        return psi_apply(n1, psi_apply(n2, psi_apply(
            n3, [1 if c == a else 0 for c in range(DIM)])))

    def TD(s):
        comps = compositions(s, 3, 1, NE - 1)
        assert comps, f'no compositions for s={s}, parts<= {NE-1}'
        rows = []
        for a in I_BASIS:
            acc = [0] * DIM
            for (n1, n2, n3) in comps:
                t = triple(n1, n2, n3, a)
                acc = [bxor(acc[c], t[c]) for c in range(DIM)]
            rows.append(acc)
        return rows

    def nonzero_disj(vecs):
        lits = []
        for v in vecs:
            for c in range(DIM):
                if is_znum(v[c]): continue
                if isinstance(v[c], int): return True
                lits.append(v[c] == BitVecVal(1, 1))
        return Or(lits) if lits else False

    def query(label, cond, expect):
        t = time.time()
        if cond is True:
            print(f'  [{label}] -> trivially sat', flush=True); return
        if cond is False:
            print(f'  [{label}] -> trivially unsat (identically 0)',
                  flush=True); return
        S.push(); S.add(cond); r = S.check(); S.pop()
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
    query('S1 Psi1^3 != 0 (expect unsat; auto for cotangent-dim<=2)',
          nonzero_disj([triple(1, 1, 1, a) for a in I_BASIS]), 'unsat')
    query('S2 Psi1 != 0 (discovery)',
          nonzero_disj([PSI[1][a] for a in I_BASIS]), None)
    query('S3 Psi2 != 0 (expect sat)',
          nonzero_disj([PSI[2][a] for a in I_BASIS]), 'sat')
    if NE >= 4:
        query('S4 Psi3 != 0 (expect sat)',
              nonzero_disj([PSI[3][a] for a in I_BASIS]), 'sat')
    xtag = ' (cross-check: MUST be unsat, Thm R8-2)' if name.startswith('x') \
        else '  (sat = counterexample SEED at this layer)'
    query(f'MAIN TD_{target_s} != 0{xtag}', nonzero_disj(TD(target_s)), None)
    print(f'===== fiber {name} done ({time.time()-T0:.1f}s) =====', flush=True)


if __name__ == '__main__':
    argv = sys.argv[1:]
    NE = 3; target_s = None; fibers = []
    i = 0
    while i < len(argv):
        if argv[i] == '--NE': NE = int(argv[i + 1]); i += 2
        elif argv[i] == '--s': target_s = int(argv[i + 1]); i += 2
        else: fibers.append(argv[i]); i += 1
    if not fibers: fibers = ['xmask0', 'xW3F', 'Z1']
    if target_s is None: target_s = NE + 1        # TD_{NE+1}: the first live layer at NE
    for fb in fibers:
        try:
            run_fiber(fb, NE, target_s)
        except AssertionError as ex:
            # a proposed Delta0 that fails the fiber gates (coassoc/counit/
            # phi0=0) is not a valid killed-by-2 coalgebra — skip it, don't
            # abort the batch.
            print(f'  [fiber {fb} REJECTED by gates] {ex}', flush=True)
    print('DONE rank8_zigzag', flush=True)
