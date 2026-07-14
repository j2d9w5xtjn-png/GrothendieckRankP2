#!/usr/bin/env python3
"""rank8_u3_d3.py — U3/Heisenberg fiber, the s = 3 layer D_3 (session 16).

NE = 4 clone of rank8_td4c.py.  Read that file's header for the U3 fiber
and layer bookkeeping; only the deltas are recorded here.

The U3 fiber H = F2[x,y,z]/(x^2,y^2,z^2), Dz = z@1 + 1@z + x@y, has
phi_0(z) = xy != 0 and phi_0^2 = 0 — it is killed by 4, NOT by 2.  So a
U3-fiber order-8 group scheme is the single most natural counterexample
candidate: the fiber already has [4] = 0 but [4] != 0-would-be, and the
question is whether a deformation pushes [8] = Phi^3 off zero.

Phi = sum_r e^r Psi_r with Psi_0 = phi_0 (constant, != 0), and

  [8]^# = Phi^3 = sum_s e^s D_s,   D_s = sum_{i+j+k=s, i,j,k>=0} Psi_i Psi_j Psi_k.

Session 15 (Theorem R8-3) proved D_0 = D_1 = D_2 = 0 at FULL deformation
strength over F2[e]/e^3.  The FIRST OPEN layer is

  D_3 = sum_{i+j+k=3, i,j,k>=0} Psi_i Psi_j Psi_k
      = [Psi_0 Psi_0 Psi_3 sym(3)] + [Psi_0 Psi_1 Psi_2 sym(6)]
        + [Psi_1 Psi_1 Psi_1] + [Psi_0 Psi_3 ... ] ...   (10 compositions)

which needs Psi_3, i.e. e^3-level (digit-3) deformation data.  This script
imposes the FULL bialgebra axioms at digits 1, 2, 3 over F2[e]/e^4 and asks

  MAIN:  can D_3 != 0 ?

WHY A `sat` WOULD BE A COUNTEREXAMPLE, NOT MERELY A SEED.  Over F2[e]/e^4
the full axioms make A the function bialgebra of a genuine rank-8 R-group
scheme (antipode automatic: the counit-augmentation is nilpotent over the
Artin-local base, so id is convolution-invertible — cf. order-4 Lemma
2.1, and here it needs no killed-by-2 hypothesis, only local-Artin base).
With D_0 = D_1 = D_2 = 0 (regression gates below) and D_3 != 0, we get
  [8]^# = Phi^3 = e^3 D_3 != 0 in A,
i.e. an order-8 group scheme over F2[e]/e^4 NOT killed by 8.  That is an
actual counterexample to Grothendieck's question (pending only a by-hand
recheck of the antipode and flatness, both routine here).  Contrast the
killed-by-2 TD_s probes, where a `sat` is only a seed.

`unsat` closes the s = 3 layer for the U3 fiber over EVERY curvilinear
base F2[e]/e^N at exact-F2 strength (truncation principle, THEORY_rank8
§1); the next open layer is then D_4 (NE = 5).

Gates:
  fiber   counit / coassoc / phi0(z)=xy / phi0^2 = 0   (asserts, as td4c)
  S0      axioms only            -> expect sat  (non-vacuity at NE = 4)
  G-D1    D_1 != 0               -> expect unsat (R8-3 regression at NE=4)
  G-D2    D_2 != 0               -> expect unsat (R8-3 regression at NE=4;
                                    the MAIN result of session 15, must
                                    persist under the stronger digit-3 axioms)
  S-P3    Psi_3 != 0             -> expect sat   (layer-3 non-vacuity)
  MAIN    D_3 != 0               -> THE question

Run:  ~/.venvs/z3env/bin/python rank8_u3_d3.py
"""
import time
from z3 import Solver, BitVec, BitVecVal, Or, sat

D = 3
DIM = 1 << D
NE = 4                       # digits 0,1,2,3  (e^4 = 0)   <-- td4c had NE = 3
LAYERS = list(range(1, NE))  # deformation layers 1,2,3
AXIOM_DIGITS = list(range(1, NE))
I_BASIS = list(range(1, DIM))
T0 = time.time()

def mul_monom(a, b): return None if (a & b) else (a | b)
def t2i(a, b): return a * DIM + b
def t2u(i): return divmod(i, DIM)
def t3i(a, b, c): return (a * DIM + b) * DIM + c

def band(x, y):
    if isinstance(x, int): return y if x else 0
    if isinstance(y, int): return x if y else 0
    return x & y

def bxor(x, y):
    if isinstance(x, int):
        if x == 0: return y
        return 1 - y if isinstance(y, int) else y ^ BitVecVal(1, 1)
    if isinstance(y, int):
        return x if y == 0 else x ^ BitVecVal(1, 1)
    return x ^ y

def is_znum(x): return isinstance(x, int) and x == 0

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

DG = {1: (1 << t2i(1, 0)) ^ (1 << t2i(0, 1)),
      2: (1 << t2i(2, 0)) ^ (1 << t2i(0, 2)),
      4: (1 << t2i(4, 0)) ^ (1 << t2i(0, 4)) ^ (1 << t2i(1, 2))}
def dmono(m):
    res = 1 << t2i(0, 0)
    for g in (1, 2, 4):
        if m & g: res = vmul(res, DG[g])
    return res
DELTA0 = [dmono(m) for m in range(DIM)]

# fiber gates: counit, coassoc, phi0(z)=xy, phi0^2=0  (identical to td4c)
for m in range(DIM):
    left = 0; right = 0; vv = DELTA0[m]
    while vv:
        l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
        a, b = t2u(idx)
        if a == 0: left ^= 1 << b
        if b == 0: right ^= 1 << a
    assert left == (1 << m) and right == (1 << m), 'counit FAIL'
for m in range(DIM):
    lhs = 0; rhs = 0; vv = DELTA0[m]
    while vv:
        l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
        a, b = t2u(idx)
        da = DELTA0[a]
        while da:
            l2 = da & -da; j = l2.bit_length() - 1; da ^= l2
            p, q = t2u(j)
            lhs ^= 1 << t3i(p, q, b)
        db = DELTA0[b]
        while db:
            l2 = db & -db; j = l2.bit_length() - 1; db ^= l2
            p, q = t2u(j)
            rhs ^= 1 << t3i(a, p, q)
    assert lhs == rhs, f'coassoc FAIL at {bin(m)}'
PHI0 = [0] * DIM
for m in range(DIM):
    res = 0; vv = DELTA0[m]
    while vv:
        l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
        a, b = t2u(idx)
        c = mul_monom(a, b)
        if c is not None: res ^= 1 << c
    PHI0[m] = res
assert PHI0[4] == (1 << 3), 'phi0(z) != xy'
def apply0(v_bits):
    res = 0; vv = v_bits
    while vv:
        l = vv & -vv; a = l.bit_length() - 1; vv ^= l
        res ^= PHI0[a]
    return res
assert all(apply0(apply0(1 << a)) == 0 for a in I_BASIS), 'phi0^2 != 0'
print('fiber gates (counit/coassoc/phi0(z)=xy/phi0^2=0): OK', flush=True)

MU = {}; WV = {}
for l in LAYERS:
    for ii, a in enumerate(I_BASIS):
        for b in I_BASIS[ii:]:
            MU[(l, a, b)] = [0] + [BitVec(f'U3_m{l}_{a}_{b}_{o}', 1)
                                   for o in I_BASIS]
    for a in I_BASIS:
        v = [0] * (DIM * DIM)
        for p in I_BASIS:
            for q in I_BASIS:
                v[t2i(p, q)] = BitVec(f'U3_w{l}_{a}_{p}_{q}', 1)
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
                    Dr[i + l][idx] = bxor(Dr[i + l][idx], band(xa, wv[idx]))
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

S = Solver()
neq = 0
def assert_zero(x):
    global neq
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
            for r in AXIOM_DIGITS:
                for co in range(DIM):
                    assert_zero(bxor(ABC[r][co], ABC2[r][co]))
print(f'[{time.time()-T0:8.1f}s] building Delta-multiplicativity...',
      flush=True)
for ii, a in enumerate(I_BASIS):
    for b in I_BASIS[ii:]:
        LHS = Delta_apply(A_mul(basis_elt(a), basis_elt(b)))
        RHS = T2_mul(Delta_apply(basis_elt(a)), Delta_apply(basis_elt(b)))
        for r in AXIOM_DIGITS:
            for co in range(DIM * DIM):
                assert_zero(bxor(LHS[r][co], RHS[r][co]))
print(f'[{time.time()-T0:8.1f}s] building coassociativity...', flush=True)
for a in I_BASIS:
    Cd = coassoc_defect(a)
    for r in AXIOM_DIGITS:
        for co in range(DIM ** 3):
            assert_zero(Cd[r][co])
print(f'[{time.time()-T0:8.1f}s] axioms built: {neq} equations', flush=True)

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
# digit-0 must equal PHI0 (constant)
for a in I_BASIS:
    for c in range(DIM):
        v = PSI[0][a][c]
        assert isinstance(v, int), 'phi0 digit not constant'
        assert v == ((PHI0[a] >> c) & 1), 'phi0 mismatch'
print('phi digit-0 = PHI0 verified', flush=True)

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

def layer_sum(s):
    """D_s = sum_{i+j+k=s, 0<=i,j,k<NE} Psi_i Psi_j Psi_k on each e_a."""
    rows = []
    for a in I_BASIS:
        acc = [0] * DIM
        for i in range(NE):
            for j in range(NE - i):
                k = s - i - j
                if k < 0 or k >= NE: continue
                t = triple(i, j, k, a)
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
        print(f'  [{label}] -> trivially sat (constant)', flush=True); return
    if cond is False:
        print(f'  [{label}] -> trivially unsat (identically 0)', flush=True)
        return
    S.push(); S.add(cond); r = S.check(); S.pop()
    tag = ''
    if expect is not None:
        tag = '  [GATE OK]' if str(r) == expect else '  [GATE **FAIL**]'
    print(f'  [{label}] -> {r}{tag}   ({time.time()-t:.1f}s)', flush=True)

t = time.time()
r0 = S.check()
print(f'  [S0 axioms only] -> {r0}'
      f'{"  [GATE OK]" if r0 == sat else "  [GATE **FAIL**]"}'
      f'   ({time.time()-t:.1f}s)', flush=True)
# D_0 = phi0^3 = 0 (constant check)
d0 = layer_sum(0)
assert all(all(is_znum(v) for v in row) for row in d0), 'D0 != 0'
print('  [D0 = phi0^3 identically 0] OK', flush=True)
query('G-D1 D1 != 0 (expect unsat, R8-3 regression at NE=4)',
      nonzero_disj(layer_sum(1)), 'unsat')
query('G-D2 D2 != 0 (expect unsat, R8-3 MAIN regression at NE=4)',
      nonzero_disj(layer_sum(2)), 'unsat')
query('S-P3 Psi3 != 0 (expect sat, layer-3 non-vacuity)',
      nonzero_disj([PSI[3][a] for a in I_BASIS]), 'sat')
query('MAIN D3 != 0  (sat = ORDER-8 COUNTEREXAMPLE over F2[e]/e^4)',
      nonzero_disj(layer_sum(3)), None)
print('DONE rank8_u3_d3', flush=True)
