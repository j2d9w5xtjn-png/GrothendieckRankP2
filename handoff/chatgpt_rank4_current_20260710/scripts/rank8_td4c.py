#!/usr/bin/env python3
"""rank8_td4c.py — rank-8 Heisenberg/U3 fiber: FULL-deformation layer probe
(session 15).  Companion to rank8_td4.py; same encoding, but the fiber is
the handoff's non-killed-by-2 U3 fiber

  H = F2[x,y,z]/(x^2,y^2,z^2),  Dx,Dy primitive,  Dz = z(x)1+1(x)z+x(x)y,

with phi_0(z) = xy != 0, phi_0^2 = 0 (fiber killed by 4).  Here
[8]^# = Phi^3 with Phi = sum_r e^r Psi_r, Psi_0 = phi_0, so the layer sums
include Psi_0 sandwiches:

  D_s = sum_{i+j+k=s, i,j,k>=0} Psi_i Psi_j Psi_k.

D_0 = phi_0^3 = 0.  The handoff's rank8_heis_firstorder_phi3.py proved
D_1 = 0 for all first-order deformations (gate below re-derives this in
the present encoding); its D_2 check (rank8_polycheck.py,
rank8_exact_certificate.py) was FIXED-ALGEBRA ONLY (mu undeformed).  This
script asks the full-deformation question over F2[e]/e^3:

  MAIN:  can D_2 != 0 with both mu and Delta deformed?

`unsat` for D_1 and D_2 = every rank-8 group scheme over F2[e]/e^3 with
U3 fiber is killed by 8, full deformation strength, and any counterexample
over a longer curvilinear base must first appear at layer s >= 3 (needs
Psi_3, not encoded here).

Run:  ~/.venvs/z3env/bin/python rank8_td4c.py
"""
import time
from z3 import Solver, BitVec, BitVecVal, Or, sat

D = 3
DIM = 1 << D
NE = 3
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

# fiber gates: counit, coassoc, multiplicativity; phi0, phi0^2
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
for l in (1, 2):
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
print(f'[{time.time()-T0:8.1f}s] axioms built: {neq} equations', flush=True)

PSI = {0: {}, 1: {}, 2: {}}
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
    for n in (0, 1, 2):
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
    rows = []
    for a in I_BASIS:
        acc = [0] * DIM
        for i in range(min(s, 2) + 1):
            for j in range(min(s - i, 2) + 1):
                k = s - i - j
                if k < 0 or k > 2: continue
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
query('D1 != 0 (expect unsat; full-deformation upgrade of handoff '
      'first-order result)', nonzero_disj(layer_sum(1)), 'unsat')
query('MAIN D2 != 0 (full deformation; handoff checked fixed-algebra only)',
      nonzero_disj(layer_sum(2)), None)
print('DONE rank8_td4c', flush=True)
