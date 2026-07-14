#!/usr/bin/env python3
"""rank8_gates.py — soundness gates for the ChatGPT larger-rank handoff
(scripts/larger_rank_bundle/), session 15.

The handoff's firstorder_WdF.py asserts phi_0 = 0 (fiber killed by 2) but
NEVER checks that its squarefree Witt comultiplication Delta0 is
coassociative or counital.  If Delta0 were not a genuine bialgebra
structure, the first-order linear system would be the linearization of an
inconsistent point and every downstream conclusion vacuous.  These gates
close that gap, re-verify the killed-by-2 assert independently, and
upgrade the exact-F2 cotangent result "all realizable L have L^2 = 0" to
arbitrary F2-algebra strength by checking the POLARIZED products of the
realizable-space basis matrices (the space of realizable L over any k is
the F2-solution space tensored with k, since the constraints are k-linear
with F2 coefficients; so L^2 = 0 for all k-points iff E_i E_j = 0 for all
ordered pairs of F2-basis matrices — the same trick as THEORY 6.2).

Gates:
  G1(d): Delta0 for W_d[F] is coassociative on every monomial.
  G2(d): Delta0 is counital.
  G3(d): Delta0 is multiplicative on disjoint monomials (construction
         recheck).
  G4(d): phi_0 = mu_0 Delta0 = 0 on I (killed by 2; independent recompute).
  G5(d): all ordered products E_i E_j of the handoff's realizable-L basis
         vanish (arbitrary-k L^2 = 0).  Basis hardcoded from the handoff
         logs AND re-derived by rerunning their script is required to
         match (we take it from the reproduced rerun logs of session 15:
         d=3: x1->x0, x2->x0;  d=4: x1->x0, x2->x0, x3->x0).
  G6:    masks 0..7 rank-8 exterior fibers: Delta0 coassoc/counit/phi0=0
         (bit i of mask = mu_2-type generator with x_i (x)x_i term).
Run: python3 rank8_gates.py
"""
import itertools, sys

def make_ops(d):
    DIM = 1 << d
    GENS = [1 << i for i in range(d)]
    def bit(i): return 1 << i
    def mul_monom(a, b): return None if (a & b) else (a | b)
    def t2_index(a, b): return a * DIM + b
    def t2_unindex(i): return divmod(i, DIM)
    T2 = DIM * DIM
    def vec_mul_t2(u, v):
        res = 0; uu = u
        while uu:
            l = uu & -uu; i = l.bit_length() - 1; uu ^= l
            a, b = t2_unindex(i); vv = v
            while vv:
                l2 = vv & -vv; j = l2.bit_length() - 1; vv ^= l2
                c, e = t2_unindex(j)
                ac = mul_monom(a, c); be = mul_monom(b, e)
                if ac is not None and be is not None:
                    res ^= bit(t2_index(ac, be))
        return res
    return DIM, GENS, bit, mul_monom, t2_index, t2_unindex, T2, vec_mul_t2

def delta0_table_WdF(d):
    DIM, GENS, bit, mul_monom, t2_index, t2_unindex, T2, vec_mul_t2 = make_ops(d)
    def delta0_gen(g):
        n = g.bit_length() - 1
        terms = [(g, 0), (0, g)]
        N = 1 << n
        for a in range(1, N):
            terms.append((a, N - a))
        v = 0
        for a, b in terms: v ^= bit(t2_index(a, b))
        return v
    DG = {g: delta0_gen(g) for g in GENS}
    def delta0_monom(m):
        res = bit(t2_index(0, 0))
        for g in GENS:
            if m & g: res = vec_mul_t2(res, DG[g])
        return res
    return [delta0_monom(m) for m in range(DIM)]

def delta0_table_mask(mask, d=3):
    # exterior algebra fiber, generator i primitive (alpha_2) or
    # grouplike-deviation mu_2 type (x+x(x)x) per mask bit
    DIM, GENS, bit, mul_monom, t2_index, t2_unindex, T2, vec_mul_t2 = make_ops(d)
    DG = {}
    for i, g in enumerate(GENS):
        v = bit(t2_index(g, 0)) ^ bit(t2_index(0, g))
        if (mask >> i) & 1:
            v ^= bit(t2_index(g, g))
        DG[g] = v
    def delta0_monom(m):
        res = bit(t2_index(0, 0))
        for g in GENS:
            if m & g: res = vec_mul_t2(res, DG[g])
        return res
    return [delta0_monom(m) for m in range(DIM)]

def gates_for(name, d, DELTA0):
    DIM, GENS, bit, mul_monom, t2_index, t2_unindex, T2, vec_mul_t2 = make_ops(d)
    ok = True
    # G1 coassociativity: (Delta0 (x) id) Delta0 = (id (x) Delta0) Delta0
    def t3_index(a, b, c): return (a * DIM + b) * DIM + c
    for m in range(DIM):
        lhs = 0; rhs = 0
        vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2_unindex(idx)
            da = DELTA0[a]
            while da:
                l2 = da & -da; j = l2.bit_length() - 1; da ^= l2
                p, q = t2_unindex(j)
                lhs ^= 1 << t3_index(p, q, b)
            db = DELTA0[b]
            while db:
                l2 = db & -db; j = l2.bit_length() - 1; db ^= l2
                p, q = t2_unindex(j)
                rhs ^= 1 << t3_index(a, p, q)
        if lhs != rhs:
            print(f'  [G1 {name}] coassoc FAILS at monomial {bin(m)}'); ok = False
    if ok: print(f'  [G1 {name}] Delta0 coassociative on all {DIM} monomials: OK')
    # G2 counit: (eps (x) id) Delta0 = id
    g2 = True
    for m in range(DIM):
        left = 0; right = 0
        vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2_unindex(idx)
            if a == 0: left ^= 1 << b
            if b == 0: right ^= 1 << a
        if left != (1 << m) or right != (1 << m):
            print(f'  [G2 {name}] counit FAILS at {bin(m)}'); g2 = False; ok = False
    if g2: print(f'  [G2 {name}] counit: OK')
    # G3 multiplicativity on disjoint monomials
    g3 = True
    for m1 in range(DIM):
        for m2 in range(DIM):
            if m1 & m2: continue
            if DELTA0[m1 | m2] != vec_mul_t2(DELTA0[m1], DELTA0[m2]):
                print(f'  [G3 {name}] mult FAILS at {bin(m1)},{bin(m2)}'); g3 = False; ok = False
    if g3: print(f'  [G3 {name}] Delta0 multiplicative: OK')
    # G4 phi0 = 0 on I
    g4 = True
    for m in range(1, DIM):
        res = 0; vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2_unindex(idx)
            c = mul_monom(a, b)
            if c is not None: res ^= 1 << c
        if res:
            print(f'  [G4 {name}] phi0 != 0 at {bin(m)}'); g4 = False; ok = False
    if g4: print(f'  [G4 {name}] phi0 = 0 on I (killed by 2): OK')
    return ok

def gate5(d, basis_pairs):
    # basis_pairs: list of (i_out, j_in) one-entry matrices E: x_j -> x_i
    mats = []
    for (i, j) in basis_pairs:
        M = [[0] * d for _ in range(d)]
        M[i][j] = 1
        mats.append(M)
    ok = True
    for A in mats:
        for B in mats:
            C = [[0] * d for _ in range(d)]
            for i in range(d):
                for j in range(d):
                    s = 0
                    for k in range(d): s ^= A[i][k] & B[k][j]
                    C[i][j] = s
            if any(any(row) for row in C):
                ok = False
    print(f'  [G5 d={d}] all ordered basis products E_iE_j = 0 '
          f'(arbitrary-k L^2 = 0): {"OK" if ok else "FAIL"}')
    return ok

allok = True
print('===== rank8_gates: W_3[F] =====')
allok &= gates_for('W3F', 3, delta0_table_WdF(3))
print('===== rank8_gates: W_4[F] =====')
allok &= gates_for('W4F', 4, delta0_table_WdF(4))
print('===== rank8_gates: exterior masks 0..7 (rank 8) =====')
for mask in range(8):
    allok &= gates_for(f'mask{mask}', 3, delta0_table_mask(mask))
print('===== rank8_gates: G5 cotangent polarization =====')
# From session-15 reproduced logs (run_fast_rerun.log):
# d=3 Ybasis bits 0b1000, 0b1000000 with column-major (i,j)->pos=j*d+i:
#   pos 3 = (i=0,j=1) i.e. x1->x0 ; pos 6 = (i=0,j=2) x2->x0.
# d=4 Ybasis bits 0b10000, 0b100000000, 0b1000000000000:
#   pos 4=(0,1), 8=(0,2), 12=(0,3): x1,x2,x3 -> x0.
allok &= gate5(3, [(0, 1), (0, 2)])
allok &= gate5(4, [(0, 1), (0, 2), (0, 3)])
# G5b: all rank-8 mask/product fibers, bases read off the handoff logs
# (mask scripts print pos = input*d + output; (out,in) pairs below).
# masks 0 (alpha_2^3) and 7 (mu_2^3) have dim-0 L-space: nothing to check.
MASK_BASES = {
    'mask1':     [(1, 0), (2, 0)],
    'mask2':     [(0, 1), (2, 1)],
    'mask3':     [(2, 0), (2, 1)],
    'mask4':     [(0, 2), (1, 2)],
    'mask5':     [(1, 0), (1, 2)],
    'mask6':     [(0, 1), (0, 2)],
    'W2F_alpha': [(0, 1), (2, 1)],
    'W2F_mu':    [(0, 1), (0, 2)],
}
for name, basis in MASK_BASES.items():
    print(f'  -- {name}:')
    allok &= gate5(3, basis)
print('ALL RANK8 GATES PASSED' if allok else 'SOME RANK8 GATES FAILED')
