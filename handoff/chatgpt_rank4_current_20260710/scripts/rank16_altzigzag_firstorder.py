#!/usr/bin/env python3
"""rank16_altzigzag_firstorder.py — first-order cotangent PREFILTER for rank-16
killed-by-2 fibers, hunting the leading counterexample seed  Psi_1^4 != 0.

CONTEXT.  ChatGPT's DETAILED_HANDOFF_HIGHER_RANK_COUNTEREXAMPLE_DIRECTIONS §7
names the one rank-16 direction that Theorem R8-6 does NOT pre-empt: the
length-4 ALTERNATING zigzag Dieudonne fibers (both F,V != 0, a genuine
length-4 F/V string).  For rank 2^d the leading obstruction to killed-by-2^d
is  Psi_1^d = 0  (rank 16 => d = 4 => Psi_1^4).  Its "dream signal" is a
realizable first-order symbol L on the cotangent space I/I^2 with L^4 != 0.

WHAT THIS SCRIPT DOES (the §7 prefilter, done at arbitrary-k' strength).
For each candidate rank-16 killed-by-2 fiber it:
  1. gates the Hopf algebra (counit, coassoc, phi0 = mu.Delta0 = 0);
  2. builds the FULL first-order deformation linear system over F2
     (associativity, Delta-multiplicativity, coassociativity at digit 1),
     with variables mu_1 (mult) and w_1 = Delta_1 (comult, counital => in I(x)I);
  3. extracts L = symbol of Psi_1 on I/I^2 (a c x c matrix, c = #generators =
     cotangent dim), as the space of realizable matrices cut out by the
     linear relations;
  4. searches the realizable L-space for L^2, L^3, L^4 != 0.
Because the equations have F2 coefficients and L^k != 0 is checked at the
basis-product level, an "all L^k = 0" verdict is valid over EVERY F2-algebra
(handoff §3, §9.2): a genuine arbitrary-k' first-order theorem.

READING THE VERDICT.
  PREFILTER ONLY -- see the SOUNDNESS WARNING at the L^k search below.  Matrix
  powers of the generator-entry block are NOT Psi_1^k (Psi_1 does not preserve
  I^2), so nothing here is a verdict.  A long-Jordan-chain hit is a CANDIDATE to
  hand to the honest full-axiom Z3 composite test (rank16_c44_seed_z3.py);
  an all-short-chain sweep is (weak) evidence that no leading seed exists.
  The gates, by contrast, ARE sound: a Delta0 rejected by coassoc is not a
  coalgebra, which is how the "Jordan chain" fibers die (primitivity obstruction:
  a V-coupling m(x)m needs m primitive; in the exterior algebra only the socle
  generator is primitive -> star shape, never a chain).

The general monomial-algebra machinery (mixed-radix caps + MUL table) is
lifted verbatim from rank8_zigzag.py; the first-order solver + L^k search is
generalized from ChatGPT's rank16_firstorder_W4F.py (their exterior mul_monom
and hand-Witt Delta0 replaced by the general MUL table and the fiber's Delta0).

Run:  ~/.venvs/z3env/bin/python rank16_altzigzag_firstorder.py [fiber ...]
      (no z3 needed; pure F2 linear algebra.  default: all fibers.)
"""
import sys, time, itertools

T0 = time.time()

# ---------------- general monomial algebra (from rank8_zigzag.py) ----------
def make_fiber(caps):
    r = len(caps)
    strides = [1] * r
    for i in range(1, r):
        strides[i] = strides[i - 1] * caps[i - 1]
    DIM = strides[-1] * caps[-1]
    def idx_of(exps):
        return sum(e * s for e, s in zip(exps, strides))
    def exps_of(m):
        return [(m // strides[i]) % caps[i] for i in range(r)]
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
    strides = [1] * len(caps)
    for i in range(1, len(caps)):
        strides[i] = strides[i - 1] * caps[i - 1]
    return strides[which]

# ---------------- candidate fibers ----------------------------------------
# delta0: dict gen_index -> list of monomial-index pairs (p,q); the primitive
#         part (g,0),(0,g) MUST be listed explicitly.  Delta of a product is
#         the product of the generators' Delta0 (algebra map) -- built by dmono.
def build_fiber(name):
    if name == 'W4F':
        # rank-16 W_4[F]: exterior F2[x0..x3]/(xi^2), squarefree Witt addition.
        # BASELINE / cross-check: ChatGPT reports L^2 = 0 here (star shape).
        caps = (2, 2, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        # Witt terms in bitmask indices (index == bitmask since strides=1,2,4,8)
        delta0 = {
            1: [(1, 0), (0, 1)],
            2: [(2, 0), (0, 2), (1, 1)],
            4: [(4, 0), (0, 4), (3, 1), (1, 3), (2, 2)],
            8: [(8, 0), (0, 8), (7, 1), (3, 5), (5, 3), (1, 7), (6, 2), (2, 6), (4, 4)],
        }
    elif name == 'alpha2_4':
        # (alpha_2)^4 exterior, ALL primitive: phi0 = 0 trivially, L = 0.
        caps = (2, 2, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        delta0 = {gen_index(caps, i): [(gen_index(caps, i), 0), (0, gen_index(caps, i))]
                  for i in range(4)}
    elif name == 'AZ_X8Y2':
        # F2[X,Y]/(X^8,Y^2): F-chain X->X^2->X^4 (len 3) capped by V: V(Y)=X^4.
        # module {X,X^2,X^4,Y}, zigzag  X ->F X^2 ->F X^4 <-V Y   (length 4).
        caps = (8, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        X = idx_of([1, 0]); X4 = idx_of([4, 0]); Y = idx_of([0, 1])
        delta0 = {X: [(X, 0), (0, X)],
                  Y: [(Y, 0), (0, Y), (X4, X4)]}
    elif name == 'AZ_X4Y4_a':
        # F2[X,Y]/(X^4,Y^4): F:X->X^2, Y->Y^2; V:Y->X^2.
        # zigzag  X ->F X^2 <-V Y ->F Y^2   (length 4, alternating F,V,F).
        caps = (4, 4)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        X = idx_of([1, 0]); X2 = idx_of([2, 0]); Y = idx_of([0, 1])
        delta0 = {X: [(X, 0), (0, X)],
                  Y: [(Y, 0), (0, Y), (X2, X2)]}
    elif name == 'AZ_X4Y4_b':
        # F2[X,Y]/(X^4,Y^4), cross-coupled: V(X)=Y^2, V(Y)=X^2 (and F on both).
        # square:  X^2 <-F X ->V Y^2,  Y^2 <-F Y ->V X^2.
        caps = (4, 4)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        X = idx_of([1, 0]); X2 = idx_of([2, 0]); Y = idx_of([0, 1]); Y2 = idx_of([0, 2])
        delta0 = {X: [(X, 0), (0, X), (Y2, Y2)],
                  Y: [(Y, 0), (0, Y), (X2, X2)]}
    elif name == 'AZ_X4Y2Z2_star':
        # F2[X,Y,Z]/(X^4,Y^2,Z^2): F:X->X^2; V(Y)=X^2, V(Z)=X^2 (double sink).
        caps = (4, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        X = idx_of([1, 0, 0]); X2 = idx_of([2, 0, 0])
        Y = idx_of([0, 1, 0]); Z = idx_of([0, 0, 1])
        delta0 = {X: [(X, 0), (0, X)],
                  Y: [(Y, 0), (0, Y), (X2, X2)],
                  Z: [(Z, 0), (0, Z), (X2, X2)]}
    elif name == 'AZ_X4Y2Z2_chain':
        # F2[X,Y,Z]/(X^4,Y^2,Z^2): F:X->X^2; V(Y)=X^2; V(Z)=XY  (try a 2nd step).
        # XY is primitive?  gate will decide (Delta(XY)=Delta X * Delta Y).
        caps = (4, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        X = idx_of([1, 0, 0]); X2 = idx_of([2, 0, 0])
        Y = idx_of([0, 1, 0]); Z = idx_of([0, 0, 1]); XY = idx_of([1, 1, 0])
        delta0 = {X: [(X, 0), (0, X)],
                  Y: [(Y, 0), (0, Y), (X2, X2)],
                  Z: [(Z, 0), (0, Z), (XY, XY)]}
    elif name == 'W2F_W2F':
        # (W_2[F])^2 exterior, decomposable: V(x1)=x0, V(x3)=x2 (two V-arrows).
        caps = (2, 2, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        x0, x1, x2, x3 = 1, 2, 4, 8
        delta0 = {
            x0: [(x0, 0), (0, x0)],
            x1: [(x1, 0), (0, x1), (x0, x0)],
            x2: [(x2, 0), (0, x2)],
            x3: [(x3, 0), (0, x3), (x2, x2)],
        }
    elif name == 'W3F_a2':
        # W_3[F] x alpha_2 exterior, decomposable: rank-8 W3[F] chain + primitive x3.
        caps = (2, 2, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        x0, x1, x2, x3 = 1, 2, 4, 8
        x0x1 = idx_of([1, 1, 0, 0])
        delta0 = {
            x0: [(x0, 0), (0, x0)],
            x1: [(x1, 0), (0, x1), (x0, x0)],
            x2: [(x2, 0), (0, x2), (x0, x0x1), (x1, x1), (x0x1, x0)],
            x3: [(x3, 0), (0, x3)],
        }
    elif name == 'AZ_X8Y2_mid':
        # F2[X,Y]/(X^8,Y^2): F-chain X->X^2->X^4, V(Y)=X^2 branches off mid-chain.
        caps = (8, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        X = idx_of([1, 0]); X2 = idx_of([2, 0]); Y = idx_of([0, 1])
        delta0 = {X: [(X, 0), (0, X)],
                  Y: [(Y, 0), (0, Y), (X2, X2)]}
    elif name == 'AZ_X4Y4_c':
        # F2[X,Y]/(X^4,Y^4) mirror of _a: V(X)=Y^2, Y primitive.
        caps = (4, 4)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        X = idx_of([1, 0]); Y = idx_of([0, 1]); Y2 = idx_of([0, 2])
        delta0 = {X: [(X, 0), (0, X), (Y2, Y2)],
                  Y: [(Y, 0), (0, Y)]}
    elif name == 'AZ_X4Y2Z2_2V':
        # F2[X,Y,Z]/(X^4,Y^2,Z^2): F:X->X^2; V(Y)=X^2, V(Z)=Y? -> use X^2 & mixed.
        # Both Y,Z couple to X^2 but Z ALSO gets an X-primitive twist: V(Z)=X^2.
        # (indecomposable via shared sink X^2; a 3-gen genuine zigzag.)
        caps = (4, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        X = idx_of([1, 0, 0]); X2 = idx_of([2, 0, 0])
        Y = idx_of([0, 1, 0]); Z = idx_of([0, 0, 1])
        delta0 = {X: [(X, 0), (0, X)],
                  Y: [(Y, 0), (0, Y), (X2, X2)],
                  Z: [(Z, 0), (0, Z), (X, X), (X2, X2)]}
    elif name.startswith('c44_ca'):
        # ChatGPT's carry family: A0 = F2[a,b]/(a^4,b^4), Delta(a)=prim+C_a,
        # Delta(b)=prim+C_b, C in <a^2(x)a^2, b^2(x)b^2, a^2(x)b^2+b^2(x)a^2>.
        # name form 'c44_ca<X>_cb<Y>' with X,Y in 0..7 (bit0=PP,bit1=QQ,bit2=PQ+QP).
        import re
        mm = re.match(r'c44_ca(\d)_cb(\d)', name)
        ca, cb = int(mm.group(1)), int(mm.group(2))
        caps = (4, 4)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        a = idx_of([1, 0]); b = idx_of([0, 1])
        P = idx_of([2, 0]); Q = idx_of([0, 2])          # a^2, b^2
        carry = [[(P, P)], [(Q, Q)], [(P, Q), (Q, P)]]
        da = [(a, 0), (0, a)]; db = [(b, 0), (0, b)]
        for i in range(3):
            if (ca >> i) & 1: da += carry[i]
            if (cb >> i) & 1: db += carry[i]
        delta0 = {a: da, b: db}
    elif name == 'W4F_chain_try':
        # exterior F2[x0,x1,x2,x3]/(xi^2), ATTEMPT a Jordan chain
        # x1->x0, x2->x1, x3->x2 via couplings.  Only x0 is primitive, so the
        # x2/x3 couplings to non-primitives x1,x2 should FAIL coassoc (gate
        # rejects) -- this row demonstrates the primitivity obstruction.
        caps = (2, 2, 2, 2)
        DIM, strides, idx_of, exps_of, MUL = make_fiber(caps)
        x0, x1, x2, x3 = 1, 2, 4, 8
        delta0 = {
            x0: [(x0, 0), (0, x0)],
            x1: [(x1, 0), (0, x1), (x0, x0)],
            x2: [(x2, 0), (0, x2), (x1, x1)],
            x3: [(x3, 0), (0, x3), (x2, x2)],
        }
    else:
        raise ValueError(name)
    return name, caps, DIM, idx_of, exps_of, MUL, delta0

ALL_FIBERS = ['W4F', 'alpha2_4', 'W2F_W2F', 'W3F_a2',
              'AZ_X8Y2', 'AZ_X8Y2_mid', 'AZ_X4Y4_a', 'AZ_X4Y4_b', 'AZ_X4Y4_c',
              'AZ_X4Y2Z2_star', 'AZ_X4Y2Z2_2V',
              'AZ_X4Y2Z2_chain', 'W4F_chain_try']

# ---------------- online F2 row basis (from rank16_firstorder_W4F.py) -------
class RowBasis:
    def __init__(self): self.basis = {}; self.rank = 0
    def reduce(self, row):
        while row:
            p = (row & -row).bit_length() - 1
            b = self.basis.get(p)
            if b is None: return row
            row ^= b
        return 0
    def add(self, row):
        row = self.reduce(row)
        if row:
            p = (row & -row).bit_length() - 1
            self.basis[p] = row; self.rank += 1
            return True
        return False

# ---------------- per-fiber run --------------------------------------------
def run_fiber(name):
    name, caps, DIM, idx_of, exps_of, MUL, DELTA0_GEN = build_fiber(name)
    GENS = [gen_index(caps, i) for i in range(len(caps))]
    c = len(GENS)                                   # cotangent dimension
    I_BASIS = list(range(1, DIM))
    def mul_monom(a, b):
        m = MUL[a][b]
        return None if m < 0 else m
    def t2i(a, b): return a * DIM + b
    def t2u(i): return divmod(i, DIM)
    def t3i(a, b, c_): return (a * DIM + b) * DIM + c_
    T2 = DIM * DIM; T3 = DIM ** 3

    # ---- Delta0 as bitset over T2 ----
    def vmul_t2(u, v):
        res = 0; uu = u
        while uu:
            l = uu & -uu; i = l.bit_length() - 1; uu ^= l
            a, b = t2u(i); vv = v
            while vv:
                l2 = vv & -vv; j = l2.bit_length() - 1; vv ^= l2
                cc, e = t2u(j); ac = mul_monom(a, cc); be = mul_monom(b, e)
                if ac is not None and be is not None:
                    res ^= 1 << t2i(ac, be)
        return res
    DG = {}
    for g, terms in DELTA0_GEN.items():
        v = 0
        for (p, q) in terms: v ^= 1 << t2i(p, q)
        DG[g] = v
    def dmono(m):
        res = 1 << t2i(0, 0)
        for slot, e in enumerate(exps_of(m)):
            g = gen_index(caps, slot)
            for _ in range(e): res = vmul_t2(res, DG[g])
        return res
    DELTA0 = [dmono(m) for m in range(DIM)]

    # ---- gates: counit, coassoc, phi0 = 0 ----
    for m in range(DIM):
        left = right = 0; vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2u(idx)
            if a == 0: left ^= 1 << b
            if b == 0: right ^= 1 << a
        assert left == (1 << m) and right == (1 << m), f'{name}: counit FAIL at {exps_of(m)}'
    for m in range(DIM):
        lhs = rhs = 0; vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2u(idx); da = DELTA0[a]
            while da:
                l2 = da & -da; j = l2.bit_length() - 1; da ^= l2
                p, q = t2u(j); lhs ^= 1 << t3i(p, q, b)
            db = DELTA0[b]
            while db:
                l2 = db & -db; j = l2.bit_length() - 1; db ^= l2
                p, q = t2u(j); rhs ^= 1 << t3i(a, p, q)
        assert lhs == rhs, f'{name}: coassoc FAIL at {exps_of(m)}'
    for m in I_BASIS:
        res = 0; vv = DELTA0[m]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            a, b = t2u(idx); cc = mul_monom(a, b)
            if cc is not None: res ^= 1 << cc
        assert res == 0, f'{name}: NOT killed by 2 (phi0!=0) at {exps_of(m)}'
    nonext = any(cp > 2 for cp in caps)
    print(f'  gates OK (counit/coassoc/phi0=0); DIM={DIM} cotangent-dim c={c} '
          f'{"NON-exterior(F!=0)" if nonext else "exterior(F=0)"}', flush=True)

    # ---- first-order deformation variables ----
    # mu1[(a,b)][out], a<=b in I, out in I ;  w1[a][(p,q)], a in I, p,q in I.
    vars_list = []; vidx = {}
    def newvar(key):
        vidx[key] = len(vars_list); vars_list.append(key)
    pairs = [(a, b) for ii, a in enumerate(I_BASIS) for b in I_BASIS[ii:]]
    for (a, b) in pairs:
        for out in I_BASIS: newvar(('m', a, b, out))
    for a in I_BASIS:
        for p in I_BASIS:
            for q in I_BASIS: newvar(('d', a, p, q))
    NV = len(vars_list)

    def mu1_vec(a, b):                              # -> list over A (DIM) of bit-forms
        res = [0] * DIM
        if a == 0 or b == 0: return res
        if a > b: a, b = b, a
        for out in I_BASIS: res[out] = 1 << vidx[('m', a, b, out)]
        return res
    def d1_t2(a):                                   # -> list over T2 of bit-forms
        res = [0] * T2
        if a == 0: return res
        for p in I_BASIS:
            for q in I_BASIS: res[t2i(p, q)] = 1 << vidx[('d', a, p, q)]
        return res
    MU1 = {}
    def mu1c(a, b):
        if a > b: a, b = b, a
        v = MU1.get((a, b))
        if v is None: v = mu1_vec(a, b); MU1[(a, b)] = v
        return v
    D1 = {a: d1_t2(a) for a in [0] + I_BASIS}

    RB = RowBasis()
    def add_forms(vec):
        for f in vec:
            if f: RB.add(f)

    def A_add(u, v): return [u[i] ^ v[i] for i in range(len(u))]
    # constant monomial (m) times linear A-vector U
    def A_cmul_left(m, U):
        res = [0] * DIM
        if m == 0: return U[:]
        for i, f in enumerate(U):
            if f:
                cc = mul_monom(m, i)
                if cc is not None: res[cc] ^= f
        return res
    # mu1 on two constant monomials (bits sets) -- here single monomials
    def mu1_on_monoms(a, b):
        return mu1c(a, b)[:] if (a and b) else [0] * DIM
    # Delta0 applied to a linear A-vector -> T2
    def D0_on_A(U):
        res = [0] * T2
        for a, f in enumerate(U):
            if f:
                vv = DELTA0[a]
                while vv:
                    l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
                    res[idx] ^= f
        return res
    # constant T2 monomial-set c_bits (each idx = (a,b)) times linear T2 U (legwise mu0)
    def t2_cmul(c_bits, U, left=True):
        res = [0] * T2; cc = c_bits
        while cc:
            l = cc & -cc; idx = l.bit_length() - 1; cc ^= l
            a, b = t2u(idx)
            for j, f in enumerate(U):
                if f:
                    p, q = t2u(j)
                    ap = mul_monom(a, p) if left else mul_monom(p, a)
                    bq = mul_monom(b, q) if left else mul_monom(q, b)
                    if ap is not None and bq is not None: res[t2i(ap, bq)] ^= f
        return res
    # mu1-tensor on two constant T2 sets U_bits,V_bits -> T2  (legwise, one leg mu1)
    def mu1_tensor_const(U_bits, V_bits):
        res = [0] * T2; uu = U_bits
        while uu:
            l = uu & -uu; i = l.bit_length() - 1; uu ^= l
            a, b = t2u(i); vv = V_bits
            while vv:
                l2 = vv & -vv; j = l2.bit_length() - 1; vv ^= l2
                cc, d2 = t2u(j)
                bd = mul_monom(b, d2)
                if bd is not None:
                    for out, f in enumerate(mu1_on_monoms(a, cc)):
                        if f: res[t2i(out, bd)] ^= f
                ac = mul_monom(a, cc)
                if ac is not None:
                    for out, f in enumerate(mu1_on_monoms(b, d2)):
                        if f: res[t2i(ac, out)] ^= f
        return res
    def D0_tensor_id_lin(U):                        # (Delta0 (x) id) on linear T2 -> T3
        res = [0] * T3
        for idx, f in enumerate(U):
            if f:
                a, b = t2u(idx); vv = DELTA0[a]
                while vv:
                    l = vv & -vv; j = l.bit_length() - 1; vv ^= l
                    p, q = t2u(j); res[t3i(p, q, b)] ^= f
        return res
    def id_tensor_D0_lin(U):
        res = [0] * T3
        for idx, f in enumerate(U):
            if f:
                a, b = t2u(idx); vv = DELTA0[b]
                while vv:
                    l = vv & -vv; j = l.bit_length() - 1; vv ^= l
                    p, q = t2u(j); res[t3i(a, p, q)] ^= f
        return res
    def D1_tensor_id_const(C):                      # (D1 (x) id) on const T2 set -> T3
        res = [0] * T3; cc = C
        while cc:
            l = cc & -cc; idx = l.bit_length() - 1; cc ^= l
            a, b = t2u(idx); Da = D1[a]
            for j, f in enumerate(Da):
                if f:
                    p, q = t2u(j); res[t3i(p, q, b)] ^= f
        return res
    def id_tensor_D1_const(C):
        res = [0] * T3; cc = C
        while cc:
            l = cc & -cc; idx = l.bit_length() - 1; cc ^= l
            a, b = t2u(idx); Db = D1[b]
            for j, f in enumerate(Db):
                if f:
                    p, q = t2u(j); res[t3i(a, p, q)] ^= f
        return res

    # ---- equations ----
    # associativity (first order):  mu1(ab,c)+mu1(a,b)*c + mu1(a,bc)+a*mu1(b,c) = 0
    for a, b, cc in itertools.product(I_BASIS, repeat=3):
        res = [0] * DIM
        ab = mul_monom(a, b)
        if ab is not None and ab != 0: res = A_add(res, mu1c(ab, cc))
        res = A_add(res, A_cmul_left(cc, mu1c(a, b)))      # (a*b)_1 * c
        bc = mul_monom(b, cc)
        if bc is not None and bc != 0: res = A_add(res, mu1c(a, bc))
        res = A_add(res, A_cmul_left(a, mu1c(b, cc)))       # a * (b*c)_1
        add_forms(res)
    # Delta-multiplicativity (first order)
    for a, b in itertools.product(I_BASIS, repeat=2):
        ab = mul_monom(a, b)
        left = [0] * T2
        if ab is not None and ab != 0: left = A_add(left, D1[ab])
        left = A_add(left, D0_on_A(mu1c(a, b)))
        right = t2_cmul(DELTA0[b], D1[a], left=False)       # D1(a)*Delta0(b)
        right = A_add(right, t2_cmul(DELTA0[a], D1[b], left=True))
        right = A_add(right, mu1_tensor_const(DELTA0[a], DELTA0[b]))
        add_forms(A_add(left, right))
    # coassociativity (first order)
    for a in I_BASIS:
        left = A_add(D1_tensor_id_const(DELTA0[a]), D0_tensor_id_lin(D1[a]))
        right = A_add(id_tensor_D1_const(DELTA0[a]), id_tensor_D0_lin(D1[a]))
        add_forms(A_add(left, right))
    print(f'  first-order system: NV={NV}  rank={RB.rank}  '
          f'solution-dim={NV-RB.rank}  ({time.time()-T0:.1f}s)', flush=True)

    # ---- symbol Psi_1 on generators, reduced mod I^2 -> L matrix ----
    # psi1(a) = mu0.D1(a) + mu1.Delta0(a)      (valued in A)
    def psi1(a):
        res = [0] * DIM
        for idx, f in enumerate(D1[a]):
            if f:
                p, q = t2u(idx); m = mul_monom(p, q)
                if m is not None: res[m] ^= f
        vv = DELTA0[a]
        while vv:
            l = vv & -vv; idx = l.bit_length() - 1; vv ^= l
            p, q = t2u(idx)
            if p and q: res = A_add(res, mu1c(p, q))
        return res
    # L is c x c: rows = input gen, cols = output gen (mod I^2 == read at GENS)
    forms = []
    for gi in GENS:
        ps = psi1(gi)
        for go in GENS: forms.append(RB.reduce(ps[go]))
    # relations among the c*c reduced forms (linear syzygies over F2)
    def relations(rows):
        rows = rows[:]; trans = [1 << i for i in range(len(rows))]; rank = 0
        for col in range(NV):
            p = None
            for i in range(rank, len(rows)):
                if (rows[i] >> col) & 1: p = i; break
            if p is None: continue
            rows[rank], rows[p] = rows[p], rows[rank]
            trans[rank], trans[p] = trans[p], trans[rank]
            for i in range(len(rows)):
                if i != rank and ((rows[i] >> col) & 1):
                    rows[i] ^= rows[rank]; trans[i] ^= trans[rank]
            rank += 1
            if rank == len(rows): break
        rels = [trans[i] for i in range(rank, len(rows)) if rows[i] == 0]
        return rank, rels
    img_dim, rels = relations(forms)
    print(f'  realizable L-space: image-dim={img_dim} of {c*c} entries, '
          f'{len(rels)} relations', flush=True)

    # ---- search realizable L-space for L^k != 0  (k=2,3,4) ----
    def bits_to_mat(bits):
        M = [[0] * c for _ in range(c)]; pos = 0
        for j in range(c):
            for i in range(c):
                M[i][j] = (bits >> pos) & 1; pos += 1
        return M
    def matmul(A, B):
        C = [[0] * c for _ in range(c)]
        for i in range(c):
            for j in range(c):
                s = 0
                for kk in range(c): s ^= A[i][kk] & B[kk][j]
                C[i][j] = s
        return C
    def mnz(A): return any(A[i][j] for i in range(c) for j in range(c))
    def matpow(M, k):
        P = M
        for _ in range(k - 1): P = matmul(P, M)
        return P
    def nilp_index(M):
        # smallest k>=1 with M^k == 0, or None if not nilpotent (M^c != 0).
        P = M
        for k in range(1, c + 1):
            if not mnz(P): return k
            P = matmul(P, M)
        return None                                 # M^c != 0 => NOT nilpotent

    # !!! SOUNDNESS WARNING (rev. session 18 — the ORIGINAL rationale here was
    #     WRONG; see AUDIT_REPORT_GROTHENDIECK_..._2026-07-09.md §11 and
    #     THEORY_rank8 §1.  Kept and corrected, not deleted.) !!!
    #
    # CORRECTED PICTURE.  Under the FULL linearized axioms with a killed-by-2
    # fiber, the universal product-kill lemma (THEORY_rank8 §1, used by Thm
    # R8-1's own proof) gives Psi_1(I^2) = 0.  Hence the induced endomorphism
    # L of I/I^2 IS well-defined and L^k = Psi_1^k mod I^2: matrix powers of a
    # CORRECTLY computed entry block are meaningful.  The original text here
    # claimed the opposite ("mu_1 lowers degree, so Psi_1 does not preserve
    # I^2") — term-by-term reasoning; the mu_1.Delta_0 degree drop is exactly
    # cancelled through digit-1 multiplicativity of phi.  It also contradicted
    # banked Theorem R8-1 without noticing.
    #
    # THE REAL BUG in the c44 false positive (found by the 2026-07-09 external
    # audit): RowBasis.reduce above RETURNS EARLY at the first pivotless bit.
    # That is sound for membership tests (reduce(row)==0 iff row in span), but
    # the returned vector is NOT a canonical coset representative; treating
    # those outputs as a linear family corrupted the derived entry-relation
    # sets in ChatGPT's scanner (c44_ca1_cb1: reported image masks {5,10};
    # the true image is {0, all-ones}, and the all-ones 2x2 matrix squares to
    # 0 in char 2).  THIS SCRIPT computes `rels` with the same RowBasis
    # pattern, so any image DIMENSION or positive matrix signal below needs a
    # canonical-reduction rerun before being believed; negative rows are
    # conservative.
    #
    # Composite queries beyond the cotangent quotient (Psi_1^k as a full map
    # on A, mixed Psi-words) are bilinear in the unknowns and are decided by
    # honest Z3 (rank16_c44_seed_z3.py, rank16_leading_z3.py) or M2 ideal
    # membership — whose verdicts (no seeds; Psi_1^2 = 0 mod I^2, Psi_1^3 =
    # Psi_1^4 = 0) all STAND.  This script remains a PREFILTER, not a verdict.
    total = 0; max_nilp_idx = 1; nonnilp = 0; best = None
    for bits in range(1 << (c * c)):
        ok = True
        for r in rels:
            if (bits & r).bit_count() & 1: ok = False; break
        if not ok: continue
        total += 1
        M = bits_to_mat(bits)
        ni = nilp_index(M)
        if ni is None:
            nonnilp += 1
        elif ni > max_nilp_idx:
            max_nilp_idx = ni; best = M
    # max_nilp_idx = m  <=>  exists nilpotent realizable L with L^{m-1} != 0, L^m = 0.
    l2 = max_nilp_idx >= 3          # L^2 != 0 (nilpotent)
    l3 = max_nilp_idx >= 4          # L^3 != 0 (nilpotent, size-4 Jordan chain)
    print(f'  realizable matrices: {total} ({nonnilp} non-nilpotent: powers untrustworthy); '
          f'max NILPOTENT index={max_nilp_idx}  '
          f'=> L^2!=0(nilp): {"YES" if l2 else "no"}  '
          f'L^3!=0(nilp): {"YES" if l3 else "no"}', flush=True)
    if l3:
        print(f'  *** GENUINE LEADING SEED at fiber {name}: nilpotent L with '
              f'L^3 != 0 (size-4 Jordan chain), matrix={best} ***', flush=True)
    hits = {2: l2, 3: l3, 4: False, 'idx': max_nilp_idx, 'nonnilp': nonnilp}
    return name, c, hits


if __name__ == '__main__':
    fibers = sys.argv[1:] or ALL_FIBERS
    print(f'=== rank16_altzigzag_firstorder: {len(fibers)} fibers ===', flush=True)
    summary = []
    for fb in fibers:
        print(f'----- fiber {fb} -----', flush=True)
        try:
            nm, c, hits = run_fiber(fb)
            tag = 'SEED' if hits[3] else 'dead'
            summary.append((nm, c, hits['idx'], hits[2], hits[3], tag))
        except AssertionError as ex:
            print(f'  [fiber {fb} REJECTED by gates] {ex}', flush=True)
            summary.append((fb, '-', '-', '-', '-', 'REJECTED'))
    print('\n=== SUMMARY (rank-16 first-order leading prefilter; NILPOTENT L only) ===', flush=True)
    print(f'{"fiber":18} {"c":>3} {"nilpIdx":>7} {"L^2":>5} {"L^3":>5}  verdict', flush=True)
    for row in summary:
        nm, c, idx, l2, l3, tag = row
        def s(x): return x if isinstance(x, str) else ('YES' if x else 'no')
        print(f'{nm:18} {str(c):>3} {str(idx):>7} {s(l2):>5} {s(l3):>5}  {tag}', flush=True)
    print(f'DONE rank16_altzigzag_firstorder ({time.time()-T0:.1f}s)', flush=True)
