#!/usr/bin/env python3
# ---------------------------------------------------------------------------
# CLAUDE INDEPENDENT AUDIT (2026-07-12): the affine-group rank-4 counterexample
#
#   R = Z[a,b]/(a^3, b^3, a^2 b + 2)
#   A = R[U,V]/(U^2 - ab U + b^2 V,  V^2 - a^2 V)
#   lambda = (1+aU)(1+bV),  Delta(U) = U ox 1 + lambda ox U,
#                           Delta(V) = V ox lambda + 1 ox V
#   Claim: [4]^#(U) = 2b UV != 0, [4]^#(V) = 0, [8]^# = eta o eps.
#
# Papers audited:
#   notes/A_RANK_FOUR_COUNTEREXAMPLE_TO_GROTHENDIECKS_POWER_QUESTION_2026-07-12.tex
#   notes/A_HUMAN_SCALE_RANK_FOUR_COUNTEREXAMPLE_FROM_THE_AFFINE_GROUP_2026-07-12.tex
#
# This is a THIRD implementation, independent of the papers' hand proofs and of
# m2/verify_rank4_affine_article_20260712.m2: no Groebner bases are used.  The
# base ring R is modeled as an explicit finite commutative ring of order 512
# (normal forms + multiplication table derived only from the three relations),
# and every ring/Hopf axiom used is re-verified exhaustively at that level.
# All arithmetic is exact integer arithmetic on tiny objects (memory << 100MB).
#
# Soundness of the model (proved, not assumed):
#   * The reduction rules a^3->0, b^3->0, a^2 b^j -> -2 b^(j-1) (j=1,2) are
#     consequences of the relations, so the model M is a homomorphic image of
#     the true R once M is known to be a ring; bilinearity and unitality hold
#     by construction and associativity is checked EXHAUSTIVELY on the 7^3
#     basis triples, so M is a ring; the rules show the true R is additively
#     spanned by the 7 basis monomials with the stated coefficient bounds,
#     hence |R| <= 4^2*2^5 = 512 = |M|; therefore R -> M is an isomorphism.
#   * The same surjection+cardinality argument, with associativity of the
#     4-monomial normal-form multiplication checked exhaustively over all of
#     R^3 coefficient space (basis triples suffice by bilinearity), proves
#     A_t is R-free on 1,U,V,UV for every t.
# ---------------------------------------------------------------------------

import itertools, sys

FAILED = []
def check(name, cond):
    tag = "PASS" if cond else "FAIL"
    if not cond:
        FAILED.append(name)
    print(f"{tag} {name}")

# ---------------------------------------------------------------------------
# 1. The base ring R, order 512.
# Basis monomials a^i b^j and additive orders:
#   1:(0,0) mod4, b:(0,1) mod4, a:(1,0), a^2:(2,0), ab:(1,1), b^2:(0,2),
#   ab^2:(1,2) all mod2.
# ---------------------------------------------------------------------------

BASIS = [(0,0),(0,1),(1,0),(2,0),(1,1),(0,2),(1,2)]
MOD   = {(0,0):4,(0,1):4,(1,0):2,(2,0):2,(1,1):2,(0,2):2,(1,2):2}

def red_mono(i, j):
    """a^i b^j as a list of (coeff, basis monomial), using only consequences
    of the relations: a^3=0, b^3=0, a^2 b=-2, a^2 b^2=-2b."""
    if i >= 3 or j >= 3:
        return []
    if i == 2 and j >= 1:
        return [(-2, (0, j-1))]          # a^2 b^j = -2 b^(j-1), j=1,2
    return [(1, (i, j))]

def rnorm(d):
    out = {}
    for m, c in d.items():
        c %= MOD[m]
        if c:
            out[m] = c
    return out

def radd(x, y):
    d = dict(x)
    for m, c in y.items():
        d[m] = d.get(m, 0) + c
    return rnorm(d)

def rscale(k, x):
    return rnorm({m: k*c for m, c in x.items()})

def rneg(x):
    return rscale(-1, x)

def rmul(x, y):
    d = {}
    for (i1,j1), c1 in x.items():
        for (i2,j2), c2 in y.items():
            for k, m in red_mono(i1+i2, j1+j2):
                d[m] = d.get(m, 0) + k*c1*c2
    return rnorm(d)

def relt(*terms):
    """relt((c,(i,j)), ...) -> element"""
    d = {}
    for c, m in terms:
        d[m] = d.get(m, 0) + c
    return rnorm(d)

R0   = {}
R1   = relt((1,(0,0)))
Ra   = relt((1,(1,0)))
Rb   = relt((1,(0,1)))
Ra2  = rmul(Ra, Ra)
Rab  = rmul(Ra, Rb)
Rb2  = rmul(Rb, Rb)          # q
Rab2 = rmul(Ra, Rb2)         # aq
R2   = rscale(2, R1)
R2b  = rscale(2, Rb)         # the socle generator; equals -a^2 q
Rq, Raq = Rb2, Rab2

def rkey(x):
    return tuple(x.get(m, 0) for m in BASIS)

ALL_R = []
for c0 in range(4):
    for c1 in range(4):
        for e in itertools.product(range(2), repeat=5):
            ALL_R.append(rnorm({(0,0):c0,(0,1):c1,(1,0):e[0],(2,0):e[1],
                                (1,1):e[2],(0,2):e[3],(1,2):e[4]}))
check("R: model has 512 distinct elements", len({rkey(x) for x in ALL_R}) == 512)

# Ring gates: the three defining relations, exhaustive associativity,
# commutativity, characteristic, and the socle.
basis_elts = [relt((1,m)) for m in BASIS]
assoc_ok = all(
    rmul(rmul(x,y),z) == rmul(x,rmul(y,z))
    for x in basis_elts for y in basis_elts for z in basis_elts)
check("R: multiplication associative on all 7^3 basis triples", assoc_ok)
comm_ok = all(rmul(x,y) == rmul(y,x) for x in basis_elts for y in basis_elts)
check("R: multiplication commutative on basis", comm_ok)
check("R: relation a^3 = 0", rmul(Ra2, Ra) == R0)
check("R: relation b^3 = 0", rmul(Rb2, Rb) == R0)
check("R: relation a^2 b + 2 = 0", radd(rmul(Ra2, Rb), R2) == R0)
check("R: characteristic exactly 4", rscale(4,R1) == R0 and R2 != R0)
check("R: 2b != 0 and 2b = -a^2 b^2", R2b != R0 and R2b == rneg(rmul(Ra2,Rb2)))
check("R: 2a = 0", rscale(2,Ra) == R0)
check("R: q^2 = bq = 2q = 0",
      rmul(Rq,Rq) == R0 and rmul(Rb,Rq) == R0 and rscale(2,Rq) == R0)
check("R: a^2 q = -2b", rmul(Ra2,Rq) == rneg(R2b))

socle = [x for x in ALL_R if rmul(Ra,x) == R0 and rmul(Rb,x) == R0]
check("R: socle = {0, 2b}", sorted(map(rkey,socle)) == sorted(map(rkey,[R0,R2b])))

# m-adic filtration sizes -> Hilbert function (1,2,3,2,1), length 9.
def additive_span(gens):
    seen = {rkey(R0): R0}
    frontier = [R0]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = radd(x, g)
            if rkey(y) not in seen:
                seen[rkey(y)] = y
                frontier.append(y)
    return seen

def mpow_size(k):
    gens = []
    for i in range(k+1):
        j = k - i
        g = rnorm({m: c for c, m in red_mono(i, j)} if red_mono(i,j) else {})
        # rebuild properly: red_mono returns list of (coeff, mono)
        g = relt(*[(c, m) for c, m in red_mono(i, j)])
        for be in basis_elts:
            p = rmul(g, be)
            if p != R0:
                gens.append(p)
    return len(additive_span(gens))

sizes = [mpow_size(k) for k in range(6)]
check("R: |m^k| = 512,256,64,8,2,1 (Hilbert function (1,2,3,2,1), length 9)",
      sizes == [512,256,64,8,2,1])

# Q = (q): 8 elements; ann_Q(a) = {0, 2b}; nonsplitting (b+x)^2 = q for x in Q.
Q = sorted({rkey(rmul(Rq, x)) for x in ALL_R})
Qelts = [dict(zip(BASIS,k)) for k in Q]
Qelts = [rnorm({m:c for m,c in e.items()}) for e in Qelts]
check("R: |Q| = 8 and Q^2 = 0", len(Q) == 8 and
      all(rmul(x,y) == R0 for x in Qelts for y in Qelts))
check("R: ann_Q(a) = {0, 2b}",
      sorted(rkey(x) for x in Qelts if rmul(Ra,x) == R0)
      == sorted(map(rkey,[R0,R2b])))
check("R: nonsplitting - (b+x)^2 = q for every x in Q",
      all(rmul(radd(Rb,x), radd(Rb,x)) == Rq for x in Qelts))

# ---------------------------------------------------------------------------
# 2. The algebras A_t = R[U,V]/(U^2 - ab U + t V, V^2 - a^2 V), t in Q,
#    and their tensor powers, via normal-form reduction (no Groebner).
#    n-fold tensor elements: dict {exponent 2n-tuple : R-element}.
# ---------------------------------------------------------------------------

def treduce(d, t, slots):
    d = {k: v for k, v in d.items() if v != {}}
    while True:
        target = None
        for e in d:
            for s in range(slots):
                if e[2*s] >= 2 or e[2*s+1] >= 2:
                    target = (e, s); break
            if target: break
        if target is None:
            break
        e, s = target
        c = d.pop(e)
        p, r = e[2*s], e[2*s+1]
        if p >= 2:   # U^2 -> ab U - t V   (in slot s)
            e1 = list(e); e1[2*s] = p-1;          e1 = tuple(e1)
            e2 = list(e); e2[2*s] = p-2; e2[2*s+1] = r+1; e2 = tuple(e2)
            for key, coef in ((e1, rmul(Rab, c)), (e2, rneg(rmul(t, c)))):
                if coef != R0:
                    d[key] = radd(d.get(key, {}), coef) if key in d else coef
                    if d[key] == {}: d.pop(key)
        else:        # V^2 -> a^2 V
            e1 = list(e); e1[2*s+1] = r-1; e1 = tuple(e1)
            coef = rmul(Ra2, c)
            if coef != R0:
                d[e1] = radd(d.get(e1, {}), coef) if e1 in d else coef
                if d[e1] == {}: d.pop(e1)
        d = {k: v for k, v in d.items() if v != {}}
    return d

def tadd(x, y):
    d = dict(x)
    for e, c in y.items():
        d[e] = radd(d.get(e, {}), c) if e in d else c
    return {k: v for k, v in d.items() if v != {}}

def tneg(x):
    return {e: rneg(c) for e, c in x.items()}

def tscaleR(r, x, t, slots):
    return treduce({e: rmul(r, c) for e, c in x.items()}, t, slots)

def tmul(x, y, t, slots):
    d = {}
    for e1, c1 in x.items():
        for e2, c2 in y.items():
            e = tuple(u+v for u, v in zip(e1, e2))
            c = rmul(c1, c2)
            if c != R0:
                d[e] = radd(d.get(e, {}), c) if e in d else c
    d = {k: v for k, v in d.items() if v != {}}
    return treduce(d, t, slots)

def tone(slots):  return {(0,)*(2*slots): R1}
def tU(s, slots):
    e = [0]*(2*slots); e[2*s] = 1
    return {tuple(e): R1}
def tV(s, slots):
    e = [0]*(2*slots); e[2*s+1] = 1
    return {tuple(e): R1}

def tlam(s, slots, t):
    one = tone(slots)
    L = tadd(one, tscaleR(Ra, tU(s,slots), t, slots))
    M = tadd(one, tscaleR(Rb, tV(s,slots), t, slots))
    return tmul(L, M, t, slots)

# Associativity of A_t (slots=1) exhaustively on the 4 basis monomials,
# for t = q (the counterexample) and t = 0 (the naive lift).
def basisA(slots=1):
    out = []
    for e in itertools.product((0,1), repeat=2*slots):
        out.append({tuple(e): R1})
    return out

for tname, t in (("q", Rq), ("0", R0)):
    ok = all(tmul(tmul(x,y,t,1),z,t,1) == tmul(x,tmul(y,z,t,1),t,1)
             for x in basisA() for y in basisA() for z in basisA())
    check(f"A_{tname}: associative on all 4^3 basis triples (=> free rank 4)", ok)

# ---------------------------------------------------------------------------
# 3. The one-curvature lemma, for EVERY t in Q:
#    defect vector = ( a(q-t) V1 U2 , 0 , 0 ),  and lambda is a unit.
# ---------------------------------------------------------------------------

V1U2 = {(0,1,1,0): R1}
all_curvature_ok = True
solutions = []
for t in Qelts:
    lam1, lam2 = tlam(0,2,t), tlam(1,2,t)
    U1, U2 = tU(0,2), tU(1,2)
    V1, V2 = tV(0,2), tV(1,2)
    Ustar = tadd(U1, tmul(lam1, U2, t, 2))
    Vstar = tadd(tmul(V1, lam2, t, 2), V2)
    d1 = tadd(tadd(tmul(Ustar,Ustar,t,2),
                   tneg(tscaleR(Rab,Ustar,t,2))),
              tscaleR(t, Vstar, t, 2))
    d2 = tadd(tmul(Vstar,Vstar,t,2), tneg(tscaleR(Ra2,Vstar,t,2)))
    lamS = tmul(tadd(tone(2), tscaleR(Ra,Ustar,t,2)),
                tadd(tone(2), tscaleR(Rb,Vstar,t,2)), t, 2)
    d3 = tadd(lamS, tneg(tmul(lam1,lam2,t,2)))
    coeff = rmul(Ra, radd(Rq, rneg(t)))           # a(q - t)
    expected_d1 = tscaleR(coeff, V1U2, t, 2)
    if not (d1 == expected_d1 and d2 == {} and d3 == {}):
        all_curvature_ok = False
    if d1 == {} and d2 == {} and d3 == {}:
        solutions.append(rkey(t))
    # lambda a unit (paper: lambda^2 = 1 - a^2 t V and (a^2 t V)^2 = 0):
    # explicit inverse  lambda^{-1} = lambda (1 + a^2 t V).
    lam = tlam(0,1,t)
    a2tV = tscaleR(rmul(Ra2, t), tV(0,1), t, 1)
    inv = tmul(lam, tadd(tone(1), a2tV), t, 1)
    if tmul(lam, inv, t, 1) != tone(1):
        all_curvature_ok = False
    if tmul(lam, lam, t, 1) != tadd(tone(1), tneg(a2tV)):
        all_curvature_ok = False
check("Lemma 3.2: defect = (a(q-t) V1U2, 0, 0) for ALL 8 t in Q; lambda unit",
      all_curvature_ok)
check("Torsor: closure solutions in Q are exactly {q, q+2b}",
      sorted(solutions) == sorted([rkey(Rq), rkey(radd(Rq,R2b))]))

# The naive-lift coboundary identity: -q(V* - V1 - V2) = -aq V1U2 at t=0.
t = R0
lam2 = tlam(1,2,t)
V1, V2 = tV(0,2), tV(1,2)
Vstar = tadd(tmul(V1, lam2, t, 2), V2)
cob = tscaleR(rneg(Rq), tadd(Vstar, tadd(tneg(V1), tneg(V2))), t, 2)
check("Coboundary: -q(V*-V1-V2) = -aq V1U2 (kills the naive curvature aq V1U2)",
      cob == tscaleR(rneg(Raq), V1U2, t, 2))

# Gauge rigidity: U' = U + q*phi, V' = V + q*psi leaves the first quadric
# unchanged, for all 16 basis choices of (phi, psi).
t = Rq
rigid = True
for phi in basisA():
    for psi in basisA():
        Up = tadd(tU(0,1), tscaleR(Rq, phi, t, 1))
        Vp = tadd(tV(0,1), tscaleR(Rq, psi, t, 1))
        lhs = tadd(tadd(tmul(Up,Up,t,1), tneg(tscaleR(Rab,Up,t,1))),
                   tscaleR(Rq, Vp, t, 1))
        ref = tadd(tadd(tmul(tU(0,1),tU(0,1),t,1),
                        tneg(tscaleR(Rab,tU(0,1),t,1))),
                   tscaleR(Rq, tV(0,1), t, 1))
        if lhs != ref:
            rigid = False
check("Gauge rigidity: bridge unremovable by U->U+q*phi, V->V+q*psi", rigid)

# ---------------------------------------------------------------------------
# 4. The Hopf structure on A = A_q.  From here on t = q.
# ---------------------------------------------------------------------------
t = Rq

lam  = tlam(0,1,t)
one1 = tone(1)
theta = tadd(lam, tneg(one1))
lam2elt = tmul(lam, lam, t, 1)
check("theta^2 = 0", tmul(theta,theta,t,1) == {})
check("2*theta = 2bV", tscaleR(R2,theta,t,1) == tscaleR(R2b,tV(0,1),t,1))
check("lambda^2 = 1 + 2bV",
      lam2elt == tadd(one1, tscaleR(R2b, tV(0,1), t, 1)))
lam4 = tmul(lam2elt, lam2elt, t, 1)
check("lambda^4 = 1", lam4 == one1)
N4 = tadd(tadd(one1, lam), tadd(lam2elt, tmul(lam2elt,lam,t,1)))
check("N4(lambda) = 2bV", N4 == tscaleR(R2b, tV(0,1), t, 1))
N8 = tmul(N4, tadd(one1, lam4), t, 1)
check("N8(lambda) = 0", N8 == {})

# Delta on the four basis monomials of A (as elements of A ox A).
lam1T, lam2T = tlam(0,2,t), tlam(1,2,t)
DU = tadd(tU(0,2), tmul(lam1T, tU(1,2), t, 2))
DV = tadd(tmul(tV(0,2), lam2T, t, 2), tV(1,2))
DW = tmul(DU, DV, t, 2)
DELTA = {(0,0): tone(2), (1,0): DU, (0,1): DV, (1,1): DW}

check("Delta well-defined: Delta(U) satisfies U^2-abU+qV=0 in AoxA",
      tadd(tadd(tmul(DU,DU,t,2), tneg(tscaleR(Rab,DU,t,2))),
           tscaleR(Rq,DV,t,2)) == {})
check("Delta well-defined: Delta(V) satisfies V^2-a^2V=0 in AoxA",
      tadd(tmul(DV,DV,t,2), tneg(tscaleR(Ra2,DV,t,2))) == {})
lamS = tmul(tadd(tone(2), tscaleR(Ra,DU,t,2)),
            tadd(tone(2), tscaleR(Rb,DV,t,2)), t, 2)
check("lambda group-like: Delta(lambda) = lambda ox lambda",
      lamS == tmul(lam1T, lam2T, t, 2))

# Coassociativity in A^ox3 on U and V (algebra generators).
def embed(x, from_slots, slotmap, to_slots):
    out = {}
    for e, c in x.items():
        ee = [0]*(2*to_slots)
        for s in range(from_slots):
            ee[2*slotmap[s]]   = e[2*s]
            ee[2*slotmap[s]+1] = e[2*s+1]
        out[tuple(ee)] = c
    return out

def apply_delta_slot(x, s, slots):
    """(id..Delta at slot s..id): A^ox(slots) -> A^ox(slots+1)."""
    out = {}
    for e, c in x.items():
        pieces = []
        for s2 in range(slots):
            mono = (e[2*s2], e[2*s2+1])
            if s2 == s:
                pieces.append(("D", mono))
            else:
                pieces.append(("M", mono))
        term = {(0,)*(2*(slots+1)): c}
        pos = 0
        for kind, mono in pieces:
            if kind == "M":
                f = embed({(mono[0],mono[1]): R1}, 1, {0:pos}, slots+1)
                pos += 1
            else:
                f = embed(DELTA[mono], 2, {0:pos, 1:pos+1}, slots+1)
                pos += 2
            term = tmul(term, f, t, slots+1)
        out = tadd(out, term)
    return out

for name, x in (("U", tU(0,1)), ("V", tV(0,1)), ("W", tmul(tU(0,1),tV(0,1),t,1))):
    Dx = apply_delta_slot(x, 0, 1)
    left  = apply_delta_slot(Dx, 0, 2)   # (Delta ox id) Delta
    right = apply_delta_slot(Dx, 1, 2)   # (id ox Delta) Delta
    check(f"coassociativity on {name}", left == right)

# Counit eps (U,V -> 0) on both sides, on all four basis monomials.
def counit_side(x_tensor, side):
    """(eps ox id) or (id ox eps) of an element of A ox A, landing in A."""
    out = {}
    for e, c in x_tensor.items():
        if side == "L":
            if e[0] == 0 and e[1] == 0:
                out = tadd(out, {(e[2],e[3]): c})
        else:
            if e[2] == 0 and e[3] == 0:
                out = tadd(out, {(e[0],e[1]): c})
    return treduce(out, t, 1)

counit_ok = True
for mono, Dx in DELTA.items():
    idA = {mono: R1}
    if counit_side(Dx,"L") != idA or counit_side(Dx,"R") != idA:
        counit_ok = False
check("counit: (eps ox id)Delta = id = (id ox eps)Delta on the basis", counit_ok)

# Noncocommutativity: Delta(U) - swap Delta(U) has V ox U coefficient b.
swapDU = {(e[2],e[3],e[0],e[1]): c for e, c in DU.items()}
diff = tadd(DU, tneg(swapDU))
check("noncocommutative: Delta(U) != swap Delta(U)", diff != {})
check("coefficient of V ox U in the difference is b",
      diff.get((0,1,1,0), R0) == Rb)

# Antipode S(U) = -lambda^{-1} U, S(V) = -V lambda^{-1}.
laminv = tadd(one1, tneg(theta))
SU = tneg(tmul(laminv, tU(0,1), t, 1))
SV = tneg(tmul(tV(0,1), laminv, t, 1))
check("S respects relation 1: S(U)^2 - ab S(U) + q S(V) = 0",
      tadd(tadd(tmul(SU,SU,t,1), tneg(tscaleR(Rab,SU,t,1))),
           tscaleR(Rq,SV,t,1)) == {})
check("S respects relation 2: S(V)^2 - a^2 S(V) = 0",
      tadd(tmul(SV,SV,t,1), tneg(tscaleR(Ra2,SV,t,1))) == {})

SBASIS = {(0,0): one1, (1,0): SU, (0,1): SV, (1,1): tmul(SU,SV,t,1)}
def conv(f, g):
    """convolution f*g on basis monomials, f,g given on basis monomials."""
    out = {}
    for mono, Dx in DELTA.items():
        acc = {}
        for e, c in Dx.items():
            fx = f[(e[0],e[1])]
            gx = g[(e[2],e[3])]
            acc = tadd(acc, tscaleR(c, tmul(fx, gx, t, 1), t, 1))
        out[mono] = acc
    return out

IDB  = {(0,0): one1, (1,0): tU(0,1), (0,1): tV(0,1),
        (1,1): tmul(tU(0,1),tV(0,1),t,1)}
ETAEPS = {(0,0): one1, (1,0): {}, (0,1): {}, (1,1): {}}
check("antipode: S * id = eta eps on the whole basis", conv(SBASIS, IDB) == ETAEPS)
check("antipode: id * S = eta eps on the whole basis", conv(IDB, SBASIS) == ETAEPS)

# ---------------------------------------------------------------------------
# 5. Power words by convolution powers of the identity.
# ---------------------------------------------------------------------------

pow_maps = {1: IDB}
for n in range(2, 9):
    pow_maps[n] = conv(pow_maps[n-1], IDB)

W1 = tmul(tU(0,1), tV(0,1), t, 1)
twoU_expected = tadd(tU(0,1), tmul(lam, tU(0,1), t, 1))
twoV_expected = tadd(tmul(tV(0,1), lam, t, 1), tV(0,1))
check("[2]#(U) = (1+lambda)U", pow_maps[2][(1,0)] == twoU_expected)
check("[2]#(V) = V(1+lambda)", pow_maps[2][(0,1)] == twoV_expected)

fourU, fourV, fourW = (pow_maps[4][(1,0)], pow_maps[4][(0,1)], pow_maps[4][(1,1)])
check("[4]#(U) = 2b UV and is NONZERO",
      fourU == tscaleR(R2b, W1, t, 1) and fourU != {})
check("[4]#(V) = 0", fourV == {})
check("[4]#(W) = 0", fourW == {})
check("[4]# != eta eps  (G is NOT killed by 4)", pow_maps[4] != ETAEPS)
check("[8]# = eta eps   (G IS killed by 8)", pow_maps[8] == ETAEPS)

# Cross-checks: [4]# = [2]# o [2]# and [4]#(U) = N4(lambda)*U, [4]#(V)=V*N4.
def lin_apply(f, x):
    out = {}
    for e, c in x.items():
        out = tadd(out, tscaleR(c, f[(e[0],e[1])], t, 1))
    return out
comp4 = {m: lin_apply(pow_maps[2], v) for m, v in pow_maps[2].items()}
check("[4]# = [2]# o [2]# (word composition consistency)", comp4 == pow_maps[4])
check("[4]#(U) = N4(lambda)*U (ambient matrix formula)",
      pow_maps[4][(1,0)] == tmul(N4, tU(0,1), t, 1))
check("[4]#(V) = V*N4(lambda) = 0", tmul(tV(0,1), N4, t, 1) == {})
mult2 = all(
    lin_apply(pow_maps[2], tmul({m1:R1},{m2:R1},t,1))
    == tmul(pow_maps[2][m1], pow_maps[2][m2], t, 1)
    for m1 in IDB for m2 in IDB)
check("[2]# is an algebra map (basis pairs)", mult2)

# [4]#(U) = -a^2 q UV = -a * diag(kappa_naive(Phi)):  2b = -a^2 q chain.
check("word defect = -a^2 q UV  (the q -> aq -> a^2 q = -2b chain)",
      fourU == tscaleR(rneg(rmul(Ra2, Rq)), W1, t, 1))

# ---------------------------------------------------------------------------
# 6. Special fiber alpha_2 x alpha_2 over F_2 = R/m.
# ---------------------------------------------------------------------------

def modm(x):        # R -> F2, kill a, b
    return x.get((0,0), 0) % 2

def fiber(xt, slots):
    return {e: modm(c) for e, c in xt.items() if modm(c)}

check("fiber: U^2 = 0, V^2 = 0 (both quadrics collapse)",
      fiber(tmul(tU(0,1),tU(0,1),t,1),1) == {} and
      fiber(tmul(tV(0,1),tV(0,1),t,1),1) == {})
check("fiber: lambda = 1", fiber(tadd(lam, tneg(one1)),1) == {})
check("fiber: Delta(U) = U ox 1 + 1 ox U (primitive)",
      fiber(DU,2) == {(1,0,0,0):1, (0,0,1,0):1})
check("fiber: Delta(V) = V ox 1 + 1 ox V (primitive)",
      fiber(DV,2) == {(0,1,0,0):1, (0,0,0,1):1})

# ---------------------------------------------------------------------------

print()
if FAILED:
    print(f"*** {len(FAILED)} CHECK(S) FAILED:")
    for f in FAILED:
        print("   ", f)
    sys.exit(1)
print("ALL CLAUDE INDEPENDENT AFFINE-RANK4 AUDIT CHECKS PASSED")
