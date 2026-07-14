#!/usr/bin/env python3
r"""s4cert.py -- gate battery for the THIRD external handoff
(`order4_further_push_s4_t4.md`, received 2026-07-09 after the crash):
claimed closure of the s = 4 divided-[4] identity for the t^4 fiber,

    D4 := Psi1 Psi3 + Psi2 Psi2 + Psi3 Psi1 = 0,

via (i) aB = 0  [from the note's predecessor `order4_sustained_attempt_note.md`,
NOT on disk here -- unaudited dependency, gated below], (ii) Lambda = b B^2,
(iii) BC = 0, feeding the four-scalar reduction of THEORY 12.6.6(e).

Golden-rule-4 discipline: every displayed identity of the note is gated as a
negation-unsat query BEFORE any of it is banked.  Notation = THEORY 12.6.4 +
12.6.6(e); basis e1,e2,e3 = t,t^2,t^3; K-digits via digit(R,.,l):

  c1 = (w0 t)_{t (x) t^2},  c4 = (w0 t)_{t^2 (x) t^2}
  beta = w1 t, Y = w1 t^2, Theta = w1 t^3   (K-valued 3x3 matrices)
  gamma = w2 t, V = w2 t^2, U = w2 t^3
  p,p2,p3 = mu1(t,t);  q,q2,q3 = mu1(t,t^2);  u = mu1(t^2,t^2) = (a,b,a c1)
  v = mu2(t^2,t^2) = (v1,v2,v3);  z_t = mu3(t^2,t^2)_t
  B,C = (Psi1 t)_{t^2,t^3};  P,Q,R = Psi2 t;  lam = p c1 + p3 + a c1^2
  sigma2 = p p2 + q p3 + mu2(t,t)_t;  sigma3 = p q2 + q q3 + mu2(t,t^2)_t
  Lambda = (Psi3 t)_t + Q p + R q + B sigma2 + C sigma3

Rings:
  F2[eps]/eps^4          (KF2)   -- fast; catches coefficient-extraction errors
  (F2[u]/u^2)[eps]/eps^4 (KDual) -- NEW class ExtD below; kills the Frobenius
                                    collapse (over F2, B^3 = B for bits, so an
                                    F2 verdict cannot separate aB from aB^3;
                                    dual numbers can: B = B1 u gives B^3 = 0)
  F4[eps]/eps^4          (KF4)   -- expensive; run last, endpoint off by default

CAUTION on ExtD semantics: deform ranges over eps*R (the LAYERED fiber = mod-eps
semantics of THEORY 12.6), NOT over the maximal ideal m = (u, eps) -- u is a
coefficient-ring direction, not a deformation direction.  ExtD is therefore
DELIBERATELY not an order4sat-style Artin-local class and must NOT be added to
ringcheck CASES or used in killed-by-4 searches; it exists only for gating
k'-linear digit identities with k' = F2[u]/u^2.  Ring axioms + reference
multiplication are self-gated at startup (gate R0) instead.

D4/F2 full endpoint deliberately NOT rerun here: that is s4probe.py gate T2
(same encoding, running in parallel).  s4probe T3 ("a*B != 0 realizable",
discovery) is the same query as our G-aB gate over F2 -- verdicts must agree.
"""
import sys
from z3 import BitVec, BitVecVal, Solver, Or, And, simplify, is_true, set_param

sys.path.insert(0, ".")
from order4sat_beyond import F2epsN
from order4sat import Ext, fresh
from s2check import build_blocks
from s3gates import KF2, KF4

T4F = {(1, 1, 2): 1, (1, 2, 3): 1}
FAILED = [0]


class ExtD:
    """R[u]/(u^2): dual-number coefficient extension (see CAUTION above)."""
    def __init__(self, base):
        self.R = base
        self.name = base.name + "[u]/(u^2)"
    def zero(self): return (self.R.zero(), self.R.zero())
    def one(self):  return (self.R.one(),  self.R.zero())
    def var(self, tag): return (self.R.var(tag + "u"), self.R.var(tag + "v"))
    def add(self, x, y): return (self.R.add(x[0], y[0]), self.R.add(x[1], y[1]))
    def sub(self, x, y): return (self.R.sub(x[0], y[0]), self.R.sub(x[1], y[1]))
    def mul(self, x, y):
        u1, v1 = x; u2, v2 = y
        R = self.R
        return (R.mul(u1, u2), R.add(R.mul(u1, v2), R.mul(u2, v1)))
    def eq0(self, x):  return And(self.R.eq0(x[0]), self.R.eq0(x[1]))
    def neq0(self, x): return Or(self.R.neq0(x[0]), self.R.neq0(x[1]))
    def lowzero(self, x): return And(self.R.lowzero(x[0]), self.R.lowzero(x[1]))
    def deform(self, tag):
        return (self.R.deform(tag + "u"), self.R.deform(tag + "v"))


class KDual:
    """F2[u]/u^2, element = (a0, a1) pair of bits = a0 + a1 u."""
    name = "F2[u]/u^2"
    def zero(self): return (BitVecVal(0, 1), BitVecVal(0, 1))
    def one(self):  return (BitVecVal(1, 1), BitVecVal(0, 1))
    def add(self, a, b): return (a[0] ^ b[0], a[1] ^ b[1])
    def mul(self, a, b):
        return (a[0] & b[0], (a[0] & b[1]) ^ (a[1] & b[0]))
    def eq0(self, a):  return And(a[0] == 0, a[1] == 0)
    def neq0(self, a): return Or(a[0] != 0, a[1] != 0)


def digit_(R, x, l):
    if isinstance(R, (Ext, ExtD)):
        return (x[0][l], x[1][l])
    return x[l]


def gateR0_extd(R):
    """Self-gate for ExtD(F2epsN(N)): reference polynomial multiplication in
    F2[u,eps]/(u^2,eps^N) on integer masks vs R.mul, on ALL pairs from a
    generating sample; plus u^2 = 0 and eps^(N-1)*eps = 0."""
    N = R.R.n
    def to_masks(x):
        mu = sum(simplify(x[0][l]).as_long() << l for l in range(N))
        mv = sum(simplify(x[1][l]).as_long() << l for l in range(N))
        return mu, mv
    def of_masks(mu, mv):
        return (tuple(BitVecVal((mu >> l) & 1, 1) for l in range(N)),
                tuple(BitVecVal((mv >> l) & 1, 1) for l in range(N)))
    def polymul(m1, m2):
        out = 0
        for i in range(N):
            for j in range(N):
                if i + j < N and (m1 >> i) & 1 and (m2 >> j) & 1:
                    out ^= 1 << (i + j)
        return out
    def refmul(x, y):
        (u1, v1), (u2, v2) = to_masks(x), to_masks(y)
        return polymul(u1, u2), polymul(u1, v2) ^ polymul(v1, u2)
    # sample: 1, u, eps, u eps, eps^2, 1+u+eps, eps^3+u eps^2, 1+eps^3, u+u eps^3
    sample = [of_masks(a, b) for a, b in
              [(1, 0), (0, 1), (2, 0), (0, 2), (4, 0), (3, 1),
               (0, 4 | (1 << (N - 1)) * 0), (8, 0), (1 | 8, 0), (0, 1 | 8),
               (5, 3), (15, 15)]]
    bad = 0
    for x in sample:
        for y in sample:
            got = R.mul(x, y)
            if to_masks(got) != refmul(x, y):
                bad += 1
    uu = R.mul(of_masks(0, 1), of_masks(0, 1))
    ee = R.mul(of_masks(1 << (N - 1), 0), of_masks(2, 0))
    ok = (bad == 0 and to_masks(uu) == (0, 0) and to_masks(ee) == (0, 0))
    if not ok:
        FAILED[0] += 1
    print(f"  [R0 : ExtD reference-mult x{len(sample)**2}, u^2=0, "
          f"eps^{N-1}*eps=0] -> {'OK' if ok else 'FAILED -- STOP'}"
          f"  [{'GATE OK' if ok else 'GATE FAILED'}]", flush=True)


def run_ring(R, K, endpoint):
    print(f"===== s4cert over {R.name} =====", flush=True)
    if isinstance(R, ExtD):
        gateR0_extd(R)
        if FAILED[0]:
            print("===== R0 FAILED -- ABORT =====", flush=True)
            sys.exit(1)
    A, Mb, Cc_, F, phi, c, Mtab = build_blocks(R, T4F)
    base = A + Mb + Cc_ + F
    d = lambda x, l: digit_(R, x, l)
    M = lambda i, j, r: Mtab[(min(i, j), max(i, j), r)]
    kadd, kmul = K.add, K.mul

    def ksum(*xs):
        out = xs[0]
        for x in xs[1:]:
            out = kadd(out, x)
        return out

    def gate(label, zero_claims, expect="unsat"):
        s = Solver()
        s.set("timeout", 43200 * 1000)
        for e in base:
            s.add(e)
        s.add(Or(*[K.neq0(x) for x in zero_claims]))
        r = s.check()
        ok = (str(r) == expect)
        if not ok:
            FAILED[0] += 1
        tag = "GATE OK" if ok else f"GATE FAILED (expect {expect}) -- STOP"
        print(f"  [{label}] -> {r}  [{tag}]", flush=True)

    def probe(label, constraint, expect=None):
        s = Solver()
        s.set("timeout", 43200 * 1000)
        for e in base:
            s.add(e)
        s.add(constraint)
        r = s.check()
        note = f" (expect {expect})" if expect else " (discovery)"
        if expect and str(r) != expect:
            FAILED[0] += 1
            note += "  [GATE FAILED -- STOP]"
        print(f"  [{label}] -> {r}{note}", flush=True)

    P1 = {(i, r): d(phi[i][r], 1) for i in range(1, 4) for r in range(4)}
    P2 = {(i, r): d(phi[i][r], 2) for i in range(1, 4) for r in range(4)}
    P3 = {(i, r): d(phi[i][r], 3) for i in range(1, 4) for r in range(4)}

    c1 = d(c[(1, 1, 2)], 0); c4 = d(c[(1, 2, 2)], 0)
    beta = {(j, k): d(c[(1, j, k)], 1) for j in range(1, 4) for k in range(1, 4)}
    Y = {(j, k): d(c[(2, j, k)], 1) for j in range(1, 4) for k in range(1, 4)}
    Th = {(j, k): d(c[(3, j, k)], 1) for j in range(1, 4) for k in range(1, 4)}
    gam = {(j, k): d(c[(1, j, k)], 2) for j in range(1, 4) for k in range(1, 4)}
    V = {(j, k): d(c[(2, j, k)], 2) for j in range(1, 4) for k in range(1, 4)}
    U = {(j, k): d(c[(3, j, k)], 2) for j in range(1, 4) for k in range(1, 4)}

    p = d(M(1, 1, 1), 1); p2 = d(M(1, 1, 2), 1); p3 = d(M(1, 1, 3), 1)
    q = d(M(1, 2, 1), 1); q2 = d(M(1, 2, 2), 1); q3 = d(M(1, 2, 3), 1)
    a = d(M(2, 2, 1), 1); b = d(M(2, 2, 2), 1)
    v1 = d(M(2, 2, 1), 2); v2 = d(M(2, 2, 2), 2); v3 = d(M(2, 2, 3), 2)
    zt = d(M(2, 2, 1), 3)
    m2tt = d(M(1, 1, 1), 2); m2tt2 = d(M(1, 2, 1), 2)
    m2tt3 = d(M(1, 3, 1), 2); m2t2t3 = d(M(2, 3, 1), 2); m2t3t3 = d(M(3, 3, 1), 2)

    B, C = P1[(1, 2)], P1[(1, 3)]
    P, Q, Rr = P2[(1, 1)], P2[(1, 2)], P2[(1, 3)]
    lam = ksum(kmul(p, c1), p3, kmul(a, kmul(c1, c1)))
    sig2 = ksum(kmul(p, p2), kmul(q, p3), m2tt)
    sig3 = ksum(kmul(p, q2), kmul(q, q3), m2tt2)
    Lam = ksum(P3[(1, 1)], kmul(Q, p), kmul(Rr, q), kmul(B, sig2), kmul(C, sig3))
    ThT = ksum(q3, kmul(a, c4), kmul(b, c1))     # claimed value of Th12 = Th21

    probe("S0 : axioms sat", And(True), expect="sat")

    # -- formula consistency with the handoff's closed forms (THEORY 12.6.4) --
    gate("F1 : B = beta11 + c4 b", [ksum(B, beta[(1, 1)], kmul(c4, b))])
    gate("F2 : C = beta12 + beta21", [ksum(C, beta[(1, 2)], beta[(2, 1)])])

    # -- first-order facts (note SS2; E_T of SS3.3) --
    gate("G-T  : Theta12 = Theta21 = q3 + a c4 + b c1",
         [ksum(Th[(1, 2)], ThT), ksum(Th[(2, 1)], ThT)])
    gate("G-co0: beta13 = beta31 (order-1 coassoc, regate at eps^4)",
         [ksum(beta[(1, 3)], beta[(3, 1)])])
    gate("G-co1: beta23 = beta32", [ksum(beta[(2, 3)], beta[(3, 2)])])
    gate("G-co2: beta33 = beta11 c1^2",
         [ksum(beta[(3, 3)], kmul(beta[(1, 1)], kmul(c1, c1)))])
    gate("G-c4C: c4 C = 0 (note Lemma 2.2 step 1)", [kmul(c4, C)])

    # -- note Lemma 2.1: aC = 0 --
    gate("G-aC : a C = 0 (note Lemma 2.1)", [kmul(a, C)])

    # -- note Lemma 2.2: order-2 coassoc extractions and BC = 0 --
    E112 = ksum(gam[(1, 3)], kmul(Th[(1, 2)], beta[(1, 3)]), kmul(c4, V[(1, 1)]),
                kmul(c1, V[(1, 2)]), kmul(kmul(c1, c1), U[(1, 1)]),
                kmul(beta[(1, 2)], lam))
    E211 = ksum(gam[(3, 1)], kmul(Th[(2, 1)], beta[(3, 1)]), kmul(c4, V[(1, 1)]),
                kmul(c1, V[(2, 1)]), kmul(kmul(c1, c1), U[(1, 1)]),
                kmul(beta[(2, 1)], lam))
    E121 = ksum(gam[(1, 3)], gam[(3, 1)], kmul(Th[(1, 2)], beta[(3, 1)]),
                kmul(Th[(2, 1)], beta[(1, 3)]),
                kmul(c1, kadd(V[(1, 2)], V[(2, 1)])),
                kmul(beta[(1, 1)], C), kmul(C, lam))
    gate("G-E112: order-2 coassoc extraction (1,1,2)", [E112])
    gate("G-E211: order-2 coassoc extraction (2,1,1)", [E211])
    gate("G-E121: order-2 coassoc extraction (1,2,1)", [E121])
    gate("G-b11C: beta11 C = 0", [kmul(beta[(1, 1)], C)])
    gate("G-BC : B C = 0 (note Lemma 2.2)", [kmul(B, C)])

    # -- the MISSING predecessor note's claim (unaudited dependency) --
    gate("G-aB : a B = 0  [predecessor note, NOT on disk -- load-bearing]",
         [kmul(a, B)])
    gate("G-ab11: a beta11 = 0", [kmul(a, beta[(1, 1)])])

    # -- note SS3.1: layer-3 diagonal at t^2, coefficient (2,2) --
    g22 = []
    for pp in range(1, 4):
        for qq in range(1, 4):
            for rr in range(1, 4):
                for ss_ in range(1, 4):
                    w = kmul(Y[(pp, qq)], Y[(rr, ss_)])
                    g22.append(kmul(w, kadd(
                        kmul(d(M(pp, rr, 2), 1), d(M(qq, ss_, 2), 0)),
                        kmul(d(M(pp, rr, 2), 0), d(M(qq, ss_, 2), 1)))))
    gate("G-G22: Gamma_1(Y,Y) coefficient (2,2) = 0", [ksum(*g22)])
    gate("G-diag: c4 z_t = v1 b22 + v2 p c4 + v3 q c4 + a g22 + b V22 + a c1 U22",
         [ksum(kmul(c4, zt), kmul(v1, beta[(2, 2)]), kmul(v2, kmul(p, c4)),
               kmul(v3, kmul(q, c4)), kmul(a, gam[(2, 2)]), kmul(b, V[(2, 2)]),
               kmul(kmul(a, c1), U[(2, 2)]))])

    # -- note SS3.2: associativity values for mu2 t-components --
    gate("G-as1: mu2(t,t^3)_t = v1 + a p2 + q q2 + a q3",
         [ksum(m2tt3, v1, kmul(a, p2), kmul(q, q2), kmul(a, q3))])
    gate("G-as2: mu2(t^2,t^3)_t = a p + b q + a^2 c1 + q^2 + a q2",
         [ksum(m2t2t3, kmul(a, p), kmul(b, q), kmul(kmul(a, a), c1),
               kmul(q, q), kmul(a, q2))])
    gate("G-as3: mu2(t^3,t^3)_t = a b + a q",
         [ksum(m2t3t3, kmul(a, b), kmul(a, q))])

    # -- note SS3.3: layer-2 multiplicativity extractions at (2,2) --
    EV = ksum(V[(2, 2)], kmul(beta[(1, 1)], beta[(1, 1)]),
              kmul(p, beta[(2, 2)]), kmul(c4, m2tt),
              kmul(c4, kmul(p, p2)), kmul(c4, kmul(p3, q)),
              kmul(kmul(b, b), kmul(c4, c4)))
    EU = ksum(U[(2, 2)], V[(1, 2)], V[(2, 1)],
              kmul(a, kadd(beta[(2, 3)], beta[(3, 2)])),
              kmul(q2, kadd(beta[(1, 2)], beta[(2, 1)])),
              kmul(q, beta[(2, 2)]), kmul(c4, m2tt2),
              kmul(c4, kmul(p, q2)), kmul(c4, kmul(q, q3)))
    gate("G-EV : E_V = 0 (Delta(t t) = Delta t^2 at (2,2))", [EV])
    gate("G-EU : E_U = 0 (Delta(t t^2) = Delta t Delta t^2 at (2,2))", [EU])

    # -- note SS3 main identity and the two open scalars of 12.6.6(e) --
    gate("G-LAM: Lambda = b B^2  [MAIN]",
         [ksum(Lam, kmul(b, kmul(B, B)))])
    gate("G-LB : Lambda B = b B^3", [ksum(kmul(Lam, B), kmul(b, kmul(B, kmul(B, B))))])
    gate("G-LC : Lambda C = 0", [kmul(Lam, C)])

    # -- D4 assembly (THEORY 12.6.6(e)) --
    def d4comp(i, ss):
        terms = []
        for r in range(1, 4):
            terms.append(kmul(P1[(i, r)], P3[(r, ss)]))
            terms.append(kmul(P2[(i, r)], P2[(r, ss)]))
            terms.append(kmul(P3[(i, r)], P1[(r, ss)]))
        return ksum(*terms)
    gate("G-D4a: D4(t^2) = 0 (3 comps)", [d4comp(2, s_) for s_ in range(1, 4)])
    gate("G-D4b: D4(t^3) = 0 (3 comps)", [d4comp(3, s_) for s_ in range(1, 4)])
    gate("G-D4c: D4(t) = 0 (3 comps)", [d4comp(1, s_) for s_ in range(1, 4)])
    if endpoint:
        gate("G-D4 : FULL s=4 endpoint, all 9 components",
             [d4comp(i, s_) for i in range(1, 4) for s_ in range(1, 4)])

    # -- non-vacuity --
    probe("N1 : a != 0 realizable", K.neq0(a), expect="sat")
    probe("N2 : B != 0 realizable", K.neq0(B), expect="sat")
    probe("N3 : Lambda != 0 realizable", K.neq0(Lam))
    probe("N4 : b B^2 != 0 realizable", K.neq0(kmul(b, kmul(B, B))))


if __name__ == "__main__":
    set_param("parallel.enable", True)
    run_ring(F2epsN(4), KF2(), endpoint=False)   # F2 D4 endpoint = s4probe T2
    run_ring(ExtD(F2epsN(4)), KDual(), endpoint=True)
    if "--nof4" not in sys.argv:
        run_ring(Ext(F2epsN(4)), KF4(), endpoint=("--f4endpoint" in sys.argv))
    verdict = ("ALL S4CERT GATES PASSED" if FAILED[0] == 0
               else f"{FAILED[0]} GATE(S) FAILED")
    print(f"===== {verdict} =====", flush=True)
    print("DONE s4cert", flush=True)
