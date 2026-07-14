#!/usr/bin/env python3
r"""s3xy2gates.py -- session-10 lemma-level machine gates for the s = 3
layer identity, xy fiber (THEORY 12.6.5-to-be; endpoint battery is
s3xygates.py, this file gates every STEP of the hand proof).

Basis e1 = x, e2 = y, e3 = z = xy; I^2 = k'z; all squares in I vanish.
R = k'[eps]/eps^3 (k' = F2 and F4), fiber2, mu = mu0+eps mu1+eps^2 mu2,
w = w0+eps w1+eps^2 w2, Psi1 = mu0 w1 + mu1 w0, Psi2 = mu0 w2 + mu1 w1 + mu2 w0.

Universal lemmas (no pin on Delta_0):
  H1 (12.1.1 layers)  Psi1(z) = 0; counit rows of Psi1, Psi2 vanish.
  H2 (L2 Hochschild)  mu1(x,z), mu1(y,z) in I^2; mu1(z,z) = 0.
  H3 (X1)             Psi1(mu1(x,x)) = 0 and Psi1(mu1(y,y)) = 0
                      (layer-2 multiplicativity at (a,a), mu0(a,a)=0,
                       (Psi1 a)^2 = 0 since all I-squares vanish).
  H4 (Step 1 at z)    Psi2(z) = Psi1(mu1(x,y)) + Psi1(x)Psi1(y)
                      (cross-validates s3xygates GXm).

Pinned split models (digit-0 of w0 pinned per 12.4.1; k' contains the
needed field of definition -- F2 suffices for all four split tables):
  a2a2   A1 Psi1(x),Psi1(y) in I^2; mu1(x,x),mu1(y,y) have no z-comp.
         A3 X2-at-x: a1*w1x + a2*w1y = w0(mu2(x,x))  (full matrix).
         A9 endpoint.
  W2F    B1 Psi1(x) = 0 exactly; Psi1(y) = lam*x exactly (c_y = 0 is NEW).
         B2 mu1(x,x) = lam x, mu1(y,y) = nu x (shape).
         B3 L4-at-x: c_x = 0; (w1x)22 = (w1x)13 = (w1x)31;
            (w1x)23 = (w1x)32 = (w1x)33 = 0.
         B4 X2-at-x: w0(mu2(x,x)) = lam*w1x  (full matrix; key entry
            lam*(w1x)22 = 0).
         B5 X2-at-y: w0(mu2(y,y)) = nu*w1x + lam^2 x@x  (key entry
            nu*(w1x)22 = 0).
         B6 L4'-at-x (order-2 coassoc, x@x@x): c2_x = 0.
         B9 endpoint; BN discovery (lam, nu, lam*nu realizable).
  mu2mu2 C1 mu1(x,x) = mu1(y,y) = 0 (Prim = 0).
         C2 mu2(x,x) = mu2(y,y) = 0 (X2 + Prim = 0).
         C3 Psi1(x), Psi1(y) in I^2.   C9 endpoint.
  mu2a2  E1 Psi1(y) = 0 exactly; Psi1(x) = lam*y exactly (c_x = 0 is NEW).
         E2 mu1(x,x) = lam y, mu1(y,y) = nu y (shape).
         E3 L4-at-x: c_x = 0, (w1x)13 = (w1x)31 = 0.
         E4 L4-at-y: c_y = 0; (w1y)12 = (w1y)21 = (w1y)13 = (w1y)31;
            (w1y)23 = (w1y)32 = (w1y)33 = 0.
         E5 X2-at-x: w0(mu2(x,x)) = lam*w1y + lam^2 y@y  (key entry
            lam*(w1y)22 = lam^2).
         E6 X2-at-y: w0(mu2(y,y)) = nu*w1y  (key entry nu*(w1y)22 = 0).
         E7 L4'-at-y (x@x@y, y@x@x, x@y@x): c2_y = 0.
         E8 nu*lam^2 = 0 (the dangerous product; follows from E5+E6).
         E9 endpoint; EN discovery (lam, nu, lam*(w1y)11 realizable).

Every gate asserts axioms (+pin) plus the NEGATION of one lemma and must be
unsat over BOTH F2[eps]/eps^3 and F4[eps]/eps^3.  A sat on a gate = the hand
proof is wrong there; the model is the counterexample (golden rule 1).
Builder = s2check.build_blocks (gate-validated); digit machinery = s3gates.
"""
import sys
from z3 import Solver, Or, And, sat, unsat, set_param

sys.path.insert(0, ".")
from order4sat import F2eps3, Ext
from s2check import build_blocks
from s3gates import KF2, KF4, digit

XY = {(1, 2, 3): 1}
FAILED = [0]

CASES = {
    "a2a2":   {(3, 1, 2), (3, 2, 1)},
    "W2F":    {(2, 1, 1), (3, 1, 2), (3, 2, 1)},
    "mu2mu2": {(1, 1, 1), (2, 2, 2), (3, 1, 2), (3, 2, 1), (3, 1, 3),
               (3, 3, 1), (3, 2, 3), (3, 3, 2), (3, 3, 3)},
    "mu2a2":  {(1, 1, 1), (3, 1, 2), (3, 2, 1), (3, 1, 3), (3, 3, 1)},
}


def run(R, K):
    print(f"===== s3xy2gates over {R.name} =====", flush=True)
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, XY)
    base = A + Mb + C + F

    d = lambda x, l: digit(R, x, l)
    M = lambda i, j, r: Mtab[(min(i, j), max(i, j), r)]
    kadd, kmul = K.add, K.mul

    def ksum(*xs):
        out = xs[0]
        for x in xs[1:]:
            out = kadd(out, x)
        return out

    def keq(x, y):
        return K.eq0(K.add(x, y))

    P1 = {(i, r): d(phi[i][r], 1) for i in range(1, 4) for r in range(4)}
    P2 = {(i, r): d(phi[i][r], 2) for i in range(1, 4) for r in range(4)}
    w1 = {(i, j, k): d(c[(i, j, k)], 1)
          for i in range(1, 4) for j in range(1, 4) for k in range(1, 4)}
    w2 = {(i, j, k): d(c[(i, j, k)], 2)
          for i in range(1, 4) for j in range(1, 4) for k in range(1, 4)}
    cx1 = kadd(w1[(1, 1, 2)], w1[(1, 2, 1)])   # z-coeff of mu0(w1 x)
    cy1 = kadd(w1[(2, 1, 2)], w1[(2, 2, 1)])
    cx2 = kadd(w2[(1, 1, 2)], w2[(1, 2, 1)])   # z-coeff of mu0(w2 x)
    cy2 = kadd(w2[(2, 1, 2)], w2[(2, 2, 1)])

    def gate(label, zero_claims, axioms=None, expect="unsat", extra=None):
        s = Solver()
        s.set("timeout", 7200 * 1000)
        for e in (base if axioms is None else axioms):
            s.add(e)
        if extra:
            for e in extra:
                s.add(e)
        s.add(Or(*[K.neq0(x) for x in zero_claims]))
        r = s.check()
        ok = (str(r) == expect)
        if not ok:
            FAILED[0] += 1
        tag = "GATE OK" if ok else f"GATE FAILED (expect {expect}) -- STOP"
        print(f"  [{label}] -> {r}  [{tag}]", flush=True)

    def probe(label, constraint, expect=None, extra=None):
        s = Solver()
        s.set("timeout", 7200 * 1000)
        for e in base:
            s.add(e)
        if extra:
            for e in extra:
                s.add(e)
        s.add(constraint)
        r = s.check()
        note = f" (expect {expect})" if expect else " (discovery)"
        if expect and str(r) != expect:
            FAILED[0] += 1
            note += "  [GATE FAILED -- STOP]"
        print(f"  [{label}] -> {r}{note}", flush=True)

    def endpoint_sums():
        g9 = []
        for i in range(1, 4):
            for ss in range(1, 4):
                terms = []
                for r in range(1, 4):
                    terms.append(kmul(P2[(i, r)], P1[(r, ss)]))
                    terms.append(kmul(P1[(i, r)], P2[(r, ss)]))
                g9.append(ksum(*terms))
        return g9

    def pin_of(nm):
        pins = CASES[nm]
        out = []
        for i in range(1, 4):
            for j in range(1, 4):
                for k_ in range(1, 4):
                    tgt = K.one() if (i, j, k_) in pins else K.zero()
                    out.append(keq(d(c[(i, j, k_)], 0), tgt))
        return out

    # ---------------- universal gates ----------------
    probe("H0 : axioms sat", And(True), expect="sat")

    gate("H1 : Psi1(z) = 0; counit rows",
         [P1[(3, r)] for r in range(4)]
         + [P1[(i, 0)] for i in (1, 2)] + [P2[(i, 0)] for i in range(1, 4)])

    gate("H2 : mu1(x,z), mu1(y,z) in I^2; mu1(z,z) = 0",
         [d(M(1, 3, 1), 1), d(M(1, 3, 2), 1),
          d(M(2, 3, 1), 1), d(M(2, 3, 2), 1),
          d(M(3, 3, 1), 1), d(M(3, 3, 2), 1), d(M(3, 3, 3), 1)])

    x1 = []
    for ii in (1, 2):
        for ss in range(1, 4):
            x1.append(ksum(*[kmul(d(M(ii, ii, r), 1), P1[(r, ss)])
                             for r in range(1, 4)]))
    gate("H3 : X1  Psi1(mu1(x,x)) = 0, Psi1(mu1(y,y)) = 0", x1)

    h4 = []
    for ss in range(1, 4):
        rhs = ksum(*[kmul(d(M(1, 2, r), 1), P1[(r, ss)]) for r in range(1, 4)])
        if ss == 3:
            rhs = kadd(rhs, kadd(kmul(P1[(1, 1)], P1[(2, 2)]),
                                 kmul(P1[(1, 2)], P1[(2, 1)])))
        h4.append(kadd(P2[(3, ss)], rhs))
    gate("H4 : Step1 at z  Psi2(z) = Psi1(mu1(x,y)) + Psi1(x)Psi1(y)", h4)

    # ---------------- case a2a2 ----------------
    pin = pin_of("a2a2")
    probe("a2a2 : pin sanity", And(True), expect="sat", extra=pin)
    gate("A1 : Psi1(x),Psi1(y) in I^2; mu1 diag no z-comp",
         [P1[(i, s_)] for i in (1, 2) for s_ in (1, 2)]
         + [d(M(1, 1, 3), 1), d(M(2, 2, 3), 1)], extra=pin)
    a1_ = d(M(1, 1, 1), 1); a2_ = d(M(1, 1, 2), 1)
    d3 = d(M(1, 1, 3), 2)
    a3 = []
    for j in range(1, 4):
        for k_ in range(1, 4):
            lhs = kadd(kmul(a1_, w1[(1, j, k_)]), kmul(a2_, w1[(2, j, k_)]))
            tgt = d3 if (j, k_) in ((1, 2), (2, 1)) else K.zero()
            a3.append(kadd(lhs, tgt))
    gate("A3 : X2-at-x  a1 w1x + a2 w1y = w0(mu2(x,x))", a3, extra=pin)
    gate("A9 : endpoint", endpoint_sums(), extra=pin)

    # ---------------- case W2F ----------------
    pin = pin_of("W2F")
    lam = d(M(1, 1, 1), 1); nu = d(M(2, 2, 1), 1)
    probe("W2F  : pin sanity", And(True), expect="sat", extra=pin)
    gate("B1 : Psi1(x) = 0; Psi1(y) = lam x exactly (c_y = 0)",
         [P1[(1, r)] for r in range(1, 4)]
         + [kadd(P1[(2, 1)], lam), P1[(2, 2)], P1[(2, 3)]], extra=pin)
    gate("B2 : mu1(x,x) = lam x, mu1(y,y) = nu x",
         [d(M(1, 1, 2), 1), d(M(1, 1, 3), 1),
          d(M(2, 2, 2), 1), d(M(2, 2, 3), 1)], extra=pin)
    gate("B3 : L4-at-x  c_x = 0; (w1x)22=(w1x)13=(w1x)31; 23=32=33=0",
         [cx1, kadd(w1[(1, 2, 2)], w1[(1, 1, 3)]),
          kadd(w1[(1, 2, 2)], w1[(1, 3, 1)]),
          w1[(1, 2, 3)], w1[(1, 3, 2)], w1[(1, 3, 3)]], extra=pin)
    dd2 = d(M(1, 1, 2), 2); dd3 = d(M(1, 1, 3), 2)
    b4tgt = {(1, 1): dd2, (1, 2): dd3, (2, 1): dd3}
    b4 = [kadd(kmul(lam, w1[(1, j, k_)]), b4tgt.get((j, k_), K.zero()))
          for j in range(1, 4) for k_ in range(1, 4)]
    gate("B4 : X2-at-x  w0(mu2(x,x)) = lam w1x  [lam*(w1x)22 = 0]",
         b4, extra=pin)
    ff2 = d(M(2, 2, 2), 2); ff3 = d(M(2, 2, 3), 2)
    lam2 = kmul(lam, lam)
    b5tgt = {(1, 1): kadd(ff2, lam2), (1, 2): ff3, (2, 1): ff3}
    b5 = [kadd(kmul(nu, w1[(1, j, k_)]), b5tgt.get((j, k_), K.zero()))
          for j in range(1, 4) for k_ in range(1, 4)]
    gate("B5 : X2-at-y  w0(mu2(y,y)) = nu w1x + lam^2 x@x  [nu*(w1x)22 = 0]",
         b5, extra=pin)
    gate("B6 : L4'-at-x  c2_x = 0", [cx2], extra=pin)
    gate("B9 : endpoint", endpoint_sums(), extra=pin)
    probe("BN1: lam != 0 realizable", K.neq0(lam), expect="sat", extra=pin)
    probe("BN2: nu != 0 realizable", K.neq0(nu), expect="sat", extra=pin)
    probe("BN3: lam*nu != 0 realizable", K.neq0(kmul(lam, nu)), extra=pin)

    # ---------------- case mu2mu2 ----------------
    pin = pin_of("mu2mu2")
    probe("mu2mu2: pin sanity", And(True), expect="sat", extra=pin)
    gate("C1 : mu1(x,x) = 0, mu1(y,y) = 0",
         [d(M(i, i, r), 1) for i in (1, 2) for r in range(1, 4)], extra=pin)
    gate("C2 : mu2(x,x) = 0, mu2(y,y) = 0",
         [d(M(i, i, r), 2) for i in (1, 2) for r in range(1, 4)], extra=pin)
    gate("C3 : Psi1(x),Psi1(y) in I^2",
         [P1[(i, s_)] for i in (1, 2) for s_ in (1, 2)], extra=pin)
    gate("C9 : endpoint", endpoint_sums(), extra=pin)

    # ---------------- case mu2a2 ----------------
    pin = pin_of("mu2a2")
    lam = d(M(1, 1, 2), 1); nu = d(M(2, 2, 2), 1)
    probe("mu2a2: pin sanity", And(True), expect="sat", extra=pin)
    gate("E1 : Psi1(y) = 0; Psi1(x) = lam y exactly (c_x = 0)",
         [P1[(2, r)] for r in range(1, 4)]
         + [P1[(1, 1)], kadd(P1[(1, 2)], lam), P1[(1, 3)]], extra=pin)
    gate("E2 : mu1(x,x) = lam y, mu1(y,y) = nu y",
         [d(M(1, 1, 1), 1), d(M(1, 1, 3), 1),
          d(M(2, 2, 1), 1), d(M(2, 2, 3), 1)], extra=pin)
    gate("E3 : L4-at-x  c_x = 0, (w1x)13 = (w1x)31 = 0",
         [cx1, w1[(1, 1, 3)], w1[(1, 3, 1)]], extra=pin)
    gate("E4 : L4-at-y  c_y = 0; (w1y)12=21=13=31; 23=32=33=0",
         [cy1, kadd(w1[(2, 1, 2)], w1[(2, 2, 1)]),
          kadd(w1[(2, 1, 2)], w1[(2, 1, 3)]),
          kadd(w1[(2, 1, 2)], w1[(2, 3, 1)]),
          w1[(2, 2, 3)], w1[(2, 3, 2)], w1[(2, 3, 3)]], extra=pin)
    dd1 = d(M(1, 1, 1), 2); dd3 = d(M(1, 1, 3), 2)
    lam2 = kmul(lam, lam)
    e5tgt = {(1, 1): dd1, (1, 2): dd3, (2, 1): dd3, (1, 3): dd3, (3, 1): dd3,
             (2, 2): lam2}
    e5 = [kadd(kmul(lam, w1[(2, j, k_)]), e5tgt.get((j, k_), K.zero()))
          for j in range(1, 4) for k_ in range(1, 4)]
    gate("E5 : X2-at-x  w0(mu2(x,x)) = lam w1y + lam^2 y@y  [lam*(w1y)22 = lam^2]",
         e5, extra=pin)
    ff1 = d(M(2, 2, 1), 2); ff3 = d(M(2, 2, 3), 2)
    e6tgt = {(1, 1): ff1, (1, 2): ff3, (2, 1): ff3, (1, 3): ff3, (3, 1): ff3}
    e6 = [kadd(kmul(nu, w1[(2, j, k_)]), e6tgt.get((j, k_), K.zero()))
          for j in range(1, 4) for k_ in range(1, 4)]
    gate("E6 : X2-at-y  w0(mu2(y,y)) = nu w1y  [nu*(w1y)22 = 0]",
         e6, extra=pin)
    gate("E7 : L4'-at-y  c2_y = 0", [cy2], extra=pin)
    gate("E8 : nu lam^2 = 0", [kmul(nu, lam2)], extra=pin)
    gate("E9 : endpoint", endpoint_sums(), extra=pin)
    probe("EN1: lam != 0 realizable", K.neq0(lam), expect="sat", extra=pin)
    probe("EN2: nu != 0 realizable", K.neq0(nu), expect="sat", extra=pin)
    probe("EN3: lam*(w1y)11 != 0 realizable (mu2(x,x) escapes I^2)",
          K.neq0(kmul(lam, w1[(2, 1, 1)])), extra=pin)


if __name__ == "__main__":
    set_param("parallel.enable", True)
    if "--f4only" not in sys.argv:   # crash recovery: F2 half already PASSED in full (log 06:36)
        run(F2eps3(), KF2())
    if "--f2only" not in sys.argv:
        run(Ext(F2eps3()), KF4())
    verdict = ("ALL S3XY2 GATES PASSED" if FAILED[0] == 0
               else f"{FAILED[0]} GATE(S) FAILED -- hand proof wrong there")
    print(f"===== {verdict} =====", flush=True)
    print("DONE s3xy2gates", flush=True)
