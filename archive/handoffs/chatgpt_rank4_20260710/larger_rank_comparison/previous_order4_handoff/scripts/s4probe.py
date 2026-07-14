#!/usr/bin/env python3
r"""s4probe.py -- session-10 calibration probe for the s = 4 layer identity
over F2[eps]/eps^4 (THEORY 12.6.6; both fibers, F2 only -- eps^4 at F4 would
be too slow for a probe).

Layers mu = mu0+..+eps^3 mu3, w = w0+..+eps^3 w3;
Psi_n = sum_{j+l=n} mu_j w_l;  D4 := Psi1 Psi3 + Psi2 Psi2 + Psi3 Psi1.

t^4 fiber (notation of 12.6.4: B,C = t^2,t^3-comps of Psi1 t; P = (Psi2 t)_t;
a = mu1(t^2,t^2)_t; p = mu1(t,t)_t; beta11 = (w1 t)_{11}; a c4 = 0 so
a B = a beta11):
  T1  (Psi3 t^2)_t = p P + a B^2      [layer-3 multiplicativity at (t,t),
       12.6.6(a); hand-derived session 10]                    expect unsat
  T2  D4 = 0 (endpoint, all 9 components)                     expect unsat
       (cross-validates s2check's eps^4 row = S'; a sat = encoding bug or
        a fake -- STOP, golden rule 3)
  T3  a*B    != 0   discovery -- is the D4(t^2) = a B^2 Psi1(t) obstruction
  T4  a*B^2  != 0   discovery    killed at the a*B level, the a*B^2 level,
  T5  a*B^3  != 0   expect unsat (forced by T2: D4(t^2)_{t^2} = a B^3)
  T6  a*B^2*C != 0  expect unsat (D4(t^2)_{t^3} = a B^2 C)

xy fiber:
  X1g Gamma-vanishing (12.6.6(c)) at W = w1 x: the mu1-x-mu0 half of
      Gamma_1(W,W) has all components zero                    expect unsat
  X3  layer-3 X1-analogue at (x,x): Psi2(mu1(x,x)) + Psi1(mu2(x,x))
      + mu1(Psi1 x, Psi1 x) = 0                               expect unsat
  X2g D4 = 0 (endpoint)                                       expect unsat

Run AFTER s3xy2gates finishes (chain-queued; box is saturated).
"""
import sys
from z3 import Solver, Or, And, set_param

sys.path.insert(0, ".")
from order4sat_beyond import F2epsN
from s2check import build_blocks
from s3gates import KF2, digit

T4F = {(1, 1, 2): 1, (1, 2, 3): 1}
XYF = {(1, 2, 3): 1}
FAILED = [0]


def run_fiber(R, K, fib, name):
    print(f"===== s4probe over {R.name}, fiber {name} =====", flush=True)
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
    base = A + Mb + C + F
    d = lambda x, l: digit(R, x, l)
    M = lambda i, j, r: Mtab[(min(i, j), max(i, j), r)]
    kadd, kmul = K.add, K.mul

    def ksum(*xs):
        out = xs[0]
        for x in xs[1:]:
            out = kadd(out, x)
        return out

    P1 = {(i, r): d(phi[i][r], 1) for i in range(1, 4) for r in range(4)}
    P2 = {(i, r): d(phi[i][r], 2) for i in range(1, 4) for r in range(4)}
    P3 = {(i, r): d(phi[i][r], 3) for i in range(1, 4) for r in range(4)}

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

    probe("Q0 : axioms sat", And(True), expect="sat")

    d4 = []
    for i in range(1, 4):
        for ss in range(1, 4):
            terms = []
            for r in range(1, 4):
                terms.append(kmul(P1[(i, r)], P3[(r, ss)]))
                terms.append(kmul(P2[(i, r)], P2[(r, ss)]))
                terms.append(kmul(P3[(i, r)], P1[(r, ss)]))
            d4.append(ksum(*terms))

    if name == "t4":
        p = d(M(1, 1, 1), 1)
        a = d(M(2, 2, 1), 1)
        B, Cc = P1[(1, 2)], P1[(1, 3)]
        P = P2[(1, 1)]
        gate("T1 : (Psi3 t^2)_t = p P + a B^2",
             [ksum(P3[(2, 1)], kmul(p, P), kmul(a, kmul(B, B)))])
        gate("T2 : s=4 endpoint D4 = 0", d4)
        probe("T3 : a*B != 0 realizable", K.neq0(kmul(a, B)))
        probe("T4 : a*B^2 != 0 realizable", K.neq0(kmul(a, kmul(B, B))))
        gate("T5 : a*B^3 = 0", [kmul(kmul(a, B), kmul(B, B))])
        gate("T6 : a*B^2*C = 0", [kmul(kmul(a, B), kmul(B, Cc))])
    else:
        w1x = {(j, k): d(c[(1, j, k)], 1)
               for j in range(1, 4) for k in range(1, 4)}
        g_ = []
        for r in range(1, 4):
            terms = []
            for pp in range(1, 4):
                for qq in range(1, 4):
                    coef = kadd(kmul(w1x[(pp, 1)], w1x[(qq, 2)]),
                                kmul(w1x[(pp, 2)], w1x[(qq, 1)]))
                    terms.append(kmul(coef, d(M(pp, qq, r), 1)))
            g_.append(ksum(*terms))
        gate("X1g: Gamma_1(w1x, w1x) mu1-half = 0", g_)
        x3 = []
        for ss in range(1, 4):
            terms = []
            for r in range(1, 4):
                terms.append(kmul(d(M(1, 1, r), 1), P2[(r, ss)]))
                terms.append(kmul(d(M(1, 1, r), 2), P1[(r, ss)]))
                terms.append(kmul(kmul(P1[(1, r)], P1[(1, r)]),
                                  d(M(r, r, ss), 1)))
            x3.append(ksum(*terms))
        gate("X3 : layer-3 X1-analogue at (x,x)", x3)
        gate("X2g: s=4 endpoint D4 = 0", d4)


if __name__ == "__main__":
    set_param("parallel.enable", True)
    R = F2epsN(4)
    run_fiber(R, KF2(), T4F, "t4")
    run_fiber(R, KF2(), XYF, "xy")
    verdict = ("ALL S4 PROBE GATES PASSED" if FAILED[0] == 0
               else f"{FAILED[0]} GATE(S) FAILED")
    print(f"===== {verdict} =====", flush=True)
    print("DONE s4probe", flush=True)
