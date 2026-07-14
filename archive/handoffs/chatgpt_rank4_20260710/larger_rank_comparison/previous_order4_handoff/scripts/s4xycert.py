#!/usr/bin/env python3
"""s4xycert.py  (session 12, 2026-07-09)

Coefficient-robust gate battery for the FOURTH external note
(order4_max_pass_xy_s4.md): the per-split-model reduction of the s = 4
divided-[4] identity D4 = Psi1 Psi3 + Psi2^2 + Psi3 Psi1 = 0 for the xy fiber.

The note's own gates (bundle: s4xy_case_reduction_gates.py) run over
F2[eps]/eps^4 ONLY.  Several of its identities have Frobenius-collapsible
shapes (lam*(L x)_y = rho^2 etc. -- over k' = F2, rho^2 = rho), so per the
12.6.6(e) CAUTION they do NOT settle the arbitrary-k' shape.  This battery
reruns every displayed identity over

  F2[eps]/eps^4            (KF2)   -- fast reproduction of the note's verdicts
                                      (cross-validation of the port);
  (F2[u]/u^2)[eps]/eps^4   (KDual) -- dual numbers break Frobenius collapse
                                      (rho = rho1*u gives rho^2 = 0 != rho);
                                      ring self-gated by s4cert.gateR0_extd;
  F4[eps]/eps^4            (KF4)   -- expensive; run last.

Same CAUTION as s4cert: ExtD is a layered-coefficient class, NOT Artin-local;
do not add to ringcheck; deform ranges over eps*R.

Verdict discipline: every identity gate must come back unsat; Q0 must be sat.
'unknown' counts as NOT passed.  Final line: ALL S4XYCERT GATES PASSED /
N GATE(S) FAILED, then DONE s4xycert.  (Golden rule 4: check the final line
before citing.)

The arbitrary-k' THEOREM upgrade is s4xygen.m2 (ideal membership); this
battery is the cheap wide net that would catch a wrong identity long before
the GB terminates.
"""
import sys

sys.path.insert(0, ".")
from z3 import Solver, Or, sat, unsat, set_param

from order4sat_beyond import F2epsN
from order4sat import Ext
from s2check import build_blocks
from s3gates import KF2, KF4
from s4cert import ExtD, KDual, digit_, gateR0_extd

XY = {(1, 2, 3): 1}
FAILED = [0]

# split-model Delta_0 pins (verified by hand session 12 = bundle CASES)
CASES = {
    "a2a2":   {(3, 1, 2), (3, 2, 1)},
    "W2F":    {(2, 1, 1), (3, 1, 2), (3, 2, 1)},
    "mu2mu2": {(1, 1, 1), (2, 2, 2), (3, 1, 2), (3, 2, 1), (3, 1, 3),
               (3, 3, 1), (3, 2, 3), (3, 3, 2), (3, 3, 3)},
    "mu2a2":  {(1, 1, 1), (3, 1, 2), (3, 2, 1), (3, 1, 3), (3, 3, 1)},
}


def run_ring(R, K, endpoint=True):
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, XY)
    base = A + Mb + C + F
    d = lambda x, l: digit_(R, x, l)

    def add(*xs):
        out = xs[0]
        for x in xs[1:]:
            out = K.add(out, x)
        return out

    mul = K.mul

    def keq(x, y):
        return K.eq0(add(x, y))

    P = {n: {(i, r): d(phi[i][r], n) for i in range(1, 4) for r in range(1, 4)}
         for n in (1, 2, 3)}
    w1 = {(i, j, k): d(c[(i, j, k)], 1)
          for i in range(1, 4) for j in range(1, 4) for k in range(1, 4)}
    Mco = lambda i, j, r, n: d(Mtab[(min(i, j), max(i, j), r)], n)

    def pin_of(case):
        out = []
        pins = CASES[case]
        for i in range(1, 4):
            for j in range(1, 4):
                for k in range(1, 4):
                    out.append(keq(d(c[(i, j, k)], 0),
                                   K.one() if (i, j, k) in pins else K.zero()))
        return out

    def comp(a, b, i, ss):
        return add(*[mul(P[a][(i, r)], P[b][(r, ss)]) for r in (1, 2, 3)])

    def d4_all():
        return [add(comp(1, 3, i, j), comp(2, 2, i, j), comp(3, 1, i, j))
                for i in (1, 2, 3) for j in (1, 2, 3)]

    def make_case(case):
        s = Solver()
        s.set("timeout", 3600000)
        for e in base + pin_of(case):
            s.add(e)
        print(f"===== {case} over {R.name} =====", flush=True)
        r0 = s.check()
        print(f"  [Q0 axioms sat] -> {r0}"
              + ("" if r0 == sat else "  [GATE FAILED]"), flush=True)
        if r0 != sat:
            FAILED[0] += 1

        def gate(label, exprs):
            s.push()
            s.add(Or(*[K.neq0(e) for e in exprs]))
            r = s.check()
            s.pop()
            ok = r == unsat
            if not ok:
                FAILED[0] += 1
            print(f"  [{label}] -> {r}" + ("  [GATE OK]" if ok else "  [GATE FAILED]"),
                  flush=True)

        def probe(label, cond):
            s.push()
            s.add(cond)
            r = s.check()
            s.pop()
            print(f"  [{label}] -> {r} (discovery)", flush=True)

        return s, gate, probe

    def image_line(case):
        s, gate, probe = make_case(case)
        cx, cy = P[1][(1, 3)], P[1][(2, 3)]
        gate("N has image in kz and N(z)=0",
             [P[1][(1, 1)], P[1][(1, 2)], P[1][(2, 1)], P[1][(2, 2)],
              P[1][(3, 1)], P[1][(3, 2)], P[1][(3, 3)]])
        if case == "mu2mu2":
            gate("M(z)=0", [P[2][(3, 1)], P[2][(3, 2)], P[2][(3, 3)]])
            gate("L(z)=0", [P[3][(3, 1)], P[3][(3, 2)], P[3][(3, 3)]])
        else:
            gate("M(z) in kz", [P[2][(3, 1)], P[2][(3, 2)]])
        for g, cg in [(1, cx), (2, cy), (3, K.zero())]:
            for ss in (1, 2):
                gate(f"M^2({g})_{ss} + N({g})*L(z)_{ss}=0",
                     [add(comp(2, 2, g, ss), mul(cg, P[3][(3, ss)]))])
            ellLg = add(mul(cx, P[3][(g, 1)]), mul(cy, P[3][(g, 2)]))
            gate(f"z-component identity for input {g}",
                 [add(comp(2, 2, g, 3), mul(cg, P[3][(3, 3)]), ellLg)])
        probe("ell != 0 realizable", Or(K.neq0(cx), K.neq0(cy)))
        if endpoint:
            gate("endpoint D4=0", d4_all())

    def rank_one(case):
        s, gate, probe = make_case(case)
        if case == "W2F":
            lam = Mco(1, 1, 1, 1); nu = Mco(2, 2, 1, 1); mm = Mco(1, 2, 2, 1)
            alpha = w1[(1, 1, 1)]; delta = w1[(1, 2, 2)]
            rho = add(mul(lam, alpha), mul(nu, delta)); Cfree = P[2][(2, 3)]
            gate("Psi1: x->0, y->lambda x, z->0",
                 [P[1][(1, r)] for r in (1, 2, 3)]
                 + [add(P[1][(2, 1)], lam), P[1][(2, 2)], P[1][(2, 3)]]
                 + [P[1][(3, r)] for r in (1, 2, 3)])
            gate("Psi2(x)=rho x",
                 [add(P[2][(1, 1)], rho), P[2][(1, 2)], P[2][(1, 3)]])
            gate("(Psi2 y)_y=rho", [add(P[2][(2, 2)], rho)])
            gate("Psi2(z)=m lambda x",
                 [add(P[2][(3, 1)], mul(mm, lam)), P[2][(3, 2)], P[2][(3, 3)]])
            gate("lambda (Psi3 x)_y=rho^2",
                 [add(mul(lam, P[3][(1, 2)]), mul(rho, rho))])
            gate("lambda (Psi3 x)_z=rho (Psi2 y)_z",
                 [add(mul(lam, P[3][(1, 3)]), mul(rho, Cfree))])
            gate("(Psi3 z)_y=m rho", [add(P[3][(3, 2)], mul(mm, rho))])
            gate("lambda((Psi3 y)_y+(Psi3 x)_x+m(Psi2 y)_z)=0",
                 [mul(lam, add(P[3][(2, 2)], P[3][(1, 1)], mul(mm, Cfree)))])
        else:
            lam = Mco(1, 1, 2, 1); nu = Mco(2, 2, 2, 1); mm = Mco(1, 2, 1, 1)
            alpha = w1[(2, 1, 1)]; delta = w1[(2, 2, 2)]
            rho = add(mul(lam, alpha), mul(nu, delta)); Cfree = P[2][(1, 3)]
            gate("Psi1: x->lambda y, y->0, z->0",
                 [P[1][(1, 1)], add(P[1][(1, 2)], lam), P[1][(1, 3)]]
                 + [P[1][(2, r)] for r in (1, 2, 3)]
                 + [P[1][(3, r)] for r in (1, 2, 3)])
            gate("Psi2(y)=rho y",
                 [P[2][(2, 1)], add(P[2][(2, 2)], rho), P[2][(2, 3)]])
            gate("(Psi2 x)_x=rho", [add(P[2][(1, 1)], rho)])
            gate("Psi2(z)=m lambda y",
                 [P[2][(3, 1)], add(P[2][(3, 2)], mul(mm, lam)), P[2][(3, 3)]])
            gate("lambda (Psi3 y)_x=rho^2",
                 [add(mul(lam, P[3][(2, 1)]), mul(rho, rho))])
            gate("lambda (Psi3 y)_z=rho (Psi2 x)_z",
                 [add(mul(lam, P[3][(2, 3)]), mul(rho, Cfree))])
            gate("(Psi3 z)_x=m rho", [add(P[3][(3, 1)], mul(mm, rho))])
            gate("lambda((Psi3 x)_x+(Psi3 y)_y+m(Psi2 x)_z)=0",
                 [mul(lam, add(P[3][(1, 1)], P[3][(2, 2)], mul(mm, Cfree)))])
        probe("lam != 0 realizable", K.neq0(lam))
        probe("rho != 0 realizable", K.neq0(rho))
        if endpoint:
            gate("endpoint D4=0", d4_all())

    image_line("a2a2")
    rank_one("W2F")
    image_line("mu2mu2")
    rank_one("mu2a2")


if __name__ == "__main__":
    set_param("parallel.enable", True)
    run_ring(F2epsN(4), KF2(), endpoint=True)          # note reproduction
    RD = ExtD(F2epsN(4))
    gateR0_extd(RD)
    run_ring(RD, KDual(), endpoint=True)               # Frobenius-breaking
    if "--nof4" not in sys.argv:
        run_ring(Ext(F2epsN(4)), KF4(),
                 endpoint=("--f4endpoint" in sys.argv))
    verdict = ("ALL S4XYCERT GATES PASSED" if FAILED[0] == 0
               else f"{FAILED[0]} GATE(S) FAILED")
    print(f"===== {verdict} =====", flush=True)
    print("DONE s4xycert", flush=True)
