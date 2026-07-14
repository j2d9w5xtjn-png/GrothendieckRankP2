#!/usr/bin/env python3
r"""s3xygates.py -- calibration battery for the s = 3 identity, xy fiber
(session 9; the t^4 half is Theorem K / THEORY 12.6.4 -- this prepares the
xy half, THEORY 12.6.4.5 remaining item (i)).

Basis e1 = x, e2 = y, e3 = z = xy;  I^2 = k'z.  Over R = k'[eps]/eps^3
(k' = F2 and F4), fiber2, all deformation layers free:

  GXmult : the layer-2 multiplicativity instance at z = mu0(x,y):
             Psi2(z) = Psi1(mu1(x,y)) + Psi1(x) *_0 Psi1(y)
           (the fiber-agnostic Step 1 of THEORY 12.6.4 -- the xy proof will
           lean on it exactly as the t^4 proof did).            [expect unsat]
  GX9    : endpoint s = 3 identity Psi1 Psi2 + Psi2 Psi1 = 0.   [expect unsat]
  GX9nc  : endpoint with coassociativity dropped (A+M+F only) -- discovery;
           t^4 analogue was unsat (s3gates G9nc).
  Discovery rows (unpinned): which components of Psi1, Psi2 can stick out of
  I^2 (per component), calibrating how much of the 12.4.3 case mechanism
  survives at layer 2.
  Per pinned split model (12.4.1: a2a2, W2F, mu2mu2, mu2a2 -- digit-0 of the
  comultiplication pinned to the classification table, all higher layers and
  the multiplication deformation free): pin sanity [sat], endpoint
  [expect unsat], and 'Psi2 escapes I^2' / 'Psi1 escapes I^2' discovery.

Everything reuses the gate-validated builder (s2check.build_blocks) and the
digit machinery of s3gates.py.  A sat on GXmult / GX9 = hand-proof-to-be is
wrong / encoding bug -- stop and debug (golden rule 1).
"""
import sys
from z3 import Solver, Or, And, sat, unsat, set_param

sys.path.insert(0, ".")
from order4sat import F2eps3, Ext
from s2check import build_blocks
from s3gates import KF2, KF4, digit

XY = {(1, 2, 3): 1}
FAILED = [0]

# 12.4.1 split models: digit-0 pins for w0 (coefficient of e_j (x) e_k in
# w0(e_i) at (i,j,k)); every unlisted (i,j,k) is pinned to digit-0 = 0.
CASES = {
    "a2a2":   {(3, 1, 2), (3, 2, 1)},
    "W2F":    {(2, 1, 1), (3, 1, 2), (3, 2, 1)},
    "mu2mu2": {(1, 1, 1), (2, 2, 2), (3, 1, 2), (3, 2, 1), (3, 1, 3),
               (3, 3, 1), (3, 2, 3), (3, 3, 2), (3, 3, 3)},
    "mu2a2":  {(1, 1, 1), (3, 1, 2), (3, 2, 1), (3, 1, 3), (3, 3, 1)},
}


def run(R, K):
    print(f"===== s3xygates over {R.name} =====", flush=True)
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, XY)
    base = A + Mb + C + F
    base_noC = A + Mb + F

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

    def probe(label, constraint, expect=None, axioms=None, extra=None):
        s = Solver()
        s.set("timeout", 7200 * 1000)
        for e in (base if axioms is None else axioms):
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

    probe("G0  : axioms sat", And(True), expect="sat")

    # layer-2 multiplicativity at z = mu0(x,y):
    #   Psi2(z)_s = sum_r mu1(x,y)_r^{(1)} P1[r][s]  (+ product term at s=z)
    mults = []
    for s_ in range(4):
        rhs = ksum(*[kmul(d(M(1, 2, r), 1), P1[(r, s_)]) for r in range(1, 4)])
        if s_ == 3:  # z-component of Psi1(x) *_0 Psi1(y)
            rhs = kadd(rhs, kadd(kmul(P1[(1, 1)], P1[(2, 2)]),
                                 kmul(P1[(1, 2)], P1[(2, 1)])))
        mults.append(kadd(P2[(3, s_)], rhs))
    gate("GXm : Psi2(z) = Psi1(mu1(x,y)) + Psi1(x)Psi1(y)", mults)

    # endpoint s = 3
    g9 = []
    for i in range(1, 4):
        for s_ in range(1, 4):
            terms = []
            for r in range(1, 4):
                terms.append(kmul(P2[(i, r)], P1[(r, s_)]))
                terms.append(kmul(P1[(i, r)], P2[(r, s_)]))
            g9.append(ksum(*terms))
    gate("GX9 : s=3 identity Psi1 Psi2 + Psi2 Psi1 = 0", g9)
    probe("GX9nc: s=3 violated, coassociativity DROPPED",
          Or(*[K.neq0(x) for x in g9]), axioms=base_noC)

    # unpinned escape discovery
    for (i, s_), nm in [((1, 1), "(Psi1 x)_x"), ((1, 2), "(Psi1 x)_y"),
                        ((3, 1), "(Psi1 z)_x")]:
        probe(f"D1  : {nm} != 0 realizable", K.neq0(P1[(i, s_)]))
    for (i, s_), nm in [((1, 1), "(Psi2 x)_x"), ((1, 2), "(Psi2 x)_y"),
                        ((2, 1), "(Psi2 y)_x"), ((3, 1), "(Psi2 z)_x"),
                        ((3, 2), "(Psi2 z)_y")]:
        probe(f"D2  : {nm} != 0 realizable", K.neq0(P2[(i, s_)]))

    # per pinned split model
    for nm, pins in CASES.items():
        pin = []
        for i in range(1, 4):
            for j in range(1, 4):
                for k_ in range(1, 4):
                    tgt = K.one() if (i, j, k_) in pins else K.zero()
                    pin.append(_eqK(K, d(c[(i, j, k_)], 0), tgt))
        probe(f"{nm}: pin sanity", And(*pin), expect="sat")
        gate(f"{nm}: s=3 endpoint", g9, extra=pin + [And(True)])
        if nm == "a2a2":
            # session-9 hand sketch: with w0x = w0y = 0 and w0z = x*y,
            # order-1 coassociativity at x (RHS = 0) forces w1x (likewise
            # w1y) to have NO z-legs: (w1 e_i)_{pz} = (w1 e_i)_{zp} = 0.
            nolegs = [d(c[(i, j, k_)], 1)
                      for i in (1, 2) for j in range(1, 4)
                      for k_ in range(1, 4) if j == 3 or k_ == 3]
            gate("a2a2: w1(x), w1(y) have no z-legs", nolegs, extra=pin)
        probe(f"{nm}: some Psi2 escapes I^2",
              Or(*[K.neq0(P2[(i, s_)]) for i in range(1, 4) for s_ in (1, 2)]),
              extra=pin)
        probe(f"{nm}: some Psi1 escapes I^2",
              Or(*[K.neq0(P1[(i, s_)]) for i in range(1, 4) for s_ in (1, 2)]),
              extra=pin)


def _eqK(K, x, y):
    return K.eq0(K.add(x, y))


if __name__ == "__main__":
    set_param("parallel.enable", True)
    if "--f4only" not in sys.argv:   # crash recovery: F2 half already complete (log 08:02)
        run(F2eps3(), KF2())
    if "--f2only" not in sys.argv:
        run(Ext(F2eps3()), KF4())
    verdict = ("ALL S3XY GATES PASSED" if FAILED[0] == 0
               else f"{FAILED[0]} GATE(S) FAILED")
    print(f"===== {verdict} =====", flush=True)
    print("DONE s3xygates", flush=True)
