#!/usr/bin/env python3
r"""s4pred.py -- micro-gates for the PREDECESSOR external note
(`order4_sustained_attempt_note.md`, received 2026-07-09): its hand Lemma
aB = 0 for every second-order lift (i.e. already over k'[eps]/eps^3) of a
killed-by-2 t^4 fiber.  s4cert.py gates the CONCLUSION at eps^4; this script
gates the note's intermediate steps at the note's own level eps^3, plus its
"relative first-order" contrast:

  Y11  : (w1 t^2)_{t,t} = 0        [note's step 1; the stated degree argument
  Th11 : (w1 t^3)_{t,t} = 0         has a gap -- unit-leg x w0t-monomial
                                    mu1-carries like c1 mu1(t,t^2) (x) t DO hit
                                    t(x)t and die only by symmetric-pair
                                    cancellation; see THEORY 14.6 -- so gate it]
  AB3  : a beta11 = 0 and a B = 0 over eps^3   [the Lemma itself]
  AB2  : a beta11 != 0 over eps^2 -> expect SAT [the contrast: genuinely
                                    relative -- first-order data alone does
                                    NOT force it; a second-order lift does]

Rings: F2[eps]/eps^N and F4[eps]/eps^N (N = 2, 3) -- cheap at these lengths.
"""
import sys
from z3 import Solver, Or, And, set_param

sys.path.insert(0, ".")
from order4sat_beyond import F2epsN
from order4sat import Ext
from s2check import build_blocks
from s3gates import KF2, KF4, digit

T4F = {(1, 1, 2): 1, (1, 2, 3): 1}
FAILED = [0]


def run(R, K, N):
    print(f"===== s4pred over {R.name} =====", flush=True)
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, T4F)
    base = A + Mb + C + F
    d = lambda x, l: digit(R, x, l)
    M = lambda i, j, r: Mtab[(min(i, j), max(i, j), r)]

    def q(label, constraint, expect):
        s = Solver()
        s.set("timeout", 43200 * 1000)
        for e in base:
            s.add(e)
        s.add(constraint)
        r = s.check()
        ok = (str(r) == expect)
        if not ok:
            FAILED[0] += 1
        tag = "GATE OK" if ok else f"GATE FAILED (expect {expect}) -- STOP"
        print(f"  [{label}] -> {r}  [{tag}]", flush=True)

    a = d(M(2, 2, 1), 1)
    b11 = d(c[(1, 1, 1)], 1)
    q("P0 : axioms sat", And(True), "sat")
    if N >= 3:
        q("Y11 : (w1 t^2)_(t,t) = 0", K.neq0(d(c[(2, 1, 1)], 1)), "unsat")
        q("Th11: (w1 t^3)_(t,t) = 0", K.neq0(d(c[(3, 1, 1)], 1)), "unsat")
        q("AB3a: a beta11 = 0 over eps^3", K.neq0(K.mul(a, b11)), "unsat")
        q("AB3b: a B = 0 over eps^3", K.neq0(K.mul(a, d(phi[1][2], 1))), "unsat")
    else:
        q("AB2 : a beta11 != 0 over eps^2 (relative contrast)",
          K.neq0(K.mul(a, b11)), "sat")


if __name__ == "__main__":
    set_param("parallel.enable", True)
    run(F2epsN(2), KF2(), 2)
    run(F2epsN(3), KF2(), 3)
    run(Ext(F2epsN(2)), KF4(), 2)
    run(Ext(F2epsN(3)), KF4(), 3)
    verdict = ("ALL S4PRED GATES PASSED" if FAILED[0] == 0
               else f"{FAILED[0]} GATE(S) FAILED")
    print(f"===== {verdict} =====", flush=True)
    print("DONE s4pred", flush=True)
