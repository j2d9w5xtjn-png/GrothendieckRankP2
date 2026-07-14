#!/usr/bin/env python3
"""firstorder_gates.py -- machine gates for the session-8 HAND PROOF of the
first-order symbol theorem ("Theorem I"):

    For any base ring k' (here k' = F_2, F_4 exactly), any killed-by-2 fiber
    bialgebra structure Delta_0 on H = k'[x,y]/(x^2,y^2) or k'[t]/t^4, and any
    first-order bialgebra deformation over R = k'[eps]/eps^2 (fiber2 imposed,
    NO liftability hypothesis), the divided squaring symbol
        psi = eps-digit of phi = mu Delta   (a k'-linear map I_H -> I_H)
    satisfies psi o psi = 0.

Each 'expect unsat' below is a LEMMA of the hand proof (THEORY section 12):
  P1/P1b (xy): mu1(x,x), mu1(y,y) are Delta_0-primitive
               [diagonal instance of first-order Delta-multiplicativity;
                ring-level encoding: Delta(P) + P ox 1 + 1 ox P = 0 for
                P = e_i *_A e_i, which lies in eps*A]
  P2  (xy): e3*e3 = 0                       [Hochschild relation kills mu1(z,z)]
  P6  (xy): phi(e3) = 0                     [psi kills I^2]
  P3  (t4): mu1(t^2,t^2) is Delta_0-primitive
  P4  (t4): e1-coefficient of phi(e1) = 0   [psi(t) in I^2 -- the key t4 claim]
  P5  (t4): phi(e2) = phi(e3) = 0           [psi kills I^2]
  P7 (both): psi o psi = 0                  [the theorem's endpoint]
Pinned-fiber checks (F_2, direct checks of the case computations in the proof):
  PIN-a2a2   (xy, alpha_2 x alpha_2):  mu'(x,x) has no z-part; psi(x) in I^2
  PIN-W2F    (xy, W_2[F]):             phi(e1) = 0;  mu'(x,x) in k.x
  PIN-mu2mu2 (xy, mu_2 x mu_2):        x*x = 0, y*y = 0
  PIN-mu2a2  (xy, mu_2 x alpha_2):     phi(e2) = 0;  mu'(x,x) in k.y
  PIN-aF2    (t4, alpha_{F^2}):        phi(e1)[e1] = 0
  PIN-c4     (t4, w0(t) = t^2 ox t^2): sanity sat (the c4-family exists);
                                       phi(e1)[e1] = 0  [the a*c4 = 0 mechanism]
Non-vacuity 'expect sat' gates guard against vacuous unsats.

Ring classes are ringcheck-validated (Ext(F2epsN(2)) added to CASES this
session -- golden rule 1b).  Equation builder = s2check.build_blocks (itself
copied from ablate.py, whose gates were reproduced; nothing in the equation
generation is new here -- only assertions on top of it).
"""
import sys
from z3 import BitVecVal, Solver, Or, And, sat, unsat, set_param

from order4sat import Ext
from order4sat_beyond import F2epsN
from s2check import build_blocks

FIBS = [("xy", {(1, 2, 3): 1}), ("t4", {(1, 1, 2): 2 // 2, (1, 2, 3): 1})]
# NB (1,1,2):1 -- written oddly above to avoid typo; assert below:
assert FIBS[1][1] == {(1, 1, 2): 1, (1, 2, 3): 1}

FAILED = []


def report(label, got, expect):
    ok = (str(got) == expect)
    tag = "PASS" if ok else "FAIL"
    if not ok:
        FAILED.append(label)
    print(f"  [{label}] -> {got}   (expect {expect})  {tag}", flush=True)


def check(base, extra, label, expect):
    s = Solver()
    s.set("timeout", 3600 * 1000)
    for a in base:
        s.add(a)
    for a in extra:
        s.add(a)
    report(label, s.check(), expect)


# --- k'-digit helpers -------------------------------------------------------
# F2epsN(2) element: tuple (d0, d1) of 1-bit BVs.  k = F_2: 1-tuple of bits.
# Ext(F2epsN(2)) element: pair (u, v) of the above.  k = F_4: 2-tuple (a0, a1)
# representing a0 + a1 w, w^2 = w + 1.

def dig1(R, a):
    if isinstance(R, Ext):
        return (a[0][1], a[1][1])
    return (a[1],)


def kadd(x, y):
    return tuple(p ^ q for p, q in zip(x, y))


def kmul(x, y):
    if len(x) == 1:
        return (x[0] & y[0],)
    a0, a1 = x
    b0, b1 = y
    return ((a0 & b0) ^ (a1 & b1), (a0 & b1) ^ (a1 & b0) ^ (a1 & b1))


def kneq0(x):
    return Or(*[b != 0 for b in x])


# --- assertion builders -----------------------------------------------------

def not_primitive(R, P, c):
    """P = 4-vector of coordinates of an element of eps*A with P[0] = 0.
    Returns the z3 condition 'the eps-digit of P is NOT Delta_0-primitive',
    encoded ring-level: some (j,k>=1)-component of Delta(P)+P ox 1+1 ox P != 0,
    i.e. sum_r P[r]*c[(r,j,k)] != 0."""
    conds = []
    for j in range(1, 4):
        for k in range(1, 4):
            w = R.zero()
            for r in range(1, 4):
                w = R.add(w, R.mul(P[r], c[(r, j, k)]))
            conds.append(R.neq0(w))
    return Or(*conds)


def psi_matrix(R, phi):
    return {(i, r): dig1(R, phi[i][r]) for i in range(1, 4) for r in range(1, 4)}


def psi2_nonzero(R, phi):
    psi = psi_matrix(R, phi)
    conds = []
    for i in range(1, 4):
        for t in range(1, 4):
            acc = kmul(psi[(i, 1)], psi[(1, t)])
            for r in range(2, 4):
                acc = kadd(acc, kmul(psi[(i, r)], psi[(r, t)]))
            conds.append(kneq0(acc))
    return Or(*conds)


def pin_digit0(c, pins):
    """F_2[eps]/eps^2 only: pin digit 0 of all 27 c-vars.
    pins = set of (i,j,k) with digit-0 = 1; all others 0."""
    out = []
    for i in range(1, 4):
        for j in range(1, 4):
            for k in range(1, 4):
                v = 1 if (i, j, k) in pins else 0
                out.append(c[(i, j, k)][0] == BitVecVal(v, 1))
    return out


# --- main gate battery ------------------------------------------------------

def run_ring(R):
    print(f"===== base {R.name} =====", flush=True)
    for fname, fib in FIBS:
        A, Mb, C, fiber2, phi, c, Mtab = build_blocks(R, fib)
        base = A + Mb + C + fiber2
        S11 = [R.zero()] + [Mtab[(1, 1, r)] for r in range(1, 4)]
        S22 = [R.zero()] + [Mtab[(2, 2, r)] for r in range(1, 4)]
        S33 = [R.zero()] + [Mtab[(3, 3, r)] for r in range(1, 4)]
        pre = f"{fname}"
        check(base, [], f"{pre} sanity (level 1)", "sat")
        if fname == "xy":
            check(base, [not_primitive(R, S11, c)],
                  f"{pre} P1  mu'(x,x) not primitive", "unsat")
            check(base, [not_primitive(R, S22, c)],
                  f"{pre} P1b mu'(y,y) not primitive", "unsat")
            check(base, [Or(*[R.neq0(S33[r]) for r in range(1, 4)])],
                  f"{pre} P2  z*z != 0", "unsat")
            check(base, [Or(*[R.neq0(phi[3][r]) for r in range(4)])],
                  f"{pre} P6  phi(e3) != 0", "unsat")
            check(base, [Or(*[R.neq0(S11[r]) for r in range(1, 4)])],
                  f"{pre} NV1 x*x != 0 (non-vacuity)", "sat")
        else:
            check(base, [not_primitive(R, S22, c)],
                  f"{pre} P3  mu'(t2,t2) not primitive", "unsat")
            check(base, [R.neq0(phi[1][1])],
                  f"{pre} P4  phi(e1) has e1-component", "unsat")
            check(base, [Or(*[R.neq0(phi[2][r]) for r in range(4)]),
                         ],
                  f"{pre} P5a phi(e2) != 0", "unsat")
            check(base, [Or(*[R.neq0(phi[3][r]) for r in range(4)])],
                  f"{pre} P5b phi(e3) != 0", "unsat")
            check(base, [Or(*[R.neq0(S22[r]) for r in range(1, 4)])],
                  f"{pre} NV3 t2*t2 != 0 (non-vacuity)", "sat")
        check(base, [psi2_nonzero(R, phi)],
              f"{pre} P7  psi^2 != 0", "unsat")
        check(base, [Or(*[kneq0(dig1(R, phi[i][r]))
                          for i in range(1, 4) for r in range(1, 4)])],
              f"{pre} NV4 psi != 0 (non-vacuity)", "sat")


def run_pins():
    R = F2epsN(2)
    print(f"===== pinned fibers over {R.name} =====", flush=True)
    xyfib, t4fib = FIBS[0][1], FIBS[1][1]

    def fresh_blocks(fib):
        A, Mb, C, fiber2, phi, c, Mtab = build_blocks(R, fib)
        return A + Mb + C + fiber2, phi, c, Mtab

    # alpha_2 x alpha_2 : w0x = w0y = 0, w0z = x oy
    base, phi, c, Mtab = fresh_blocks(xyfib)
    pins = pin_digit0(c, {(3, 1, 2), (3, 2, 1)})
    check(base, pins, "PIN-a2a2 sanity", "sat")
    check(base, pins + [R.neq0(Mtab[(1, 1, 3)])],
          "PIN-a2a2 mu'(x,x) has z-part", "unsat")
    check(base, pins + [Or(R.neq0(phi[1][1]), R.neq0(phi[1][2]))],
          "PIN-a2a2 psi(x) not in I^2", "unsat")

    # W2[F] : w0x = 0, w0y = x ox x, w0z = x o y
    base, phi, c, Mtab = fresh_blocks(xyfib)
    pins = pin_digit0(c, {(2, 1, 1), (3, 1, 2), (3, 2, 1)})
    check(base, pins, "PIN-W2F sanity", "sat")
    check(base, pins + [Or(*[R.neq0(phi[1][r]) for r in range(4)])],
          "PIN-W2F phi(e1) != 0", "unsat")
    check(base, pins + [Or(R.neq0(Mtab[(1, 1, 2)]), R.neq0(Mtab[(1, 1, 3)]))],
          "PIN-W2F mu'(x,x) not in k.x", "unsat")
    check(base, pins + [R.neq0(Mtab[(1, 1, 1)])],
          "PIN-W2F mu'(x,x) = p.x, p != 0 (non-vacuity)", "sat")

    # mu2 x mu2 : w0x = x ox x, w0y = y ox y, w0z = x o y + x o z + y o z + z ox z
    base, phi, c, Mtab = fresh_blocks(xyfib)
    pins = pin_digit0(c, {(1, 1, 1), (2, 2, 2),
                          (3, 1, 2), (3, 2, 1), (3, 1, 3), (3, 3, 1),
                          (3, 2, 3), (3, 3, 2), (3, 3, 3)})
    check(base, pins, "PIN-mu2mu2 sanity", "sat")
    check(base, pins + [Or(*[R.neq0(Mtab[(1, 1, r)]) for r in range(1, 4)])],
          "PIN-mu2mu2 x*x != 0", "unsat")
    check(base, pins + [Or(*[R.neq0(Mtab[(2, 2, r)]) for r in range(1, 4)])],
          "PIN-mu2mu2 y*y != 0", "unsat")

    # mu2 x alpha_2 : w0x = x ox x, w0y = 0, w0z = x o y + x o z
    base, phi, c, Mtab = fresh_blocks(xyfib)
    pins = pin_digit0(c, {(1, 1, 1), (3, 1, 2), (3, 2, 1), (3, 1, 3), (3, 3, 1)})
    check(base, pins, "PIN-mu2a2 sanity", "sat")
    check(base, pins + [Or(*[R.neq0(phi[2][r]) for r in range(4)])],
          "PIN-mu2a2 phi(e2) != 0", "unsat")
    check(base, pins + [Or(R.neq0(Mtab[(1, 1, 1)]), R.neq0(Mtab[(1, 1, 3)]))],
          "PIN-mu2a2 mu'(x,x) not in k.y", "unsat")
    check(base, pins + [R.neq0(Mtab[(1, 1, 2)])],
          "PIN-mu2a2 mu'(x,x) = q.y, q != 0 (non-vacuity)", "sat")

    # t4, alpha_{F^2} : w0t = 0, w0t2 = 0, w0t3 = t o t2
    base, phi, c, Mtab = fresh_blocks(t4fib)
    pins = pin_digit0(c, {(3, 1, 2), (3, 2, 1)})
    check(base, pins, "PIN-aF2 sanity", "sat")
    check(base, pins + [R.neq0(phi[1][1])],
          "PIN-aF2 phi(e1) has e1-component", "unsat")

    # t4, c4-family : w0t = t2 ox t2, w0t2 = 0, w0t3 = t o t2
    base, phi, c, Mtab = fresh_blocks(t4fib)
    pins = pin_digit0(c, {(1, 2, 2), (3, 1, 2), (3, 2, 1)})
    check(base, pins, "PIN-c4 sanity (c4-family exists)", "sat")
    check(base, pins + [R.neq0(phi[1][1])],
          "PIN-c4 phi(e1) has e1-component", "unsat")
    check(base, pins + [Or(*[R.neq0(Mtab[(2, 2, r)]) for r in range(1, 4)])],
          "PIN-c4 mu'(t2,t2) != 0 (non-vacuity)", "sat")


if __name__ == "__main__":
    set_param("parallel.enable", True)
    for R in [F2epsN(2), Ext(F2epsN(2))]:
        run_ring(R)
    run_pins()
    if FAILED:
        print(f"GATES FAILED: {FAILED}", flush=True)
    else:
        print("ALL FIRSTORDER GATES PASSED", flush=True)
    print("DONE firstorder_gates", flush=True)
