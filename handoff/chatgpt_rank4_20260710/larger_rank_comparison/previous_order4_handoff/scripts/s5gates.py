#!/usr/bin/env python3
"""s5gates.py (session 13, 2026-07-09) -- machine gates for the FIFTH external
note (order4_fifth_push_relative_defect.md; audit THEORY section 15).

Batteries (all k = F_2; the hand theorems cover arbitrary k -- these gates
validate encodings + give exact-ring confirmation, per golden rule 1):

A. Base F2[u,v]/(u,v)^2 ("FatPoint2", NEW ring class -- added to
   order4sat_beyond.py and ringcheck.py CASES in the same session; do not
   cite these rows before ringcheck.log's rerun shows ALL PASSED):
   the first SQUARE-ZERO EMBDIM-2 base ever probed directly.
     S0  axioms+fiber2                              -> expect sat
     S1  + S'-HOLDS witness                          -> expect sat
     S2  + S'-FAIL (ForAll over syzygy divisions)    -> expect UNSAT
         = machine confirmation of THEOREM N (fifth note section 3:
           S' universal over equal-char square-zero bases).
     PW0 + psi_u != 0 and psi_v != 0                 -> expect sat
         (non-vacuity: both directional symbols realizable at once)
     PW  + (psi_u psi_v != 0 or psi_v psi_u != 0)    -> expect UNSAT
         = machine confirmation of PAIRWISE NILPOTENCE (fifth note
           Lemma 2.1) -- psi_u, psi_v are the u-/v-digit symbol matrices.
   Both fiber shapes (t4 and xy).

B. Base F2[eps]/eps^5, t^4 fiber, Delta_0 pinned to the (c1,c4) normal form
   (bundle probe encoding, s5_t4_partial_probe.py, verified in-session;
   over F_2 the c1 vs c1^2 pin difference is Frobenius-invisible), with the
   BANKED D2-D4 identities as constraints:
     rows (2,3),(3,1),(3,2),(3,3): expect unsat -- cross-validation of the
       Lemma 1.1 product-row prediction (bundle had no verdicts for these);
     row (1,3): THE open cotangent component -- expect unsat, NO timeout;
       this may grind for hours and is deliberately LAST in the script.

Crash-resume: each verdict prints+flushes immediately; on relaunch, rows
whose verdicts already appear in s5gates.log can be trusted (encodings are
deterministic); use --skip-a to jump straight to battery B.
"""
import sys
from z3 import (BitVec, BitVecVal, Solver, Or, And, Not, sat, unsat,
                is_true, simplify)

from order4sat_beyond import F2Quot, F2epsN, FatPoint2
from s2check import build_blocks, phi_of_coords, elems_of, canon
from s2check_np import gen_xy, gateR_np, sp_np_constraints
from s3gates import KF2, digit

T4 = {(1, 1, 2): 1, (1, 2, 3): 1}
XY = {(1, 2, 3): 1}
FAILED = False


def check(label, constraints, expect):
    global FAILED
    s = Solver()
    for e in constraints:
        s.add(e)
    r = s.check()
    verdict = "OK" if (expect is None or str(r) == expect) else "MISMATCH"
    if verdict == "MISMATCH":
        FAILED = True
    print(f"  [{label}] -> {r}  (expect {expect})  [{verdict}]", flush=True)
    return r


def xor_all(bits):
    out = BitVecVal(0, 1)
    for b in bits:
        out = out ^ b
    return out


def battery_A():
    R = FatPoint2
    gx, gy = gateR_np(R)   # asserts m = uR + vR; prints |Syz_1| (expect 16)
    for fib, fname in ((T4, "t^4"), (XY, "xy")):
        print(f"===== A: base {R.name}, fiber {fname} =====", flush=True)
        A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
        base = A + Mb + C + F
        holds, fail = sp_np_constraints(R, phi, gx, gy, f"fp2{fname}")
        check("S0 : axioms+fiber2", base, "sat")
        check("S1 : + S'-HOLDS witness", base + [holds], "sat")
        check("S2 : + S'-FAIL  [THEOREM N GATE]", base + [fail], "unsat")
        # directional symbols: psi_u[i][r] = u-coord of phi(e_i)_r, etc.
        pu = {(i, r): phi[i][r][1] for i in range(1, 4) for r in range(1, 4)}
        pv = {(i, r): phi[i][r][2] for i in range(1, 4) for r in range(1, 4)}
        comp = lambda P1, P2, i, r: xor_all(
            [P2[(i, rho)] & P1[(rho, r)] for rho in range(1, 4)])
        pw_nz = Or(*[comp(P1, P2, i, r) != 0
                     for (P1, P2) in ((pu, pv), (pv, pu))
                     for i in range(1, 4) for r in range(1, 4)])
        pu_nz = Or(*[pu[(i, r)] != 0 for i in range(1, 4) for r in range(1, 4)])
        pv_nz = Or(*[pv[(i, r)] != 0 for i in range(1, 4) for r in range(1, 4)])
        check("PW0: + psi_u != 0, psi_v != 0 (non-vacuity)",
              base + [pu_nz, pv_nz], "sat")
        check("PW : + psi_u psi_v != 0 or psi_v psi_u != 0  [LEMMA 2.1 GATE]",
              base + [pw_nz], "unsat")


def battery_B():
    K = KF2()

    def ksum(xs):
        out = K.zero()
        for x in xs:
            out = K.add(out, x)
        return out

    def dmat(P, s):
        out = {}
        for i in range(1, 4):
            for ss in range(1, 4):
                terms = []
                for n in range(1, s):
                    m = s - n
                    if n in P and m in P:
                        for r in range(1, 4):
                            terms.append(K.mul(P[n][(i, r)], P[m][(r, ss)]))
                out[(i, ss)] = ksum(terms)
        return out

    R = F2epsN(5)
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, T4)
    base = A + Mb + C + F
    c1 = BitVec('pin_c1_s5g', 1)
    c4 = BitVec('pin_c4_s5g', 1)

    def pin0(i, j, k):
        if i == 1:
            if (j, k) in [(1, 2), (2, 1), (2, 3), (3, 2)]:
                return c1     # over F_2, c1^2 = c1 (Frobenius-invisible)
            if (j, k) == (2, 2):
                return c4
            return BitVecVal(0, 1)
        if i == 2:
            return BitVecVal(0, 1)
        if (j, k) in [(1, 2), (2, 1)]:
            return BitVecVal(1, 1)
        if (j, k) in [(2, 3), (3, 2)]:
            return c1
        return BitVecVal(0, 1)

    for i in range(1, 4):
        for j in range(1, 4):
            for k in range(1, 4):
                base.append(digit(R, c[(i, j, k)], 0) == pin0(i, j, k))
    P = {n: {(i, r): digit(R, phi[i][r], n)
             for i in range(1, 4) for r in range(1, 4)} for n in range(1, 5)}
    known = (list(dmat(P, 2).values()) + list(dmat(P, 3).values())
             + list(dmat(P, 4).values()))
    D5 = dmat(P, 5)
    print("===== B: base F2[eps]/eps^5, t^4 pinned, banked D2-D4 =====",
          flush=True)
    for key in [(2, 3), (3, 1), (3, 2), (3, 3)]:
        s = Solver()
        for e in base:
            s.add(e)
        for x in known:
            s.add(K.eq0(x))
        s.add(K.neq0(D5[key]))
        print(f"  [D5{key} negation (Lemma 1.1 row)] -> {s.check()}"
              "  (expect unsat)", flush=True)
    print("  -- now the open cotangent component D5(1,3), NO timeout --",
          flush=True)
    s = Solver()
    for e in base:
        s.add(e)
    for x in known:
        s.add(K.eq0(x))
    s.add(K.neq0(D5[(1, 3)]))
    print(f"  [D5(1,3) negation  [THE GAP]] -> {s.check()}  (expect unsat)",
          flush=True)


if __name__ == "__main__":
    if "--skip-a" not in sys.argv:
        battery_A()
    battery_B()
    print("DONE s5gates" + ("" if not FAILED else "  -- WITH MISMATCHES"),
          flush=True)
