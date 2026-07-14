#!/usr/bin/env python3
r"""
s2check_np.py -- S' probe over NON-PRINCIPAL maximal ideals (session 5).

s2check.py probed S'-universality (THEORY Conj 7.5.4) over curvilinear rings,
where m = (t) makes the solution set of t*k = phi(e_i) a single ann(t)-coset.
This script covers the non-principal case flagged as REQUIRED in HANDOFF
§0-4.2:  base rings with m = (x, y), namely

    BiDual    = F_2[x,y]/(x^2,y^2)   (length 4, non-curvilinear)
    FatPoint3 = F_2[x,y]/(x,y)^3     (length 6, m^2 != 0)

S' at e_i now reads:  EXISTS a, b in K := ker(phi) \cap I  with
phi(e_i) = x*a + y*b.  The solution set of x*a + y*b = v is a coset of the
syzygy module Syz(x,y)^3, which is NOT a single ann-shift (per coordinate
|Syz_1| = 32 over BiDual), and unlike the curvilinear case there is no defect
shortcut: changing the division (a,b) within the coset changes (phi(a),
phi(b)).  So "S' fails" is encoded with a genuine universal quantifier over
bitvectors (handoff design option (i), MBQI):

    FAIL_i  =  ForAll a, b in I:  (x*a + y*b = phi(e_i))  ->  not (a,b in K^2)

which is exactly  phi(e_i) not in m*K  (sound with or without fiber2, since
m*K = x*K + y*K -- K is an R-submodule).  S'-FAIL = FAIL_1 or FAIL_2 or
FAIL_3; S'-HOLDS stays quantifier-free (symbolic witnesses a_i, b_i).

Readings (same as s2check.py):
  * [S2] -> unsat = S' holds for EVERY rank-4 bialgebra with killed-by-2
    local fiber over this exact ring => (THEORY Thm 7.1) every free rank-4
    bialgebra with killed-by-2 fiber over EVERY socle-line extension of it
    is killed by 4.  This is the first S' datum outside principal m.
  * [S2] -> sat = an S'-violating bialgebra (still killed by 4!).  NOT a
    Grothendieck counterexample; it refutes universality of S' and redirects
    Lemma 7.4.  Apply HANDOFF §D discipline before believing the model.
  * [S2] -> unknown = MBQI gave up; fall back to design option (ii)
    (syzygy-coset unrolling with symmetry reduction).

Gates (golden rule 1; the script ABORTS before the main table if any fails):
  gateR_np (per ring) : enumeration check m = x*R + y*R (uses only mul +
                        simplify, independent of lowzero/deform), and the
                        |Syz_1| fingerprint (32 over BiDual).
  gate0  (BiDual, xy) : axioms+fiber2 sat (level-1 reproduction).
  gate1  (BiDual, xy) : pinned point + S'-FAIL -> must be unsat.  The point
                        is the handoff-16.2 point with eps^2 replaced by the
                        socle element xy of the BASE (same formal identities:
                        d^2 = 0, 2d = 0, d*m = 0).  Hand check: phi(e1) =
                        xy*e3 = x*(y e3), phi(y e3) = y*phi(e3) = 0, and
                        phi(e2) = phi(e3) = 0, so S' HOLDS there.
  gate1b (BiDual, xy) : same point + S'-HOLDS witness -> must be sat (also
                        certifies the pinned point satisfies the axioms).
  gate2  (BiDual, xy) : Delta-mult dropped (A+C+F) + S'-FAIL -> must be sat
                        (ablate.py logic: A+C+F admits [4]^# != 0 models and
                        S' => [4]^# = 0 by linearity; expected to persist
                        over this base).
  gate3  (BiDual, xy) : S'-HOLDS + S'-FAIL together -> must be unsat
                        (machine-checks that FAIL is the negation of HOLDS).

Ring classes BiDual / FatPoint3 are ringcheck.py-validated (golden rule 1b;
no ring class is added or edited here).  The equation builder is imported
from s2check.py (which reproduced its own gates on 2026-07-08).
"""
import sys
from z3 import (BitVecVal, Solver, Or, And, Not, Implies, ForAll,
                simplify, sat, unsat, set_param, is_true)

from order4sat_beyond import BiDual, FatPoint3
from s2check import build_blocks, phi_of_coords, elems_of, canon


GATE_FAILED = False


def gen_xy(R):
    """The two generators x = e_1, y = e_2 of m, as concrete elements."""
    gx = tuple(BitVecVal(1 if i == 1 else 0, 1) for i in range(R.n))
    gy = tuple(BitVecVal(1 if i == 2 else 0, 1) for i in range(R.n))
    return gx, gy


def gateR_np(R):
    """Enumeration check (independent of lowzero/deform, mul only):
    m := {z : lowzero(z)} equals x*R + y*R; report |Syz_1| fingerprint."""
    els = elems_of(R)
    gx, gy = gen_xy(R)
    m_low = {canon(z) for z in els if is_true(simplify(R.lowzero(z)))}
    span = {canon(R.add(R.mul(gx, a), R.mul(gy, b))) for a in els for b in els}
    assert span == m_low, f"{R.name}: m != xR + yR"
    syz1 = [(a, b) for a in els for b in els
            if is_true(simplify(R.eq0(R.add(R.mul(gx, a), R.mul(gy, b)))))]
    assert len(els) ** 2 == len(m_low) * len(syz1), \
        f"{R.name}: |R|^2 != |xR+yR| * |Syz_1|"
    print(f"  gateR_np {R.name}: m = xR + yR ({len(m_low)} elts), "
          f"|Syz_1| = {len(syz1)}  [OK]", flush=True)
    return gx, gy


def module_div_eqs(R, phi_i, av, bv, gx, gy):
    """Constraints: x*a + y*b = phi(e_i) as elements of I (coords 1..3)."""
    return [R.eq0(R.sub(R.add(R.mul(gx, av[r - 1]), R.mul(gy, bv[r - 1])),
                        phi_i[r]))
            for r in range(1, 4)]


def in_kernel(R, phi, vec):
    """vec = [v1,v2,v3] in I lies in ker phi (phi is R-linear)."""
    return And(*[R.eq0(t) for t in phi_of_coords(R, phi, vec)])


def sp_np_constraints(R, phi, gx, gy, tag):
    """(sp_holds, sp_fail) for non-principal m = (x, y).
    sp_holds: quantifier-free, one witness pair (a_i, b_i) per basis element.
    sp_fail : Or over i of ForAll-quantified 'no solution pair lies in K^2'."""
    holds, fails = [], []
    for i in range(1, 4):
        ah = [R.var(f"{tag}ah{i}_{r}") for r in range(1, 4)]
        bh = [R.var(f"{tag}bh{i}_{r}") for r in range(1, 4)]
        holds.append(And(*module_div_eqs(R, phi[i], ah, bh, gx, gy),
                         in_kernel(R, phi, ah), in_kernel(R, phi, bh)))

        af = [R.var(f"{tag}af{i}_{r}") for r in range(1, 4)]
        bf = [R.var(f"{tag}bf{i}_{r}") for r in range(1, 4)]
        bits = [bit for e in af + bf for bit in e]
        soln = And(*module_div_eqs(R, phi[i], af, bf, gx, gy))
        inK = And(in_kernel(R, phi, af), in_kernel(R, phi, bf))
        fails.append(ForAll(bits, Implies(soln, Not(inK))))
    return And(*holds), Or(*fails)


def check(label, constraints, expect=None):
    global GATE_FAILED
    s = Solver()
    s.set("timeout", 7200 * 1000)
    for a in constraints:
        s.add(a)
    res = s.check()
    tag = ""
    if expect is not None:
        if str(res) == expect:
            tag = "  [GATE OK]"
        else:
            tag = f"  [GATE FAILED: expected {expect} -- encoding wrong, ABORT]"
            GATE_FAILED = True
    print(f"  [{label}] -> {res}{tag}", flush=True)
    if res == sat and expect is None:
        try:
            m = s.model()
            nz = sorted((str(d), m[d].as_long()) for d in m.decls()
                        if d.arity() == 0 and m[d].as_long() != 0)
            print(f"    S'-violating bialgebra witness (NOT a counterexample "
                  f"to killed-by-4; see HANDOFF §D discipline): {nz}",
                  flush=True)
        except Exception as e:
            print(f"    (model print failed: {e})", flush=True)
    return res


FIBS = [("F_q[x,y]/(x^2,y^2)", {(1, 2, 3): 1}),
        ("F_q[t]/t^4", {(1, 1, 2): 1, (1, 2, 3): 1})]


def run_gates():
    print("===== GATES (base F2[x,y]/(x^2,y^2), fiber xy) =====", flush=True)
    R = BiDual
    gx, gy = gateR_np(R)
    fn, fib = FIBS[0]
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
    sp_holds, sp_fail = sp_np_constraints(R, phi, gx, gy, "g")

    check("gate0: A+M+C+F sanity", A + Mb + C + F, expect="sat")

    # pinned point: 16.2 with eps^2 -> socle element xy of the BASE.
    # Delta(e1) += xy * e2 (x) e1;  Delta(e3) = forced + xy * e2 (x) e3;
    # multiplication undeformed.
    sxy = tuple(BitVecVal(1 if i == 3 else 0, 1) for i in range(R.n))
    one, zero = R.one(), R.zero()
    pinned = {(1, 2, 1): sxy, (3, 1, 2): one, (3, 2, 1): one, (3, 2, 3): sxy}
    pin = []
    for key, cv in c.items():
        target = pinned.get(key, zero)
        pin.append(R.eq0(R.sub(cv, target)))
    for key, mv in Mtab.items():
        base = one if fib.get(key, 0) else zero
        pin.append(R.eq0(R.sub(mv, base)))

    check("gate1 : pinned point + S'-FAIL (S' holds there by hand)",
          A + Mb + C + F + pin + [sp_fail], expect="unsat")
    check("gate1b: pinned point + S'-HOLDS witness",
          A + Mb + C + F + pin + [sp_holds], expect="sat")
    check("gate2 : A+C+F (Delta-mult dropped) + S'-FAIL",
          A + C + F + [sp_fail], expect="sat")
    check("gate3 : S'-HOLDS + S'-FAIL together",
          A + Mb + C + F + [sp_holds, sp_fail], expect="unsat")
    if GATE_FAILED:
        print("===== A GATE FAILED -- ABORTING BEFORE MAIN TABLE =====",
              flush=True)
        sys.exit(1)
    print("===== ALL GATES PASSED =====\n", flush=True)


def run_ring(R):
    try:
        print(f"===== base {R.name} =====", flush=True)
        gx, gy = gateR_np(R)
        for fn, fib in FIBS:
            print(f"  --- fiber {fn} ---", flush=True)
            A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
            sp_holds, sp_fail = sp_np_constraints(R, phi, gx, gy, "q")
            check("S1: axioms+fiber2+S'-HOLDS (expect sat)",
                  A + Mb + C + F + [sp_holds], expect="sat")
            check("S2: axioms+fiber2 + S'-FAILS", A + Mb + C + F + [sp_fail])
    except AssertionError as e:
        print(f"  RING GATE FAILED for {R.name}: {e} -- SKIPPING RING",
              flush=True)


if __name__ == "__main__":
    set_param("parallel.enable", True)
    run_gates()
    for R in [BiDual, FatPoint3]:
        run_ring(R)
    print("DONE s2check_np", flush=True)
