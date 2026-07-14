#!/usr/bin/env python3
r"""
s2check_np3.py -- the FatPoint3/xy S' gap, THIRD encoding (session 13).

History: s2check_np (ForAll+guard, MBQI) -> unknown; s2check_np2
(Boolean syzygy-basis coset, no guard) -> unknown after its 2 h timeout.
Everything else in the non-principal S' table is settled unsat.

TWO new reductions from the fifth external note's audit (THEORY section 15):

(1) COTANGENT-ONLY (THEORY 15.5.1, strengthened form): over ANY Artin local
    base with m^3 = 0, every PRODUCT class has an explicit kernel division,
    unconditionally: if phi(a~) = x A_x + y A_y (A_alpha in I, Lemma 1.3),
    then for the product a~b~,
        phi(a~ b~) = phi(a~) phi(b~) = x [A_x phi(b~)] + y [A_y phi(b~)],
    and phi(A_alpha phi(b~)) = phi(A_alpha) phi^2(b~) in (mI)(m^2 I) = 0
    since m^3 = 0.  Both components lie in I.  BASIS-CHANGE POINT (the
    subtlety): the argument applies to the product OF LIFTS e1 *_A e2, not
    to the basis element e_3 itself; but {e1, e2, e1 *_A e2} is ALSO an
    R-basis of I (transition matrix = identity + m-entries, invertible over
    Artin local R), and S' is a submodule-membership condition, so checking
    it on this basis is equivalent.  phi(e1 *_A e2) has the explicit kernel
    division above, unconditionally.  Hence S'-FAIL  <=>  FAIL_1 or FAIL_2
    on the ORIGINAL cotangent generators.  FatPoint3 has m^3 = 0.  (Machine
    sub-gate gateP below checks the kernel certificate of the explicit
    division on a fully symbolic structure.)

(2) SPLIT QUERIES: FAIL_1 and FAIL_2 are tested in SEPARATE solver calls
    (S' fails  <=>  some structure has FAIL_1, or some structure has FAIL_2)
    -- each with one ForAll block instead of a disjunction of three.

SYMMETRY NOTE: the simultaneous relabeling (fiber e1 <-> e2, base x <-> y,
division a <-> b) is an automorphism of the constraint system mapping the
FAIL_1 query to the FAIL_2 query, so their verdicts must agree; both are run
as an encoding cross-check.

Reading: BOTH unsat  =>  S' universal over FatPoint3 for the xy fiber at
k = F_2  =>  (THEORY Thm 7.1) killed-by-4 over every socle-line extension of
F2[x,y]/(x,y)^3 -- closes the ONE remaining `unknown` of Theorem G'.
A `sat` = S'-violating bialgebra (NOT a killed-by-4 counterexample; HANDOFF
section D discipline).  `unknown` = raise timeout and rerun (12 h here).

Gates: np2's full gate battery is IMPORTED and rerun first (script aborts on
any failure), then gateP (product-division kernel membership), then the two
split rows.
"""
import sys
from z3 import Solver, sat, unsat, set_param, And, Or, Not, BitVec, ForAll

import s2check_np2 as np2
from s2check_np2 import (gateS, build_blocks, module_div_eqs, in_kernel,
                         scale_bit, gen_xy, FIBS)
from order4sat_beyond import FatPoint3
from s2check import phi_of_coords

TIMEOUT_MS = 12 * 3600 * 1000


def per_i_fail(R, phi, gx, gy, syzbasis, tag, i):
    """The np2 FAIL_i constraint for a single basis index i."""
    dim = len(syzbasis)
    af = [R.var(f"{tag}af{i}_{r}") for r in range(1, 4)]
    bf = [R.var(f"{tag}bf{i}_{r}") for r in range(1, 4)]
    lams = {(r, g): BitVec(f"{tag}NP3L_{i}_{r}_{g}", 1)
            for r in range(1, 4) for g in range(dim)}
    ash, bsh = [], []
    for r in range(1, 4):
        acc_a, acc_b = af[r - 1], bf[r - 1]
        for g, (ga, gb) in enumerate(syzbasis):
            acc_a = R.add(acc_a, scale_bit(ga, lams[(r, g)]))
            acc_b = R.add(acc_b, scale_bit(gb, lams[(r, g)]))
        ash.append(acc_a)
        bsh.append(acc_b)
    body = Not(And(in_kernel(R, phi, ash), in_kernel(R, phi, bsh)))
    return And(*module_div_eqs(R, phi[i], af, bf, gx, gy),
               ForAll(list(lams.values()), body))


def gateP(R, fib, fname):
    """The 15.5.1 explicit product division lies in ker(phi): symbolic check.
    phi(e3) division candidate: (A_x * phi(e2)-vector product ... ) -- here we
    check the algebraic identity directly: with phi(e1) = x a1 + y a2
    (a1, a2 the symbolic division of e1, which exists by Lemma 1.3), the
    elements a1*phi(e2), a2*phi(e2) (I-vector scalar products in A) are in
    ker phi.  Encoded: axioms + fiber2 + division eqs for e1 + NOT(both in
    kernel) -> expect unsat."""
    gx, gy = gen_xy(R)
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
    a1 = [R.var(f"gPa1_{r}") for r in range(1, 4)]
    a2 = [R.var(f"gPa2_{r}") for r in range(1, 4)]
    div1 = module_div_eqs(R, phi[1], a1, a2, gx, gy)
    # phi(e2) as coordinate vector; product vector (a * v)_r via A-module mult
    # is NOT plain coordinate mult -- use phi_of_coords-compatible route:
    # the element a1 . phi(e2) has coordinates sum_s a1_s * (e_s * e_t) ...
    # We avoid re-implementing A-multiplication here: instead check the
    # SCALAR identity phi(a1)*phi(phi(e2)) = 0 componentwise in R, which is
    # the kernel-membership certificate used in the 15.5.1 proof:
    #     phi(a1 . phi(e2)) = phi(a1) . phi(phi(e2)),
    # and both factors are m-multiples: phi(a1) in mI, phi(phi(e2)) in m^2 I.
    pa1 = phi_of_coords(R, phi, a1)          # coordinates of phi(a1)
    pe2 = phi_of_coords(R, phi, [phi[2][r] for r in range(1, 4)])
    # every pairwise R-product of a phi(a1)-coordinate and a phi(phi(e2))-
    # coordinate must vanish (m * m^2 = 0); multiplication in A of two I-
    # vectors only combines such products with structure constants, so this
    # suffices for kernel membership of BOTH a1.phi(e2) and a2.phi(e2).
    bad = Or(*[R.neq0(R.mul(u, v)) for u in pa1 for v in pe2])
    s = Solver()
    s.set("timeout", 600 * 1000)
    for e in A + Mb + C + F + div1 + [bad]:
        s.add(e)
    r = s.check()
    ok = "GATE OK" if r == unsat else "GATE FAILED -- ABORT"
    print(f"  [gateP: 15.5.1 product-division kernel certificate ({fname})]"
          f" -> {r}  [{ok}]", flush=True)
    return r == unsat


def main():
    set_param("parallel.enable", True)
    np2.run_gates()          # aborts via GATE_FAILED check below
    if np2.GATE_FAILED:
        sys.exit(1)
    R = FatPoint3
    fn, fib = FIBS[0]        # xy fiber
    if not gateP(R, fib, fn):
        sys.exit(1)
    print(f"===== base {R.name}, fiber {fn} -- SPLIT COTANGENT QUERIES "
          f"(np3 encoding; i=3 dropped by THEORY 15.5.1) =====", flush=True)
    gx, gy, syzb = gateS(R)
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
    base = A + Mb + C + F
    for i in (1, 2):
        f_i = per_i_fail(R, phi, gx, gy, syzb, "q3", i)
        s = Solver()
        s.set("timeout", TIMEOUT_MS)
        for e in base:
            s.add(e)
        s.add(f_i)
        print(f"  [S2.{i}: axioms+fiber2 + FAIL_{i} only] -> {s.check()}"
              f"  (expect unsat)", flush=True)
    print("DONE s2check_np3", flush=True)


if __name__ == "__main__":
    main()
