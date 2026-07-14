#!/usr/bin/env python3
r"""
s2check_np2.py -- S' probe over non-principal m, second encoding (session 9).

s2check_np.py (design option (i): 24-bit bitvector ForAll with an implication
guard, MBQI) settled three of the four (base, fiber) rows and returned
`unknown` on FatPoint3/xy.  This script re-encodes S'-FAIL with the
quantifier ranging over a CONCRETE F2-BASIS of the syzygy module -- design
option (ii) of HANDOFF §0-4.2, in Boolean-parameterized rather than unrolled
form:

    Syz_1 = {(alpha, beta) in R^2 : x alpha + y beta = 0}   (an R-submodule,
            hence an F2-subspace; |Syz_1| = 32 over BiDual, 128 over FatPoint3)

    gateS  enumerates Syz_1, extracts an F2-basis by Gaussian elimination,
           and VERIFIES span(basis) = Syz_1 exhaustively.

    The full division-ambiguity module is Syz(x,y; I) = Syz_1^3
    (coordinate-wise, I free of rank 3), so the solution coset of
    x*a + y*b = phi(e_i) is (a0, b0) + span of 3*dim(Syz_1) concrete
    generators.  Then

    FAIL_i = [x*a0 + y*b0 = phi(e_i)]  AND
             ForAll lambda in {0,1}^(3 dim):
                 not ( a0 + A(lambda) in K  and  b0 + B(lambda) in K )

    with (A, B)(lambda) = sum lambda_g * gen_g, gen_g concrete.  No
    implication guard: every lambda instantiation IS a coset point, which is
    exactly the structure MBQI likes.  K = ker(phi) /\ I as usual.
    S'-HOLDS stays quantifier-free (symbolic witness pair per basis vector).

Readings identical to s2check_np.py: S2 unsat = S' holds universally over
this exact ring => (THEORY Thm 7.1) killed-by-4 over every socle-line
extension.  S2 sat = S'-violating bialgebra (NOT a Grothendieck
counterexample); apply HANDOFF §D discipline.

Gates (script ABORTS before the main table if any fails):
  gateS (per ring)   : Syz_1 enumeration + basis-spans-Syz_1 verification +
                       |Syz_1| fingerprint (32 / 128).
  gate0/1/1b/2/3     : ported from s2check_np.py verbatim (same pinned point,
                       same expectations), but with the new FAIL encoding --
                       in particular gate3 (HOLDS /\ FAIL -> unsat)
                       machine-checks coset completeness of the
                       basis parameterization.
Cross-validation: the three rows s2check_np already settled (BiDual xy,
BiDual t4, FatPoint3 t4) are re-run first; they must reproduce `unsat`
before the FatPoint3/xy verdict counts.
"""
import sys
from z3 import (BitVec, BitVecVal, Solver, Or, And, Not, ForAll,
                simplify, sat, unsat, set_param, is_true)

from order4sat_beyond import BiDual, FatPoint3
from s2check import build_blocks, phi_of_coords, elems_of, canon

GATE_FAILED = False
FRESHNP = [0]


def gen_xy(R):
    gx = tuple(BitVecVal(1 if i == 1 else 0, 1) for i in range(R.n))
    gy = tuple(BitVecVal(1 if i == 2 else 0, 1) for i in range(R.n))
    return gx, gy


def elem_to_mask(pair, n):
    a, b = pair
    m = 0
    for i in range(n):
        m |= simplify(a[i]).as_long() << i
        m |= simplify(b[i]).as_long() << (n + i)
    return m


def mask_to_elem(mask, n):
    a = tuple(BitVecVal((mask >> i) & 1, 1) for i in range(n))
    b = tuple(BitVecVal((mask >> (n + i)) & 1, 1) for i in range(n))
    return a, b


def gateS(R):
    """Enumerate Syz_1, extract an F2-basis, verify span == Syz_1."""
    els = elems_of(R)
    n = R.n
    gx, gy = gen_xy(R)
    syz = [(a, b) for a in els for b in els
           if is_true(simplify(R.eq0(R.add(R.mul(gx, a), R.mul(gy, b)))))]
    masks = sorted({elem_to_mask(s, n) for s in syz})
    assert len(masks) == len(syz), f"{R.name}: duplicate syzygies?!"
    basis = []
    for m in masks:
        cur = m
        for b in basis:
            cur = min(cur, cur ^ b)
        if cur:
            basis.append(cur)
            basis.sort(reverse=True)
    span = {0}
    for b in basis:
        span |= {s ^ b for s in span}
    assert span == set(masks), f"{R.name}: basis does not span Syz_1"
    assert 2 ** len(basis) == len(syz), f"{R.name}: |Syz_1| != 2^dim"
    print(f"  gateS {R.name}: |Syz_1| = {len(syz)} = 2^{len(basis)}, "
          f"basis verified to span  [OK]", flush=True)
    return gx, gy, [mask_to_elem(b, n) for b in basis]


def scale_bit(el, bit):
    """Ring element el (tuple of 1-bit components) scaled by a 1-bit scalar."""
    return tuple(bit & comp for comp in el)


def module_div_eqs(R, phi_i, av, bv, gx, gy):
    return [R.eq0(R.sub(R.add(R.mul(gx, av[r - 1]), R.mul(gy, bv[r - 1])),
                        phi_i[r]))
            for r in range(1, 4)]


def in_kernel(R, phi, vec):
    return And(*[R.eq0(t) for t in phi_of_coords(R, phi, vec)])


def sp_np2_constraints(R, phi, gx, gy, syzbasis, tag):
    """(sp_holds, sp_fail) with the Boolean-basis coset parameterization."""
    dim = len(syzbasis)
    holds, fails = [], []
    for i in range(1, 4):
        ah = [R.var(f"{tag}ah{i}_{r}") for r in range(1, 4)]
        bh = [R.var(f"{tag}bh{i}_{r}") for r in range(1, 4)]
        holds.append(And(*module_div_eqs(R, phi[i], ah, bh, gx, gy),
                         in_kernel(R, phi, ah), in_kernel(R, phi, bh)))

        af = [R.var(f"{tag}af{i}_{r}") for r in range(1, 4)]
        bf = [R.var(f"{tag}bf{i}_{r}") for r in range(1, 4)]
        FRESHNP[0] += 1
        lams = {(r, g): BitVec(f"{tag}L{FRESHNP[0]}_{i}_{r}_{g}", 1)
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
        fails.append(And(*module_div_eqs(R, phi[i], af, bf, gx, gy),
                         ForAll(list(lams.values()), body)))
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
    print("===== GATES (base F2[x,y]/(x^2,y^2), fiber xy, np2 encoding) =====",
          flush=True)
    R = BiDual
    gx, gy, syzb = gateS(R)
    fn, fib = FIBS[0]
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
    sp_holds, sp_fail = sp_np2_constraints(R, phi, gx, gy, syzb, "g")

    check("gate0: A+M+C+F sanity", A + Mb + C + F, expect="sat")

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
    check("gate3 : S'-HOLDS + S'-FAIL together (coset completeness)",
          A + Mb + C + F + [sp_holds, sp_fail], expect="unsat")
    if GATE_FAILED:
        print("===== A GATE FAILED -- ABORTING BEFORE MAIN TABLE =====",
              flush=True)
        sys.exit(1)
    print("===== ALL GATES PASSED =====\n", flush=True)


def run_row(R, fn, fib):
    print(f"===== base {R.name}, fiber {fn} =====", flush=True)
    gx, gy, syzb = gateS(R)
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
    sp_holds, sp_fail = sp_np2_constraints(R, phi, gx, gy, syzb, "q")
    check("S1: axioms+fiber2+S'-HOLDS (expect sat)",
          A + Mb + C + F + [sp_holds], expect="sat")
    check("S2: axioms+fiber2 + S'-FAILS", A + Mb + C + F + [sp_fail])


if __name__ == "__main__":
    set_param("parallel.enable", True)
    run_gates()
    if "--gaponly" not in sys.argv:
        # cross-validation rows first (all settled unsat by s2check_np), then the gap
        # (crash recovery Jul 9: all three reproduced `unsat` in the pre-crash log,
        #  so --gaponly skips them and reruns gates + the gap row only)
        run_row(BiDual, *FIBS[0])
        run_row(BiDual, *FIBS[1])
        run_row(FatPoint3, *FIBS[1])
    run_row(FatPoint3, *FIBS[0])          # THE GAP: previous verdict `unknown`
    print("DONE s2check_np2", flush=True)
