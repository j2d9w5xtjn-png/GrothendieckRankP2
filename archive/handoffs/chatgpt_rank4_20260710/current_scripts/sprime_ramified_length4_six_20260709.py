#!/usr/bin/env python3
r"""Direct S' universality queries on six ramified length-four bases.

IMPORTANT: these are S' queries, not direct [4] queries.  An UNSAT S'-FAIL
query says every encoded rank-four bialgebra over that exact base satisfies

    phi(I) subset m (ker(phi) intersect I),    phi=[2]^#.

By the socle-extension theorem in THEORY_order4.md this implies killedness by
4 over every one-dimensional socle lift of the base.  A SAT S'-FAIL result is
not a counterexample to Grothendieck's conjecture.

The six bases are the structural length-four quotients singled out in
STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md:

 principal:
   C34   = Z/4[p]/(p^3-2,p^4),
   C2tw  = Z/4[p]/(p^2-2p-2);

 nonprincipal:
   B00   = Z/4[x,y]/(2x,2y,x^2,xy,y^2),
   B1    = Z/4[x,y]/(2x,2y,x^2-2,xy,y^2),
   C4    = Z/4[y]/(2y,y^3),
   C8    = Z/8[y]/(2y,y^2).

For principal rings the exact finite ann(p)-coset encoding from s2check.py is
used.  For nonprincipal rings, FAIL_i is encoded exactly as a split universal
quantifier over all generator divisions, generalizing s2check_np.py to an
arbitrary number of maximal-ideal generators.  Splitting i=1,2,3 avoids a
large disjunction of quantified formulas.
"""

from __future__ import annotations

import itertools
import sys
import time

from z3 import (
    And, BitVec, BitVecVal, Extract, ForAll, Implies, Not, Or, Solver,
    ZeroExt, is_true, sat, set_param, simplify, unsat,
)

from order4sat import fresh
from order4sat_ramified_chain_twist_len4_20260709 import TwistedChainLen4
from order4sat_ramified_towers_20260709 import EisensteinTrunc, value
from s2check import build_blocks, phi_of_coords, sp_constraints


# Define the tiny kernel helper locally, exactly as in s2check_np.py.
def in_kernel(R, phi, vec):
    return And(*[R.eq0(z) for z in phi_of_coords(R, phi, vec)])


class Bxy:
    """B00 (square=0) or B1 (x^2=2), additive Z/4 + F2*x + F2*y."""

    def __init__(self, x2_is_two):
        self.x2_is_two = x2_is_two
        tag = "x^2-2" if x2_is_two else "x^2"
        self.name = f"Z/4[x,y]/(2x,2y,{tag},xy,y^2)"

    def zero(self):
        return BitVecVal(0, 2), BitVecVal(0, 1), BitVecVal(0, 1)

    def one(self):
        return BitVecVal(1, 2), BitVecVal(0, 1), BitVecVal(0, 1)

    def var(self, tag):
        n = fresh(tag)
        return BitVec(n + "_a", 2), BitVec(n + "_x", 1), BitVec(n + "_y", 1)

    def add(self, u, v):
        return u[0] + v[0], u[1] ^ v[1], u[2] ^ v[2]

    def sub(self, u, v):
        return u[0] - v[0], u[1] ^ v[1], u[2] ^ v[2]

    def mul(self, u, v):
        a, b, c = u
        A, B, C = v
        scalar = a * A
        if self.x2_is_two:
            scalar = scalar + BitVecVal(2, 2) * _zext1(b & B)
        xcoef = (Extract(0, 0, a) & B) ^ (b & Extract(0, 0, A))
        ycoef = (Extract(0, 0, a) & C) ^ (c & Extract(0, 0, A))
        return scalar, xcoef, ycoef

    def eq0(self, u):
        return And(*[z == 0 for z in u])

    def neq0(self, u):
        return Or(*[z != 0 for z in u])

    def lowzero(self, u):
        return Extract(0, 0, u[0]) == 0

    def deform(self, tag):
        v = self.var(tag)
        return BitVecVal(2, 2) * v[0], v[1], v[2]

    def concrete(self, a, b, c):
        return BitVecVal(a, 2), BitVecVal(b, 1), BitVecVal(c, 1)

    def elements(self):
        return [self.concrete(a, b, c)
                for a in range(4) for b in range(2) for c in range(2)]


def _zext1(bit):
    from z3 import ZeroExt
    return ZeroExt(1, bit)


class C4:
    name = "Z/4[y]/(2y,y^3)"

    def zero(self):
        return BitVecVal(0, 2), BitVecVal(0, 1), BitVecVal(0, 1)

    def one(self):
        return BitVecVal(1, 2), BitVecVal(0, 1), BitVecVal(0, 1)

    def var(self, tag):
        n = fresh(tag)
        return BitVec(n + "_a", 2), BitVec(n + "_y", 1), BitVec(n + "_y2", 1)

    def add(self, u, v):
        return u[0] + v[0], u[1] ^ v[1], u[2] ^ v[2]

    def sub(self, u, v):
        return u[0] - v[0], u[1] ^ v[1], u[2] ^ v[2]

    def mul(self, u, v):
        a, b, c = u
        A, B, C = v
        ycoef = (Extract(0, 0, a) & B) ^ (b & Extract(0, 0, A))
        y2coef = ((Extract(0, 0, a) & C) ^ (c & Extract(0, 0, A))
                  ^ (b & B))
        return a * A, ycoef, y2coef

    def eq0(self, u): return And(*[z == 0 for z in u])
    def neq0(self, u): return Or(*[z != 0 for z in u])
    def lowzero(self, u): return Extract(0, 0, u[0]) == 0
    def deform(self, tag):
        v = self.var(tag)
        return BitVecVal(2, 2) * v[0], v[1], v[2]
    def concrete(self, a, b, c):
        return BitVecVal(a, 2), BitVecVal(b, 1), BitVecVal(c, 1)
    def elements(self):
        return [self.concrete(a, b, c)
                for a in range(4) for b in range(2) for c in range(2)]


class C8:
    name = "Z/8[y]/(2y,y^2)"

    def zero(self): return BitVecVal(0, 3), BitVecVal(0, 1)
    def one(self): return BitVecVal(1, 3), BitVecVal(0, 1)
    def var(self, tag):
        n = fresh(tag)
        return BitVec(n + "_a", 3), BitVec(n + "_y", 1)
    def add(self, u, v): return u[0] + v[0], u[1] ^ v[1]
    def sub(self, u, v): return u[0] - v[0], u[1] ^ v[1]
    def mul(self, u, v):
        a, b = u
        A, B = v
        return a * A, (Extract(0, 0, a) & B) ^ (b & Extract(0, 0, A))
    def eq0(self, u): return And(u[0] == 0, u[1] == 0)
    def neq0(self, u): return Or(u[0] != 0, u[1] != 0)
    def lowzero(self, u): return Extract(0, 0, u[0]) == 0
    def deform(self, tag):
        v = self.var(tag)
        return BitVecVal(2, 3) * v[0], v[1]
    def concrete(self, a, b): return BitVecVal(a, 3), BitVecVal(b, 1)
    def elements(self):
        return [self.concrete(a, b) for a in range(8) for b in range(2)]


FIBERS = [
    ("F_2[x,y]/(x^2,y^2)", {(1, 2, 3): 1}),
    ("F_2[t]/t^4", {(1, 1, 2): 1, (1, 2, 3): 1}),
]


def flatten(elements):
    return [bit for elt in elements for bit in elt]


def module_div_eqs(R, phi_i, vecs, gens):
    eqs = []
    for r in range(1, 4):
        acc = R.zero()
        for gen, vec in zip(gens, vecs):
            acc = R.add(acc, R.mul(gen, vec[r - 1]))
        eqs.append(R.eq0(R.sub(acc, phi_i[r])))
    return eqs


def sp_nonprincipal_holds(R, phi, gens, tag):
    rows = []
    for i in range(1, 4):
        vecs = [[R.var(f"{tag}h{i}_{q}_{r}") for r in range(1, 4)]
                for q in range(len(gens))]
        rows.append(And(*module_div_eqs(R, phi[i], vecs, gens),
                        *[in_kernel(R, phi, vec) for vec in vecs]))
    return And(*rows)


def sp_nonprincipal_fail_i(R, phi, gens, tag, i):
    vecs = [[R.var(f"{tag}f{i}_{q}_{r}") for r in range(1, 4)]
            for q in range(len(gens))]
    soln = And(*module_div_eqs(R, phi[i], vecs, gens))
    all_kernel = And(*[in_kernel(R, phi, vec) for vec in vecs])
    quantified = flatten([elt for vec in vecs for elt in vec])
    return ForAll(quantified, Implies(soln, Not(all_kernel)))


def sp_b1_fail_i_coset(R, phi, gens, tag, i):
    """Optimized exact FAIL_i for B1.

    For m=(x,y), Syz(x,y) consists exactly of

      A=(2u, 0*x, c*y),   B=(2v, q*x, w*y),  u,c,v,q,w in F2.

    Hence a three-coordinate division coset needs 15 quantified Boolean bits,
    instead of 24 quantified bits plus an implication guard in the generic
    formula.  gate_b1_syz() exhaustively checks this parametrization.
    """
    assert isinstance(R, Bxy) and R.x2_is_two and len(gens) == 2
    av = [R.var(f"{tag}b1a{i}_{r}") for r in range(1, 4)]
    bv = [R.var(f"{tag}b1b{i}_{r}") for r in range(1, 4)]
    shifted_a, shifted_b, lams = [], [], []
    for r in range(3):
        u = BitVec(f"{tag}b1u_{i}_{r}", 1)
        c = BitVec(f"{tag}b1c_{i}_{r}", 1)
        v = BitVec(f"{tag}b1v_{i}_{r}", 1)
        q = BitVec(f"{tag}b1q_{i}_{r}", 1)
        w = BitVec(f"{tag}b1w_{i}_{r}", 1)
        lams += [u, c, v, q, w]
        ashift = (BitVecVal(2, 2) * ZeroExt(1, u), BitVecVal(0, 1), c)
        bshift = (BitVecVal(2, 2) * ZeroExt(1, v), q, w)
        shifted_a.append(R.add(av[r], ashift))
        shifted_b.append(R.add(bv[r], bshift))
    division = And(*module_div_eqs(R, phi[i], [av, bv], gens))
    misses = Not(And(in_kernel(R, phi, shifted_a),
                     in_kernel(R, phi, shifted_b)))
    return And(division, ForAll(lams, misses))


def gate_b1_syz(R, gens):
    els = R.elements()
    zero = R.zero()
    actual = {(value(a), value(b)) for a in els for b in els
              if value(R.add(R.mul(gens[0], a), R.mul(gens[1], b)))
              == value(zero)}
    parametrized = set()
    for u, c, v, q, w in itertools.product((0, 1), repeat=5):
        a = R.concrete(2*u, 0, c)
        b = R.concrete(2*v, q, w)
        parametrized.add((value(a), value(b)))
    assert actual == parametrized and len(actual) == 32
    print("  [B1 syzygy gate] exact 5-bit Syz(x,y), size 32 -> PASS", flush=True)


def residual_metadata(R, gens):
    """Return (Soc(R), residual syzygy generators modulo Soc(R)^q).

    Each residual generator is a q-tuple of ring elements, q=len(gens).
    In all four target rings the residual syzygy space has dimension at most
    one over F2.  The exhaustive gate below verifies the claim directly.
    """
    z = R.zero()
    els = R.elements()
    soc = [a for a in els if all(value(R.mul(a, g)) == value(z) for g in gens)]
    if isinstance(R, Bxy) and not R.x2_is_two:       # B00: m^2=0, no residual
        residual = []
    elif isinstance(R, Bxy):                         # B1: (A,B)=(0,x)
        residual = [(z, R.concrete(0, 1, 0))]
    elif isinstance(R, C4):                          # (A,B)=(y,2)
        residual = [(R.concrete(0, 1, 0), R.concrete(2, 0, 0))]
    elif isinstance(R, C8):                          # (A,B)=(0,2)
        residual = [(z, R.concrete(2, 0))]
    else:
        raise TypeError(R.name)
    return soc, residual


def gate_residual_syzygies(R, gens, soc, residual):
    """Exhaustively prove Syz(gens)=Soc(R)^q plus the listed residual line."""
    els, z = R.elements(), R.zero()
    q = len(gens)
    actual = set()
    for coeffs in itertools.product(els, repeat=q):
        total = z
        for g, a in zip(gens, coeffs):
            total = R.add(total, R.mul(g, a))
        if value(total) == value(z):
            actual.add(tuple(value(a) for a in coeffs))

    parametrized = set()
    for base in itertools.product(soc, repeat=q):
        for bits in itertools.product((0, 1), repeat=len(residual)):
            coeffs = list(base)
            for bit, shift in zip(bits, residual):
                if bit:
                    coeffs = [R.add(a, b) for a, b in zip(coeffs, shift)]
            parametrized.add(tuple(value(a) for a in coeffs))
    assert actual == parametrized
    print(f"  [quotient-syzygy gate] |Soc|={len(soc)}, |Syz|={len(actual)}, "
          f"residual dimension={len(residual)} -> PASS", flush=True)


def sp_residual_fail_i(R, phi, gens, residual, tag, i):
    """Quantifier-free exact FAIL_i after quotienting division coefficients.

    Under the fiber2 constraints every matrix entry of phi lies in m.  Hence
    Soc(R)=Ann(m) kills phi, so adding a socle element to any division
    coefficient changes neither the division equation nor kernel membership.
    gate_residual_syzygies proves that the only remaining choices are the
    listed residual F2 syzygies, independently in the three I-coordinates.
    """
    q = len(gens)
    vecs = [[R.var(f"{tag}r{i}_{j}_{r}") for r in range(1, 4)] for j in range(q)]
    division = And(*module_div_eqs(R, phi[i], vecs, gens))
    misses = []
    # All four targets have either zero or one residual syzygy generator.
    patterns = itertools.product((0, 1), repeat=3) if residual else [()]
    for pattern in patterns:
        shifted = [list(vec) for vec in vecs]
        if residual:
            shift = residual[0]
            for r, bit in enumerate(pattern):
                if bit:
                    for j in range(q):
                        shifted[j][r] = R.add(shifted[j][r], shift[j])
        misses.append(Not(And(*[in_kernel(R, phi, vec) for vec in shifted])))
    return And(division, *misses)


def check(label, constraints, timeout, expect=None):
    s = Solver()
    s.set("timeout", timeout * 1000)
    s.add(*constraints)
    t0 = time.monotonic()
    res = s.check()
    gate = ""
    if expect is not None:
        gate = " [GATE OK]" if res == expect else f" [GATE FAIL expected {expect}]"
    print(f"    [{label}] -> {res}{gate} ({time.monotonic()-t0:.2f}s)", flush=True)
    return res


def generic_ring_gate(R, gens):
    els = R.elements()
    zero, one = R.zero(), R.one()
    vals = {value(x) for x in els}
    for u, v, w in itertools.product(els, repeat=3):
        assert value(R.mul(u, one)) == value(u)
        assert value(R.mul(u, v)) == value(R.mul(v, u))
        assert value(R.mul(R.mul(u, v), w)) == value(R.mul(u, R.mul(v, w)))
        assert value(R.mul(u, R.add(v, w))) == value(R.add(R.mul(u, v), R.mul(u, w)))
    m = {value(x) for x in els if is_true(simplify(R.lowzero(x)))}
    span = set()
    for coeffs in itertools.product(els, repeat=len(gens)):
        z = zero
        for g, a in zip(gens, coeffs):
            z = R.add(z, R.mul(g, a))
        span.add(value(z))
    assert span == m
    print(f"  [ring/generator gate] |R|={len(vals)}, |m|={len(m)}, "
          f"generators={len(gens)} -> PASS", flush=True)


def run_principal(R, p, timeout):
    print(f"===== S' PRINCIPAL base {R.name} =====", flush=True)
    els = list(R.elements())
    m = {value(x) for x in els if is_true(simplify(R.lowzero(x)))}
    pR = {value(R.mul(p, x)) for x in els}
    assert m == pR
    ann = [x for x in els if is_true(simplify(R.eq0(R.mul(p, x))))]
    print(f"  [ring/generator gate] |R|={len(els)}, |m|={len(m)}, "
          f"|ann(p)|={len(ann)} -> PASS", flush=True)
    for name, fib in FIBERS:
        print(f"  --- fiber {name} ---", flush=True)
        A, M, C, F, phi, _, _ = build_blocks(R, fib)
        holds, fails = sp_constraints(R, phi, p, ann, "pr")
        check("S1 axioms+fiber2+S'-HOLDS", A+M+C+F+[holds], timeout, sat)
        check("S2 axioms+fiber2+S'-FAILS", A+M+C+F+[fails], timeout)


def run_nonprincipal(R, gens, timeout):
    print(f"===== S' NONPRINCIPAL base {R.name} =====", flush=True)
    generic_ring_gate(R, gens)
    soc, residual = residual_metadata(R, gens)
    gate_residual_syzygies(R, gens, soc, residual)
    for name, fib in FIBERS:
        print(f"  --- fiber {name} ---", flush=True)
        A, M, C, F, phi, _, _ = build_blocks(R, fib)
        base = A + M + C + F
        holds = sp_nonprincipal_holds(R, phi, gens, "np")
        check("S1 axioms+fiber2+S'-HOLDS", base+[holds], timeout, sat)
        for i in range(1, 4):
            fail_i = sp_residual_fail_i(R, phi, gens, residual, "np", i)
            check(f"S2.{i} axioms+fiber2+S'-FAIL_i", base+[fail_i], timeout)


def main():
    timeout = int(sys.argv[1]) if len(sys.argv) > 1 else 7200
    set_param("parallel.enable", True)
    print("DIRECT S' SEARCH -- RESULTS ARE NOT DIRECT [4] VERDICTS", flush=True)

    c34 = EisensteinTrunc(3, 4)
    run_principal(c34, c34.pi(), timeout)
    c2tw = TwistedChainLen4()
    run_principal(c2tw, c2tw.concrete(0, 1), timeout)

    b00 = Bxy(False)
    run_nonprincipal(b00,
        [b00.concrete(2,0,0), b00.concrete(0,1,0), b00.concrete(0,0,1)], timeout)
    b1 = Bxy(True)
    run_nonprincipal(b1, [b1.concrete(0,1,0), b1.concrete(0,0,1)], timeout)
    c4 = C4()
    run_nonprincipal(c4, [c4.concrete(2,0,0), c4.concrete(0,1,0)], timeout)
    c8 = C8()
    run_nonprincipal(c8, [c8.concrete(2,0), c8.concrete(0,1)], timeout)
    print("DONE sprime_ramified_length4_six_20260709", flush=True)


if __name__ == "__main__":
    main()
