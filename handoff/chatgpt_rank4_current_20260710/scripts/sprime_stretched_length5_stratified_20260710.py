#!/usr/bin/env python3
r"""Exact stratified S' sweep on the seven stretched length-five quotients.

The bases are precisely the seven rings in
``STRUCTURAL_LENGTH6_QUOTIENTS_F2_2026-07-10.md`` Section 3.  Every ring is
represented exactly by its finite additive coordinates (32 elements), and
the driver checks the complete ring tables, local filtration, socle, maximal
ideal generators, and the full syzygy module before constructing a Hopf
query.

For each base the query covers all six F_2-rational ``xy`` Hopf fibers and
all four ``t^4`` normal forms.  The S'-failure disjunction is split into the
three basis-vector queries FAIL_i.  Since fiber2 puts every entry of phi in
the maximal ideal, Soc(R)-shifts of a division coefficient do not change
kernel membership.  The exhaustively computed quotient

    Syz(g_1,g_2) / Soc(R)^2

has order four for each of the seven rings (it need not be elementary: the
Z/16 fiber-product row has a cyclic quotient).  Thus every FAIL_i is
unrolled over exactly 4^3=64 residual division representatives; there is no
quantified approximation.

Rows are classified separately as H0-vacuous, SAT S'-failure, UNSAT, or
unknown.  Every SAT result is validated both by evaluating every asserted
formula in the returned model and by an independent concrete check of the
division equation and all 64 residual representatives.  A compact exact
seed (multiplication, coproduct, and division coefficients) is printed.
"""

from __future__ import annotations

import argparse
import itertools
import time

from z3 import (
    And, BitVec, BitVecVal, Extract, Not, Or, Solver, ZeroExt, is_true, sat,
    set_param, simplify, unknown, unsat,
)

import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from order4sat import fresh
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_embdim2_len6_20260709 import PinCoproductResidue
from order4sat_ramified_towers_20260709 import value
from sprime_ramified_length4_six_20260709 import (
    in_kernel, module_div_eqs, sp_nonprincipal_holds,
)
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT, XY_MULT, t4_pins,
)
from s2check import build_blocks, phi_of_coords


def bv(n: int, width: int):
    return BitVecVal(n, width)


def bit0(x):
    return Extract(0, 0, x)


def allzero(xs):
    return And(*[x == 0 for x in xs])


def anynonzero(xs):
    return Or(*[x != 0 for x in xs])


class F2ChainFiberProduct:
    """F2[x,y]/(x^4,y^2,xy), basis 1,x,x^2,x^3,y."""

    key = "B_F2x4"
    name = "B(F2[x]/x^4)=F2[x,y]/(x^4,y^2,xy)"

    def zero(self): return tuple(bv(0, 1) for _ in range(5))
    def one(self): return (bv(1, 1),) + tuple(bv(0, 1) for _ in range(4))
    def var(self, tag):
        n = fresh(tag)
        return tuple(BitVec(f"{n}_{s}", 1) for s in ("a", "x", "x2", "x3", "y"))
    def add(self, u, v): return tuple(a ^ b for a, b in zip(u, v))
    def sub(self, u, v): return self.add(u, v)
    def mul(self, u, v):
        a, b, c, d, e = u
        A, B, C, D, E = v
        return (
            a & A,
            (a & B) ^ (b & A),
            (a & C) ^ (c & A) ^ (b & B),
            (a & D) ^ (d & A) ^ (b & C) ^ (c & B),
            (a & E) ^ (e & A),
        )
    def eq0(self, u): return allzero(u)
    def neq0(self, u): return anynonzero(u)
    def lowzero(self, u): return u[0] == 0
    def deform(self, tag):
        v = self.var(tag)
        return (bv(0, 1),) + v[1:]
    def concrete(self, a, x, x2, x3, y):
        return tuple(bv(q, 1) for q in (a, x, x2, x3, y))
    def elements(self):
        return [self.concrete(*q) for q in itertools.product((0, 1), repeat=5)]
    def generators(self):
        return [self.concrete(0, 1, 0, 0, 0), self.concrete(0, 0, 0, 0, 1)]
    def expected_socle(self):
        return [self.concrete(0, 0, 0, a, b) for a, b in itertools.product((0, 1), repeat=2)]
    def presentation_gate(self):
        x, y = self.generators(); z = self.zero()
        assert ev(cpow(self, x, 3)) != ev(z) and ev(cpow(self, x, 4)) == ev(z)
        assert ev(self.mul(x, y)) == ev(z) and ev(self.mul(y, y)) == ev(z)


class Z16FiberProduct:
    """Z/16[y]/(2y,y^2), additive Z/16 + F2*y."""

    key = "B_Z16"
    name = "B(Z/16)=Z/16[y]/(2y,y^2)"

    def zero(self): return bv(0, 4), bv(0, 1)
    def one(self): return bv(1, 4), bv(0, 1)
    def var(self, tag):
        n = fresh(tag); return BitVec(n + "_a", 4), BitVec(n + "_y", 1)
    def add(self, u, v): return u[0] + v[0], u[1] ^ v[1]
    def sub(self, u, v): return u[0] - v[0], u[1] ^ v[1]
    def mul(self, u, v):
        a, y = u; A, Y = v
        return a * A, (bit0(a) & Y) ^ (y & bit0(A))
    def eq0(self, u): return allzero(u)
    def neq0(self, u): return anynonzero(u)
    def lowzero(self, u): return bit0(u[0]) == 0
    def deform(self, tag):
        v = self.var(tag); return bv(2, 4) * v[0], v[1]
    def concrete(self, a, y): return bv(a, 4), bv(y, 1)
    def elements(self): return [self.concrete(a, y) for a in range(16) for y in (0, 1)]
    def generators(self): return [self.concrete(2, 0), self.concrete(0, 1)]
    def expected_socle(self):
        return [self.concrete(8 * a, b) for a, b in itertools.product((0, 1), repeat=2)]
    def presentation_gate(self):
        two, y = self.generators(); z = self.zero()
        assert ev(cpow(self, two, 3)) != ev(z) and ev(cpow(self, two, 4)) == ev(z)
        assert ev(self.mul(two, y)) == ev(z) and ev(self.mul(y, y)) == ev(z)


class QuadraticFiberProduct:
    """B(Z/4[x]/(x^2-2-2c*x)), c=0 or 1."""

    def __init__(self, twist: int):
        self.twist = twist
        self.key = f"B_quad_c{twist}"
        rel = "x^2-2" if not twist else "x^2-2x-2"
        self.name = f"B(Z/4[x]/({rel}))"
    def zero(self): return bv(0, 2), bv(0, 2), bv(0, 1)
    def one(self): return bv(1, 2), bv(0, 2), bv(0, 1)
    def var(self, tag):
        n = fresh(tag)
        return BitVec(n + "_a", 2), BitVec(n + "_x", 2), BitVec(n + "_y", 1)
    def add(self, u, v): return u[0] + v[0], u[1] + v[1], u[2] ^ v[2]
    def sub(self, u, v): return u[0] - v[0], u[1] - v[1], u[2] ^ v[2]
    def mul(self, u, v):
        a, x, y = u; A, X, Y = v
        return (
            a * A + bv(2, 2) * x * X,
            a * X + x * A + (bv(2, 2) * x * X if self.twist else bv(0, 2)),
            (bit0(a) & Y) ^ (y & bit0(A)),
        )
    def eq0(self, u): return allzero(u)
    def neq0(self, u): return anynonzero(u)
    def lowzero(self, u): return bit0(u[0]) == 0
    def deform(self, tag):
        v = self.var(tag); return bv(2, 2) * v[0], v[1], v[2]
    def concrete(self, a, x, y): return bv(a, 2), bv(x, 2), bv(y, 1)
    def elements(self):
        return [self.concrete(a, x, y) for a in range(4) for x in range(4) for y in (0, 1)]
    def generators(self): return [self.concrete(0, 1, 0), self.concrete(0, 0, 1)]
    def expected_socle(self):
        # x^3 is the active socle generator; y is the hidden one.
        x, y = self.generators(); x3 = cpow(self, x, 3)
        return [self.add(scale_concrete(self, a, x3), scale_concrete(self, b, y))
                for a, b in itertools.product((0, 1), repeat=2)]
    def presentation_gate(self):
        x, y = self.generators(); z = self.zero(); two = self.add(self.one(), self.one())
        rhs = two if not self.twist else self.add(two, self.mul(two, x))
        assert ev(self.mul(x, x)) == ev(rhs)
        assert ev(cpow(self, x, 3)) != ev(z) and ev(cpow(self, x, 4)) == ev(z)
        assert ev(self.mul(x, y)) == ev(z) and ev(self.mul(y, y)) == ev(z)


class CubicFiberProduct:
    """B(Z/4[x]/(x^3-2,x^4)), additive Z/4+F2*x+F2*x2+F2*y."""

    key = "B_cubic"
    name = "B(Z/4[x]/(x^3-2,x^4))"

    def zero(self): return bv(0, 2), bv(0, 1), bv(0, 1), bv(0, 1)
    def one(self): return bv(1, 2), bv(0, 1), bv(0, 1), bv(0, 1)
    def var(self, tag):
        n = fresh(tag)
        return (BitVec(n + "_a", 2), BitVec(n + "_x", 1),
                BitVec(n + "_x2", 1), BitVec(n + "_y", 1))
    def add(self, u, v):
        return u[0] + v[0], u[1] ^ v[1], u[2] ^ v[2], u[3] ^ v[3]
    def sub(self, u, v):
        return u[0] - v[0], u[1] ^ v[1], u[2] ^ v[2], u[3] ^ v[3]
    def mul(self, u, v):
        a, x, x2, y = u; A, X, X2, Y = v
        return (
            a * A + bv(2, 2) * ZeroExt(1, (x & X2) ^ (x2 & X)),
            (bit0(a) & X) ^ (x & bit0(A)),
            (bit0(a) & X2) ^ (x2 & bit0(A)) ^ (x & X),
            (bit0(a) & Y) ^ (y & bit0(A)),
        )
    def eq0(self, u): return allzero(u)
    def neq0(self, u): return anynonzero(u)
    def lowzero(self, u): return bit0(u[0]) == 0
    def deform(self, tag):
        v = self.var(tag); return bv(2, 2) * v[0], v[1], v[2], v[3]
    def concrete(self, a, x, x2, y):
        return bv(a, 2), bv(x, 1), bv(x2, 1), bv(y, 1)
    def elements(self):
        return [self.concrete(a, x, x2, y) for a in range(4)
                for x, x2, y in itertools.product((0, 1), repeat=3)]
    def generators(self): return [self.concrete(0, 1, 0, 0), self.concrete(0, 0, 0, 1)]
    def expected_socle(self):
        x, y = self.generators(); x3 = cpow(self, x, 3)
        return [self.add(scale_concrete(self, a, x3), scale_concrete(self, b, y))
                for a, b in itertools.product((0, 1), repeat=2)]
    def presentation_gate(self):
        x, y = self.generators(); z = self.zero(); two = self.add(self.one(), self.one())
        assert ev(cpow(self, x, 3)) == ev(two) and ev(cpow(self, x, 4)) == ev(z)
        assert ev(self.mul(x, y)) == ev(z) and ev(self.mul(y, y)) == ev(z)


class HiddenTangentQ0:
    """Q0=Z/4[x]/(x^4,2x), additive Z/4+F2*x+F2*x2+F2*x3."""

    key = "Q0"
    name = "Q0=Z/4[x]/(x^4,2x)"

    def zero(self): return bv(0, 2), bv(0, 1), bv(0, 1), bv(0, 1)
    def one(self): return bv(1, 2), bv(0, 1), bv(0, 1), bv(0, 1)
    def var(self, tag):
        n = fresh(tag)
        return (BitVec(n + "_a", 2), BitVec(n + "_x", 1),
                BitVec(n + "_x2", 1), BitVec(n + "_x3", 1))
    def add(self, u, v):
        return u[0] + v[0], u[1] ^ v[1], u[2] ^ v[2], u[3] ^ v[3]
    def sub(self, u, v):
        return u[0] - v[0], u[1] ^ v[1], u[2] ^ v[2], u[3] ^ v[3]
    def mul(self, u, v):
        a, x, x2, x3 = u; A, X, X2, X3 = v
        return (
            a * A,
            (bit0(a) & X) ^ (x & bit0(A)),
            (bit0(a) & X2) ^ (x2 & bit0(A)) ^ (x & X),
            (bit0(a) & X3) ^ (x3 & bit0(A)) ^ (x & X2) ^ (x2 & X),
        )
    def eq0(self, u): return allzero(u)
    def neq0(self, u): return anynonzero(u)
    def lowzero(self, u): return bit0(u[0]) == 0
    def deform(self, tag):
        v = self.var(tag); return bv(2, 2) * v[0], v[1], v[2], v[3]
    def concrete(self, a, x, x2, x3):
        return bv(a, 2), bv(x, 1), bv(x2, 1), bv(x3, 1)
    def elements(self):
        return [self.concrete(a, x, x2, x3) for a in range(4)
                for x, x2, x3 in itertools.product((0, 1), repeat=3)]
    def generators(self): return [self.concrete(2, 0, 0, 0), self.concrete(0, 1, 0, 0)]
    def expected_socle(self):
        two, x = self.generators(); x3 = cpow(self, x, 3)
        return [self.add(scale_concrete(self, a, two), scale_concrete(self, b, x3))
                for a, b in itertools.product((0, 1), repeat=2)]
    def presentation_gate(self):
        two, x = self.generators(); z = self.zero()
        assert ev(self.mul(two, x)) == ev(z)
        assert ev(cpow(self, x, 3)) != ev(z) and ev(cpow(self, x, 4)) == ev(z)


class HiddenTangentQ1:
    """Q1=Z/4[x]/(x^4,2x-x^3), additive Z/4+Z/4*x+F2*x2."""

    key = "Q1"
    name = "Q1=Z/4[x]/(x^4,2x-x^3)"

    def zero(self): return bv(0, 2), bv(0, 2), bv(0, 1)
    def one(self): return bv(1, 2), bv(0, 2), bv(0, 1)
    def var(self, tag):
        n = fresh(tag)
        return BitVec(n + "_a", 2), BitVec(n + "_x", 2), BitVec(n + "_x2", 1)
    def add(self, u, v): return u[0] + v[0], u[1] + v[1], u[2] ^ v[2]
    def sub(self, u, v): return u[0] - v[0], u[1] - v[1], u[2] ^ v[2]
    def mul(self, u, v):
        a, x, x2 = u; A, X, X2 = v
        return (
            a * A,
            a * X + x * A + bv(2, 2) * (
                x * ZeroExt(1, X2) + ZeroExt(1, x2) * X),
            (bit0(a) & X2) ^ (x2 & bit0(A)) ^ (bit0(x) & bit0(X)),
        )
    def eq0(self, u): return allzero(u)
    def neq0(self, u): return anynonzero(u)
    def lowzero(self, u): return bit0(u[0]) == 0
    def deform(self, tag):
        v = self.var(tag); return bv(2, 2) * v[0], v[1], v[2]
    def concrete(self, a, x, x2): return bv(a, 2), bv(x, 2), bv(x2, 1)
    def elements(self):
        return [self.concrete(a, x, x2) for a in range(4)
                for x in range(4) for x2 in (0, 1)]
    def generators(self): return [self.concrete(2, 0, 0), self.concrete(0, 1, 0)]
    def expected_socle(self):
        two, x = self.generators(); x2 = self.mul(x, x); x3 = self.mul(x2, x)
        other = self.add(two, x2)
        return [self.add(scale_concrete(self, a, x3), scale_concrete(self, b, other))
                for a, b in itertools.product((0, 1), repeat=2)]
    def presentation_gate(self):
        two, x = self.generators(); z = self.zero()
        assert ev(self.mul(two, x)) == ev(cpow(self, x, 3))
        assert ev(cpow(self, x, 3)) != ev(z) and ev(cpow(self, x, 4)) == ev(z)


def rings():
    return [
        F2ChainFiberProduct(), Z16FiberProduct(), QuadraticFiberProduct(0),
        QuadraticFiberProduct(1), CubicFiberProduct(), HiddenTangentQ0(),
        HiddenTangentQ1(),
    ]


def ev(x):
    return value(x)


def cpow(R, x, n):
    out = R.one()
    for _ in range(n): out = R.mul(out, x)
    return out


def scale_concrete(R, bit, x):
    return x if bit else R.zero()


def add_tuple(R, x, y):
    return tuple(R.add(a, b) for a, b in zip(x, y))


def tuple_key(x):
    return tuple(ev(a) for a in x)


def additive_span(addtab, zero_idx, generators):
    span = {zero_idx}
    for g in generators:
        old = list(span)
        # A generator can have additive order 4, 8, or 16.  Repeatedly close
        # under +g until no new point appears.
        frontier = list(old)
        while frontier:
            a = frontier.pop()
            b = addtab[a][g]
            if b not in span:
                span.add(b); frontier.append(b)
    return span


def exact_ring_socle_gate(R):
    """Exhaust the full finite operation tables and the (1,2,1,1) data."""
    started = time.monotonic()
    els = list(R.elements()); vals = [ev(a) for a in els]
    assert len(els) == len(set(vals)) == 32
    index = {a: i for i, a in enumerate(vals)}
    z = index[ev(R.zero())]; one = index[ev(R.one())]
    addtab = [[index[ev(R.add(a, b))] for b in els] for a in els]
    multab = [[index[ev(R.mul(a, b))] for b in els] for a in els]

    for i, j in itertools.product(range(32), repeat=2):
        assert addtab[i][j] == addtab[j][i]
        assert multab[i][j] == multab[j][i]
        assert addtab[i][z] == i and multab[i][one] == i and multab[i][z] == z
        assert ev(R.add(R.sub(els[i], els[j]), els[j])) == vals[i]
    for i, j, k in itertools.product(range(32), repeat=3):
        assert addtab[addtab[i][j]][k] == addtab[i][addtab[j][k]]
        assert multab[multab[i][j]][k] == multab[i][multab[j][k]]
        assert multab[i][addtab[j][k]] == addtab[multab[i][j]][multab[i][k]]

    m = {i for i, a in enumerate(els) if is_true(simplify(R.lowzero(a)))}
    units = {i for i in range(32) if any(multab[i][j] == one for j in range(32))}
    assert len(m) == 16 and units == set(range(32)) - m
    gens = R.generators(); genidx = [index[ev(g)] for g in gens]
    ideal = {z}
    raw = [multab[g][a] for g in genidx for a in range(32)]
    ideal = additive_span(addtab, z, raw)
    assert ideal == m

    def ideal_product(I, J):
        return additive_span(addtab, z, [multab[a][b] for a in I for b in J])
    m2 = ideal_product(m, m); m3 = ideal_product(m2, m); m4 = ideal_product(m3, m)
    assert [len(m), len(m2), len(m3), len(m4)] == [16, 4, 2, 1]

    soc = {i for i in range(32) if all(multab[i][g] == z for g in genidx)}
    expected = {index[ev(a)] for a in R.expected_socle()}
    assert soc == expected and len(soc) == 4
    assert all(multab[s][a] == z for s in soc for a in m)
    R.presentation_gate()
    print(f"  [ring/socle gate] |R|=32, |m^k|=16,4,2,1, |Soc|=4; "
          f"full ring tables + presentation -> PASS ({time.monotonic()-started:.2f}s)", flush=True)
    return gens, [els[i] for i in sorted(soc)]


def residual_syzygy_representatives(R, gens, soc):
    """Exhaustively compute and gate every coset of Syz/Soc(R)^2.

    The older depth-five routine used an F2-basis after checking that the
    quotient was elementary.  One stretched row instead has a cyclic
    order-four quotient, so direct coset representatives are required.
    """
    els, z = R.elements(), R.zero(); q = len(gens)
    syz = []
    for coeffs in itertools.product(els, repeat=q):
        total = z
        for g, a in zip(gens, coeffs): total = R.add(total, R.mul(g, a))
        if ev(total) == ev(z): syz.append(coeffs)
    actual = {tuple_key(x) for x in syz}
    socspan = {tuple_key(x): x for x in itertools.product(soc, repeat=q)}
    covered = set(); reps = []
    for x in syz:
        if tuple_key(x) in covered: continue
        reps.append(x)
        coset = {tuple_key(add_tuple(R, x, y)) for y in socspan.values()}
        assert len(coset) == 16 and coset <= actual and not (coset & covered)
        covered |= coset
    assert covered == actual and len(syz) == 64 and len(reps) == 4
    orders = []
    for x in reps:
        y = tuple(R.zero() for _ in range(q))
        for n in range(1, 5):
            y = add_tuple(R, y, x)
            if tuple_key(y) in socspan:
                orders.append(n); break
        else:
            raise AssertionError("residual quotient has order >4")
    quotient_type = "C4" if 4 in orders else "C2xC2"
    print("  [full-syzygy gate] |Syz(g1,g2)|=64, Soc^2=16, "
          f"|Syz/Soc^2|=4 ({quotient_type}) -> PASS", flush=True)
    print("    residual coset representatives: "
          + repr([[ev(a) for a in h] for h in reps]), flush=True)
    return reps


def fail_i_unrolled(R, phi, gens, residual_reps, tag, i):
    """Exact FAIL_i with all residual division representatives unrolled."""
    q = len(gens)
    vecs = [[R.var(f"{tag}v{i}_{j}_{r}") for r in range(3)] for j in range(q)]
    division = And(*module_div_eqs(R, phi[i], vecs, gens))
    shifts = residual_reps; misses = []
    shift_patterns = list(itertools.product(shifts, repeat=3))
    for coordinate_shifts in shift_patterns:
        shifted = [list(v) for v in vecs]
        for r, shift in enumerate(coordinate_shifts):
            for j in range(q): shifted[j][r] = R.add(shifted[j][r], shift[j])
        misses.append(Not(And(*[in_kernel(R, phi, v) for v in shifted])))
    assert len(misses) == 64
    return And(division, *misses), vecs, shifts


def concrete_model_term(model, x):
    if isinstance(x, tuple): return tuple(concrete_model_term(model, y) for y in x)
    y = model.eval(x, model_completion=True)
    return BitVecVal(y.as_long(), x.size())


def model_value(model, x):
    return ev(concrete_model_term(model, x))


def concrete_kernel(R, phi, vec):
    return all(ev(x) == ev(R.zero()) for x in phi_of_coords(R, phi, vec))


def validate_sat_seed(R, model, asserted, phi, gens, vecs, shifts, i, c, mtab):
    """Validate a SAT seed independently of the Boolean FAIL_i wrapper."""
    assert all(is_true(model.eval(a, model_completion=True)) for a in asserted)
    cphi = [[concrete_model_term(model, x) for x in row] for row in phi]
    cvecs = [[concrete_model_term(model, x) for x in row] for row in vecs]
    for r in range(3):
        total = R.zero()
        for g, row in zip(gens, cvecs): total = R.add(total, R.mul(g, row[r]))
        assert ev(total) == ev(cphi[i][r + 1])
    misses = 0
    for coordinate_shifts in itertools.product(shifts, repeat=3):
        shifted = [list(v) for v in cvecs]
        for r, shift in enumerate(coordinate_shifts):
            for j in range(len(gens)): shifted[j][r] = R.add(shifted[j][r], shift[j])
        assert not all(concrete_kernel(R, cphi, v) for v in shifted)
        misses += 1
    assert misses == 64
    print("      [SAT seed validation] all asserted equations true; division true; "
          "all 64 residual representatives miss simultaneous kernel -> PASS", flush=True)
    mult_seed = {str(k): model_value(model, v) for k, v in sorted(mtab.items())
                 if model_value(model, v) != ev(R.zero())}
    cop_seed = {str(k): model_value(model, v) for k, v in sorted(c.items())
                if model_value(model, v) != ev(R.zero())}
    div_seed = [[model_value(model, x) for x in row] for row in vecs]
    print(f"      SAT_SEED multiplication_nonzero={mult_seed}", flush=True)
    print(f"      SAT_SEED coproduct_nonzero={cop_seed}", flush=True)
    print(f"      SAT_SEED FAIL_{i}_division={div_seed}", flush=True)


def solve(label, constraints, timeout, sat_payload=None):
    solver = Solver(); solver.set("timeout", timeout * 1000); solver.add(*constraints)
    started = time.monotonic(); ans = solver.check(); elapsed = time.monotonic() - started
    reason = f" reason={solver.reason_unknown()}" if ans == unknown else ""
    print(f"    [{label}] -> {ans} ({elapsed:.2f}s){reason}", flush=True)
    if ans == sat and sat_payload is not None:
        sat_payload(solver.model(), constraints)
    return ans, elapsed


def run_row(base, gens, residual_reps, fib, pins, label, timeout, only_i):
    print(f"  --- {label} ---", flush=True)
    R = PinCoproductResidue(base, pins)
    A, M, C, F, phi, c, mtab = build_blocks(R, fib); core = A + M + C + F
    h0, _ = solve("H0 axioms+fiber2 sanity", core, timeout)
    record = {"H0": str(h0), "S1": "not-run", "S2": {}}
    if h0 == unsat:
        print("    [H0-VACUOUS: residue Hopf fiber has no lift over this base]", flush=True)
        record["class"] = "H0-vacuous"
        return record
    if h0 == unknown:
        print("    [ROW UNKNOWN: H0 did not terminate; S1/S2 skipped]", flush=True)
        record["class"] = "unknown"
        return record

    holds = sp_nonprincipal_holds(R, phi, gens, "stretchH")
    s1, _ = solve("S1 axioms+fiber2+S'-HOLDS", core + [holds], timeout)
    record["S1"] = str(s1)
    if s1 != sat:
        print("    [S1 sanity warning: no S'-holding lift found]", flush=True)
    row_class = "UNSAT"
    for i in only_i:
        failure, vecs, shifts = fail_i_unrolled(
            R, phi, gens, residual_reps, "stretchF", i)
        asserted = core + [failure]
        def payload(model, asserted_constraints, i=i, vecs=vecs, shifts=shifts):
            validate_sat_seed(base, model, asserted_constraints, phi, gens, vecs,
                              shifts, i, c, mtab)
        ans, _ = solve(f"S2.{i} axioms+fiber2+S'-FAIL_i", asserted, timeout,
                       sat_payload=payload)
        record["S2"][str(i)] = str(ans)
        if ans == sat: row_class = "SAT S'-failure"
        elif ans == unknown and row_class != "SAT S'-failure": row_class = "unknown"
    record["class"] = row_class
    print(f"    [ROW CLASS] {row_class}", flush=True)
    return record


def parse_t4_forms(items):
    out = []
    for item in items:
        if len(item) != 2 or any(x not in "01" for x in item):
            raise SystemExit("--t4-forms entries must be 00, 01, 10, or 11")
        out.append((int(item[0]), int(item[1])))
    return out


def main():
    all_rings = rings(); by_key = {R.key: R for R in all_rings}
    ap = argparse.ArgumentParser()
    ap.add_argument("--rings", nargs="+", choices=tuple(by_key) + ("all",), default=("all",))
    ap.add_argument("--fibers", choices=("xy", "t4", "all"), default="all")
    ap.add_argument("--xy-models", nargs="+", choices=tuple(XY_MODELS), default=tuple(XY_MODELS))
    ap.add_argument("--t4-forms", nargs="+", default=("00", "01", "10", "11"))
    ap.add_argument("--only-i", nargs="+", type=int, choices=(1, 2, 3), default=(1, 2, 3))
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--gates-only", action="store_true")
    args = ap.parse_args()
    set_param("parallel.enable", True)
    selected = all_rings if "all" in args.rings else [by_key[k] for k in args.rings]
    print("EXACT S' SWEEP -- SEVEN STRETCHED LENGTH-FIVE QUOTIENTS", flush=True)
    print("Results are S' verdicts, not direct [4] verdicts.", flush=True)
    print("xy pins=" + ",".join(args.xy_models), flush=True)
    print("t4 forms=" + ",".join(args.t4_forms), flush=True)
    summary = []
    for base in selected:
        print(f"===== STRETCHED S' base {base.key}: {base.name} =====", flush=True)
        gens, soc = exact_ring_socle_gate(base)
        residual_reps = residual_syzygy_representatives(base, gens, soc)
        if args.gates_only: continue
        if args.fibers in ("xy", "all"):
            for name in args.xy_models:
                label = f"{base.key}/xy/{name}"
                summary.append((base.key, f"xy/{name}", run_row(
                    base, gens, residual_reps, XY_MULT, XY_MODELS[name], label,
                    args.timeout, args.only_i)))
        if args.fibers in ("t4", "all"):
            for c1, c4 in parse_t4_forms(args.t4_forms):
                fiber = f"t4/c1={c1},c4={c4}"; label = f"{base.key}/{fiber}"
                summary.append((base.key, fiber, run_row(
                    base, gens, residual_reps, T4_MULT, t4_pins(c1, c4), label,
                    args.timeout, args.only_i)))

    print("===== STRETCHED TERMINAL SUMMARY =====", flush=True)
    counts = {"H0-vacuous": 0, "SAT S'-failure": 0, "UNSAT": 0, "unknown": 0}
    for key, fiber, rec in summary:
        cls = rec["class"]; counts[cls] += 1
        s2 = ",".join(f"{i}:{v}" for i, v in sorted(rec["S2"].items())) or "not-run"
        print(f"  {key} {fiber}: class={cls}; H0={rec['H0']}; "
              f"S1={rec['S1']}; S2={s2}", flush=True)
    print("COUNTS " + ", ".join(f"{k}={v}" for k, v in counts.items()), flush=True)
    print("DONE sprime_stretched_length5_stratified_20260710", flush=True)


if __name__ == "__main__":
    main()
