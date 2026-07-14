#!/usr/bin/env python3
r"""Independent exact S' tests on the four rank-one length-five quotients.

The rings are the four rational forms with Hilbert function (1,3,1):

  D0 = F2[x,u,v]/(x^3,xu,xv,u^2,uv,v^2),
  Da = Z/8[u,v]/(2u,2v,u^2,uv,v^2),
  Dr = Z/4[x,v]/(2x,2v,x^3,xv,v^2),
  D2 = Z/4[x,u,v]/(x^2-2,x^3,xu,xv,u^2,uv,v^2).

For every ring, exhaustive concrete gates check all ring axioms, locality,
the complete m-adic filtration, the socle, the chosen maximal-ideal
generators, and the full division-syzygy set.  The quotient of that syzygy
set by Soc(R)^3 is derived and checked rather than hard-coded.

The Hopf search uses all six F2-rational xy fibers (including the two
nonsplit mu2^2 forms) and all four t^4 normal forms.  H0 is the full bialgebra
nonvacuity query with killed-by-2 fiber.  S1 asks for explicit S' witnesses.
Each S2.i is the exact failure query at augmentation basis vector e_i.  The
finite residual universal quantifier is expanded completely, so there is no
MBQI/ForAll approximation.

An S2 SAT result would refute S' on that exact ring/fiber, but would not by
itself be a Grothendieck counterexample.  An S2 UNSAT result proves S' for
that exact stratum.
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time

from z3 import (
    And,
    BitVec,
    BitVecVal,
    Extract,
    Or,
    Solver,
    ZeroExt,
    is_true,
    sat,
    set_param,
    simplify,
    unsat,
)

sys.path.insert(0, __file__.rsplit("/", 1)[0])

from order4sat import fresh  # noqa: E402
from order4sat_ramified_towers_20260709 import value  # noqa: E402
from s2check import build_blocks, phi_of_coords  # noqa: E402


def zext(bit, width):
    return ZeroExt(width - 1, bit)


class D0:
    """F2-basis 1,x,u,v,s with x^2=s and all other m-products zero."""

    name = "D0=F2[x,u,v]/(x^3,xu,xv,u^2,uv,v^2)"
    characteristic = 2

    def zero(self):
        return tuple(BitVecVal(0, 1) for _ in range(5))

    def one(self):
        return (BitVecVal(1, 1),) + tuple(BitVecVal(0, 1) for _ in range(4))

    def var(self, tag):
        n = fresh(tag)
        return tuple(BitVec(f"{n}_{q}", 1) for q in ("a", "x", "u", "v", "s"))

    def add(self, a, b):
        return tuple(x ^ y for x, y in zip(a, b))

    sub = add

    def mul(self, a, b):
        A, x, u, v, s = a
        B, y, w, z, t = b
        return (
            A & B,
            (A & y) ^ (x & B),
            (A & w) ^ (u & B),
            (A & z) ^ (v & B),
            (A & t) ^ (s & B) ^ (x & y),
        )

    def eq0(self, a):
        return And(*[x == 0 for x in a])

    def neq0(self, a):
        return Or(*[x != 0 for x in a])

    def lowzero(self, a):
        return a[0] == 0

    def deform(self, tag):
        v = self.var(tag)
        return (BitVecVal(0, 1),) + v[1:]

    def concrete(self, *a):
        return tuple(BitVecVal(x, 1) for x in a)

    def elements(self):
        return [self.concrete(*a) for a in itertools.product((0, 1), repeat=5)]

    def named(self):
        return {
            "x": self.concrete(0, 1, 0, 0, 0),
            "u": self.concrete(0, 0, 1, 0, 0),
            "v": self.concrete(0, 0, 0, 1, 0),
            "s": self.concrete(0, 0, 0, 0, 1),
        }

    def generators(self):
        n = self.named()
        return [n["x"], n["u"], n["v"]]

    def expected_socle(self):
        n = self.named()
        return additive_closure(self, [n["s"], n["u"], n["v"]])

    def presentation_gate(self):
        n = self.named()
        z = value(self.zero())
        assert value(self.mul(n["x"], n["x"])) == value(n["s"])
        for a, b in (("x", "s"), ("x", "u"), ("x", "v"),
                     ("u", "u"), ("u", "v"), ("v", "v")):
            assert value(self.mul(n[a], n[b])) == z


class Da:
    """Additive Z/8{1} + F2{u,v}; m=(2,u,v), m^2=(4)."""

    name = "Da=Z/8[u,v]/(2u,2v,u^2,uv,v^2)"
    characteristic = 8

    def zero(self):
        return BitVecVal(0, 3), BitVecVal(0, 1), BitVecVal(0, 1)

    def one(self):
        return BitVecVal(1, 3), BitVecVal(0, 1), BitVecVal(0, 1)

    def var(self, tag):
        n = fresh(tag)
        return BitVec(n + "_a", 3), BitVec(n + "_u", 1), BitVec(n + "_v", 1)

    def add(self, a, b):
        return a[0] + b[0], a[1] ^ b[1], a[2] ^ b[2]

    def sub(self, a, b):
        return a[0] - b[0], a[1] ^ b[1], a[2] ^ b[2]

    def mul(self, a, b):
        A, u, v = a
        B, w, z = b
        a0, b0 = Extract(0, 0, A), Extract(0, 0, B)
        return A * B, (a0 & w) ^ (u & b0), (a0 & z) ^ (v & b0)

    def eq0(self, a):
        return And(a[0] == 0, a[1] == 0, a[2] == 0)

    def neq0(self, a):
        return Or(a[0] != 0, a[1] != 0, a[2] != 0)

    def lowzero(self, a):
        return Extract(0, 0, a[0]) == 0

    def deform(self, tag):
        v = self.var(tag)
        return BitVecVal(2, 3) * v[0], v[1], v[2]

    def concrete(self, a, u, v):
        return BitVecVal(a, 3), BitVecVal(u, 1), BitVecVal(v, 1)

    def elements(self):
        return [self.concrete(a, u, v)
                for a in range(8) for u, v in itertools.product((0, 1), repeat=2)]

    def named(self):
        return {
            "two": self.concrete(2, 0, 0),
            "four": self.concrete(4, 0, 0),
            "u": self.concrete(0, 1, 0),
            "v": self.concrete(0, 0, 1),
        }

    def generators(self):
        n = self.named()
        return [n["two"], n["u"], n["v"]]

    def expected_socle(self):
        n = self.named()
        return additive_closure(self, [n["four"], n["u"], n["v"]])

    def presentation_gate(self):
        n = self.named()
        z = value(self.zero())
        assert value(self.mul(n["two"], n["two"])) == value(n["four"])
        for a, b in (("two", "u"), ("two", "v"), ("u", "u"),
                     ("u", "v"), ("v", "v")):
            assert value(self.mul(n[a], n[b])) == z


class Dr:
    """Additive Z/4{1} + F2{x,s,v}; x^2=s, and 2,x-radical direction."""

    name = "Dr=Z/4[x,v]/(2x,2v,x^3,xv,v^2)"
    characteristic = 4

    def zero(self):
        return BitVecVal(0, 2), *(BitVecVal(0, 1) for _ in range(3))

    def one(self):
        return BitVecVal(1, 2), *(BitVecVal(0, 1) for _ in range(3))

    def var(self, tag):
        n = fresh(tag)
        return BitVec(n + "_a", 2), BitVec(n + "_x", 1), \
            BitVec(n + "_s", 1), BitVec(n + "_v", 1)

    def add(self, a, b):
        return a[0] + b[0], *(x ^ y for x, y in zip(a[1:], b[1:]))

    def sub(self, a, b):
        return a[0] - b[0], *(x ^ y for x, y in zip(a[1:], b[1:]))

    def mul(self, a, b):
        A, x, s, v = a
        B, y, t, w = b
        a0, b0 = Extract(0, 0, A), Extract(0, 0, B)
        return (
            A * B,
            (a0 & y) ^ (x & b0),
            (a0 & t) ^ (s & b0) ^ (x & y),
            (a0 & w) ^ (v & b0),
        )

    def eq0(self, a):
        return And(*[x == 0 for x in a])

    def neq0(self, a):
        return Or(*[x != 0 for x in a])

    def lowzero(self, a):
        return Extract(0, 0, a[0]) == 0

    def deform(self, tag):
        v = self.var(tag)
        return BitVecVal(2, 2) * v[0], v[1], v[2], v[3]

    def concrete(self, a, x, s, v):
        return BitVecVal(a, 2), BitVecVal(x, 1), BitVecVal(s, 1), BitVecVal(v, 1)

    def elements(self):
        return [self.concrete(a, x, s, v) for a in range(4)
                for x, s, v in itertools.product((0, 1), repeat=3)]

    def named(self):
        return {
            "two": self.concrete(2, 0, 0, 0),
            "x": self.concrete(0, 1, 0, 0),
            "s": self.concrete(0, 0, 1, 0),
            "v": self.concrete(0, 0, 0, 1),
        }

    def generators(self):
        n = self.named()
        return [n["two"], n["x"], n["v"]]

    def expected_socle(self):
        n = self.named()
        return additive_closure(self, [n["two"], n["s"], n["v"]])

    def presentation_gate(self):
        n = self.named()
        z = value(self.zero())
        assert value(self.mul(n["x"], n["x"])) == value(n["s"])
        for a, b in (("two", "x"), ("two", "v"), ("x", "s"),
                     ("x", "v"), ("v", "v")):
            assert value(self.mul(n[a], n[b])) == z


class D2:
    """Additive Z/4{1} + F2{x,u,v}; x^2=2 and all other m-products zero."""

    name = "D2=Z/4[x,u,v]/(x^2-2,x^3,xu,xv,u^2,uv,v^2)"
    characteristic = 4

    def zero(self):
        return BitVecVal(0, 2), *(BitVecVal(0, 1) for _ in range(3))

    def one(self):
        return BitVecVal(1, 2), *(BitVecVal(0, 1) for _ in range(3))

    def var(self, tag):
        n = fresh(tag)
        return BitVec(n + "_a", 2), BitVec(n + "_x", 1), \
            BitVec(n + "_u", 1), BitVec(n + "_v", 1)

    def add(self, a, b):
        return a[0] + b[0], *(x ^ y for x, y in zip(a[1:], b[1:]))

    def sub(self, a, b):
        return a[0] - b[0], *(x ^ y for x, y in zip(a[1:], b[1:]))

    def mul(self, a, b):
        A, x, u, v = a
        B, y, w, z = b
        a0, b0 = Extract(0, 0, A), Extract(0, 0, B)
        scalar = A * B + BitVecVal(2, 2) * zext(x & y, 2)
        return (
            scalar,
            (a0 & y) ^ (x & b0),
            (a0 & w) ^ (u & b0),
            (a0 & z) ^ (v & b0),
        )

    def eq0(self, a):
        return And(*[x == 0 for x in a])

    def neq0(self, a):
        return Or(*[x != 0 for x in a])

    def lowzero(self, a):
        return Extract(0, 0, a[0]) == 0

    def deform(self, tag):
        v = self.var(tag)
        return BitVecVal(2, 2) * v[0], v[1], v[2], v[3]

    def concrete(self, a, x, u, v):
        return BitVecVal(a, 2), BitVecVal(x, 1), BitVecVal(u, 1), BitVecVal(v, 1)

    def elements(self):
        return [self.concrete(a, x, u, v) for a in range(4)
                for x, u, v in itertools.product((0, 1), repeat=3)]

    def named(self):
        return {
            "two": self.concrete(2, 0, 0, 0),
            "x": self.concrete(0, 1, 0, 0),
            "u": self.concrete(0, 0, 1, 0),
            "v": self.concrete(0, 0, 0, 1),
        }

    def generators(self):
        n = self.named()
        return [n["x"], n["u"], n["v"]]

    def expected_socle(self):
        n = self.named()
        return additive_closure(self, [n["two"], n["u"], n["v"]])

    def presentation_gate(self):
        n = self.named()
        z = value(self.zero())
        assert value(self.mul(n["x"], n["x"])) == value(n["two"])
        for a, b in (("two", "x"), ("x", "u"), ("x", "v"),
                     ("u", "u"), ("u", "v"), ("v", "v")):
            assert value(self.mul(n[a], n[b])) == z


RINGS = {"D0": D0, "Da": Da, "Dr": Dr, "D2": D2}


# All six F2-rational xy Hopf fibers.  The final two are nonsplit rational
# forms and must not be inferred from the first four geometric forms.
XY_PINS = {
    "a2a2": {(3, 1, 2): 1, (3, 2, 1): 1},
    "W2F": {(2, 1, 1): 1, (3, 1, 2): 1, (3, 2, 1): 1},
    "mu2mu2": {
        (1, 1, 1): 1, (2, 2, 2): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
    "mu2a2": {
        (1, 1, 1): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
    },
    "mu2mu2_unipotent": {
        (1, 1, 1): 1, (1, 2, 2): 1, (1, 2, 3): 1,
        (1, 3, 2): 1, (1, 3, 3): 1,
        (2, 2, 2): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
    "mu2mu2_irreducible": {
        (1, 2, 2): 1, (1, 1, 3): 1, (1, 3, 1): 1, (1, 3, 3): 1,
        (2, 1, 1): 1, (2, 2, 2): 1,
        (2, 1, 3): 1, (2, 3, 1): 1,
        (2, 2, 3): 1, (2, 3, 2): 1, (2, 3, 3): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
}

XY_MULT = {(1, 2, 3): 1}
T4_MULT = {(1, 1, 2): 1, (1, 2, 3): 1}


def t4_pins(c1, c4):
    ans = {(3, 1, 2): 1, (3, 2, 1): 1}
    if c1:
        for key in ((1, 1, 2), (1, 2, 1), (1, 2, 3), (1, 3, 2),
                    (3, 2, 3), (3, 3, 2)):
            ans[key] = 1
    if c4:
        ans[(1, 2, 2)] = 1
    return ans


class PinnedRing:
    """Fix c_ijk modulo m while leaving all higher digits free."""

    def __init__(self, ring, pins, label):
        self.R = ring
        self.pins = pins
        self.name = ring.name + " [" + label + "]"

    def __getattr__(self, key):
        return getattr(self.R, key)

    def var(self, tag):
        if len(tag) == 4 and tag[0] == "c" and tag[1:].isdigit():
            i, j, k = map(int, tag[1:])
            base = self.R.one() if self.pins.get((i, j, k), 0) else self.R.zero()
            return self.R.add(base, self.R.deform(tag))
        return self.R.var(tag)


def key(x):
    return value(x)


def element(R, k):
    if isinstance(k, tuple):
        return R.concrete(*k)
    raise TypeError(k)


def additive_closure(R, generators):
    zero = key(R.zero())
    span = {zero}
    gens = [key(g) for g in generators]
    changed = True
    while changed:
        changed = False
        old = list(span)
        for a in old:
            for b in gens:
                c = key(R.add(element(R, a), element(R, b)))
                if c not in span:
                    span.add(c)
                    changed = True
    return span


def ideal_product(R, left, right):
    products = [R.mul(element(R, a), element(R, b)) for a in left for b in right]
    return additive_closure(R, products)


def characteristic_gate(R):
    z = key(R.zero())
    cur = R.zero()
    for n in range(1, 65):
        cur = R.add(cur, R.one())
        if key(cur) == z:
            assert n == R.characteristic
            return
    raise AssertionError("characteristic did not close")


def ring_gates(R):
    started = time.monotonic()
    els = R.elements()
    keys = {key(x) for x in els}
    assert len(els) == len(keys) == 32
    z, o = key(R.zero()), key(R.one())

    R.presentation_gate()
    characteristic_gate(R)

    for a, b, c in itertools.product(els, repeat=3):
        assert key(R.add(a, R.zero())) == key(a)
        assert key(R.add(a, b)) in keys
        assert key(R.add(a, b)) == key(R.add(b, a))
        assert key(R.add(R.add(a, b), c)) == key(R.add(a, R.add(b, c)))
        assert key(R.mul(a, R.one())) == key(a)
        assert key(R.mul(a, b)) in keys
        assert key(R.mul(a, b)) == key(R.mul(b, a))
        assert key(R.mul(R.mul(a, b), c)) == key(R.mul(a, R.mul(b, c)))
        assert key(R.mul(a, R.add(b, c))) == key(R.add(R.mul(a, b), R.mul(a, c)))

    m = {key(x) for x in els if is_true(simplify(R.lowzero(x)))}
    assert len(m) == 16 and z in m and o not in m
    # Check the chosen generators span exactly m.
    assert additive_closure(R, [R.mul(g, a) for g in R.generators() for a in els]) == m

    m2 = ideal_product(R, m, m)
    m3 = ideal_product(R, m2, m)
    assert [len(m), len(m2), len(m3)] == [16, 2, 1]

    soc = {key(a) for a in els
           if all(key(R.mul(a, element(R, b))) == z for b in m)}
    assert len(soc) == 8
    assert soc == R.expected_socle()

    # Every element outside m must be a unit; no element of m may be a unit.
    units = {key(a) for a in els
             if any(key(R.mul(a, b)) == o for b in els)}
    assert units == keys - m

    print(f"  [ring gate] |R|=32, char={R.characteristic}, "
          f"|m^i|=16,2,1, |Soc|=8 -> PASS ({time.monotonic()-started:.2f}s)",
          flush=True)
    return m, soc


def tuple_key(xs):
    return tuple(key(x) for x in xs)


def add_tuple(R, xs, ys):
    return tuple(R.add(x, y) for x, y in zip(xs, ys))


def syzygy_gate(R, gens, soc):
    started = time.monotonic()
    els = R.elements()
    z = key(R.zero())
    syz = []
    for coeffs in itertools.product(els, repeat=len(gens)):
        total = R.zero()
        for g, a in zip(gens, coeffs):
            total = R.add(total, R.mul(g, a))
        if key(total) == z:
            syz.append(coeffs)

    socels = [element(R, s) for s in soc]
    span = {tuple_key(x): x for x in itertools.product(socels, repeat=len(gens))}
    for x in syz:
        assert tuple_key(add_tuple(R, x, x)) in span

    basis = []
    for x in syz:
        if tuple_key(x) in span:
            continue
        basis.append(x)
        for y in list(span.values()):
            w = add_tuple(R, y, x)
            span[tuple_key(w)] = w

    assert set(span) == {tuple_key(x) for x in syz}
    assert len(syz) == 2048
    assert len(basis) == 2
    print(f"  [syzygy gate] |Syz|={len(syz)}, |Soc^3|={len(soc)**3}, "
          f"dim_F2(Syz/Soc^3)={len(basis)} -> PASS "
          f"({time.monotonic()-started:.2f}s)", flush=True)
    return basis


def residual_span(R, basis, q):
    out = [tuple(R.zero() for _ in range(q))]
    for b in basis:
        out += [add_tuple(R, x, b) for x in list(out)]
    return out


def in_kernel(R, phi, vec):
    return And(*[R.eq0(x) for x in phi_of_coords(R, phi, vec)])


def division_constraints(R, phi_i, gens, vecs):
    ans = []
    for r in range(3):
        total = R.zero()
        for g, vec in zip(gens, vecs):
            total = R.add(total, R.mul(g, vec[r]))
        ans.append(R.eq0(R.sub(total, phi_i[r + 1])))
    return ans


def sprime_holds(R, phi, gens, tag):
    rows = []
    for i in range(1, 4):
        vecs = [[R.var(f"{tag}_h_{i}_{j}_{r}") for r in range(3)]
                for j in range(len(gens))]
        rows.append(And(*division_constraints(R, phi[i], gens, vecs),
                        *[in_kernel(R, phi, vec) for vec in vecs]))
    return And(*rows)


def sprime_fail_i(R, phi, gens, residual, tag, i):
    q = len(gens)
    vecs = [[R.var(f"{tag}_f_{i}_{j}_{r}") for r in range(3)] for j in range(q)]
    division = And(*division_constraints(R, phi[i], gens, vecs))
    misses = []
    # A different division differs, independently in each I-coordinate, by
    # one of the fully enumerated residual syzygies.  Socle shifts have no
    # effect because phi(I) is in mI and Soc*m=0.
    for coordinate_shifts in itertools.product(residual, repeat=3):
        shifted = [list(vec) for vec in vecs]
        for r, shift in enumerate(coordinate_shifts):
            for j in range(q):
                shifted[j][r] = R.add(shifted[j][r], shift[j])
        misses.append(Or(*[Or(*[R.neq0(x) for x in phi_of_coords(R, phi, vec)])
                             for vec in shifted]))
    assert len(misses) == len(residual) ** 3 == 64
    return And(division, *misses)


def solve(label, constraints, timeout):
    s = Solver()
    s.set("timeout", timeout * 1000)
    s.add(*constraints)
    t0 = time.monotonic()
    ans = s.check()
    print(f"    [{label}] -> {ans} ({time.monotonic()-t0:.2f}s)", flush=True)
    return ans


def run_stratum(base, gens, basis, fib, pins, label, timeout):
    print(f"  --- {label} ---", flush=True)
    R = PinnedRing(base, pins, label)
    A, M, C, F, phi, _, _ = build_blocks(R, fib)
    core = A + M + C + F
    h0 = solve("H0 full bialgebra+fiber2", core, timeout)
    if h0 == unsat:
        print("    [VACUOUS] no bialgebra lift in this exact stratum", flush=True)
        return ("vacuous",)
    if h0 != sat:
        return ("open-H0", str(h0))

    s1 = solve("S1 explicit S'-HOLDS witness", core + [
        sprime_holds(R, phi, gens, "rk1")], timeout)
    if s1 != sat:
        return ("invalid-S1", str(s1))

    residual = residual_span(base, basis, len(gens))
    out = []
    for i in range(1, 4):
        fail = sprime_fail_i(R, phi, gens, residual, "rk1", i)
        out.append(solve(f"S2.{i} exact S'-FAIL_i", core + [fail], timeout))
    return tuple(map(str, out))


def run_ring(base, timeout, fibers):
    print(f"===== base {base.name} =====", flush=True)
    _, soc = ring_gates(base)
    gens = base.generators()
    basis = syzygy_gate(base, gens, soc)
    results = []
    if fibers in ("xy", "all"):
        for name, pins in XY_PINS.items():
            label = "xy/" + name
            results.append((label, run_stratum(
                base, gens, basis, XY_MULT, pins, label, timeout)))
    if fibers in ("t4", "all"):
        for c1, c4 in itertools.product((0, 1), repeat=2):
            label = f"t4/c1={c1},c4={c4}"
            results.append((label, run_stratum(
                base, gens, basis, T4_MULT, t4_pins(c1, c4), label, timeout)))
    print("  SUMMARY", flush=True)
    for label, ans in results:
        print(f"    {label}: {','.join(ans)}", flush=True)
    return results


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ring", choices=tuple(RINGS) + ("all",), default="all")
    ap.add_argument("--fibers", choices=("xy", "t4", "all"), default="all")
    ap.add_argument("--timeout", type=int, default=1800)
    args = ap.parse_args()
    set_param("parallel.enable", True)

    names = tuple(RINGS) if args.ring == "all" else (args.ring,)
    print("EXACT S' RANK-ONE LENGTH-FIVE SWEEP (EVIDENCE-MAP INDEPENDENT RUN)",
          flush=True)
    grand = []
    for name in names:
        grand.append((name, run_ring(RINGS[name](), args.timeout, args.fibers)))
    print("===== GRAND SUMMARY =====", flush=True)
    for name, rows in grand:
        for label, ans in rows:
            print(f"  {name} {label}: {','.join(ans)}", flush=True)
    print("DONE sprime_rankone_len5_evidence_map_20260710", flush=True)


if __name__ == "__main__":
    main()
