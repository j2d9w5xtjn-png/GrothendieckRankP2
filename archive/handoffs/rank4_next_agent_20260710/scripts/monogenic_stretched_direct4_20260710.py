#!/usr/bin/env python3
r"""Direct rank-four search on the two hard stretched quotient branches.

This program does *not* test the stronger auxiliary condition S'.  It tests
the actual counterexample condition ``[4]^# != eta epsilon`` on every
length-seven Gorenstein socle lift of the two quotient rings whose old S'
queries timed out:

    s_f2 = F2[x,y]/(x^5,xy,y^2),
    q00  = Z[x]/(x^5,2x,4).

There are six deliberately redundant coordinate presentations.  They cover
three isomorphism classes; keeping both choices of an adapted generator is a
useful encoding cross-check.

The special Hopf fibre is the unresolved t4 normal form (c1,c4)=(1,1).  Every
lift of the algebra k[T]/T^4 is monogenic, so the generic algebra is normalized
as

    A = R[T]/(T^4-aT-bT^2-dT^3),       a,b,d in m_R.

Only Delta(T) is parameterized.  Relation stability makes Delta an algebra
map, and coassociativity is checked on T.  If q=[2]^#=mu Delta, the main query
is q(q(T)) != 0.  Since T generates A, this is exactly [4]^# != eta epsilon.

Every concrete base ring is exhaustively gated before a solver is created:
all 128^3 associativity and distributivity triples, units/locality, maximal
ideal powers, socle, Gorenstein pairing, and the 128^2 quotient-operation
table.  A SAT model is re-evaluated by a separate concrete arithmetic path and
can be written as JSON for later independent verification.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import itertools
import json
import os
from pathlib import Path
import resource
import shlex
import sys
import time
from typing import Dict, Iterable, List, Mapping, Sequence, Tuple

from z3 import (
    And, BitVec, BitVecVal, Extract, Or, Solver, SolverFor, ZeroExt,
    sat, set_param, unknown,
)


Coord = Tuple[int, ...]
Products = Mapping[Tuple[int, int], Mapping[int, int]]
SYMBOL_FRESH = [0]


def _clean_products(products: Products) -> Dict[Tuple[int, int], Dict[int, int]]:
    return {
        tuple(sorted(key)): {target: coefficient for target, coefficient in out.items()
                             if coefficient}
        for key, out in products.items()
    }


def _fresh(tag: str) -> str:
    SYMBOL_FRESH[0] += 1
    return f"{tag}__mono4_{SYMBOL_FRESH[0]}"


def _cast_bitvector(value, width: int):
    old = value.size()
    if old == width:
        return value
    if old < width:
        return ZeroExt(width - old, value)
    return Extract(width - 1, 0, value)


class SymbolicRing:
    """Z3 arithmetic on a direct sum of cyclic 2-power groups."""

    def __init__(self, name: str, widths: Sequence[int], products: Products):
        self.name = name
        self.widths = tuple(widths)
        self.products = _clean_products(products)
        for i in range(len(self.widths)):
            self.products[(0, i)] = {i: 1}

    def zero(self):
        return tuple(BitVecVal(0, width) for width in self.widths)

    def one(self):
        out = list(self.zero())
        out[0] = BitVecVal(1, self.widths[0])
        return tuple(out)

    def var(self, tag: str):
        name = _fresh(tag)
        return tuple(BitVec(f"{name}_{i}", width)
                     for i, width in enumerate(self.widths))

    def add(self, left, right):
        return tuple(a + b for a, b in zip(left, right))

    def sub(self, left, right):
        return tuple(a - b for a, b in zip(left, right))

    def mul(self, left, right):
        out = [BitVecVal(0, width) for width in self.widths]
        for i, a in enumerate(left):
            for j, b in enumerate(right):
                for target, coefficient in self.products.get(
                        tuple(sorted((i, j))), {}).items():
                    width = self.widths[target]
                    term = (_cast_bitvector(a, width) * _cast_bitvector(b, width)
                            * BitVecVal(coefficient, width))
                    out[target] = out[target] + term
        return tuple(out)

    def eq0(self, value):
        return And(*[component == 0 for component in value])

    def neq0(self, value):
        return Or(*[component != 0 for component in value])

    def lowzero(self, value):
        return (value[0] & 1) == 0

    def deform(self, tag: str):
        value = self.var(tag)
        return (2 * value[0],) + value[1:]


@dataclass(frozen=True)
class CaseSpec:
    key: str
    quotient: str
    alpha: int
    gamma: int
    widths: Tuple[int, ...]
    products: Products
    z: Coord
    active_x: Coord

    def symbolic_ring(self) -> SymbolicRing:
        return SymbolicRing(self.key, self.widths, self.products)


def _sf2_case(gamma: int, alpha: int) -> CaseSpec:
    if gamma == 0:
        # basis 1,x,x^2,x^3,x^4,y,z; z=x^5=y^2 and 2=0
        widths = (1, 1, 1, 1, 1, 1, 1)
        z = (0, 0, 0, 0, 0, 0, 1)
        products = {
            (1, 1): {2: 1},
            (1, 2): {3: 1},
            (1, 3): {4: 1},
            (1, 4): {6: 1},
            (2, 2): {4: 1},
            (2, 3): {6: 1},
            (1, 5): {6: alpha},
            (5, 5): {6: 1},
        }
        x = (0, 1, 0, 0, 0, 0, 0)
    else:
        # basis 1 (mod 4),x,x^2,x^3,x^4,y; z=2=x^5=y^2
        widths = (2, 1, 1, 1, 1, 1)
        z = (2, 0, 0, 0, 0, 0)
        products = {
            (1, 1): {2: 1},
            (1, 2): {3: 1},
            (1, 3): {4: 1},
            (1, 4): {0: 2},
            (2, 2): {4: 1},
            (2, 3): {0: 2},
            (1, 5): {0: 2 * alpha},
            (5, 5): {0: 2},
        }
        x = (0, 1, 0, 0, 0, 0)
    return CaseSpec(
        key=f"sf2_g{gamma}_a{alpha}", quotient="s_f2", alpha=alpha,
        gamma=gamma, widths=widths, products=_clean_products(products), z=z,
        active_x=x,
    )


def _q00_case(alpha: int) -> CaseSpec:
    # basis 1 (mod 8),u,x^2,x^3,x^4, with x=2*alpha+u and z=4=x^5.
    # Thus u^2=x^2+alpha*z.  The two alpha choices are isomorphic via
    # x -> x+2, but both are retained as an exact normalization cross-check.
    widths = (3, 1, 1, 1, 1)
    products = {
        (1, 1): {2: 1, 0: 4 * alpha},
        (1, 2): {3: 1},
        (1, 3): {4: 1},
        (1, 4): {0: 4},
        (2, 2): {4: 1},
        (2, 3): {0: 4},
    }
    return CaseSpec(
        key=f"q00_a{alpha}", quotient="q00", alpha=alpha, gamma=1,
        widths=widths, products=_clean_products(products),
        z=(4, 0, 0, 0, 0), active_x=(2 * alpha, 1, 0, 0, 0),
    )


CASE_SPECS = {
    case.key: case
    for case in (
        _sf2_case(0, 0), _sf2_case(0, 1),
        _sf2_case(1, 0), _sf2_case(1, 1),
        _q00_case(0), _q00_case(1),
    )
}
CASE_KEYS = tuple(CASE_SPECS)


class ConcreteRing:
    """Independent integer arithmetic for a CaseSpec (no Z3 expressions)."""

    def __init__(self, spec: CaseSpec):
        self.spec = spec
        self.widths = spec.widths
        self.moduli = tuple(1 << w for w in self.widths)
        self.offsets = []
        offset = 0
        for width in self.widths:
            self.offsets.append(offset)
            offset += width
        self.bit_length = offset
        self.size = 1 << offset
        self.products = _clean_products(spec.products)
        for i in range(len(self.widths)):
            self.products[(0, i)] = {i: 1}
        self.zero = tuple(0 for _ in self.widths)
        self.one = (1,) + tuple(0 for _ in self.widths[1:])
        self.elements = tuple(self.decode(code) for code in range(self.size))

    def encode(self, a: Coord) -> int:
        return sum((value % modulus) << offset
                   for value, modulus, offset in zip(a, self.moduli, self.offsets))

    def decode(self, code: int) -> Coord:
        return tuple((code >> offset) & (modulus - 1)
                     for modulus, offset in zip(self.moduli, self.offsets))

    def add(self, a: Coord, b: Coord) -> Coord:
        return tuple((x + y) % modulus for x, y, modulus in zip(a, b, self.moduli))

    def neg(self, a: Coord) -> Coord:
        return tuple((-x) % modulus for x, modulus in zip(a, self.moduli))

    def sub(self, a: Coord, b: Coord) -> Coord:
        return self.add(a, self.neg(b))

    def mul(self, a: Coord, b: Coord) -> Coord:
        out = [0] * len(self.widths)
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                for target, coefficient in self.products.get(
                        tuple(sorted((i, j))), {}).items():
                    out[target] += ai * bj * coefficient
        return tuple(value % modulus for value, modulus in zip(out, self.moduli))

    def smul(self, scalar: int, a: Coord) -> Coord:
        return tuple((scalar * x) % modulus for x, modulus in zip(a, self.moduli))

    def is_maximal(self, a: Coord) -> bool:
        return a[0] % 2 == 0


def additive_closure(R: ConcreteRing, generators: Iterable[Coord]) -> set[Coord]:
    closure = {R.zero}
    for generator in generators:
        new = set()
        multiple = R.zero
        for _ in range(R.size):
            new.update(R.add(old, multiple) for old in closure)
            multiple = R.add(multiple, generator)
            if multiple == R.zero:
                break
        closure = new
    return closure


def ideal_product(R: ConcreteRing, left: Iterable[Coord], right: Iterable[Coord]) -> set[Coord]:
    return additive_closure(R, (R.mul(a, b) for a in left for b in right))


def f2_t4_11_pin_gate() -> None:
    """Independent bit-mask check of the fixed special-fibre Hopf algebra."""
    idx2 = lambda i, j: 4 * i + j
    idx3 = lambda i, j, k: 16 * i + 4 * j + k

    def mul_t2(left: int, right: int) -> int:
        out = 0
        for i, j, r, s in itertools.product(range(4), repeat=4):
            if not ((left >> idx2(i, j)) & 1 and (right >> idx2(r, s)) & 1):
                continue
            if i + r < 4 and j + s < 4:
                out ^= 1 << idx2(i + r, j + s)
        return out

    pins = {(1, 2), (2, 1), (2, 3), (3, 2), (2, 2)}
    delta = (1 << idx2(1, 0)) ^ (1 << idx2(0, 1))
    for i, j in pins:
        delta ^= 1 << idx2(i, j)
    powers = [1 << idx2(0, 0), delta]
    for _ in range(2, 5):
        powers.append(mul_t2(powers[-1], delta))
    assert powers[4] == 0, "t4_11 pin does not preserve T^4=0"

    left, right = 0, 0
    for r, s in itertools.product(range(4), repeat=2):
        if not ((delta >> idx2(r, s)) & 1):
            continue
        for i, j in itertools.product(range(4), repeat=2):
            if (powers[r] >> idx2(i, j)) & 1:
                left ^= 1 << idx3(i, j, s)
            if (powers[s] >> idx2(i, j)) & 1:
                right ^= 1 << idx3(r, i, j)
    assert left == right, "t4_11 pin is not coassociative"

    q_t = 0
    for r, s in itertools.product(range(4), repeat=2):
        if (delta >> idx2(r, s)) & 1 and r + s < 4:
            q_t ^= 1 << (r + s)
    assert q_t == 0, "t4_11 pin is not killed by two"
    print("FIBER_PIN_GATE t4_11 relation_stability=PASS coassoc=PASS "
          "q_T_zero=PASS arithmetic=independent_F2_bitmask", flush=True)


def quotient_target(quotient: str) -> Tuple[ConcreteRing, callable]:
    if quotient == "s_f2":
        target = CaseSpec(
            key="s_f2_quotient", quotient="s_f2", alpha=0, gamma=0,
            widths=(1, 1, 1, 1, 1, 1),
            products=_clean_products({
                (1, 1): {2: 1}, (1, 2): {3: 1},
                (1, 3): {4: 1}, (2, 2): {4: 1},
            }),
            z=(0, 0, 0, 0, 0, 0), active_x=(0, 1, 0, 0, 0, 0),
        )
        return ConcreteRing(target), None
    if quotient == "q00":
        target = CaseSpec(
            key="q00_quotient", quotient="q00", alpha=0, gamma=0,
            widths=(2, 1, 1, 1, 1),
            products=_clean_products({
                (1, 1): {2: 1}, (1, 2): {3: 1},
                (1, 3): {4: 1}, (2, 2): {4: 1},
            }),
            z=(0, 0, 0, 0, 0), active_x=(0, 1, 0, 0, 0),
        )
        return ConcreteRing(target), None
    raise ValueError(quotient)


def quotient_map(spec: CaseSpec, a: Coord) -> Coord:
    if spec.quotient == "s_f2":
        if spec.gamma == 0:
            return tuple(a[:6])
        return (a[0] % 2,) + tuple(a[1:])
    # In q00, u=x-2*alpha, so u maps to x+2*alpha modulo the top z=4.
    return ((a[0] + 2 * spec.alpha * a[1]) % 4, a[1], a[2], a[3], a[4])


def duplicate_coordinate_map(source: CaseSpec, a: Coord) -> Coord:
    """Map an alpha=1 presentation to its alpha=0 companion."""
    assert source.alpha == 1
    out = list(a)
    if source.quotient == "s_f2":
        # y_source -> y_target+x^4.
        out[4] = (out[4] + a[5]) % (1 << source.widths[4])
    else:
        # x_source -> x_target+2.  In the chosen u=x-2*alpha bases this
        # fixes u, while (x_source)^2 -> (x_target)^2+z.
        out[0] = (out[0] + 4 * a[2]) % 8
    return tuple(out)


def exhaustive_ring_gate(spec: CaseSpec) -> ConcreteRing:
    started = time.monotonic()
    R = ConcreteRing(spec)
    codes = range(R.size)
    add = [[0] * R.size for _ in codes]
    mul = [[0] * R.size for _ in codes]
    for i in codes:
        a = R.elements[i]
        for j in codes:
            b = R.elements[j]
            add[i][j] = R.encode(R.add(a, b))
            mul[i][j] = R.encode(R.mul(a, b))
    zero, one = R.encode(R.zero), R.encode(R.one)
    for i in codes:
        assert mul[one][i] == i == mul[i][one]
        for j in codes:
            assert mul[i][j] == mul[j][i]
            for k in codes:
                assert mul[mul[i][j]][k] == mul[i][mul[j][k]]
                assert mul[i][add[j][k]] == add[mul[i][j]][mul[i][k]]

    maximal = {a for a in R.elements if R.is_maximal(a)}
    units = {
        R.elements[i] for i in codes
        if any(mul[i][j] == one for j in codes)
    }
    assert units == set(R.elements) - maximal
    powers = [maximal]
    while powers[-1] != {R.zero}:
        powers.append(ideal_product(R, powers[-1], maximal))
        assert len(powers) <= 7
    assert [len(power) for power in powers] == [64, 16, 8, 4, 2, 1]
    socle = {a for a in R.elements if all(R.mul(a, m) == R.zero for m in maximal)}
    assert socle == {R.zero, spec.z}

    # The two-by-two top multiplication pairing must be nonsingular.  Its
    # rows are the two socle classes of Q, and its columns are x and the
    # hidden tangent.  The explicit presentations normalize the determinant
    # to one; testing the resulting R-socle above is equivalent, and these
    # displayed checks make the normalization visible.
    x = spec.active_x
    if spec.quotient == "s_f2":
        y = tuple(int(i == len(spec.widths) - (1 if spec.gamma else 2))
                  for i in range(len(spec.widths)))
        x4 = R.mul(R.mul(x, x), R.mul(x, x))
        assert R.mul(x4, x) == spec.z
        assert R.mul(x4, y) == R.zero
        assert R.mul(y, y) == spec.z
    else:
        two = R.smul(2, R.one)
        x2 = R.mul(x, x)
        x4 = R.mul(x2, x2)
        assert R.mul(x4, x) == spec.z
        assert R.mul(x4, two) == R.zero
        assert R.mul(two, two) == spec.z

    target, _ = quotient_target(spec.quotient)
    fibres: Dict[Coord, int] = {}
    for a in R.elements:
        qa = quotient_map(spec, a)
        fibres[qa] = fibres.get(qa, 0) + 1
    assert set(fibres) == set(target.elements)
    assert set(fibres.values()) == {2}
    for a in R.elements:
        qa = quotient_map(spec, a)
        for b in R.elements:
            qb = quotient_map(spec, b)
            assert quotient_map(spec, R.add(a, b)) == target.add(qa, qb)
            assert quotient_map(spec, R.mul(a, b)) == target.mul(qa, qb)
    assert quotient_map(spec, spec.z) == target.zero
    if spec.alpha == 1:
        target_spec = (CASE_SPECS[f"sf2_g{spec.gamma}_a0"]
                       if spec.quotient == "s_f2" else CASE_SPECS["q00_a0"])
        target_ring = ConcreteRing(target_spec)
        images = {duplicate_coordinate_map(spec, a) for a in R.elements}
        assert images == set(target_ring.elements)
        for a in R.elements:
            image_a = duplicate_coordinate_map(spec, a)
            for b in R.elements:
                image_b = duplicate_coordinate_map(spec, b)
                assert duplicate_coordinate_map(spec, R.add(a, b)) \
                    == target_ring.add(image_a, image_b)
                assert duplicate_coordinate_map(spec, R.mul(a, b)) \
                    == target_ring.mul(image_a, image_b)
        print(f"DUPLICATE_ISOMORPHISM_GATE case={spec.key} -> {target_spec.key} "
              "bijection_and_all_128^2_ops=PASS", flush=True)
    print(
        f"RING_GATE case={spec.key} |R|=128 exhaustive_assoc_distrib=128^3 "
        f"units={len(units)} m_powers=64,16,8,4,2,1 socle=<z> "
        f"quotient={spec.quotient} fibres=2 all_128^2_ops=PASS "
        f"elapsed={time.monotonic()-started:.2f}s",
        flush=True,
    )
    return R


def vzero(R, n: int):
    return [R.zero() for _ in range(n)]


def vadd(R, left, right):
    return [R.add(a, b) for a, b in zip(left, right)]


def vsub(R, left, right):
    return [R.sub(a, b) for a, b in zip(left, right)]


def vscale(R, scalar, vector):
    return [R.mul(scalar, value) for value in vector]


def symbolic_system(spec: CaseSpec):
    """Build the normalized monogenic coassociative bialgebra equations."""
    R = spec.symbolic_ring()
    zero, one = R.zero(), R.one()
    a, b, d = (R.deform("rel_a"), R.deform("rel_b"), R.deform("rel_d"))

    def basis(index: int):
        return [one if i == index else zero for i in range(4)]

    # Powers T^0,...,T^6 in A.  Multiplication by T uses the monic relation.
    powers = [basis(i) for i in range(4)]

    def mul_by_t(vector):
        return [
            zero,
            R.add(vector[0], R.mul(a, vector[3])),
            R.add(vector[1], R.mul(b, vector[3])),
            R.add(vector[2], R.mul(d, vector[3])),
        ]

    for _ in range(4, 7):
        powers.append(mul_by_t(powers[-1]))

    def mul_a(left, right):
        out = vzero(R, 4)
        for i in range(4):
            for j in range(4):
                out = vadd(R, out, vscale(R, R.mul(left[i], right[j]), powers[i + j]))
        return out

    def idx2(i, j):
        return 4 * i + j

    def idx3(i, j, k):
        return 16 * i + 4 * j + k

    def mul_t2(left, right):
        out = vzero(R, 16)
        for i, j, r, s in itertools.product(range(4), repeat=4):
            coefficient = R.mul(left[idx2(i, j)], right[idx2(r, s)])
            left_product, right_product = powers[i + r], powers[j + s]
            for u, v in itertools.product(range(4), repeat=2):
                term = R.mul(coefficient, R.mul(left_product[u], right_product[v]))
                out[idx2(u, v)] = R.add(out[idx2(u, v)], term)
        return out

    pin = {
        (1, 2), (2, 1), (2, 3), (3, 2), (2, 2),
    }
    c = {}
    delta_t = vzero(R, 16)
    delta_t[idx2(1, 0)] = one
    delta_t[idx2(0, 1)] = one
    for i, j in itertools.product(range(1, 4), repeat=2):
        value = R.deform(f"cop_{i}_{j}")
        if (i, j) in pin:
            value = R.add(one, value)
        c[(i, j)] = value
        delta_t[idx2(i, j)] = value

    tensor_one = vzero(R, 16)
    tensor_one[idx2(0, 0)] = one
    delta_powers = [tensor_one, delta_t]
    for _ in range(2, 5):
        delta_powers.append(mul_t2(delta_powers[-1], delta_t))

    relation_stability = delta_powers[4]
    relation_stability = vsub(R, relation_stability, vscale(R, a, delta_powers[1]))
    relation_stability = vsub(R, relation_stability, vscale(R, b, delta_powers[2]))
    relation_stability = vsub(R, relation_stability, vscale(R, d, delta_powers[3]))

    coassoc = vzero(R, 64)
    for r, s in itertools.product(range(4), repeat=2):
        coefficient = delta_t[idx2(r, s)]
        for i, j in itertools.product(range(4), repeat=2):
            coassoc[idx3(i, j, s)] = R.add(
                coassoc[idx3(i, j, s)],
                R.mul(coefficient, delta_powers[r][idx2(i, j)]),
            )
            coassoc[idx3(r, i, j)] = R.sub(
                coassoc[idx3(r, i, j)],
                R.mul(coefficient, delta_powers[s][idx2(i, j)]),
            )

    q_t = vzero(R, 4)
    for r, s in itertools.product(range(4), repeat=2):
        q_t = vadd(R, q_t, vscale(R, delta_t[idx2(r, s)], powers[r + s]))
    q_powers = [basis(0), q_t]
    q_powers.append(mul_a(q_t, q_t))
    q_powers.append(mul_a(q_powers[2], q_t))
    qq_t = vzero(R, 4)
    for i in range(4):
        qq_t = vadd(R, qq_t, vscale(R, q_t[i], q_powers[i]))

    core = [R.eq0(value) for value in relation_stability + coassoc]
    # Safety condition: the fixed t4_11 fibre is killed by two.  These are
    # redundant for the pinned residue table but guard against transcription.
    core.extend(R.lowzero(value) for value in q_t)
    direct_nonzero = Or(*[R.neq0(value) for value in qq_t])
    return {
        "R": R, "a": a, "b": b, "d": d, "c": c,
        "core": core, "q_t": q_t, "qq_t": qq_t,
        "direct_nonzero": direct_nonzero,
    }


def eval_ring_element(model, element) -> Coord:
    return tuple(model.eval(component, model_completion=True).as_long()
                 for component in element)


class ConcreteMonogenic:
    """Concrete re-evaluator independent of symbolic_system's vector code."""

    def __init__(self, R: ConcreteRing, a: Coord, b: Coord, d: Coord):
        self.R, self.a, self.b, self.d = R, a, b, d
        self.zero = R.zero
        self.one = R.one
        self.basis = [tuple(self.one if i == j else self.zero for i in range(4))
                      for j in range(4)]
        self.powers = list(self.basis)
        for _ in range(4, 7):
            self.powers.append(self.mul_by_t(self.powers[-1]))

    def addv(self, left, right):
        return tuple(self.R.add(a, b) for a, b in zip(left, right))

    def subv(self, left, right):
        return tuple(self.R.sub(a, b) for a, b in zip(left, right))

    def scale(self, scalar, vector):
        return tuple(self.R.mul(scalar, value) for value in vector)

    def mul_by_t(self, vector):
        R = self.R
        return (
            self.zero,
            R.add(vector[0], R.mul(self.a, vector[3])),
            R.add(vector[1], R.mul(self.b, vector[3])),
            R.add(vector[2], R.mul(self.d, vector[3])),
        )

    def mul(self, left, right):
        out = tuple(self.zero for _ in range(4))
        for i, j in itertools.product(range(4), repeat=2):
            coefficient = self.R.mul(left[i], right[j])
            out = self.addv(out, self.scale(coefficient, self.powers[i + j]))
        return out


def verify_certificate_data(spec: CaseSpec, certificate: Mapping, verbose=True) -> None:
    R = ConcreteRing(spec)
    a, b, d = (tuple(certificate[key]) for key in ("a", "b", "d"))
    c = {tuple(map(int, key.split(","))): tuple(value)
         for key, value in certificate["c"].items()}
    assert all(R.is_maximal(value) for value in (a, b, d))
    pin = {(1, 2), (2, 1), (2, 3), (3, 2), (2, 2)}
    for key, value in c.items():
        assert (value[0] & 1) == int(key in pin)

    A = ConcreteMonogenic(R, a, b, d)
    idx2 = lambda i, j: 4 * i + j
    idx3 = lambda i, j, k: 16 * i + 4 * j + k

    delta = [R.zero] * 16
    delta[idx2(1, 0)] = R.one
    delta[idx2(0, 1)] = R.one
    for key, value in c.items():
        delta[idx2(*key)] = value

    def addv(left, right):
        return tuple(R.add(a0, b0) for a0, b0 in zip(left, right))

    def subv(left, right):
        return tuple(R.sub(a0, b0) for a0, b0 in zip(left, right))

    def scale(scalar, vector):
        return tuple(R.mul(scalar, value) for value in vector)

    def mul_t2(left, right):
        out = tuple(R.zero for _ in range(16))
        for i, j, r, s in itertools.product(range(4), repeat=4):
            coefficient = R.mul(left[idx2(i, j)], right[idx2(r, s)])
            for u, v in itertools.product(range(4), repeat=2):
                term = R.mul(coefficient, R.mul(A.powers[i + r][u], A.powers[j + s][v]))
                mutable = list(out)
                mutable[idx2(u, v)] = R.add(mutable[idx2(u, v)], term)
                out = tuple(mutable)
        return out

    tensor_one = [R.zero] * 16
    tensor_one[idx2(0, 0)] = R.one
    dp = [tuple(tensor_one), tuple(delta)]
    for _ in range(2, 5):
        dp.append(mul_t2(dp[-1], dp[1]))
    relation = subv(dp[4], scale(a, dp[1]))
    relation = subv(relation, scale(b, dp[2]))
    relation = subv(relation, scale(d, dp[3]))
    assert all(value == R.zero for value in relation)

    coassoc = [R.zero] * 64
    for r, s in itertools.product(range(4), repeat=2):
        coefficient = delta[idx2(r, s)]
        for i, j in itertools.product(range(4), repeat=2):
            coassoc[idx3(i, j, s)] = R.add(
                coassoc[idx3(i, j, s)], R.mul(coefficient, dp[r][idx2(i, j)]))
            coassoc[idx3(r, i, j)] = R.sub(
                coassoc[idx3(r, i, j)], R.mul(coefficient, dp[s][idx2(i, j)]))
    assert all(value == R.zero for value in coassoc)

    q_t = tuple(R.zero for _ in range(4))
    for r, s in itertools.product(range(4), repeat=2):
        q_t = addv(q_t, scale(delta[idx2(r, s)], A.powers[r + s]))
    assert all(R.is_maximal(value) for value in q_t)
    qpow = [A.basis[0], q_t, A.mul(q_t, q_t)]
    qpow.append(A.mul(qpow[2], q_t))
    qq_t = tuple(R.zero for _ in range(4))
    for i in range(4):
        qq_t = addv(qq_t, scale(q_t[i], qpow[i]))
    assert any(value != R.zero for value in qq_t)
    if "q_t" in certificate:
        assert tuple(tuple(row) for row in certificate["q_t"]) == q_t
    if "qq_t" in certificate:
        assert tuple(tuple(row) for row in certificate["qq_t"]) == qq_t
    if verbose:
        print(f"INDEPENDENT_CERTIFICATE_VERIFY case={spec.key} relation=PASS "
              f"coassoc=PASS fiber2=PASS direct_D_T_nonzero=PASS qqT={qq_t}",
              flush=True)


def certificate_from_model(spec: CaseSpec, system, model) -> Dict:
    certificate = {
        "format": "rank4-monogenic-direct4-v1",
        "case": spec.key,
        "a": eval_ring_element(model, system["a"]),
        "b": eval_ring_element(model, system["b"]),
        "d": eval_ring_element(model, system["d"]),
        "c": {f"{i},{j}": eval_ring_element(model, value)
              for (i, j), value in sorted(system["c"].items())},
        "q_t": [eval_ring_element(model, value) for value in system["q_t"]],
        "qq_t": [eval_ring_element(model, value) for value in system["qq_t"]],
    }
    verify_certificate_data(spec, certificate)
    return certificate


def atomic_json_write(path: Path, payload: Mapping) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + f".part.{os.getpid()}")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    os.replace(temporary, path)


def solve_case(spec: CaseSpec, args) -> int:
    process_started = time.monotonic()
    f2_t4_11_pin_gate()
    exhaustive_ring_gate(spec)
    if args.validate_only:
        print(f"VALIDATE_ONLY_DONE case={spec.key}", flush=True)
        print(f"DONE monogenic_stretched_direct4_20260710 case={spec.key}", flush=True)
        return 0

    system_started = time.monotonic()
    system = symbolic_system(spec)
    print(f"SYSTEM_BUILT case={spec.key} core_constraints={len(system['core'])} "
          f"ring_variables=12 elapsed={time.monotonic()-system_started:.2f}s",
          flush=True)
    solver = Solver() if args.engine == "smt" else SolverFor("QF_BV")
    solver.set("timeout", args.gate_timeout * 1000)
    solver.add(*system["core"])
    started = time.monotonic()
    h0 = solver.check()
    h0_elapsed = time.monotonic() - started
    reason = f" reason={solver.reason_unknown()}" if h0 == unknown else ""
    print(f"H0 core -> {h0} elapsed={h0_elapsed:.2f}s{reason}", flush=True)
    if h0 != sat:
        classification = "H0-vacuous" if str(h0) == "unsat" else "inconclusive"
        print(f"DIRECT4_RESULT case={spec.key} classification={classification}", flush=True)
        maxrss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        maxrss_mib = maxrss / (1024 * 1024) if sys.platform == "darwin" else maxrss / 1024
        print(f"PROCESS_RESOURCE elapsed_total={time.monotonic()-process_started:.2f}s "
              f"maxrss_mib={maxrss_mib:.2f} platform={sys.platform}", flush=True)
        print(f"DONE monogenic_stretched_direct4_20260710 case={spec.key}", flush=True)
        return 0

    solver.push()
    solver.add(system["direct_nonzero"])
    solver.set("timeout", args.timeout * 1000)
    started = time.monotonic()
    answer = solver.check()
    elapsed = time.monotonic() - started
    reason = f" reason={solver.reason_unknown()}" if answer == unknown else ""
    print(f"D1 core+[4](T)!=0 -> {answer} elapsed={elapsed:.2f}s{reason}", flush=True)
    if answer == sat:
        certificate = certificate_from_model(spec, system, solver.model())
        print("SAT_CERTIFICATE_JSON " + json.dumps(certificate, sort_keys=True), flush=True)
        if args.certificate_out:
            atomic_json_write(Path(args.certificate_out), certificate)
            print(f"SAT_CERTIFICATE_WRITTEN path={args.certificate_out}", flush=True)
        classification = "SAT-ACTUAL-COUNTEREXAMPLE-CANDIDATE"
    elif str(answer) == "unsat":
        classification = "direct-[4]-UNSAT"
    else:
        classification = "inconclusive"
    solver.pop()
    maxrss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    maxrss_mib = maxrss / (1024 * 1024) if sys.platform == "darwin" else maxrss / 1024
    print(f"DIRECT4_RESULT case={spec.key} classification={classification} "
          f"engine={args.engine} elapsed_total={time.monotonic()-process_started:.2f}s "
          f"maxrss_mib={maxrss_mib:.2f} platform={sys.platform}", flush=True)
    print(f"DONE monogenic_stretched_direct4_20260710 case={spec.key}", flush=True)
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=CASE_KEYS)
    parser.add_argument("--engine", choices=("smt", "qfbv"), default="smt")
    parser.add_argument("--gate-timeout", type=int, default=600,
                        help="seconds for the core nonvacuity check")
    parser.add_argument("--timeout", type=int, default=10800,
                        help="seconds for the direct [4]!=e query")
    parser.add_argument("--memory-mb", type=int, default=6144)
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--certificate-out")
    parser.add_argument("--verify-certificate")
    args = parser.parse_args()
    if args.verify_certificate:
        certificate = json.loads(Path(args.verify_certificate).read_text())
        key = certificate.get("case")
        if key not in CASE_SPECS:
            parser.error(f"certificate has unknown case {key!r}")
        exhaustive_ring_gate(CASE_SPECS[key])
        verify_certificate_data(CASE_SPECS[key], certificate)
        print(f"CERTIFICATE_FILE_VERIFIED path={args.verify_certificate}", flush=True)
        return 0
    if not args.case:
        parser.error("--case is required unless --verify-certificate is used")
    if args.timeout <= 0 or args.gate_timeout <= 0:
        parser.error("timeouts must be positive")
    if args.memory_mb <= 0:
        parser.error("--memory-mb must be positive")

    set_param("parallel.enable", False)
    set_param("smt.threads", 1)
    set_param("sat.threads", 1)
    set_param("memory_max_size", args.memory_mb)
    print("MONOGENIC DIRECT-[4] SEARCH -- STRETCHED t4_11 SOCLE LIFTS", flush=True)
    print("COMMAND " + shlex.join([sys.executable] + sys.argv), flush=True)
    print(f"CONFIG case={args.case} engine={args.engine} gate_timeout={args.gate_timeout}s "
          f"main_timeout={args.timeout}s memory={args.memory_mb}MiB threads=1",
          flush=True)
    return solve_case(CASE_SPECS[args.case], args)


if __name__ == "__main__":
    raise SystemExit(main())
