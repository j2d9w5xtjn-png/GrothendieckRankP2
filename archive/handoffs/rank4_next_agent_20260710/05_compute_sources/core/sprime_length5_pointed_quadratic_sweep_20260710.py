#!/usr/bin/env python3
r"""Exact S' sweep for the fourteen length-five pointed-quadratic rings.

These are the rings with Hilbert function (1,2,2) in
STRUCTURAL_LENGTH6_QUOTIENTS_F2_2026-07-10.md.  The implementation uses a
uniform additive-basis multiplication table.  Before any Hopf query, every
32-element table is checked exhaustively for the ring axioms, locality,
maximal-ideal filtration, deformation range, socle, generator span, and the
complete division syzygy.

The S'-failure formula is the exact finite unrolling from
sprime_ramified_nonprincipal_depth5_stratified_20260709.py.  It checks all six
F_2-rational xy Hopf fibers and all four killed-by-two t^4 normal forms.
"""

from __future__ import annotations

import argparse
import itertools
import sys

from z3 import (
    And, BitVec, BitVecVal, Extract, Or, ZeroExt, is_true, sat, set_param,
    simplify, unknown, unsat,
)

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat import fresh
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_embdim2_len6_20260709 import PinCoproductResidue
from order4sat_ramified_towers_20260709 import value
from ringcheck import Tab, check_axioms, check_locality, ev
from sprime_ramified_length4_six_20260709 import sp_nonprincipal_holds
from sprime_ramified_nonprincipal_depth5_stratified_20260709 import (
    fail_i_residual,
    residual_syzygy_basis,
    solve,
)
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT,
    XY_MULT,
    t4_pins,
)
from s2check import build_blocks


def cast(x, width):
    old = x.size()
    if old == width:
        return x
    if old < width:
        return ZeroExt(width - old, x)
    return Extract(width - 1, 0, x)


class AdditiveTableRing:
    """Finite commutative ring on a direct sum of cyclic 2-power groups."""

    def __init__(self, name, widths, products):
        self.name = name
        self.widths = tuple(widths)
        self.products = {}

        # e_0 is the multiplicative unit.
        for i in range(len(widths)):
            self.products[(0, i)] = {i: 1}
        for (i, j), out in products.items():
            key = tuple(sorted((i, j)))
            if key[0] == 0:
                raise ValueError("do not override unit products")
            self.products[key] = dict(out)

    def zero(self):
        return tuple(BitVecVal(0, w) for w in self.widths)

    def one(self):
        out = list(self.zero())
        out[0] = BitVecVal(1, self.widths[0])
        return tuple(out)

    def var(self, tag):
        nm = fresh(tag)
        return tuple(BitVec(nm + f"_{i}", w) for i, w in enumerate(self.widths))

    def concrete(self, *coords):
        assert len(coords) == len(self.widths)
        return tuple(BitVecVal(a, w) for a, w in zip(coords, self.widths))

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def mul(self, a, b):
        out = [BitVecVal(0, w) for w in self.widths]
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                image = self.products.get(tuple(sorted((i, j))), {})
                for k, coeff in image.items():
                    w = self.widths[k]
                    term = cast(ai, w) * cast(bj, w) * BitVecVal(coeff, w)
                    out[k] = out[k] + term
        return tuple(out)

    def eq0(self, a):
        return And(*[x == 0 for x in a])

    def neq0(self, a):
        return Or(*[x != 0 for x in a])

    def lowzero(self, a):
        return (a[0] & 1) == 0

    def deform(self, tag):
        v = self.var(tag)
        return (2 * v[0],) + v[1:]

    def elements(self):
        return [self.concrete(*coords) for coords in itertools.product(
            *[range(1 << w) for w in self.widths])]


def char2_ring(q):
    """C(q;0), basis 1,x,y and an adapted basis of m^2."""
    if q == "x2":
        products = {(1, 1): {}, (1, 2): {3: 1}, (2, 2): {4: 1}}
    elif q == "xy":
        products = {(1, 1): {3: 1}, (1, 2): {}, (2, 2): {4: 1}}
    elif q == "irr":
        products = {(1, 1): {3: 1}, (1, 2): {4: 1},
                    (2, 2): {3: 1, 4: 1}}
    else:
        raise ValueError(q)
    R = AdditiveTableRing(f"C({q};0)", (1, 1, 1, 1, 1), products)
    return R, [R.concrete(0, 1, 0, 0, 0), R.concrete(0, 0, 1, 0, 0)]


def degree2_ring(q, w):
    """C(q;w), basis 1,x,y,z with the pointed quadratic w identified with 2."""
    cases = {
        ("x2", "y2"): ({}, {3: 1}, {0: 2}),
        ("x2", "xy"): ({}, {0: 2}, {3: 1}),
        ("x2", "xy+y2"): ({}, {0: 2, 3: 1}, {3: 1}),
        ("xy", "x2"): ({0: 2}, {}, {3: 1}),
        ("xy", "x2+y2"): ({0: 2, 3: 1}, {}, {3: 1}),
        ("irr", "x2"): ({0: 2}, {3: 1}, {0: 2, 3: 1}),
    }
    x2, xy, y2 = cases[(q, w)]
    R = AdditiveTableRing(
        f"C({q};{w})", (2, 1, 1, 1),
        {(1, 1): x2, (1, 2): xy, (2, 2): y2})
    return R, [R.concrete(0, 1, 0, 0), R.concrete(0, 0, 1, 0)]


def tangent_ring(label):
    """The five C(q;p) rings, in bases adapted to p=2 and one tangent r."""
    if label == "x2_x":
        # widths: Z/4 . 1 + Z/4 . y + F_2 . y^2; y^2 is the last basis vector.
        R = AdditiveTableRing("C(x2;x)", (2, 2, 1), {(1, 1): {2: 1}})
    elif label == "x2_y":
        # Z/8 . 1 + Z/4 . x, with x^2=0.
        R = AdditiveTableRing("C(x2;y)", (3, 2), {(1, 1): {}})
    elif label == "xy_x":
        # Z/8 . 1 + F_2 . y + F_2 . y^2.
        R = AdditiveTableRing("C(xy;x)", (3, 1, 1), {(1, 1): {2: 1}})
    elif label == "xy_x+y":
        # Z/8 . 1 + Z/4 . x, with x^2=2x.
        R = AdditiveTableRing("C(xy;x+y)", (3, 2), {(1, 1): {1: 2}})
    elif label == "irr_x":
        # Z/8 . 1 + Z/4 . y, with y^2=4+2y.
        R = AdditiveTableRing("C(irr;x)", (3, 2), {(1, 1): {0: 4, 1: 2}})
    else:
        raise ValueError(label)
    coords = [0] * len(R.widths)
    coords[0] = 2
    p = R.concrete(*coords)
    coords = [0] * len(R.widths)
    coords[1] = 1
    r = R.concrete(*coords)
    return R, [p, r]


def all_rings():
    out = {}
    for q in ("x2", "xy", "irr"):
        out[f"eq_{q}"] = char2_ring(q)
    for label in ("x2_x", "x2_y", "xy_x", "xy_x+y", "irr_x"):
        out[f"tan_{label}"] = tangent_ring(label)
    for q, w in (("x2", "y2"), ("x2", "xy"), ("x2", "xy+y2"),
                 ("xy", "x2"), ("xy", "x2+y2"), ("irr", "x2")):
        out[f"deg2_{q}_{w}"] = degree2_ring(q, w)
    assert len(out) == 14
    return out


def validate_presentation(key, R, gens):
    """Check the advertised q=0 and 2=p/w relations inside the table."""
    z = R.zero()
    two = R.add(R.one(), R.one())

    if key.startswith("eq_") or key.startswith("deg2_"):
        x, y = gens
    elif key == "tan_x2_x":
        x, y = gens[0], gens[1]
    elif key == "tan_x2_y":
        x, y = gens[1], gens[0]
    elif key == "tan_xy_x":
        x, y = gens[0], gens[1]
    elif key == "tan_xy_x+y":
        x, y = gens[1], R.sub(gens[0], gens[1])
    elif key == "tan_irr_x":
        x, y = gens[0], gens[1]
    else:
        raise ValueError(key)

    x2, xy, y2 = R.mul(x, x), R.mul(x, y), R.mul(y, y)
    qname = key.split("_")[1]
    if qname == "x2":
        qval = x2
    elif qname == "xy":
        qval = xy
    elif qname == "irr":
        qval = R.add(R.add(x2, xy), y2)
    else:
        raise ValueError(qname)
    assert value(qval) == value(z), f"{key}: q relation failed"

    if key.startswith("eq_"):
        assert value(two) == value(z), f"{key}: expected characteristic two"
    elif key.startswith("tan_"):
        point = {
            "tan_x2_x": x,
            "tan_x2_y": y,
            "tan_xy_x": x,
            "tan_xy_x+y": R.add(x, y),
            "tan_irr_x": x,
        }[key]
        assert value(two) == value(point), f"{key}: tangent point 2=p failed"
    else:
        wname = key.split("_", 2)[2]
        point = {
            "y2": y2,
            "xy": xy,
            "xy+y2": R.add(xy, y2),
            "x2": x2,
            "x2+y2": R.add(x2, y2),
        }[wname]
        assert value(two) == value(point), f"{key}: degree-two point 2=w failed"


def validate_ring(key, R, gens):
    els = R.elements()
    T = Tab(R, els)
    check_axioms(T, [ev(x) for x in els], triple_cap=32)
    nm, residue, powers = check_locality(T, expect_residue_deg=1)
    assert (len(els), nm, powers) == (32, 16, [16, 4, 1])

    # The displayed pair must generate the full maximal ideal as an R-module.
    span = set()
    for coeffs in itertools.product(els, repeat=2):
        z = R.zero()
        for a, g in zip(coeffs, gens):
            z = R.add(z, R.mul(a, g))
        span.add(value(z))
    maximal = {value(a) for a in els if is_true(simplify(R.lowzero(a)))}
    assert span == maximal

    soc = [a for a in els if all(value(R.mul(a, g)) == value(R.zero())
                                 for g in gens)]
    assert len(soc) == 4
    validate_presentation(key, R, gens)
    print(f"VALIDATED {R.name}", flush=True)
    print(f"  |R|=32, |m|=16, residue F_{residue}, |m^k|={powers}, |Soc|=4",
          flush=True)
    _, basis = residual_syzygy_basis(R, gens)
    return basis


def run_pointed_model(base, gens, basis, fib, pins, label, timeout, only_i):
    """Classify H0-vacuity separately from exact S'-failure."""
    print(f"  --- {label} ---", flush=True)
    R = PinCoproductResidue(base, pins)
    A, M, C, F, phi, _, _ = build_blocks(R, fib)
    core = A + M + C + F
    h0 = solve("H0 axioms+fiber2 sanity", core, timeout)
    if h0 == unsat:
        print("    [H0-VACUOUS: no bialgebra lift in this stratum]", flush=True)
        return {"class": "H0-vacuous", "H0": "unsat", "S1": "not-run", "S2": {}}
    if h0 == unknown:
        return {"class": "unknown", "H0": "unknown", "S1": "not-run", "S2": {}}

    holds = sp_nonprincipal_holds(R, phi, gens, "pqH")
    s1 = solve("S1 axioms+fiber2+S'-HOLDS", core + [holds], timeout)
    if s1 != sat:
        # S1 is only an existential sanity witness.  Its failure must not
        # suppress the logically decisive universal-failure queries below.
        print("    [S1 SANITY WARNING; continuing to exact FAIL_i queries]",
              flush=True)

    outcomes = {}
    full_split = set(only_i) == {1, 2, 3}
    row_class = "UNSAT" if full_split else "PARTIAL-UNSAT"
    for i in only_i:
        failure = fail_i_residual(base, phi, gens, basis, "pqF", i, unroll=True)
        ans = solve(f"S2.{i} axioms+fiber2+S'-FAIL_i", core + [failure], timeout)
        outcomes[str(i)] = str(ans)
        if ans == sat:
            row_class = "SAT S'-failure"
        elif ans == unknown and row_class != "SAT S'-failure":
            row_class = "unknown"
    return {"class": row_class, "H0": "sat", "S1": str(s1), "S2": outcomes}


def main():
    rings = all_rings()
    ap = argparse.ArgumentParser()
    ap.add_argument("--rings", nargs="+", choices=tuple(rings), default=tuple(rings))
    ap.add_argument("--fibers", choices=("xy", "t4", "all"), default="all")
    ap.add_argument("--xy-models", nargs="+", choices=tuple(XY_MODELS),
                    default=tuple(XY_MODELS))
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--validate-only", action="store_true")
    ap.add_argument("--only-i", nargs="+", type=int, choices=(1, 2, 3),
                    default=(1, 2, 3))
    args = ap.parse_args()
    set_param("parallel.enable", True)

    for key in args.rings:
        R, gens = rings[key]
        print(f"===== POINTED QUADRATIC {key}: {R.name} =====", flush=True)
        basis = validate_ring(key, R, gens)
        if args.validate_only:
            continue
        results = []
        if args.fibers in ("xy", "all"):
            for model in args.xy_models:
                label = f"xy/{model}"
                result = run_pointed_model(
                    R, gens, basis, XY_MULT, XY_MODELS[model], label,
                    args.timeout, tuple(args.only_i))
                results.append((label, result))
        if args.fibers in ("t4", "all"):
            for c1, c4 in itertools.product((0, 1), repeat=2):
                label = f"t4/c1={c1},c4={c4}"
                result = run_pointed_model(
                    R, gens, basis, T4_MULT, t4_pins(c1, c4), label,
                    args.timeout, tuple(args.only_i))
                results.append((label, result))
        print("SUMMARY", flush=True)
        for label, result in results:
            s2 = ",".join(f"{i}:{v}" for i, v in sorted(result["S2"].items()))
            print(f"  {label}: class={result['class']}; H0={result['H0']}; "
                  f"S1={result['S1']}; S2={s2 or 'not-run'}", flush=True)
        print(f"DONE {key}", flush=True)

    print("DONE sprime_length5_pointed_quadratic_sweep_20260710", flush=True)


if __name__ == "__main__":
    main()
