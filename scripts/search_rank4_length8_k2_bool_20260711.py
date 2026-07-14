#!/usr/bin/env python3
"""Exact Boolean search on the k=2 length-eight complete intersection.

This is a specialized, independently checkable companion to
``search_rank4_length8_ci_20260711.py``.  It treats only

    R = Z[x,y]/(x^2, y^4, x*y^2-2)

and encodes elements of the maximal ideal by seven Booleans, ordered as

    x, y, y^2, xy, y^3, 2, 2y.

The only non-vector-space carry in this coordinate system is y+y=2y.
Products are written directly in the associated filtration coordinates.
Thus Z3 receives Boolean XOR/AND circuits rather than multiplication of
mixed-width bit-vectors.  The default query asks whether target 2 of the
universal alpha_2^2 chart is exactly the socle generator 2y.

Every SAT result is re-evaluated using the separate concrete ring arithmetic
from ``search_rank4_length8_ci_20260711.py`` before a witness is accepted.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path
from typing import Dict, Iterable, Sequence, Tuple


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, "/tmp/rank4_z3")

import z3

import scripts.audit_universal_rank4_quadratic as universal
import scripts.search_rank4_length8_ci_20260711 as reference


# Coordinates: X,Y,U,V,P,Q,S = x,y,y^2,xy,y^3,2,2y.
X, Y, U, V, P, Q, S = range(7)
Elt = Tuple[z3.BoolRef, ...]
Bits = Tuple[int, ...]


def bxor(*args):
    """Small simplifying XOR constructor."""
    parity = False
    kept = []
    for arg in args:
        if z3.is_true(arg):
            parity = not parity
        elif not z3.is_false(arg):
            kept.append(arg)
    if not kept:
        return z3.BoolVal(parity)
    if len(kept) == 1:
        return z3.Not(kept[0]) if parity else kept[0]
    out = kept[0]
    for arg in kept[1:]:
        out = z3.Xor(out, arg)
    return z3.Not(out) if parity else out


def band(*args):
    """Small simplifying AND constructor."""
    kept = []
    for arg in args:
        if z3.is_false(arg):
            return z3.BoolVal(False)
        if not z3.is_true(arg):
            kept.append(arg)
    if not kept:
        return z3.BoolVal(True)
    if len(kept) == 1:
        return kept[0]
    return z3.And(*kept)


FALSE = z3.BoolVal(False)
ZERO: Elt = (FALSE,) * 7


def even_integer(value: int) -> Elt:
    """An even integer in R; all chart constants are even."""
    assert value % 2 == 0
    out = [FALSE] * 7
    out[Q] = z3.BoolVal(bool((value >> 1) & 1))
    return tuple(out)


def add(left: Elt, right: Elt) -> Elt:
    """Exact addition; the high y bit receives the binary carry."""
    out = [bxor(a, b) for a, b in zip(left, right)]
    out[S] = bxor(left[S], right[S], band(left[Y], right[Y]))
    return tuple(out)


def scale(coefficient: int, value: Elt) -> Elt:
    """Exact integer scaling in the additive group (Z/2)^5 x (Z/4)."""
    if coefficient & 1:
        out = list(value)
        if (coefficient >> 1) & 1:
            out[S] = bxor(out[S], value[Y])
        return tuple(out)
    if (coefficient >> 1) & 1:
        out = [FALSE] * 7
        out[S] = value[Y]
        return tuple(out)
    return ZERO


def mul(left: Elt, right: Elt) -> Elt:
    """Exact multiplication of two elements in the maximal ideal."""
    out = [FALSE] * 7
    out[U] = band(left[Y], right[Y])
    out[V] = bxor(band(left[X], right[Y]), band(left[Y], right[X]))
    out[P] = bxor(band(left[Y], right[U]), band(left[U], right[Y]))
    out[Q] = bxor(
        band(left[X], right[U]), band(left[U], right[X]),
        band(left[Y], right[V]), band(left[V], right[Y]),
    )
    out[S] = bxor(
        band(left[Q], right[Y]), band(left[Y], right[Q]),
        band(left[P], right[X]), band(left[X], right[P]),
        band(left[U], right[V]), band(left[V], right[U]),
    )
    return tuple(out)


def bits_add(left: Bits, right: Bits) -> Bits:
    out = [a ^ b for a, b in zip(left, right)]
    out[S] ^= left[Y] & right[Y]
    return tuple(out)


def bits_scale(coefficient: int, value: Bits) -> Bits:
    out = tuple((coefficient & 1) * bit for bit in value)
    if (coefficient >> 1) & 1:
        out = out[:S] + (out[S] ^ value[Y],)
    return out


def bits_mul(left: Bits, right: Bits) -> Bits:
    out = [0] * 7
    out[U] = left[Y] & right[Y]
    out[V] = (left[X] & right[Y]) ^ (left[Y] & right[X])
    out[P] = (left[Y] & right[U]) ^ (left[U] & right[Y])
    out[Q] = ((left[X] & right[U]) ^ (left[U] & right[X]) ^
              (left[Y] & right[V]) ^ (left[V] & right[Y]))
    out[S] = ((left[Q] & right[Y]) ^ (left[Y] & right[Q]) ^
              (left[P] & right[X]) ^ (left[X] & right[P]) ^
              (left[U] & right[V]) ^ (left[V] & right[U]))
    return tuple(out)


def bits_to_coord(value: Bits) -> reference.Coord:
    """Convert filtration bits to the reference basis 1,y,y2,y3,x,xy."""
    return (2 * value[Q], value[Y] + 2 * value[S],
            value[U], value[P], value[X], value[V])


def coord_to_bits(value: reference.Coord) -> Bits:
    assert value[0] in (0, 2)
    return (value[4], value[1] & 1, value[2], value[5],
            value[3], value[0] >> 1, value[1] >> 1)


def gate_boolean_ring() -> None:
    """Exhaustively compare all Boolean operations with the reference ring."""
    spec = reference.ring_spec(2)
    all_bits = [tuple((n >> i) & 1 for i in range(7)) for n in range(128)]
    for left in all_bits:
        left_coord = bits_to_coord(left)
        assert coord_to_bits(left_coord) == left
        for coefficient in range(-4, 5):
            wanted = tuple((coefficient * a) % (1 << width)
                           for a, width in zip(left_coord, spec.widths))
            assert bits_to_coord(bits_scale(coefficient, left)) == wanted
        for right in all_bits:
            right_coord = bits_to_coord(right)
            assert bits_to_coord(bits_add(left, right)) == reference.concrete_add(
                spec, left_coord, right_coord)
            assert bits_to_coord(bits_mul(left, right)) == reference.concrete_mul(
                spec, left_coord, right_coord)
    print("R2 Boolean ring gate PASS (128^2 exhaustive products/sums)", flush=True)


def parameter_names() -> Tuple[str, ...]:
    return reference.parameter_names()


def polynomial_value(poly: universal.Poly, values: Sequence[Elt], cache: Dict) -> Elt:
    def monomial_value(monomial: Tuple[int, ...]) -> Elt:
        if monomial not in cache:
            assert monomial
            if len(monomial) == 1:
                cache[monomial] = values[monomial[0]]
            else:
                cache[monomial] = mul(monomial_value(monomial[:-1]),
                                      values[monomial[-1]])
        return cache[monomial]

    out = ZERO
    for monomial, coefficient in poly.items():
        if monomial:
            term = scale(coefficient, monomial_value(monomial))
        else:
            term = even_integer(coefficient)
        out = add(out, term)
    return out


def concrete_polynomial_bits(poly: universal.Poly, values: Sequence[Bits]) -> Bits:
    cache: Dict[Tuple[int, ...], Bits] = {}

    def monomial_value(monomial: Tuple[int, ...]) -> Bits:
        if monomial not in cache:
            if len(monomial) == 1:
                cache[monomial] = values[monomial[0]]
            else:
                cache[monomial] = bits_mul(monomial_value(monomial[:-1]),
                                           values[monomial[-1]])
        return cache[monomial]

    out = (0,) * 7
    for monomial, coefficient in poly.items():
        if monomial:
            term = bits_scale(coefficient, monomial_value(monomial))
        else:
            assert coefficient % 2 == 0
            term_list = [0] * 7
            term_list[Q] = (coefficient >> 1) & 1
            term = tuple(term_list)
        out = bits_add(out, term)
    return out


def check(args: argparse.Namespace) -> str:
    gate_boolean_ring()
    universal.MAX_DEGREE = 4
    chart = universal.build_chart(0)
    assert len(chart.equations_z) == 189
    assert all(poly.get((), 0) % 2 == 0 for poly in chart.equations_z)
    assert chart.targets_z[args.target].get((), 0) % 2 == 0

    names = parameter_names()
    values: list[Elt] = [tuple(z3.Bool(f"{name}_{tag}") for tag in
                               ("x", "y", "y2", "xy", "y3", "two", "two_y"))
                         for name in names]
    cache: Dict[Tuple[int, ...], Elt] = {}
    started_build = time.time()
    equations = [polynomial_value(poly, values, cache) for poly in chart.equations_z]
    target = polynomial_value(chart.targets_z[args.target], values, cache)
    build_seconds = time.time() - started_build

    # Coordinates forced false are omitted syntactically; all surviving bits
    # are asserted.  Exact-socle is the focused lifting query; nonzero is the
    # full counterexample query for this one target coordinate of [4]^#.
    constraints = []
    for equation in equations:
        constraints.extend(z3.Not(bit) for bit in equation if not z3.is_false(bit))
    if args.condition == "exact-socle":
        for i, bit in enumerate(target):
            constraints.append(bit if i == S else z3.Not(bit))
    else:
        constraints.append(z3.Or(*target))

    solver = z3.Solver()
    solver.set(timeout=args.timeout * 1000)
    solver.set(max_memory=args.memory_mb)
    solver.add(*constraints)
    print(f"built Boolean circuit in {build_seconds:.3f}s: "
          f"parameters={len(values) * 7} constraints={len(constraints)} "
          f"cached_monomials={len(cache)}", flush=True)

    started = time.time()
    verdict = solver.check()
    solve_seconds = time.time() - started
    print(f"R2 target={args.target} condition={args.condition} verdict={verdict} "
          f"seconds={solve_seconds:.3f}", flush=True)
    if verdict != z3.sat:
        if verdict == z3.unknown:
            print(f"reason_unknown={solver.reason_unknown()}", flush=True)
        return str(verdict)

    model = solver.model()
    bit_values: list[Bits] = [tuple(1 if z3.is_true(model.eval(bit, model_completion=True))
                                          else 0 for bit in value)
                              for value in values]
    coords = [bits_to_coord(value) for value in bit_values]

    # Two independent concrete re-evaluations: the Boolean formulas above and
    # the original mixed-width reference ring implementation.
    zero_bits = (0,) * 7
    equation_bits = [concrete_polynomial_bits(poly, bit_values)
                     for poly in chart.equations_z]
    target_bits = [concrete_polynomial_bits(poly, bit_values)
                   for poly in chart.targets_z]
    assert all(value == zero_bits for value in equation_bits)
    if args.condition == "exact-socle":
        assert target_bits[args.target] == tuple(1 if i == S else 0 for i in range(7))
    else:
        assert any(target_bits[args.target])

    spec = reference.ring_spec(2)
    zero_coord = (0,) * len(spec.widths)
    equation_coords = [reference.concrete_poly(spec, poly, coords)
                       for poly in chart.equations_z]
    target_coords = [reference.concrete_poly(spec, poly, coords)
                     for poly in chart.targets_z]
    assert all(value == zero_coord for value in equation_coords)
    if args.condition == "exact-socle":
        assert target_coords[args.target] == reference.socle(spec)
    else:
        assert target_coords[args.target] != zero_coord
    assert target_coords[args.target] == bits_to_coord(target_bits[args.target])

    witness = {
        "ring": spec.name,
        "basis": spec.basis,
        "widths": spec.widths,
        "target_index": args.target,
        "condition": args.condition,
        "parameters": dict(zip(names, coords)),
        "parameter_filtration_bits": dict(zip(names, bit_values)),
        "targets": target_coords,
        "build_seconds": build_seconds,
        "solve_seconds": solve_seconds,
        "z3_version": z3.get_version_string(),
        "verification": "PASS: Boolean and reference concrete evaluators",
    }
    print("SAT witness verified; targets=" + repr(target_coords), flush=True)
    if args.output:
        args.output.write_text(json.dumps(witness, indent=2) + "\n")
        print(f"wrote {args.output}", flush=True)
    return "sat"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", type=int, choices=range(9), default=2)
    parser.add_argument("--condition", choices=("exact-socle", "nonzero"),
                        default="exact-socle")
    parser.add_argument("--timeout", type=int, default=120,
                        help="solver timeout in seconds (default: 120)")
    parser.add_argument("--memory-mb", type=int, default=2048)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    verdict = check(args)
    if verdict == "unknown":
        raise SystemExit(2)


if __name__ == "__main__":
    main()
