#!/usr/bin/env python3
"""Exact Boolean universal-alpha2^2 search on two length-eight CI rings.

The supported base rings are the split- and irreducible-quadratic examples
from ``rank4_length8_other_ci_tables_20260711.py``.  Every element of their
maximal ideals has order two, so a ring-valued deformation parameter is
represented by seven Booleans in the filtration bases

    split:       x,y,x^2,y^2,x^3,y^3,2,
    irreducible: x,y,x^2,xy,x^3,x^2y,2.

The 189 integral bialgebra equations and nine exact [4]^# coordinates are
imported from ``audit_universal_rank4_quadratic.py`` and retained through
ordinary parameter degree four.  This is exact because m^5=0.  Before each
query the full 256-element concrete table gate, all 128^2 maximal-ideal
sums/products, and independent random polynomial evaluations must pass.

A SAT answer is reported only after the model is re-evaluated by both the
concrete Boolean circuit and the separately implemented coordinate ring.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Mapping, Sequence, Tuple


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, "/tmp/rank4_z3")

import z3

import scripts.audit_universal_rank4_quadratic as universal
import scripts.rank4_length8_other_ci_tables_20260711 as reference


Elt = Tuple[z3.BoolRef, ...]
Bits = Tuple[int, ...]
FALSE = z3.BoolVal(False)
ZERO: Elt = (FALSE,) * 7
ZERO_BITS: Bits = (0,) * 7
SOCLE = 6


def bxor(*args):
    parity = False
    kept = []
    for arg in args:
        if z3.is_true(arg):
            parity = not parity
        elif not z3.is_false(arg):
            kept.append(arg)
    if not kept:
        return z3.BoolVal(parity)
    out = kept[0]
    for arg in kept[1:]:
        out = z3.Xor(out, arg)
    return z3.Not(out) if parity else out


def band(*args):
    kept = []
    for arg in args:
        if z3.is_false(arg):
            return FALSE
        if not z3.is_true(arg):
            kept.append(arg)
    if not kept:
        return z3.BoolVal(True)
    if len(kept) == 1:
        return kept[0]
    return z3.And(*kept)


@dataclass(frozen=True)
class BooleanRing:
    key: str
    labels: Tuple[str, ...]
    # output bit <- XOR of left[a] AND right[b]
    mul_terms: Mapping[int, Tuple[Tuple[int, int], ...]]

    def add(self, left: Elt, right: Elt) -> Elt:
        return tuple(bxor(a, b) for a, b in zip(left, right))

    def bits_add(self, left: Bits, right: Bits) -> Bits:
        return tuple(a ^ b for a, b in zip(left, right))

    def scale(self, coefficient: int, value: Elt) -> Elt:
        return value if coefficient & 1 else ZERO

    def bits_scale(self, coefficient: int, value: Bits) -> Bits:
        return value if coefficient & 1 else ZERO_BITS

    def mul(self, left: Elt, right: Elt) -> Elt:
        out = [FALSE] * 7
        for target, terms in self.mul_terms.items():
            out[target] = bxor(*(band(left[a], right[b]) for a, b in terms))
        return tuple(out)

    def bits_mul(self, left: Bits, right: Bits) -> Bits:
        out = [0] * 7
        for target, terms in self.mul_terms.items():
            for a, b in terms:
                out[target] ^= left[a] & right[b]
        return tuple(out)

    def even_integer(self, value: int) -> Elt:
        assert value % 2 == 0
        out = [FALSE] * 7
        out[SOCLE] = z3.BoolVal(bool((value // 2) & 1))
        return tuple(out)

    def bits_even_integer(self, value: int) -> Bits:
        assert value % 2 == 0
        out = [0] * 7
        out[SOCLE] = (value // 2) & 1
        return tuple(out)

    def bits_to_coord(self, value: Bits) -> reference.Coord:
        return (2 * value[SOCLE],) + value[:SOCLE]

    def coord_to_bits(self, value: reference.Coord) -> Bits:
        assert value[0] in (0, 2)
        return value[1:] + (value[0] // 2,)


def boolean_ring(key: str) -> BooleanRing:
    if key == "split":
        # x,y,x2,y2,x3,y3,two
        return BooleanRing(
            key,
            ("x", "y", "x2", "y2", "x3", "y3", "two"),
            {
                2: ((0, 0),),
                3: ((1, 1),),
                4: ((0, 2), (2, 0)),
                5: ((1, 3), (3, 1)),
                6: ((0, 4), (4, 0), (2, 2),
                    (1, 5), (5, 1), (3, 3)),
            },
        )
    if key == "irreducible":
        # x,y,x2,xy,x3,x2y,two
        return BooleanRing(
            key,
            ("x", "y", "x2", "xy", "x3", "x2y", "two"),
            {
                2: ((0, 0), (1, 1)),
                3: ((0, 1), (1, 0), (1, 1)),
                4: ((0, 2), (2, 0), (1, 3), (3, 1)),
                5: ((0, 3), (3, 0), (1, 2), (2, 1),
                    (1, 3), (3, 1)),
                6: ((0, 5), (5, 0), (1, 4), (4, 1),
                    (1, 5), (5, 1), (2, 3), (3, 2), (3, 3)),
            },
        )
    raise ValueError(key)


def parameter_names() -> Tuple[str, ...]:
    names = []
    for i, j in ((1, 1), (1, 2), (1, 3), (2, 2), (2, 3), (3, 3)):
        for r in range(1, 4):
            names.append(f"m{i}{j}_{r}")
    for i in range(1, 4):
        for j in range(1, 4):
            for k in range(1, 4):
                names.append(f"c{i}{j}{k}")
    assert len(names) == 45
    return tuple(names)


def gate_boolean_ring(ring: BooleanRing) -> dict:
    spec = reference.ring_spec(ring.key)
    full_summary = reference.gate_ring(spec)
    all_bits = [tuple((number >> i) & 1 for i in range(7)) for number in range(128)]
    for left in all_bits:
        left_coord = ring.bits_to_coord(left)
        assert ring.coord_to_bits(left_coord) == left
        for coefficient in range(-8, 9):
            wanted = reference.scale(spec, coefficient, left_coord)
            assert ring.bits_to_coord(ring.bits_scale(coefficient, left)) == wanted
        for right in all_bits:
            right_coord = ring.bits_to_coord(right)
            assert ring.bits_to_coord(ring.bits_add(left, right)) == reference.add(
                spec, left_coord, right_coord
            )
            assert ring.bits_to_coord(ring.bits_mul(left, right)) == reference.mul(
                spec, left_coord, right_coord
            )
    print(f"{spec.name}: Boolean maximal-ideal gate PASS (128^2 sums/products)",
          flush=True)
    return full_summary


def symbolic_poly(ring: BooleanRing, poly: universal.Poly,
                  values: Sequence[Elt], cache: Dict[Tuple[int, ...], Elt]) -> Elt:
    def monomial(mon: Tuple[int, ...]) -> Elt:
        if mon not in cache:
            assert mon
            cache[mon] = (
                values[mon[0]] if len(mon) == 1 else
                ring.mul(monomial(mon[:-1]), values[mon[-1]])
            )
        return cache[mon]

    out = ZERO
    for mon, coefficient in poly.items():
        term = (ring.scale(coefficient, monomial(mon)) if mon else
                ring.even_integer(coefficient))
        out = ring.add(out, term)
    return out


def concrete_poly_bits(ring: BooleanRing, poly: universal.Poly,
                       values: Sequence[Bits]) -> Bits:
    cache: Dict[Tuple[int, ...], Bits] = {}

    def monomial(mon: Tuple[int, ...]) -> Bits:
        if mon not in cache:
            assert mon
            cache[mon] = (values[mon[0]] if len(mon) == 1 else
                          ring.bits_mul(monomial(mon[:-1]), values[mon[-1]]))
        return cache[mon]

    out = ZERO_BITS
    for mon, coefficient in poly.items():
        term = (ring.bits_scale(coefficient, monomial(mon)) if mon else
                ring.bits_even_integer(coefficient))
        out = ring.bits_add(out, term)
    return out


def concrete_poly_coord(spec: reference.RingSpec, poly: universal.Poly,
                        values: Sequence[reference.Coord]) -> reference.Coord:
    cache: Dict[Tuple[int, ...], reference.Coord] = {}

    def monomial(mon: Tuple[int, ...]) -> reference.Coord:
        if mon not in cache:
            assert mon
            cache[mon] = (values[mon[0]] if len(mon) == 1 else
                          reference.mul(spec, monomial(mon[:-1]), values[mon[-1]]))
        return cache[mon]

    out = reference.zero(spec)
    for mon, coefficient in poly.items():
        term = (reference.scale(spec, coefficient, monomial(mon)) if mon else
                (coefficient % 4,) + (0,) * 6)
        out = reference.add(spec, out, term)
    return out


def polynomial_cross_gate(ring: BooleanRing, chart: universal.Chart,
                          trials: int) -> None:
    if not trials:
        return
    spec = reference.ring_spec(ring.key)
    rng = random.Random(20260711 + (0 if ring.key == "split" else 1000))
    polys = chart.equations_z + chart.targets_z
    for trial in range(trials):
        bits = [tuple(rng.randrange(2) for _ in range(7)) for _ in range(45)]
        coords = [ring.bits_to_coord(value) for value in bits]
        for index, poly in enumerate(polys):
            got = ring.bits_to_coord(concrete_poly_bits(ring, poly, bits))
            wanted = concrete_poly_coord(spec, poly, coords)
            assert got == wanted, (ring.key, trial, index, got, wanted)
    print(f"{spec.name}: polynomial cross-gate PASS "
          f"({trials * len(polys)} evaluations)", flush=True)


def search(args: argparse.Namespace) -> dict:
    ring = boolean_ring(args.ring)
    table_summary = gate_boolean_ring(ring)

    universal.MAX_DEGREE = 4
    chart = universal.build_chart(0)
    assert chart.name == "a2a2"
    assert len(chart.equations_z) == 189
    assert len(chart.targets_z) == 9
    assert max(len(mon) for poly in chart.equations_z + chart.targets_z
               for mon in poly) <= 4
    assert all(poly.get((), 0) % 2 == 0
               for poly in chart.equations_z + chart.targets_z)
    polynomial_cross_gate(ring, chart, args.audit_trials)

    names = parameter_names()
    values = [tuple(z3.Bool(f"{name}_{label}") for label in ring.labels)
              for name in names]
    cache: Dict[Tuple[int, ...], Elt] = {}
    build_started = time.time()
    equations = [symbolic_poly(ring, poly, values, cache) for poly in chart.equations_z]
    target = symbolic_poly(ring, chart.targets_z[args.target], values, cache)
    build_seconds = time.time() - build_started

    constraints = [z3.Not(bit) for equation in equations for bit in equation
                   if not z3.is_false(bit)]
    if args.condition == "exact-socle":
        constraints.extend(bit if i == SOCLE else z3.Not(bit)
                           for i, bit in enumerate(target))
    else:
        constraints.append(z3.Or(*target))

    solver = z3.Solver()
    solver.set(timeout=args.timeout * 1000)
    solver.set(max_memory=args.memory_mb)
    solver.set(threads=1)
    solver.add(*constraints)
    print(f"built in {build_seconds:.3f}s: bits={len(values) * 7} "
          f"constraints={len(constraints)} monomials={len(cache)}", flush=True)
    solve_started = time.time()
    verdict = solver.check()
    solve_seconds = time.time() - solve_started
    reason_unknown = solver.reason_unknown() if verdict == z3.unknown else None
    spec = reference.ring_spec(ring.key)
    print(f"{spec.name}: target={args.target} condition={args.condition} "
          f"verdict={verdict} seconds={solve_seconds:.3f}", flush=True)
    if reason_unknown:
        print("reason_unknown=" + reason_unknown, flush=True)

    result = {
        "ring_key": ring.key,
        "ring": spec.name,
        "target_index": args.target,
        "condition": args.condition,
        "verdict": str(verdict),
        "reason_unknown": reason_unknown,
        "build_seconds": build_seconds,
        "solve_seconds": solve_seconds,
        "timeout_seconds": args.timeout,
        "memory_mb": args.memory_mb,
        "threads": 1,
        "parameter_bits": 315,
        "equation_count": 189,
        "target_count": 9,
        "cached_monomials": len(cache),
        "audit_trials": args.audit_trials,
        "z3_version": z3.get_version_string(),
        "table_gate": table_summary,
    }
    if verdict != z3.sat:
        if args.output:
            args.output.write_text(json.dumps(result, indent=2) + "\n")
            print(f"wrote {args.output}", flush=True)
        return result

    model = solver.model()
    bit_values = [tuple(
        1 if z3.is_true(model.eval(bit, model_completion=True)) else 0
        for bit in value
    ) for value in values]
    coords = [ring.bits_to_coord(value) for value in bit_values]

    equation_bits = [concrete_poly_bits(ring, poly, bit_values)
                     for poly in chart.equations_z]
    target_bits = [concrete_poly_bits(ring, poly, bit_values)
                   for poly in chart.targets_z]
    assert all(value == ZERO_BITS for value in equation_bits)
    if args.condition == "exact-socle":
        assert target_bits[args.target] == (0, 0, 0, 0, 0, 0, 1)
    else:
        assert any(target_bits[args.target])

    equation_coords = [concrete_poly_coord(spec, poly, coords)
                       for poly in chart.equations_z]
    target_coords = [concrete_poly_coord(spec, poly, coords)
                     for poly in chart.targets_z]
    assert all(value == reference.zero(spec) for value in equation_coords)
    assert target_coords[args.target] == ring.bits_to_coord(target_bits[args.target])
    if args.condition == "exact-socle":
        assert target_coords[args.target] == reference.two(spec)
    else:
        assert target_coords[args.target] != reference.zero(spec)

    result.update({
        "verification": "PASS: concrete Boolean and independent coordinate evaluators",
        "parameters": dict(zip(names, coords)),
        "parameter_filtration_bits": dict(zip(names, bit_values)),
        "targets": target_coords,
    })
    print("VERIFIED SAT: stop the campaign immediately; targets=" +
          repr(target_coords), flush=True)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
        print(f"wrote {args.output}", flush=True)
    return result


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--ring", choices=("split", "irreducible"), required=True)
    parser.add_argument("--target", type=int, choices=range(9), required=True)
    parser.add_argument("--condition", choices=("nonzero", "exact-socle"),
                        default="nonzero")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--memory-mb", type=int, default=2048)
    parser.add_argument("--audit-trials", type=int, default=2)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = search(args)
    if result["verdict"] == "sat":
        # A verified SAT witness is a campaign stop condition, not an ordinary
        # successful negative query.  Distinct status makes sequential bounded
        # launchers halt before starting another target.
        raise SystemExit(10)
    if result["verdict"] == "unknown":
        raise SystemExit(2)


if __name__ == "__main__":
    main()
