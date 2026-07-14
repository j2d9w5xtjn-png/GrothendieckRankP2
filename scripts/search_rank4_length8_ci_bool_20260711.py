#!/usr/bin/env python3
"""Exact seven-Boolean search on all three length-eight CI base rings.

For k=1,2,3 this encodes the maximal ideal of

    R_k = Z[x,y]/(x^2, y^4, x*y^k-2)

in a filtration-adapted seven-bit basis.  Addition carries, doubling, and
multiplication are specified as Boolean XOR/AND circuits and exhaustively
checked against the independent coordinate tables in
``search_rank4_length8_ci_20260711.py`` before every solver query.

The universal alpha_2^2 equations and [4]^# targets are evaluated through
degree four, which is exact because m^5=0.  A SAT model is accepted only
after both this file's concrete Boolean evaluator and the original concrete
coordinate evaluator reproduce all 189 equations and the requested target.
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
import scripts.search_rank4_length8_ci_20260711 as reference


Elt = Tuple[z3.BoolRef, ...]
Bits = Tuple[int, ...]
FALSE = z3.BoolVal(False)
ZERO: Elt = (FALSE,) * 7
ZERO_BITS: Bits = (0,) * 7
SOCLE = 6                         # chosen last in every filtration basis


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
    k: int
    labels: Tuple[str, ...]
    # target <- left[source_a] & right[source_b]
    mul_terms: Mapping[int, Tuple[Tuple[int, int], ...]]
    # target <- carry left[source] & right[source] under addition
    add_carries: Tuple[Tuple[int, int], ...]
    # target <- source under multiplication by 2
    doubles: Tuple[Tuple[int, int], ...]
    two_index: int

    def add(self, left: Elt, right: Elt) -> Elt:
        out = [bxor(a, b) for a, b in zip(left, right)]
        for target, source in self.add_carries:
            out[target] = bxor(out[target], band(left[source], right[source]))
        return tuple(out)

    def bits_add(self, left: Bits, right: Bits) -> Bits:
        out = [a ^ b for a, b in zip(left, right)]
        for target, source in self.add_carries:
            out[target] ^= left[source] & right[source]
        return tuple(out)

    def scale(self, coefficient: int, value: Elt) -> Elt:
        out = list(value) if coefficient & 1 else [FALSE] * 7
        if (coefficient >> 1) & 1:
            for target, source in self.doubles:
                out[target] = bxor(out[target], value[source])
        return tuple(out)

    def bits_scale(self, coefficient: int, value: Bits) -> Bits:
        out = list(value) if coefficient & 1 else [0] * 7
        if (coefficient >> 1) & 1:
            for target, source in self.doubles:
                out[target] ^= value[source]
        return tuple(out)

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
        out[self.two_index] = z3.BoolVal(bool((value >> 1) & 1))
        return tuple(out)

    def bits_even_integer(self, value: int) -> Bits:
        assert value % 2 == 0
        out = [0] * 7
        out[self.two_index] = (value >> 1) & 1
        return tuple(out)

    def bits_to_coord(self, value: Bits) -> reference.Coord:
        if self.k == 1:
            # x,y,y2,2,y3,2y,2y2 -> 1,y,y2,y3,x
            return (2 * value[3], value[1] + 2 * value[5],
                    value[2] + 2 * value[6], value[4], value[0])
        if self.k == 2:
            # x,y,y2,xy,y3,2,2y -> 1,y,y2,y3,x,xy
            return (2 * value[5], value[1] + 2 * value[6],
                    value[2], value[4], value[0], value[3])
        # x,y,y2,xy,y3,xy2,2 -> 1,y,y2,y3,x,xy,xy2
        return (2 * value[6], value[1], value[2], value[4],
                value[0], value[3], value[5])

    def coord_to_bits(self, value: reference.Coord) -> Bits:
        assert value[0] in (0, 2)
        if self.k == 1:
            return (value[4], value[1] & 1, value[2] & 1, value[0] >> 1,
                    value[3], value[1] >> 1, value[2] >> 1)
        if self.k == 2:
            return (value[4], value[1] & 1, value[2], value[5],
                    value[3], value[0] >> 1, value[1] >> 1)
        return (value[4], value[1], value[2], value[5],
                value[3], value[6], value[0] >> 1)


def boolean_ring(k: int) -> BooleanRing:
    if k == 1:
        # x,y | y2,2 | y3,2y | 2y2
        return BooleanRing(
            1, ("x", "y", "y2", "two", "y3", "two_y", "two_y2"),
            {
                2: ((1, 1),),
                3: ((0, 1), (1, 0)),
                4: ((1, 2), (2, 1)),
                5: ((0, 2), (2, 0), (3, 1), (1, 3)),
                6: ((3, 2), (2, 3), (5, 1), (1, 5), (4, 0), (0, 4)),
            },
            ((5, 1), (6, 2)), ((5, 1), (6, 2)), 3,
        )
    if k == 2:
        # x,y | y2,xy | y3,2 | 2y
        return BooleanRing(
            2, ("x", "y", "y2", "xy", "y3", "two", "two_y"),
            {
                2: ((1, 1),),
                3: ((0, 1), (1, 0)),
                4: ((1, 2), (2, 1)),
                5: ((0, 2), (2, 0), (1, 3), (3, 1)),
                6: ((5, 1), (1, 5), (4, 0), (0, 4), (2, 3), (3, 2)),
            },
            ((6, 1),), ((6, 1),), 5,
        )
    if k == 3:
        # x,y | y2,xy | y3,xy2 | 2
        return BooleanRing(
            3, ("x", "y", "y2", "xy", "y3", "xy2", "two"),
            {
                2: ((1, 1),),
                3: ((0, 1), (1, 0)),
                4: ((1, 2), (2, 1)),
                5: ((0, 2), (2, 0), (1, 3), (3, 1)),
                6: ((0, 4), (4, 0), (1, 5), (5, 1), (2, 3), (3, 2)),
            },
            (), (), 6,
        )
    raise ValueError(k)


def gate_ring(ring: BooleanRing) -> None:
    spec = reference.ring_spec(ring.k)
    all_bits = [tuple((n >> i) & 1 for i in range(7)) for n in range(128)]
    for left in all_bits:
        lc = ring.bits_to_coord(left)
        assert ring.coord_to_bits(lc) == left
        for coefficient in range(-4, 5):
            wanted = tuple((coefficient * a) % (1 << width)
                           for a, width in zip(lc, spec.widths))
            assert ring.bits_to_coord(ring.bits_scale(coefficient, left)) == wanted
        for right in all_bits:
            rc = ring.bits_to_coord(right)
            assert ring.bits_to_coord(ring.bits_add(left, right)) == reference.concrete_add(
                spec, lc, rc)
            assert ring.bits_to_coord(ring.bits_mul(left, right)) == reference.concrete_mul(
                spec, lc, rc)
    print(f"R{ring.k} Boolean ring gate PASS (128^2 products/sums)", flush=True)


def symbolic_poly(ring: BooleanRing, poly: universal.Poly,
                  values: Sequence[Elt], cache: Dict[Tuple[int, ...], Elt]) -> Elt:
    def monomial(mon: Tuple[int, ...]) -> Elt:
        if mon not in cache:
            cache[mon] = (values[mon[0]] if len(mon) == 1 else
                          ring.mul(monomial(mon[:-1]), values[mon[-1]]))
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
            cache[mon] = (values[mon[0]] if len(mon) == 1 else
                          ring.bits_mul(monomial(mon[:-1]), values[mon[-1]]))
        return cache[mon]

    out = ZERO_BITS
    for mon, coefficient in poly.items():
        term = (ring.bits_scale(coefficient, monomial(mon)) if mon else
                ring.bits_even_integer(coefficient))
        out = ring.bits_add(out, term)
    return out


def cross_gate(ring: BooleanRing, chart: universal.Chart, trials: int) -> None:
    if not trials:
        return
    rng = random.Random(20260711 + ring.k)
    spec = reference.ring_spec(ring.k)
    polys = chart.equations_z + chart.targets_z
    for trial in range(trials):
        bits = [tuple(rng.randrange(2) for _ in range(7)) for _ in range(45)]
        coords = [ring.bits_to_coord(value) for value in bits]
        for index, poly in enumerate(polys):
            got = ring.bits_to_coord(concrete_poly_bits(ring, poly, bits))
            wanted = reference.concrete_poly(spec, poly, coords)
            assert got == wanted, (trial, index, got, wanted)
    print(f"R{ring.k} polynomial cross-gate PASS "
          f"({trials * len(polys)} evaluations)", flush=True)


def search(args: argparse.Namespace) -> str:
    ring = boolean_ring(args.k)
    gate_ring(ring)
    universal.MAX_DEGREE = 4
    chart = universal.build_chart(0)
    assert len(chart.equations_z) == 189
    assert all(poly.get((), 0) % 2 == 0
               for poly in chart.equations_z + chart.targets_z)
    cross_gate(ring, chart, args.audit_trials)

    names = reference.parameter_names()
    values = [tuple(z3.Bool(f"{name}_{label}") for label in ring.labels)
              for name in names]
    cache: Dict[Tuple[int, ...], Elt] = {}
    started = time.time()
    equations = [symbolic_poly(ring, poly, values, cache)
                 for poly in chart.equations_z]
    target = symbolic_poly(ring, chart.targets_z[args.target], values, cache)
    build_seconds = time.time() - started

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
    solver.add(*constraints)
    print(f"built in {build_seconds:.3f}s: bits=315 constraints={len(constraints)} "
          f"monomials={len(cache)}", flush=True)
    started = time.time()
    verdict = solver.check()
    solve_seconds = time.time() - started
    print(f"R{args.k} target={args.target} condition={args.condition} "
          f"verdict={verdict} seconds={solve_seconds:.3f}", flush=True)
    if verdict != z3.sat:
        if verdict == z3.unknown:
            print("reason_unknown=" + solver.reason_unknown(), flush=True)
        return str(verdict)

    model = solver.model()
    bits = [tuple(1 if z3.is_true(model.eval(bit, model_completion=True)) else 0
                  for bit in value) for value in values]
    coords = [ring.bits_to_coord(value) for value in bits]
    equation_bits = [concrete_poly_bits(ring, poly, bits) for poly in chart.equations_z]
    target_bits = [concrete_poly_bits(ring, poly, bits) for poly in chart.targets_z]
    assert all(value == ZERO_BITS for value in equation_bits)
    if args.condition == "exact-socle":
        assert target_bits[args.target] == (0, 0, 0, 0, 0, 0, 1)
    else:
        assert any(target_bits[args.target])

    spec = reference.ring_spec(args.k)
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
    assert target_coords[args.target] == ring.bits_to_coord(target_bits[args.target])

    witness = {
        "ring": spec.name, "basis": spec.basis, "widths": spec.widths,
        "target_index": args.target, "condition": args.condition,
        "parameters": dict(zip(names, coords)),
        "parameter_filtration_bits": dict(zip(names, bits)),
        "targets": target_coords, "build_seconds": build_seconds,
        "solve_seconds": solve_seconds, "z3_version": z3.get_version_string(),
        "verification": "PASS: Boolean and reference concrete evaluators",
    }
    print("SAT witness verified; targets=" + repr(target_coords), flush=True)
    if args.output:
        args.output.write_text(json.dumps(witness, indent=2) + "\n")
        print(f"wrote {args.output}", flush=True)
    return "sat"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, choices=(1, 2, 3), required=True)
    parser.add_argument("--target", type=int, choices=range(9), default=2)
    parser.add_argument("--condition", choices=("exact-socle", "nonzero"),
                        default="nonzero")
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--memory-mb", type=int, default=2048)
    parser.add_argument("--audit-trials", type=int, default=0)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    verdict = search(args)
    if verdict == "unknown":
        raise SystemExit(2)


if __name__ == "__main__":
    main()
