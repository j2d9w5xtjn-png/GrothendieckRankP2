#!/usr/bin/env python3
"""Exact universal-chart search over F2[t]/(t^7).

The 45 deformation parameters are elements of (t), encoded by their six
coefficients of t,...,t^6.  Addition is XOR and multiplication is truncated
Boolean convolution.  The ring circuit is exhaustively checked against the
independent ``ConcreteRing`` used by the direct monogenic t4_11 probe.

Branches 0 and 1 are respectively the alpha2^2 and W2F special fibres.  The
same implementation also permits the t4 branches 2 and 3 for cross-checking.
Every SAT result is concretely re-evaluated before being written.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
import time
from pathlib import Path
from typing import Dict, Sequence, Tuple


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, "/tmp/rank4_z3")

import z3

import scripts.audit_universal_rank4_quadratic as universal
import scripts.probe_principal_length7_t4_11_direct_20260711 as principal
import scripts.search_rank4_length8_ci_20260711 as names_source


Elt = Tuple[z3.BoolRef, ...]
Bits = Tuple[int, ...]
FALSE = z3.BoolVal(False)
ZERO: Elt = (FALSE,) * 6
ZERO_BITS: Bits = (0,) * 6


def bxor(*args):
    kept = [arg for arg in args if not z3.is_false(arg)]
    if not kept:
        return FALSE
    out = kept[0]
    for arg in kept[1:]:
        out = z3.Xor(out, arg)
    return out


def band(left, right):
    if z3.is_false(left) or z3.is_false(right):
        return FALSE
    return z3.And(left, right)


def add(left: Elt, right: Elt) -> Elt:
    return tuple(bxor(a, b) for a, b in zip(left, right))


def mul(left: Elt, right: Elt) -> Elt:
    # Coordinate i is t^(i+1); a+b+2 is the product exponent.
    out = [FALSE] * 6
    for a in range(6):
        for b in range(6):
            target = a + b + 1
            if target < 6:
                out[target] = bxor(out[target], band(left[a], right[b]))
    return tuple(out)


def bits_add(left: Bits, right: Bits) -> Bits:
    return tuple(a ^ b for a, b in zip(left, right))


def bits_mul(left: Bits, right: Bits) -> Bits:
    out = [0] * 6
    for a in range(6):
        for b in range(6):
            target = a + b + 1
            if target < 6:
                out[target] ^= left[a] & right[b]
    return tuple(out)


def gate_ring() -> None:
    spec = principal.principal_case()
    ref = principal.direct.ConcreteRing(spec)
    elements = [tuple((n >> i) & 1 for i in range(6)) for n in range(64)]
    for left in elements:
        lc = (0,) + left
        for right in elements:
            rc = (0,) + right
            assert (0,) + bits_add(left, right) == ref.add(lc, rc)
            assert (0,) + bits_mul(left, right) == ref.mul(lc, rc)
    print("F2[t]/t7 Boolean ring gate PASS (64^2 maximal-ideal pairs)", flush=True)


def symbolic_poly(poly: universal.Poly, values: Sequence[Elt],
                  cache: Dict[Tuple[int, ...], Elt]) -> Elt:
    def monomial(mon: Tuple[int, ...]) -> Elt:
        if mon not in cache:
            cache[mon] = (values[mon[0]] if len(mon) == 1 else
                          mul(monomial(mon[:-1]), values[mon[-1]]))
        return cache[mon]

    out = ZERO
    for mon, coefficient in poly.items():
        # Constants on these pinned charts are even and hence zero in F2.
        if mon and coefficient & 1:
            out = add(out, monomial(mon))
        elif not mon:
            assert coefficient % 2 == 0
    return out


def concrete_poly(poly: universal.Poly, values: Sequence[Bits]) -> Bits:
    cache: Dict[Tuple[int, ...], Bits] = {}

    def monomial(mon: Tuple[int, ...]) -> Bits:
        if mon not in cache:
            cache[mon] = (values[mon[0]] if len(mon) == 1 else
                          bits_mul(monomial(mon[:-1]), values[mon[-1]]))
        return cache[mon]

    out = ZERO_BITS
    for mon, coefficient in poly.items():
        if mon and coefficient & 1:
            out = bits_add(out, monomial(mon))
        elif not mon:
            assert coefficient % 2 == 0
    return out


def reference_poly(poly: universal.Poly, values: Sequence[Bits]) -> Tuple[int, ...]:
    """Independent evaluation using the direct probe's seven-coordinate ring."""
    ref = principal.direct.ConcreteRing(principal.principal_case())
    zero = ref.zero
    one = ref.one
    coords = [(0,) + value for value in values]
    out = zero
    for mon, coefficient in poly.items():
        if not (coefficient & 1):
            continue
        term = one
        for variable in mon:
            term = ref.mul(term, coords[variable])
        out = ref.add(out, term)
    return out


def polynomial_gate(chart: universal.Chart, trials: int) -> None:
    if not trials:
        return
    rng = random.Random(20260711)
    polys = chart.equations_z + chart.targets_z
    for trial in range(trials):
        values = [tuple(rng.randrange(2) for _ in range(6)) for _ in range(45)]
        for index, poly in enumerate(polys):
            got = (0,) + concrete_poly(poly, values)
            wanted = reference_poly(poly, values)
            assert got == wanted, (trial, index, got, wanted)
    print(f"polynomial cross-gate PASS ({trials * len(polys)} evaluations)", flush=True)


def search(args: argparse.Namespace) -> str:
    gate_ring()
    universal.MAX_DEGREE = 4
    chart = universal.build_chart(args.branch)
    assert len(chart.equations_z) == 189
    assert all(poly.get((), 0) % 2 == 0
               for poly in chart.equations_z + chart.targets_z)
    polynomial_gate(chart, args.audit_trials)

    names = names_source.parameter_names()
    values = [tuple(z3.Bool(f"{name}_t{power}") for power in range(1, 7))
              for name in names]
    cache: Dict[Tuple[int, ...], Elt] = {}
    started = time.time()
    equations = [symbolic_poly(poly, values, cache) for poly in chart.equations_z]
    target = symbolic_poly(chart.targets_z[args.target], values, cache)
    build_seconds = time.time() - started
    constraints = [z3.Not(bit) for equation in equations for bit in equation
                   if not z3.is_false(bit)]
    constraints.append(z3.Or(*target))

    solver = z3.Solver()
    solver.set(timeout=args.timeout * 1000)
    solver.set(max_memory=args.memory_mb)
    solver.add(*constraints)
    print(f"branch={chart.name} built={build_seconds:.3f}s bits=270 "
          f"constraints={len(constraints)} monomials={len(cache)}", flush=True)
    started = time.time()
    verdict = solver.check()
    solve_seconds = time.time() - started
    print(f"branch={chart.name} target={args.target} nonzero verdict={verdict} "
          f"seconds={solve_seconds:.3f}", flush=True)
    if verdict != z3.sat:
        if verdict == z3.unknown:
            print("reason_unknown=" + solver.reason_unknown(), flush=True)
        return str(verdict)

    model = solver.model()
    bits = [tuple(1 if z3.is_true(model.eval(bit, model_completion=True)) else 0
                  for bit in value) for value in values]
    equation_values = [concrete_poly(poly, bits) for poly in chart.equations_z]
    target_values = [concrete_poly(poly, bits) for poly in chart.targets_z]
    assert all(value == ZERO_BITS for value in equation_values)
    assert any(target_values[args.target])
    assert all(reference_poly(poly, bits) == (0,) * 7 for poly in chart.equations_z)
    assert reference_poly(chart.targets_z[args.target], bits) != (0,) * 7

    witness = {
        "ring": "F2[t]/(t^7)", "branch": chart.name,
        "target_index": args.target,
        "parameters_t_through_t6": dict(zip(names, bits)),
        "targets_t_through_t6": target_values,
        "build_seconds": build_seconds, "solve_seconds": solve_seconds,
        "z3_version": z3.get_version_string(),
        "verification": "PASS: Boolean and independent ConcreteRing evaluators",
    }
    print("SAT witness verified; targets=" + repr(target_values), flush=True)
    if args.output:
        args.output.write_text(json.dumps(witness, indent=2) + "\n")
        print(f"wrote {args.output}", flush=True)
    return "sat"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=range(4), required=True)
    parser.add_argument("--target", type=int, choices=range(9), required=True)
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
