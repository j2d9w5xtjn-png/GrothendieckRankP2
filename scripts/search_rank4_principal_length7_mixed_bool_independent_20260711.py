#!/usr/bin/env python3
r"""Independent exact Boolean search on mixed principal length-seven rings.

The bounded tranche implemented here consists of the six pure Eisenstein
presentations

    R_e = Z[t]/(t^7, 2-t^e),                 1 <= e <= 6.

Every element has a unique binary normal form sum(a_i*t^i, 0 <= i < 7).
The symbolic operations below are Boolean ripple-carry circuits.  They are
not coefficientwise XOR: the coordinates in each congruence class modulo e
form the binary digits of one additive cyclic summand.  Multiplication uses
the same decomposition and the carry t^e=2.

Before a solver query, all 128^2 symbolic-circuit sums and products (and all
small integer scalings) are compared with a separate ``CarryRing`` evaluator
which reduces integral coefficient lists by the presentation relation.  The
integral universal rank-four chart is built once with degree cap four and
once with cap eight; byte-for-byte equality proves that no terms above
ordinary parameter degree four were truncated.  A SAT model is accepted only
after all 189 equations and all nine [4]^# coordinates are re-evaluated by
both concrete evaluators.

This file deliberately does not modify or call the earlier equal-
characteristic F2[t]/t^7 search.  Nonzero tails are left for a later tranche;
``--tail`` is parsed and recorded, but this optimized Boolean circuit rejects
anything other than the all-zero tail.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import random
import resource
import sys
import time
from pathlib import Path
from typing import Dict, Iterable, Sequence, Tuple


ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, "/tmp/rank4_z3")

import z3

import scripts.audit_universal_rank4_quadratic as universal


N = 7
ALL = tuple(range(1 << N))
Bits = Tuple[int, ...]
Elt = Tuple[z3.BoolRef, ...]
FALSE = z3.BoolVal(False)
ZERO_BITS: Bits = (0,) * N
ZERO: Elt = (FALSE,) * N


def digits(value: int) -> Bits:
    return tuple((value >> i) & 1 for i in range(N))


def encode(value: Sequence[int]) -> int:
    return sum((int(bit) & 1) << i for i, bit in enumerate(value[:N]))


class CarryRing:
    """Independent integral coefficient reducer for 2=t^e+tail."""

    def __init__(self, e: int, tail: Sequence[int]):
        if not (1 <= e <= 6):
            raise ValueError(e)
        if len(tail) != 6 - e or any(bit not in (0, 1) for bit in tail):
            raise ValueError((e, tail))
        self.e = e
        self.tail = tuple(tail)
        self.support = (e,) + tuple(
            e + 1 + i for i, bit in enumerate(self.tail) if bit
        )
        self.label = f"e{e}_" + ("".join(map(str, self.tail)) or "-")

    def reduce(self, coefficients: Sequence[int]) -> int:
        work = list(coefficients[:N]) + [0] * max(0, N - len(coefficients))
        for i in range(N):
            quotient, work[i] = divmod(work[i], 2)
            if quotient:
                for shift in self.support:
                    if i + shift < N:
                        work[i + shift] += quotient
        return encode(work)

    def add(self, left: int, right: int) -> int:
        return self.reduce([a + b for a, b in zip(digits(left), digits(right))])

    def mul(self, left: int, right: int) -> int:
        a, b = digits(left), digits(right)
        coefficients = [0] * N
        for i in range(N):
            for j in range(N - i):
                coefficients[i + j] += a[i] * b[j]
        return self.reduce(coefficients)

    def scale(self, coefficient: int, value: int) -> int:
        return self.reduce([coefficient * bit for bit in digits(value)])

    def integer(self, coefficient: int) -> int:
        return self.reduce([coefficient])

    def power(self, value: int, exponent: int) -> int:
        out = 1
        for _ in range(exponent):
            out = self.mul(out, value)
        return out


def bxor(*arguments: z3.BoolRef) -> z3.BoolRef:
    parity = False
    kept = []
    for argument in arguments:
        if z3.is_true(argument):
            parity = not parity
        elif not z3.is_false(argument):
            kept.append(argument)
    if not kept:
        return z3.BoolVal(parity)
    out = kept[0]
    for argument in kept[1:]:
        out = z3.Xor(out, argument)
    return z3.Not(out) if parity else out


def band(left: z3.BoolRef, right: z3.BoolRef) -> z3.BoolRef:
    if z3.is_false(left) or z3.is_false(right):
        return FALSE
    if z3.is_true(left):
        return right
    if z3.is_true(right):
        return left
    return z3.And(left, right)


def ixor(*arguments: int) -> int:
    out = 0
    for argument in arguments:
        out ^= argument
    return out


def iand(left: int, right: int) -> int:
    return left & right


def word_add(
    left: Sequence, right: Sequence, xor, conjunction, zero
) -> Tuple:
    """Little-endian binary addition modulo 2^len(left)."""
    if len(left) != len(right):
        raise ValueError((len(left), len(right)))
    carry = zero
    out = []
    for a, b in zip(left, right):
        pair = xor(a, b)
        out.append(xor(pair, carry))
        # The two summands are disjoint, so XOR is exactly OR here.
        carry = xor(conjunction(a, b), conjunction(carry, pair))
    return tuple(out)


def word_mul(
    left: Sequence, right: Sequence, width: int, xor, conjunction, zero
) -> Tuple:
    """Little-endian schoolbook product modulo 2^width."""
    out = (zero,) * width
    for i, a in enumerate(left):
        if i >= width:
            break
        row = [zero] * width
        for j, b in enumerate(right):
            if i + j < width:
                row[i + j] = conjunction(a, b)
        out = word_add(out, row, xor, conjunction, zero)
    return out


def word_scale(
    coefficient: int, value: Sequence, xor, conjunction, zero
) -> Tuple:
    width = len(value)
    residue = coefficient % (1 << width)
    if residue == 0:
        return (zero,) * width
    if residue == 1:
        return tuple(value)
    out = (zero,) * width
    for shift in range(width):
        if (residue >> shift) & 1:
            row = (zero,) * shift + tuple(value[: width - shift])
            out = word_add(out, row, xor, conjunction, zero)
    return out


class BooleanPureChainRing:
    """Boolean circuit for the tail-zero relation 2=t^e, t^7=0."""

    def __init__(self, e: int):
        if not (1 <= e <= 6):
            raise ValueError(e)
        self.e = e
        self.chains = tuple(tuple(range(r, N, e)) for r in range(e))
        assert sorted(i for chain in self.chains for i in chain) == list(range(N))

    def _add(self, left: Sequence, right: Sequence, symbolic: bool) -> Tuple:
        xor, conjunction, zero = ((bxor, band, FALSE) if symbolic
                                  else (ixor, iand, 0))
        out = [zero] * N
        for chain in self.chains:
            word = word_add(
                [left[i] for i in chain], [right[i] for i in chain],
                xor, conjunction, zero,
            )
            for index, bit in zip(chain, word):
                out[index] = bit
        return tuple(out)

    def add(self, left: Elt, right: Elt) -> Elt:
        return self._add(left, right, True)

    def bits_add(self, left: Bits, right: Bits) -> Bits:
        return self._add(left, right, False)

    def _mul(self, left: Sequence, right: Sequence, symbolic: bool) -> Tuple:
        xor, conjunction, zero = ((bxor, band, FALSE) if symbolic
                                  else (ixor, iand, 0))
        words_left = tuple(tuple(left[i] for i in chain) for chain in self.chains)
        words_right = tuple(tuple(right[i] for i in chain) for chain in self.chains)
        accumulators = [(zero,) * len(chain) for chain in self.chains]
        for residue_left in range(self.e):
            for residue_right in range(self.e):
                exponent = residue_left + residue_right
                target = exponent % self.e
                shift = exponent // self.e
                width = len(self.chains[target])
                if shift >= width:
                    continue
                product = word_mul(
                    words_left[residue_left], words_right[residue_right],
                    width - shift, xor, conjunction, zero,
                )
                row = (zero,) * shift + product
                accumulators[target] = word_add(
                    accumulators[target], row, xor, conjunction, zero
                )
        out = [zero] * N
        for chain, word in zip(self.chains, accumulators):
            for index, bit in zip(chain, word):
                out[index] = bit
        return tuple(out)

    def mul(self, left: Elt, right: Elt) -> Elt:
        return self._mul(left, right, True)

    def bits_mul(self, left: Bits, right: Bits) -> Bits:
        return self._mul(left, right, False)

    def _scale(self, coefficient: int, value: Sequence, symbolic: bool) -> Tuple:
        xor, conjunction, zero = ((bxor, band, FALSE) if symbolic
                                  else (ixor, iand, 0))
        out = [zero] * N
        for chain in self.chains:
            word = word_scale(
                coefficient, [value[i] for i in chain],
                xor, conjunction, zero,
            )
            for index, bit in zip(chain, word):
                out[index] = bit
        return tuple(out)

    def scale(self, coefficient: int, value: Elt) -> Elt:
        return self._scale(coefficient, value, True)

    def bits_scale(self, coefficient: int, value: Bits) -> Bits:
        return self._scale(coefficient, value, False)

    def integer(self, coefficient: int) -> Elt:
        out = [FALSE] * N
        chain = self.chains[0]
        residue = coefficient % (1 << len(chain))
        for place, index in enumerate(chain):
            out[index] = z3.BoolVal(bool((residue >> place) & 1))
        return tuple(out)

    def bits_integer(self, coefficient: int) -> Bits:
        out = [0] * N
        chain = self.chains[0]
        residue = coefficient % (1 << len(chain))
        for place, index in enumerate(chain):
            out[index] = (residue >> place) & 1
        return tuple(out)


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


def canonical_polynomials(chart: universal.Chart) -> bytes:
    payload = []
    for family in (chart.equations_z, chart.targets_z):
        payload.append([
            [[list(monomial), coefficient]
             for monomial, coefficient in sorted(poly.items())]
            for poly in family
        ])
    return json.dumps(payload, separators=(",", ":")).encode()


def build_full_chart() -> Tuple[universal.Chart, str, dict]:
    universal.MAX_DEGREE = 4
    chart4 = universal.build_chart(0)
    encoded4 = canonical_polynomials(chart4)
    universal.MAX_DEGREE = 8
    chart8 = universal.build_chart(0)
    encoded8 = canonical_polynomials(chart8)
    assert encoded4 == encoded8
    assert len(chart8.equations_z) == 189 and len(chart8.targets_z) == 9
    polynomials = chart8.equations_z + chart8.targets_z
    degrees = [max((len(monomial) for monomial in poly), default=0)
               for poly in polynomials]
    assert max(degrees) <= 4
    coefficients = [coefficient for poly in polynomials for coefficient in poly.values()]
    metadata = {
        "equations": len(chart8.equations_z),
        "targets": len(chart8.targets_z),
        "ordinary_degree_max": max(degrees),
        "terms": sum(len(poly) for poly in polynomials),
        "coefficient_min": min(coefficients),
        "coefficient_max": max(coefficients),
        "degree4_equals_degree8": True,
    }
    return chart8, hashlib.sha256(encoded8).hexdigest(), metadata


def gate_ring(circuit: BooleanPureChainRing, concrete: CarryRing,
              coefficient_min: int, coefficient_max: int) -> None:
    assert not any(concrete.tail)
    t = 1 << 1
    assert concrete.power(t, 6) != 0 and concrete.power(t, 7) == 0
    assert concrete.integer(2) == concrete.power(t, concrete.e)
    expected_characteristic = 1 << ((N + concrete.e - 1) // concrete.e)
    assert concrete.integer(expected_characteristic) == 0
    assert concrete.integer(expected_characteristic // 2) != 0

    for value in ALL:
        value_bits = digits(value)
        value_symbolic = tuple(z3.BoolVal(bool(bit)) for bit in value_bits)
        for coefficient in range(coefficient_min, coefficient_max + 1):
            got = encode(circuit.bits_scale(coefficient, value_bits))
            assert got == concrete.scale(coefficient, value), (
                "scale", concrete.label, coefficient, value, got,
                concrete.scale(coefficient, value),
            )
            got_symbolic = encode(tuple(
                1 if z3.is_true(bit) else 0
                for bit in circuit.scale(coefficient, value_symbolic)
            ))
            assert got_symbolic == concrete.scale(coefficient, value)
        assert encode(circuit.bits_integer(value - 64)) == concrete.integer(value - 64)
        for other in ALL:
            other_bits = digits(other)
            other_symbolic = tuple(z3.BoolVal(bool(bit)) for bit in other_bits)
            got_add = encode(circuit.bits_add(value_bits, other_bits))
            got_mul = encode(circuit.bits_mul(value_bits, other_bits))
            assert got_add == concrete.add(value, other), (
                "add", concrete.label, value, other, got_add,
                concrete.add(value, other),
            )
            assert got_mul == concrete.mul(value, other), (
                "mul", concrete.label, value, other, got_mul,
                concrete.mul(value, other),
            )
            got_add_symbolic = encode(tuple(
                1 if z3.is_true(bit) else 0
                for bit in circuit.add(value_symbolic, other_symbolic)
            ))
            got_mul_symbolic = encode(tuple(
                1 if z3.is_true(bit) else 0
                for bit in circuit.mul(value_symbolic, other_symbolic)
            ))
            assert got_add_symbolic == concrete.add(value, other)
            assert got_mul_symbolic == concrete.mul(value, other)
    print(
        f"{concrete.label}: Boolean-vs-CarryRing gate PASS "
        f"(128^2 sums/products; 128 scalings for each c in "
        f"[{coefficient_min},{coefficient_max}])",
        flush=True,
    )


def symbolic_poly(
    ring: BooleanPureChainRing,
    poly: universal.Poly,
    values: Sequence[Elt],
    cache: Dict[Tuple[int, ...], Elt],
) -> Elt:
    def monomial(powers: Tuple[int, ...]) -> Elt:
        if powers not in cache:
            cache[powers] = (
                values[powers[0]] if len(powers) == 1
                else ring.mul(monomial(powers[:-1]), values[powers[-1]])
            )
        return cache[powers]

    out = ZERO
    for powers, coefficient in poly.items():
        term = ring.scale(coefficient, monomial(powers)) if powers else ring.integer(coefficient)
        out = ring.add(out, term)
    return out


def bits_polynomials(
    ring: BooleanPureChainRing,
    polynomials: Sequence[universal.Poly],
    values: Sequence[Bits],
) -> Tuple[Bits, ...]:
    cache: Dict[Tuple[int, ...], Bits] = {}

    def monomial(powers: Tuple[int, ...]) -> Bits:
        if powers not in cache:
            cache[powers] = (
                values[powers[0]] if len(powers) == 1
                else ring.bits_mul(monomial(powers[:-1]), values[powers[-1]])
            )
        return cache[powers]

    out = []
    for poly in polynomials:
        total = ZERO_BITS
        for powers, coefficient in poly.items():
            term = (ring.bits_scale(coefficient, monomial(powers))
                    if powers else ring.bits_integer(coefficient))
            total = ring.bits_add(total, term)
        out.append(total)
    return tuple(out)


def carry_polynomials(
    ring: CarryRing,
    polynomials: Sequence[universal.Poly],
    values: Sequence[int],
) -> Tuple[int, ...]:
    cache: Dict[Tuple[int, ...], int] = {}

    def monomial(powers: Tuple[int, ...]) -> int:
        if powers not in cache:
            cache[powers] = (
                values[powers[0]] if len(powers) == 1
                else ring.mul(monomial(powers[:-1]), values[powers[-1]])
            )
        return cache[powers]

    out = []
    for poly in polynomials:
        total = 0
        for powers, coefficient in poly.items():
            term = (ring.scale(coefficient, monomial(powers))
                    if powers else ring.integer(coefficient))
            total = ring.add(total, term)
        out.append(total)
    return tuple(out)


def polynomial_gate(
    circuit: BooleanPureChainRing,
    concrete: CarryRing,
    chart: universal.Chart,
    trials: int,
) -> None:
    polynomials = chart.equations_z + chart.targets_z
    rng = random.Random(2026071100 + concrete.e)
    for trial in range(trials):
        values = [tuple([0] + [rng.randrange(2) for _ in range(6)])
                  for _ in range(45)]
        bit_values = bits_polynomials(circuit, polynomials, values)
        concrete_values = carry_polynomials(
            concrete, polynomials, [encode(value) for value in values]
        )
        assert tuple(map(encode, bit_values)) == concrete_values, trial
    print(
        f"{concrete.label}: universal-polynomial cross-gate PASS "
        f"({trials} complete evaluations of 189 equations + 9 targets)",
        flush=True,
    )


def write_result(path: Path | None, payload: dict) -> None:
    if path is None:
        return
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"wrote {path}", flush=True)


def search(args: argparse.Namespace) -> str:
    expected_tail_length = 6 - args.e
    tail_text = args.tail if args.tail is not None else "0" * expected_tail_length
    if len(tail_text) != expected_tail_length or any(c not in "01" for c in tail_text):
        raise SystemExit(
            f"--tail must have exactly {expected_tail_length} binary digits for e={args.e}"
        )
    tail = tuple(map(int, tail_text))
    if any(tail):
        raise SystemExit(
            "this independent optimized tranche currently supports only the all-zero tail"
        )

    run_started = time.monotonic()
    chart, chart_sha256, chart_metadata = build_full_chart()
    coefficients = [coefficient
                    for poly in chart.equations_z + chart.targets_z
                    for coefficient in poly.values()]
    circuit = BooleanPureChainRing(args.e)
    concrete = CarryRing(args.e, tail)
    gate_ring(circuit, concrete, min(coefficients), max(coefficients))
    polynomial_gate(circuit, concrete, chart, args.audit_trials)

    names = parameter_names()
    values = [tuple([FALSE] + [z3.Bool(f"{name}_t{power}")
                              for power in range(1, N)])
              for name in names]
    cache: Dict[Tuple[int, ...], Elt] = {}
    build_started = time.monotonic()
    equations = [symbolic_poly(circuit, poly, values, cache)
                 for poly in chart.equations_z]
    target = symbolic_poly(circuit, chart.targets_z[args.target], values, cache)
    build_seconds = time.monotonic() - build_started

    constraints = [z3.Not(bit) for equation in equations for bit in equation
                   if not z3.is_false(bit)]
    if args.condition == "exact-socle":
        constraints.extend(bit if index == N - 1 else z3.Not(bit)
                           for index, bit in enumerate(target))
    else:
        constraints.append(z3.Or(*target))
    solver = z3.Solver()
    solver.set(timeout=args.timeout * 1000)
    solver.set(max_memory=args.memory_mb)
    solver.add(*constraints)
    print(
        f"chart=a2a2 e={args.e} tail={tail_text or '-'} target={args.target} "
        f"condition={args.condition} "
        f"parameter_bits=270 constraints={len(constraints)} "
        f"monomials={len(cache)} build_seconds={build_seconds:.3f}",
        flush=True,
    )

    solve_started = time.monotonic()
    verdict_object = solver.check()
    solve_seconds = time.monotonic() - solve_started
    verdict = str(verdict_object)
    reason = solver.reason_unknown() if verdict_object == z3.unknown else None
    print(
        f"chart=a2a2 e={args.e} target={args.target} condition={args.condition} "
        f"verdict={verdict} "
        f"solve_seconds={solve_seconds:.3f}"
        + (f" reason_unknown={reason}" if reason else ""),
        flush=True,
    )

    result = {
        "date": "2026-07-11",
        "ring": f"Z[t]/(t^7,2-t^{args.e})",
        "e": args.e,
        "tail": tail_text,
        "chart": "alpha2^2",
        "target": args.target,
        "target_meaning": f"coefficient e{args.target % 3 + 1} of [4]^#(e{args.target // 3 + 1})",
        "condition": args.condition,
        "verdict": verdict,
        "reason_unknown": reason,
        "timeout_seconds": args.timeout,
        "memory_mb": args.memory_mb,
        "processes": 1,
        "parameter_bits": 270,
        "constraints": len(constraints),
        "monomial_cache_entries": len(cache),
        "build_seconds": build_seconds,
        "solve_seconds": solve_seconds,
        "elapsed_seconds": time.monotonic() - run_started,
        "z3": z3.get_version_string(),
        "chart_sha256": chart_sha256,
        "chart_metadata": chart_metadata,
        "ring_gate": "PASS: concrete-bit and symbolic-Boolean circuits; 128^2 sums/products and coefficient scalings vs CarryRing",
        "polynomial_gate": f"PASS: {args.audit_trials} full random evaluations vs CarryRing",
        "classification": (
            "verified SAT" if verdict_object == z3.sat else
            "mathematically negative for this exact query" if verdict_object == z3.unsat else
            "inconclusive"
        ),
    }

    if verdict_object == z3.sat:
        model = solver.model()
        parameter_bits = [tuple(
            1 if z3.is_true(model.eval(bit, model_completion=True)) else 0
            for bit in value
        ) for value in values]
        all_polynomials = chart.equations_z + chart.targets_z
        bit_evaluations = bits_polynomials(circuit, all_polynomials, parameter_bits)
        carry_evaluations = carry_polynomials(
            concrete, all_polynomials, list(map(encode, parameter_bits))
        )
        assert tuple(map(encode, bit_evaluations)) == carry_evaluations
        equation_values = carry_evaluations[:189]
        target_values = carry_evaluations[189:]
        assert all(value == 0 for value in equation_values)
        if args.condition == "exact-socle":
            assert target_values[args.target] == (1 << (N - 1))
        else:
            assert target_values[args.target] != 0
        result["verification"] = (
            "PASS: all 189 equations and 9 targets agree in Boolean and CarryRing evaluators"
        )
        result["parameters_binary_t0_through_t6"] = dict(zip(names, parameter_bits))
        result["targets_binary_encoded"] = list(target_values)
        result["requested_target_bits_t0_through_t6"] = list(
            bit_evaluations[189 + args.target]
        )
        print(
            "SAT witness independently verified; targets=" + repr(target_values),
            flush=True,
        )

    peak_rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    # Darwin reports bytes; Linux reports KiB.
    result["peak_rss_mib"] = peak_rss / (1024 * 1024) if sys.platform == "darwin" else peak_rss / 1024

    write_result(args.output, result)
    print("RESULT_JSON=" + json.dumps(result, sort_keys=True), flush=True)
    if verdict_object == z3.unknown:
        return "unknown"
    return verdict


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--e", type=int, choices=range(1, 7), required=True)
    parser.add_argument(
        "--tail",
        help="binary c_(e+1)...c_6; this tranche requires every digit to be zero",
    )
    parser.add_argument("--target", type=int, choices=range(9), required=True)
    parser.add_argument(
        "--condition", choices=("nonzero", "exact-socle"), default="nonzero",
        help="exact-socle requires the selected target to equal t^6",
    )
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--memory-mb", type=int, default=2048)
    parser.add_argument("--audit-trials", type=int, default=1)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    verdict = search(args)
    if verdict == "unknown":
        raise SystemExit(2)


if __name__ == "__main__":
    main()
