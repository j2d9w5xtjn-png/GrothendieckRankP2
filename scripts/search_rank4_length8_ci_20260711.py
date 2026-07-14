#!/usr/bin/env python3
"""Search the universal alpha_2^2 rank-four chart on three length-eight CIs.

The base rings are

    R_k = Z[x,y]/(x^2, y^4, x*y^k - 2),   k=1,2,3.

Each has residue field F_2, length eight, Hilbert function (1,2,2,2,1),
and characteristic four.  The script evaluates the exact integral universal
bialgebra equations from ``audit_universal_rank4_quadratic.py`` in R_k and
asks whether one of the nine coordinates of [4]^# is nonzero.

The imported chart builder is deliberately switched from cubic truncation to
degree four before construction.  The bialgebra equations have degree at most
three, while the exact fourth-power coordinates have degree at most four.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Mapping, Sequence, Tuple

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, "/tmp/rank4_z3")

import z3

import scripts.audit_universal_rank4_quadratic as universal


Coord = Tuple[int, ...]
Products = Mapping[Tuple[int, int], Mapping[int, int]]


def cast(value, width: int):
    if value.size() == width:
        return value
    if value.size() < width:
        return z3.ZeroExt(width - value.size(), value)
    return z3.Extract(width - 1, 0, value)


@dataclass(frozen=True)
class RingSpec:
    k: int
    widths: Tuple[int, ...]
    basis: Tuple[str, ...]
    products: Products

    @property
    def name(self) -> str:
        return f"R{self.k}=Z[x,y]/(x^2,y^4,xy^{self.k}-2)"


class SymbolicRing:
    def __init__(self, spec: RingSpec):
        self.spec = spec
        self.widths = spec.widths
        self.products: Dict[Tuple[int, int], Dict[int, int]] = {
            tuple(sorted(key)): dict(value) for key, value in spec.products.items()
        }
        for i in range(len(self.widths)):
            self.products[(0, i)] = {i: 1}

    def zero(self):
        return tuple(z3.BitVecVal(0, w) for w in self.widths)

    def one(self):
        return (z3.BitVecVal(1, self.widths[0]),) + self.zero()[1:]

    def integer(self, value: int):
        return (z3.BitVecVal(value, self.widths[0]),) + self.zero()[1:]

    def var(self, name: str):
        return tuple(z3.BitVec(f"{name}_{i}", w) for i, w in enumerate(self.widths))

    def deform(self, name: str):
        value = self.var(name)
        return (2 * value[0],) + value[1:]

    def add(self, left, right):
        return tuple(a + b for a, b in zip(left, right))

    def scale(self, coefficient: int, value):
        return tuple(coefficient * part for part in value)

    def mul(self, left, right):
        out = [z3.BitVecVal(0, w) for w in self.widths]
        for i, a in enumerate(left):
            for j, b in enumerate(right):
                for target, coefficient in self.products.get(tuple(sorted((i, j))), {}).items():
                    width = self.widths[target]
                    out[target] = out[target] + (
                        cast(a, width) * cast(b, width) * z3.BitVecVal(coefficient, width)
                    )
        return tuple(out)

    @staticmethod
    def eq0(value):
        return z3.And(*(part == 0 for part in value))

    @staticmethod
    def neq0(value):
        return z3.Or(*(part != 0 for part in value))


def ring_spec(k: int) -> RingSpec:
    if k == 1:
        # 1,y,y^2 are Z/4 generators; y^3,x have order two; xy=2.
        return RingSpec(
            1, (2, 2, 2, 1, 1), ("1", "y", "y2", "y3", "x"),
            {
                (1, 1): {2: 1}, (1, 2): {3: 1},
                (1, 4): {0: 2}, (2, 4): {1: 2}, (3, 4): {2: 2},
            },
        )
    if k == 2:
        # 1,y are Z/4 generators; y^2,y^3,x,xy have order two; xy^2=2.
        return RingSpec(
            2, (2, 2, 1, 1, 1, 1), ("1", "y", "y2", "y3", "x", "xy"),
            {
                (1, 1): {2: 1}, (1, 2): {3: 1}, (1, 4): {5: 1},
                (1, 5): {0: 2}, (2, 4): {0: 2}, (2, 5): {1: 2},
                (3, 4): {1: 2},
            },
        )
    if k == 3:
        # Only 1 has order four; the six nilpotent basis vectors have order two.
        return RingSpec(
            3, (2, 1, 1, 1, 1, 1, 1),
            ("1", "y", "y2", "y3", "x", "xy", "xy2"),
            {
                (1, 1): {2: 1}, (1, 2): {3: 1}, (1, 4): {5: 1},
                (1, 5): {6: 1}, (1, 6): {0: 2},
                (2, 4): {6: 1}, (2, 5): {0: 2}, (3, 4): {0: 2},
            },
        )
    raise ValueError(k)


def concrete_add(spec: RingSpec, left: Coord, right: Coord) -> Coord:
    return tuple((a + b) % (1 << w) for a, b, w in zip(left, right, spec.widths))


def concrete_mul(spec: RingSpec, left: Coord, right: Coord) -> Coord:
    products = {tuple(sorted(key)): value for key, value in spec.products.items()}
    for i in range(len(spec.widths)):
        products[(0, i)] = {i: 1}
    out = [0] * len(spec.widths)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            for target, coefficient in products.get(tuple(sorted((i, j))), {}).items():
                out[target] += a * b * coefficient
    return tuple(value % (1 << w) for value, w in zip(out, spec.widths))


def concrete_poly(spec: RingSpec, poly: universal.Poly, values: Sequence[Coord]) -> Coord:
    zero = tuple(0 for _ in spec.widths)
    one = (1,) + zero[1:]
    out = zero
    for monomial, coefficient in poly.items():
        term = one
        for variable in monomial:
            term = concrete_mul(spec, term, values[variable])
        term = tuple((coefficient * part) % (1 << w) for part, w in zip(term, spec.widths))
        out = concrete_add(spec, out, term)
    return out


def gate_ring(spec: RingSpec) -> None:
    """Check bilinear well-definedness, identity, and associativity on a basis."""
    n = len(spec.widths)
    zero = tuple(0 for _ in spec.widths)
    basis = [tuple(1 if i == j else 0 for i in range(n)) for j in range(n)]
    for i in range(n):
        assert concrete_mul(spec, basis[0], basis[i]) == basis[i]
        assert concrete_mul(spec, basis[i], basis[0]) == basis[i]
        torsion = tuple(((1 << spec.widths[i]) * part) % (1 << w)
                        for part, w in zip(basis[i], spec.widths))
        assert torsion == zero
        for j in range(n):
            product = concrete_mul(spec, basis[i], basis[j])
            assert tuple(((1 << spec.widths[i]) * part) % (1 << w)
                         for part, w in zip(product, spec.widths)) == zero
            assert tuple(((1 << spec.widths[j]) * part) % (1 << w)
                         for part, w in zip(product, spec.widths)) == zero
            for h in range(n):
                left = concrete_mul(spec, product, basis[h])
                right = concrete_mul(spec, basis[i], concrete_mul(spec, basis[j], basis[h]))
                assert left == right, (i, j, h, left, right)
    assert sum(spec.widths) == 8
    print(f"{spec.name}: exact ring-table gate PASS", flush=True)


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


def socle(spec: RingSpec) -> Coord:
    if spec.k == 1:
        return (0, 0, 2, 0, 0)
    if spec.k == 2:
        return (0, 2, 0, 0, 0, 0)
    return (2, 0, 0, 0, 0, 0, 0)


def eq_coord(value, wanted: Coord):
    return z3.And(*(part == entry for part, entry in zip(value, wanted)))


def bridge_tangent_constraints(spec: RingSpec, values):
    """Pin the tangent symbol of the length-nine bridge (discovery only)."""
    if spec.k != 2:
        raise ValueError("the bridge-tangent seed is currently encoded only for k=2")
    # In the k=2 coordinates, tangent basis is (y,x) = (component 1, component 4).
    wanted = [(0, 0) for _ in values]
    # Delta U: y U tensor U + x V tensor U.
    wanted[18] = (1, 0)
    wanted[21] = (0, 1)
    # Delta V: y V tensor U + x V tensor V.
    wanted[30] = (1, 0)
    wanted[31] = (0, 1)
    # Delta(UV), after the two first-order cancellations.
    wanted[38] = (1, 0)  # U tensor UV
    wanted[43] = (0, 1)  # UV tensor V
    out = []
    for value, (ybit, xbit) in zip(values, wanted):
        out.append(z3.Extract(0, 0, value[1]) == ybit)
        out.append(value[4] == xbit)
    return out


def skew_bridge_constraints(ring: SymbolicRing, values):
    """Oppositely skew-primitive U,V with a shared, non-factorized lambda."""
    zero = ring.zero()
    keep_u = {18, 21, 24}
    keep_v = {30, 31, 32}
    constraints = []
    for index in range(18, 27):
        if index not in keep_u:
            constraints.append(eq_coord(values[index], tuple(0 for _ in zero)))
    for index in range(27, 36):
        if index not in keep_v:
            constraints.append(eq_coord(values[index], tuple(0 for _ in zero)))
    for left, right in ((18, 30), (21, 31), (24, 32)):
        constraints.append(z3.And(*(a == b for a, b in zip(values[left], values[right]))))
    return constraints


def search(
    spec: RingSpec,
    timeout_ms: int,
    output: Path | None,
    engine: str,
    target_index: int | None,
    require_socle: bool,
    bridge_tangent: bool,
    skew_bridge: bool,
) -> str:
    gate_ring(spec)
    universal.MAX_DEGREE = 4
    chart = universal.build_chart(0)
    assert len(chart.equations_z) == 189

    ring = SymbolicRing(spec)
    names = parameter_names()
    values = [ring.deform(name) for name in names]
    cache = {(): ring.one()}

    def monomial_value(monomial):
        if monomial not in cache:
            cache[monomial] = ring.mul(monomial_value(monomial[:-1]), values[monomial[-1]])
        return cache[monomial]

    def polynomial_value(poly):
        out = ring.zero()
        for monomial, coefficient in poly.items():
            out = ring.add(out, ring.scale(coefficient, monomial_value(monomial)))
        return out

    equations = [polynomial_value(poly) for poly in chart.equations_z]
    targets = [polynomial_value(poly) for poly in chart.targets_z]
    solver = z3.Solver() if engine == "smt" else z3.SolverFor("QF_BV")
    solver.set(timeout=timeout_ms)
    solver.set(max_memory=2048)
    solver.add(*(ring.eq0(value) for value in equations))
    if bridge_tangent:
        solver.add(*bridge_tangent_constraints(spec, values))
    if skew_bridge:
        solver.add(*skew_bridge_constraints(ring, values))

    started = time.time()
    core = solver.check()
    core_seconds = time.time() - started
    print(f"{spec.name}: core={core} seconds={core_seconds:.3f}", flush=True)
    if core != z3.sat:
        return str(core)

    selected = targets if target_index is None else [targets[target_index]]
    if require_socle:
        solver.add(z3.Or(*(eq_coord(value, socle(spec)) for value in selected)))
    else:
        solver.add(z3.Or(*(ring.neq0(value) for value in selected)))
    started = time.time()
    verdict = solver.check()
    target_seconds = time.time() - started
    print(f"{spec.name}: [4]!=e verdict={verdict} seconds={target_seconds:.3f}", flush=True)
    if verdict != z3.sat:
        if verdict == z3.unknown:
            print(f"reason_unknown={solver.reason_unknown()}", flush=True)
        return str(verdict)

    model = solver.model()
    concrete_values = []
    for value in values:
        concrete_values.append(tuple(
            model.eval(part, model_completion=True).as_long() for part in value
        ))
    equation_values = [concrete_poly(spec, p, concrete_values) for p in chart.equations_z]
    target_values = [concrete_poly(spec, p, concrete_values) for p in chart.targets_z]
    zero = tuple(0 for _ in spec.widths)
    assert all(value == zero for value in equation_values)
    assert any(value != zero for value in target_values)
    witness = {
        "ring": spec.name,
        "basis": spec.basis,
        "widths": spec.widths,
        "parameters": dict(zip(names, concrete_values)),
        "targets": target_values,
        "core_seconds": core_seconds,
        "target_seconds": target_seconds,
        "z3_version": z3.get_version_string(),
    }
    print("SAT witness targets=" + repr(target_values), flush=True)
    if output is not None:
        output.write_text(json.dumps(witness, indent=2) + "\n")
        print(f"wrote {output}", flush=True)
    return "sat"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k", type=int, choices=(1, 2, 3), required=True)
    parser.add_argument("--timeout", type=int, default=300, help="seconds per solver query")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--engine", choices=("smt", "qfbv"), default="smt")
    parser.add_argument("--target", type=int, choices=range(9))
    parser.add_argument("--socle", action="store_true",
                        help="discovery query: require the selected target to equal the socle generator")
    parser.add_argument("--bridge-tangent", action="store_true",
                        help="discovery query: pin the k=2 tangent symbol of the length-nine bridge")
    parser.add_argument("--skew-bridge", action="store_true",
                        help="discovery query: impose shared-lambda opposite skew-primitivity")
    args = parser.parse_args()
    verdict = search(
        ring_spec(args.k), args.timeout * 1000, args.output,
        args.engine, args.target, args.socle, args.bridge_tangent, args.skew_bridge,
    )
    if verdict == "unknown":
        raise SystemExit(2)


if __name__ == "__main__":
    main()
