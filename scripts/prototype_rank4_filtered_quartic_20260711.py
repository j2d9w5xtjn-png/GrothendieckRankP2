#!/usr/bin/env python3
"""Filtered quartic prototype for the universal mixed alpha_2^2 chart.

This is deliberately separate from the frozen cubic auditors.  It performs
three exact operations, all modulo q^5 for q=(2,p_0,...,p_44):

1. eliminate the rank-30 parameter part of the linear equations by formal
   implicit substitution, leaving 15 actual parameters and the 2-adic
   symbol;
2. compute a filtered standard basis through degree four, retaining exact
   integer carries before taking initial forms;
3. expose canonical product tables needed for the *filtered* middle
   catalecticant.  The homogeneous gr_4 matrix is only its first block.

No Groebner basis and no unbounded search is used.  Polynomials are sparse
integer dictionaries and are discarded as soon as their q-order is >= 5.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from dataclasses import dataclass
from itertools import combinations_with_replacement
from pathlib import Path
from typing import Iterable, Iterator

sys.path.insert(0, str(Path.cwd()))
import scripts.audit_universal_rank4_quadratic as cubic


LIMIT = 4
ORIGINAL_N = 45
TAU_ORIGINAL = 45
Mon = tuple[int, ...]
Poly = dict[Mon, int]


def v2(c: int) -> int:
    if not c:
        raise ValueError("v2(0)")
    c = abs(c)
    answer = 0
    while not c & 1:
        c //= 2
        answer += 1
    return answer


def qorder(mon: Mon, coefficient: int) -> int:
    return len(mon) + v2(coefficient)


def tidy(poly: Poly) -> Poly:
    return {
        mon: coefficient
        for mon, coefficient in poly.items()
        if coefficient and qorder(mon, coefficient) <= LIMIT
    }


def add(left: Poly, right: Poly) -> Poly:
    answer = dict(left)
    for mon, coefficient in right.items():
        answer[mon] = answer.get(mon, 0) + coefficient
        if not answer[mon]:
            del answer[mon]
    return tidy(answer)


def scale(poly: Poly, coefficient: int) -> Poly:
    return tidy({mon: coefficient * value for mon, value in poly.items()})


def multiply(left: Poly, right: Poly) -> Poly:
    answer: Poly = {}
    for lm, lc in left.items():
        for rm, rc in right.items():
            mon = tuple(sorted(lm + rm))
            answer[mon] = answer.get(mon, 0) + lc * rc
    return tidy(answer)


def variable(index: int) -> Poly:
    return {(index,): 1}


def exact_sum(polys: list[Poly], selector: int) -> Poly:
    answer: Poly = {}
    while selector:
        low = selector & -selector
        index = low.bit_length() - 1
        answer = add(answer, polys[index])
        selector ^= low
    return answer


def convert(poly: cubic.Poly) -> Poly:
    return tidy(dict(poly))


def monomial_data(nvars: int, degree: int) -> tuple[list[Mon], dict[Mon, int]]:
    mons = list(combinations_with_replacement(range(nvars), degree))
    return mons, {mon: index for index, mon in enumerate(mons)}


def initial_mask(poly: Poly, degree: int, lookup: dict[Mon, int], tau: int) -> int:
    answer = 0
    for mon, coefficient in poly.items():
        valuation = v2(coefficient)
        if len(mon) + valuation != degree:
            continue
        symbol = tuple(sorted(mon + (tau,) * valuation))
        answer ^= 1 << lookup[symbol]
    return answer


def mask_indices(mask: int) -> Iterator[int]:
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def echelon_with_combos(rows: list[int]) -> tuple[dict[int, tuple[int, int]], list[int]]:
    """High-pivot echelon basis, with exact input selectors and relations."""
    pivots: dict[int, tuple[int, int]] = {}
    relations: list[int] = []
    for index, original in enumerate(rows):
        row, selector = original, 1 << index
        while row:
            pivot = row.bit_length() - 1
            old = pivots.get(pivot)
            if old is None:
                pivots[pivot] = row, selector
                break
            row ^= old[0]
            selector ^= old[1]
        else:
            relations.append(selector)
    return pivots, relations


def filtered_basis(
    candidates: list[Poly], degree: int, lookup: dict[Mon, int], tau: int
) -> tuple[dict[int, tuple[int, Poly]], list[Poly]]:
    """Echelonize initials while carrying the exact integer residuals."""
    pivots: dict[int, tuple[int, Poly]] = {}
    residuals: list[Poly] = []
    for original in candidates:
        poly = original
        row = initial_mask(poly, degree, lookup, tau)
        while row:
            pivot = row.bit_length() - 1
            old = pivots.get(pivot)
            if old is None:
                pivots[pivot] = row, poly
                break
            row ^= old[0]
            poly = add(poly, old[1])
        else:
            if initial_mask(poly, degree, lookup, tau):
                raise AssertionError("exact filtered cancellation failed")
            residuals.append(poly)
    return pivots, residuals


def multiply_q_generator(poly: Poly, generator: int, tau: int) -> Poly:
    if generator == tau:
        return scale(poly, 2)
    return multiply(poly, variable(generator))


def homogeneous_lift(mask: int, mons: list[Mon], tau: int) -> Poly:
    """Lift an F2 initial form to an exact integer polynomial."""
    answer: Poly = {}
    for index in mask_indices(mask):
        symbol = mons[index]
        valuation = symbol.count(tau)
        mon = tuple(v for v in symbol if v != tau)
        answer = add(answer, {mon: 1 << valuation})
    return answer


def evaluate(poly: Poly, images: list[Poly]) -> Poly:
    answer: Poly = {}
    powers: dict[tuple[int, int], Poly] = {}
    for mon, coefficient in poly.items():
        term: Poly = {(): coefficient}
        for old in mon:
            key = old, mon.count(old)
            # The monomials have length at most four; the simple loop is
            # faster here than constructing a large substitution object.
            term = multiply(term, images[old])
        answer = add(answer, term)
    return answer


@dataclass
class ReducedChart:
    free_original: list[int]
    pivot_original: list[int]
    equations: list[Poly]
    targets: list[Poly]
    implicit_residual_orders: list[int]


def first_order_parameter_elimination(
    equations: list[Poly], targets: list[Poly]
) -> ReducedChart:
    """Eliminate 30 actual p-variables by q-adic implicit iteration.

    The parameter-only linear matrix has rank 30 (the full mixed matrix has
    rank 31).  We solve those 30 equations through q-order four.  The one
    remaining first-order equation is the genuinely mixed relation involving
    the 2-adic symbol; it remains among the reduced equations.
    """
    linear_mons, linear_lookup = monomial_data(ORIGINAL_N + 1, 1)
    rows_all = [initial_mask(f, 1, linear_lookup, TAU_ORIGINAL) for f in equations]
    rows_parameters = [row & ((1 << ORIGINAL_N) - 1) for row in rows_all]
    pivots, _ = echelon_with_combos(rows_parameters)
    if len(pivots) != 30:
        raise AssertionError(f"expected parameter-linear rank 30, got {len(pivots)}")
    pivot_original = sorted(pivots)
    free_original = [v for v in range(ORIGINAL_N) if v not in pivots]
    if len(free_original) != 15:
        raise AssertionError(len(free_original))

    # Exact lifts of the 30 selected linear combinations.  Echelon rows may
    # contain earlier pivot columns, so corrections are solved simultaneously
    # using the full mod-2 Jacobian rather than assuming an RREF.
    implicit = [exact_sum(equations, pivots[p][1]) for p in pivot_original]
    jac_rows = []
    pivot_position = {p: i for i, p in enumerate(pivot_original)}
    for poly in implicit:
        row = initial_mask(poly, 1, linear_lookup, TAU_ORIGINAL)
        packed = 0
        for p, position in pivot_position.items():
            if (row >> p) & 1:
                packed ^= 1 << position
        jac_rows.append(packed)
    jac_pivots, _ = echelon_with_combos(jac_rows)
    if len(jac_pivots) != 30:
        raise AssertionError("implicit Jacobian is singular")

    # Solve J * delta = residual separately for every residual monomial.
    def solve_jac(rhs_bits: int) -> int:
        # Equations are rows of J and rhs is indexed by equations.  A compact
        # Gauss-Jordan solve on the augmented transpose is simplest at size 30.
        augmented = []
        for equation, row in enumerate(jac_rows):
            augmented.append(row | (((rhs_bits >> equation) & 1) << 30))
        pivot_row = 0
        for column in range(30):
            chosen = next((r for r in range(pivot_row, 30) if (augmented[r] >> column) & 1), None)
            if chosen is None:
                raise AssertionError("singular Jacobian during solve")
            augmented[pivot_row], augmented[chosen] = augmented[chosen], augmented[pivot_row]
            for r in range(30):
                if r != pivot_row and ((augmented[r] >> column) & 1):
                    augmented[r] ^= augmented[pivot_row]
            pivot_row += 1
        solution = 0
        for r in range(30):
            pivot = next(c for c in range(30) if (augmented[r] >> c) & 1)
            if (augmented[r] >> 30) & 1:
                solution ^= 1 << pivot
        return solution

    reduced_tau = 15
    images: list[Poly] = [{} for _ in range(ORIGINAL_N)]
    for new, old in enumerate(free_original):
        images[old] = variable(new)

    for degree in range(1, LIMIT + 1):
        mons, lookup = monomial_data(16, degree)
        evaluated = [evaluate(poly, images) for poly in implicit]
        residual_masks = [initial_mask(poly, degree, lookup, reduced_tau) for poly in evaluated]
        all_columns = 0
        for mask in residual_masks:
            all_columns |= mask
        corrections = [0] * 30
        for column in mask_indices(all_columns):
            rhs = sum(((residual_masks[equation] >> column) & 1) << equation for equation in range(30))
            solution = solve_jac(rhs)
            for position in mask_indices(solution):
                corrections[position] ^= 1 << column
        for position, old in enumerate(pivot_original):
            images[old] = add(images[old], homogeneous_lift(corrections[position], mons, reduced_tau))

    evaluated_implicit = [evaluate(poly, images) for poly in implicit]
    residual_orders = [
        min((qorder(mon, coefficient) for mon, coefficient in poly.items()), default=LIMIT + 1)
        for poly in evaluated_implicit
    ]
    if min(residual_orders) <= LIMIT:
        raise AssertionError((min(residual_orders), residual_orders))

    return ReducedChart(
        free_original=free_original,
        pivot_original=pivot_original,
        equations=[evaluate(poly, images) for poly in equations],
        targets=[evaluate(poly, images) for poly in targets],
        implicit_residual_orders=residual_orders,
    )


@dataclass
class JetBasis:
    nvars: int
    tau: int
    mons: dict[int, list[Mon]]
    lookup: dict[int, dict[Mon, int]]
    bases: dict[int, dict[int, tuple[int, Poly]]]
    residuals: dict[int, list[Poly]]

    def quotient_free_columns(self, degree: int) -> list[int]:
        return [i for i in range(len(self.mons[degree])) if i not in self.bases[degree]]

    def reduce_mask(self, degree: int, row: int) -> int:
        basis = self.bases[degree]
        while row:
            pivot = row.bit_length() - 1
            old = basis.get(pivot)
            if old is None:
                # Remove this free leading column temporarily and continue;
                # it belongs in the canonical remainder.
                lower = row ^ (1 << pivot)
                return (1 << pivot) ^ self.reduce_mask(degree, lower)
            row ^= old[0]
        return 0

    def normalize_exact_degree(self, poly: Poly, degree: int) -> Poly:
        """Cancel all pivot columns in one layer, retaining carry tails."""
        basis = self.bases[degree]
        row = initial_mask(poly, degree, self.lookup[degree], self.tau)
        free = 0
        while row:
            pivot = row.bit_length() - 1
            old = basis.get(pivot)
            if old is None:
                free ^= 1 << pivot
                row ^= 1 << pivot
            else:
                row ^= old[0]
                poly = add(poly, old[1])
        check = initial_mask(poly, degree, self.lookup[degree], self.tau)
        if check != free:
            raise AssertionError("normalization changed a free initial")
        return poly

    def filtered_pair_coordinates(self, poly: Poly) -> tuple[int, int]:
        """Return canonical (degree-3, degree-4) quotient masks.

        Degree-three pivot cancellation changes the degree-four mask; this is
        precisely the filtered/Bockstein correction absent from gr_4 alone.
        """
        for degree in (1, 2, 3):
            poly = self.normalize_exact_degree(poly, degree)
        cubic_mask = initial_mask(poly, 3, self.lookup[3], self.tau)
        poly = self.normalize_exact_degree(poly, 4)
        quartic_mask = initial_mask(poly, 4, self.lookup[4], self.tau)
        return cubic_mask, quartic_mask


def build_jet_basis(equations: list[Poly]) -> JetBasis:
    nvars, tau = 16, 15
    mons: dict[int, list[Mon]] = {}
    lookup: dict[int, dict[Mon, int]] = {}
    for degree in range(1, LIMIT + 1):
        mons[degree], lookup[degree] = monomial_data(nvars, degree)

    bases: dict[int, dict[int, tuple[int, Poly]]] = {}
    residuals: dict[int, list[Poly]] = {}
    candidates = equations
    for degree in range(1, LIMIT + 1):
        bases[degree], residuals[degree] = filtered_basis(
            candidates, degree, lookup[degree], tau
        )
        if degree < LIMIT:
            candidates = [
                multiply_q_generator(poly, generator, tau)
                for _, poly in (bases[degree][p] for p in sorted(bases[degree]))
                for generator in range(nvars)
            ] + residuals[degree]
    return JetBasis(nvars, tau, mons, lookup, bases, residuals)


def mask_digest(mask: int) -> str:
    data = mask.to_bytes(max(1, (mask.bit_length() + 7) // 8), "little")
    return hashlib.sha256(data).hexdigest()


def compact_mask(mask: int, free_columns: list[int]) -> int:
    position = {column: index for index, column in enumerate(free_columns)}
    answer = 0
    for column in mask_indices(mask):
        answer ^= 1 << position[column]
    return answer


def prepare(target_index: int) -> tuple[ReducedChart, JetBasis, dict[int, int]]:
    cubic.MAX_DEGREE = LIMIT
    chart = cubic.build_chart(0)
    equations = [convert(poly) for poly in chart.equations_z]
    targets = [convert(poly) for poly in chart.targets_z]
    reduced = first_order_parameter_elimination(equations, targets)
    jet = build_jet_basis(reduced.equations)
    quotient_dimensions = {
        degree: len(jet.mons[degree]) - len(jet.bases[degree])
        for degree in range(1, LIMIT + 1)
    }
    if [quotient_dimensions[d] for d in (1, 2, 3)] != [15, 107, 509]:
        raise AssertionError(quotient_dimensions)
    return reduced, jet, quotient_dimensions


def run(target_index: int, emit_products: bool) -> dict:
    reduced, jet, quotient_dimensions = prepare(target_index)

    target3, target4 = jet.filtered_pair_coordinates(reduced.targets[target_index])
    free3 = set(jet.quotient_free_columns(3))
    free4 = set(jet.quotient_free_columns(4))
    if any(i not in free3 for i in mask_indices(target3)):
        raise AssertionError("cubic target is not in canonical quotient columns")
    if any(i not in free4 for i in mask_indices(target4)):
        raise AssertionError("quartic target is not in canonical quotient columns")

    # Socle rows are the exact degree-four normal forms of x_i*T.  They are
    # constraints on lambda_4 alone.  Keeping these rows distinct is useful
    # for a future SAT/MinRank certificate.
    socle_rows = []
    for generator in range(15):
        product = multiply(reduced.targets[target_index], variable(generator))
        _, row4 = jet.filtered_pair_coordinates(product)
        socle_rows.append(row4)

    report = {
        "chart": "mixed_a2a2",
        "q_jet_limit": 4,
        "free_original_parameters": reduced.free_original,
        "eliminated_original_parameters": reduced.pivot_original,
        "implicit_equations_residual_order_min": min(reduced.implicit_residual_orders),
        "filtered_ranks": {str(d): len(jet.bases[d]) for d in range(1, 5)},
        "filtered_relation_counts": {str(d): len(jet.residuals[d]) for d in range(1, 5)},
        "quotient_dimensions": {str(d): quotient_dimensions[d] for d in range(1, 5)},
        "target": target_index,
        "canonical_target_cubic_support": target3.bit_count(),
        "canonical_target_cubic_sha256": mask_digest(target3),
        "canonical_target_quartic_support": target4.bit_count(),
        "canonical_target_quartic_sha256": mask_digest(target4),
        "socle_constraint_rank": len(cubic.echelon_with_combos(socle_rows)[0]),
        "socle_row_sha256": hashlib.sha256(
            b"".join(
                row.to_bytes(max(1, (row.bit_length() + 7) // 8), "little")
                for row in socle_rows
            )
        ).hexdigest(),
    }

    if emit_products:
        free1 = jet.quotient_free_columns(1)
        free2 = jet.quotient_free_columns(2)
        free3cols = jet.quotient_free_columns(3)
        # Product-table hashes separate the homogeneous quartic blocks M22,
        # M31 from the filtered cubic-plus-carry block M21.
        digests = {"M22_gr4": hashlib.sha256(), "M31_gr4": hashlib.sha256(),
                   "M21_filtered_cubic": hashlib.sha256(), "M21_bockstein_quartic": hashlib.sha256()}
        for a in free2:
            pa = homogeneous_lift(1 << a, jet.mons[2], jet.tau)
            for b in free2:
                pb = homogeneous_lift(1 << b, jet.mons[2], jet.tau)
                _, q4 = jet.filtered_pair_coordinates(multiply(pa, pb))
                digests["M22_gr4"].update(q4.to_bytes(485, "little"))
            for b in free1:
                pb = homogeneous_lift(1 << b, jet.mons[1], jet.tau)
                q3, q4 = jet.filtered_pair_coordinates(multiply(pa, pb))
                digests["M21_filtered_cubic"].update(q3.to_bytes(102, "little"))
                digests["M21_bockstein_quartic"].update(q4.to_bytes(485, "little"))
        for a in free3cols:
            pa = homogeneous_lift(1 << a, jet.mons[3], jet.tau)
            for b in free1:
                pb = homogeneous_lift(1 << b, jet.mons[1], jet.tau)
                _, q4 = jet.filtered_pair_coordinates(multiply(pa, pb))
                digests["M31_gr4"].update(q4.to_bytes(485, "little"))
        report["product_table_sha256"] = {name: digest.hexdigest() for name, digest in digests.items()}

    return report


def xor_z3(z3, expressions: Iterable):
    answer = z3.BoolVal(False)
    for expression in expressions:
        answer = z3.Xor(answer, expression)
    return answer


def plain_rank(rows: Iterable[int]) -> int:
    pivots: dict[int, int] = {}
    for original in rows:
        row = original
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def rowspace_nullspace(rows: list[int], ncolumns: int) -> list[int]:
    """Basis of the orthogonal complement of the span of ``rows``."""
    pivots: dict[int, int] = {}
    for original in rows:
        row = original
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    free = [column for column in range(ncolumns) if column not in pivots]
    answer = []
    for chosen in free:
        vector = 1 << chosen
        # Each pivot equation is n_p + (lower coordinates) = 0.
        for pivot in sorted(pivots):
            lower = pivots[pivot] ^ (1 << pivot)
            if (lower & vector).bit_count() & 1:
                vector ^= 1 << pivot
        if any((row & vector).bit_count() & 1 for row in pivots.values()):
            raise AssertionError("bad orthogonal-complement vector")
        answer.append(vector)
    return answer


def solve_affine_f2(rows: list[tuple[int, int]], nvars: int) -> tuple[bool, int, int]:
    """Solve mask*x + constant = 0; return consistency, one model, rank."""
    pivots: dict[int, tuple[int, int]] = {}
    for variables, constant in rows:
        while variables:
            pivot = variables.bit_length() - 1
            old = pivots.get(pivot)
            if old is None:
                pivots[pivot] = variables, constant
                break
            variables ^= old[0]
            constant ^= old[1]
        else:
            if constant:
                return False, 0, len(pivots)
    model = 0
    for pivot in sorted(pivots):
        variables, constant = pivots[pivot]
        lower = variables ^ (1 << pivot)
        value = constant ^ ((lower & model).bit_count() & 1)
        if value:
            model ^= 1 << pivot
    for variables, constant in rows:
        if ((variables & model).bit_count() & 1) ^ constant:
            raise AssertionError("affine solver produced a bad model")
    return True, model, len(pivots)


def search_homogeneous_rank_two(target_index: int, timeout_ms: int) -> dict:
    """Search the *necessary but not sufficient* homogeneous quartic test.

    This asks for a nonzero lambda_4 satisfying the target-socle constraints
    and rank(M22(lambda_4)) <= 2.  A SAT result is not yet a filtered
    h_2 <= 2 quotient: M21 and its Bockstein quartic tail must still be
    considered modulo M31.
    """
    try:
        import z3
    except ModuleNotFoundError:
        sys.path.insert(0, "/tmp/rank4_z3")
        import z3

    reduced, jet, dimensions = prepare(target_index)
    free2 = jet.quotient_free_columns(2)
    free3 = jet.quotient_free_columns(3)
    free4 = jet.quotient_free_columns(4)
    pos4 = {column: index for index, column in enumerate(free4)}
    lambda4 = [z3.Bool(f"l4_{i}") for i in range(len(free4))]

    def value4(mask: int):
        return xor_z3(z3, (lambda4[pos4[column]] for column in mask_indices(mask)))

    # Cache exact A_2*A_2 product normal forms.
    products22: list[list[int]] = []
    for a in free2:
        pa = homogeneous_lift(1 << a, jet.mons[2], jet.tau)
        row = []
        for b in free2:
            pb = homogeneous_lift(1 << b, jet.mons[2], jet.tau)
            _, q4 = jet.filtered_pair_coordinates(multiply(pa, pb))
            row.append(q4)
        products22.append(row)

    u = [[z3.Bool(f"u_{a}_{r}") for r in range(2)] for a in range(len(free2))]
    v = [[z3.Bool(f"v_{r}_{b}") for b in range(len(free2))] for r in range(2)]
    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.set(max_memory=1024)
    for a in range(len(free2)):
        for b in range(len(free2)):
            factor = xor_z3(z3, (z3.And(u[a][r], v[r][b]) for r in range(2)))
            solver.add(factor == value4(products22[a][b]))

    target3, target4 = jet.filtered_pair_coordinates(reduced.targets[target_index])
    for generator in range(15):
        _, row4 = jet.filtered_pair_coordinates(
            multiply(reduced.targets[target_index], variable(generator))
        )
        solver.add(value4(row4) == z3.BoolVal(False))
    solver.add(z3.Or(*lambda4))
    # If the target has no cubic class, its detection is already a condition
    # on lambda_4.  When the cubic class is nonzero, lambda_3 can supply the
    # value and the homogeneous test deliberately remains only necessary.
    if not target3:
        solver.add(value4(target4) == z3.BoolVal(True))

    payload = solver.sexpr().encode()
    digest = hashlib.sha256(payload).hexdigest()
    started = time.time()
    verdict = solver.check()
    elapsed = time.time() - started
    answer = {
        "scope": "homogeneous_gr4_necessary_condition_only",
        "target": target_index,
        "A2_dimension": dimensions[2],
        "A3_dimension": dimensions[3],
        "A4_dimension": dimensions[4],
        "assertions": len(solver.assertions()),
        "smt_sha256": digest,
        "verdict": str(verdict),
        "seconds": elapsed,
    }
    if verdict == z3.sat:
        model = solver.model()
        lambda4_mask = sum(
            (1 << i) for i, bit in enumerate(lambda4)
            if z3.is_true(model.eval(bit, model_completion=True))
        )
        m22_rows = []
        for row in products22:
            packed = 0
            for b, mask in enumerate(row):
                compact = compact_mask(mask, free4)
                if (compact & lambda4_mask).bit_count() & 1:
                    packed ^= 1 << b
            m22_rows.append(packed)
        m31_rows = []
        free1 = jet.quotient_free_columns(1)
        for a in free3:
            pa = homogeneous_lift(1 << a, jet.mons[3], jet.tau)
            packed = 0
            for b, column in enumerate(free1):
                pb = homogeneous_lift(1 << column, jet.mons[1], jet.tau)
                _, mask = jet.filtered_pair_coordinates(multiply(pa, pb))
                compact = compact_mask(mask, free4)
                if (compact & lambda4_mask).bit_count() & 1:
                    packed ^= 1 << b
            m31_rows.append(packed)
        # The complete filtered degree-two rank is
        #
        # rank [[M22, M21], [0, M31]] - rank(M31).
        #
        # Once lambda_4 and rank(M22)=2 are fixed, requiring this difference
        # to be two is a *linear* problem in lambda_3.  Choose two M22 rows
        # spanning its row space.  Every other row has unique F2 coordinates
        # in that basis, and the corresponding adjusted M21 row must lie in
        # rowspace(M31).
        reference_indices: list[int] = []
        reference_rows: list[int] = []
        for index, row in enumerate(m22_rows):
            if plain_rank(reference_rows + [row]) > len(reference_rows):
                reference_indices.append(index)
                reference_rows.append(row)
        if len(reference_rows) != 2:
            raise AssertionError((len(reference_rows), plain_rank(m22_rows)))
        row_coordinates = []
        for row in m22_rows:
            coordinate = next(
                bits for bits in range(4)
                if row == ((reference_rows[0] if bits & 1 else 0)
                           ^ (reference_rows[1] if bits & 2 else 0))
            )
            row_coordinates.append(coordinate)

        free1 = jet.quotient_free_columns(1)
        pos3 = {column: index for index, column in enumerate(free3)}

        def compact3(mask: int) -> int:
            return sum(1 << pos3[column] for column in mask_indices(mask))

        # Each entry is (linear mask in lambda_3, fixed lambda_4 value).
        m21: list[list[tuple[int, int]]] = []
        for a in free2:
            pa = homogeneous_lift(1 << a, jet.mons[2], jet.tau)
            row = []
            for b in free1:
                pb = homogeneous_lift(1 << b, jet.mons[1], jet.tau)
                q3, q4 = jet.filtered_pair_coordinates(multiply(pa, pb))
                fixed = (compact_mask(q4, free4) & lambda4_mask).bit_count() & 1
                row.append((compact3(q3), fixed))
            m21.append(row)

        annihilator31 = rowspace_nullspace(m31_rows, len(free1))
        affine_rows: list[tuple[int, int]] = []
        for a, coordinate in enumerate(row_coordinates):
            for normal in annihilator31:
                variables = 0
                constant = 0
                for column in mask_indices(normal):
                    terms = [m21[a][column]]
                    if coordinate & 1:
                        terms.append(m21[reference_indices[0]][column])
                    if coordinate & 2:
                        terms.append(m21[reference_indices[1]][column])
                    for linear, fixed in terms:
                        variables ^= linear
                        constant ^= fixed
                affine_rows.append((variables, constant))

        target3_mask, target4_mask = jet.filtered_pair_coordinates(
            reduced.targets[target_index]
        )
        target3_compact = compact3(target3_mask)
        target4_value = (
            compact_mask(target4_mask, free4) & lambda4_mask
        ).bit_count() & 1
        # lambda(target)=1.
        affine_rows.append((target3_compact, target4_value ^ 1))
        consistent, lambda3_mask, affine_rank = solve_affine_f2(
            affine_rows, len(free3)
        )

        filtered_data = {
            "linear_cubic_unknowns": len(free3),
            "linear_filtered_equations": len(affine_rows),
            "linear_filtered_rank": affine_rank,
            "consistent": consistent,
            "M31_annihilator_dimension": len(annihilator31),
            "M22_reference_rows": reference_indices,
        }
        if consistent:
            numeric_m21 = []
            for row in m21:
                packed = 0
                for column, (linear, fixed) in enumerate(row):
                    value = ((linear & lambda3_mask).bit_count() & 1) ^ fixed
                    if value:
                        packed ^= 1 << column
                numeric_m21.append(packed)
            block_rows = [
                m22_rows[a] | (numeric_m21[a] << len(free2))
                for a in range(len(free2))
            ] + [row << len(free2) for row in m31_rows]
            filtered_h2 = plain_rank(block_rows) - plain_rank(m31_rows)
            target_value = (
                (target3_compact & lambda3_mask).bit_count() ^ target4_value
            ) & 1
            filtered_data.update({
                "lambda3_support": lambda3_mask.bit_count(),
                "lambda3_sha256": mask_digest(lambda3_mask),
                "filtered_block_rank": plain_rank(block_rows),
                "filtered_h2": filtered_h2,
                "target_value": target_value,
            })
            if filtered_h2 > 2 or target_value != 1:
                raise AssertionError(filtered_data)
        answer.update({
            "lambda4_support": lambda4_mask.bit_count(),
            "lambda4_sha256": mask_digest(lambda4_mask),
            "M22_rank": plain_rank(m22_rows),
            "M31_rank": plain_rank(m31_rows),
            "target_cubic_nonzero": bool(target3),
            "filtered_completion_for_this_lambda4": filtered_data,
        })
    elif verdict == z3.unknown:
        answer["reason_unknown"] = solver.reason_unknown()
    return answer


def search_filtered_rank_two(
    target_index: int, timeout_ms: int, q_rank_case: str
) -> dict:
    """Exact Boolean search for a filtered functional with h_2 <= 2.

    For lambda=(lambda_3,lambda_4), let

      M22(a,b)=lambda_4(ab),
      M31(c,x)=lambda_4(cx),
      M21(a,x)=lambda_3((ax)_3)+lambda_4((ax)_4^Bockstein).

    Then the degree-two layer of the apolar filtered quotient has dimension

      rank([[M22,M21],[0,M31]]) - rank(M31).

    Rank at most two is encoded without loss by

      M22 = U V22,  M31 = Q Z,  M21 = U V21 + W Z,

    with two columns/rows.  This is the filtered condition; omitting the
    M21 Bockstein tail gives only the insufficient homogeneous gr_4 test.
    """
    try:
        import z3
    except ModuleNotFoundError:
        sys.path.insert(0, "/tmp/rank4_z3")
        import z3

    reduced, jet, dimensions = prepare(target_index)
    free1 = jet.quotient_free_columns(1)
    free2 = jet.quotient_free_columns(2)
    free3 = jet.quotient_free_columns(3)
    free4 = jet.quotient_free_columns(4)
    positions = {
        3: {column: index for index, column in enumerate(free3)},
        4: {column: index for index, column in enumerate(free4)},
    }
    lambda3 = [z3.Bool(f"l3_{i}") for i in range(len(free3))]
    lambda4 = [z3.Bool(f"l4_{i}") for i in range(len(free4))]

    def value(mask: int, degree: int):
        variables = lambda3 if degree == 3 else lambda4
        position = positions[degree]
        return xor_z3(z3, (variables[position[column]] for column in mask_indices(mask)))

    products22: list[list[int]] = []
    products21: list[list[tuple[int, int]]] = []
    products31: list[list[int]] = []
    lifted1 = [homogeneous_lift(1 << column, jet.mons[1], jet.tau) for column in free1]
    lifted2 = [homogeneous_lift(1 << column, jet.mons[2], jet.tau) for column in free2]
    lifted3 = [homogeneous_lift(1 << column, jet.mons[3], jet.tau) for column in free3]
    for pa in lifted2:
        row22 = []
        for pb in lifted2:
            _, q4 = jet.filtered_pair_coordinates(multiply(pa, pb))
            row22.append(q4)
        products22.append(row22)
        row21 = []
        for pb in lifted1:
            row21.append(jet.filtered_pair_coordinates(multiply(pa, pb)))
        products21.append(row21)
    for pa in lifted3:
        row31 = []
        for pb in lifted1:
            _, q4 = jet.filtered_pair_coordinates(multiply(pa, pb))
            row31.append(q4)
        products31.append(row31)

    n1, n2, n3 = len(free1), len(free2), len(free3)
    u = [[z3.Bool(f"u_{a}_{r}") for r in range(2)] for a in range(n2)]
    v22 = [[z3.Bool(f"v22_{r}_{b}") for b in range(n2)] for r in range(2)]
    q = [[z3.Bool(f"q_{c}_{r}") for r in range(2)] for c in range(n3)]
    z = [[z3.Bool(f"z_{r}_{x}") for x in range(n1)] for r in range(2)]
    v21 = [[z3.Bool(f"v21_{r}_{x}") for x in range(n1)] for r in range(2)]
    w = [[z3.Bool(f"w_{a}_{r}") for r in range(2)] for a in range(n2)]

    solver = z3.Solver()
    solver.set(timeout=timeout_ms)
    solver.set(max_memory=1024)
    for a in range(n2):
        for b in range(n2):
            solver.add(
                xor_z3(z3, (z3.And(u[a][r], v22[r][b]) for r in range(2)))
                == value(products22[a][b], 4)
            )
    for c in range(n3):
        for x in range(n1):
            solver.add(
                xor_z3(z3, (z3.And(q[c][r], z[r][x]) for r in range(2)))
                == value(products31[c][x], 4)
            )
    # Guarantee rowspace(W) <= rowspace(Q), so WZ consists of genuine M31
    # correction rows.  Over F2 a two-column Q has only five rank strata;
    # splitting them removes the expensive left-inverse encoding and is
    # exhaustive.
    if q_rank_case == "2":
        has10 = z3.Or(*(z3.And(q[c][0], z3.Not(q[c][1])) for c in range(n3)))
        has01 = z3.Or(*(z3.And(z3.Not(q[c][0]), q[c][1]) for c in range(n3)))
        has11 = z3.Or(*(z3.And(q[c][0], q[c][1]) for c in range(n3)))
        solver.add(z3.Or(z3.And(has10, has01), z3.And(has10, has11), z3.And(has01, has11)))
        # The lower-rank strata were queried separately.  Hence here the
        # actual M31 has rank two, so Z has rank two.  Fix the residual GL_2
        # gauge on Q canonically: its first nonzero row is 10 and its first
        # row outside that line is 01.  This is lossless and removes the main
        # factorization symmetry.
        z_has10 = z3.Or(*(z3.And(z[0][x], z3.Not(z[1][x])) for x in range(n1)))
        z_has01 = z3.Or(*(z3.And(z3.Not(z[0][x]), z[1][x]) for x in range(n1)))
        z_has11 = z3.Or(*(z3.And(z[0][x], z[1][x]) for x in range(n1)))
        solver.add(z3.Or(z3.And(z_has10, z_has01), z3.And(z_has10, z_has11), z3.And(z_has01, z_has11)))
        seen10 = z3.BoolVal(False)
        seen01 = z3.BoolVal(False)
        for c in range(n3):
            type10 = z3.And(q[c][0], z3.Not(q[c][1]))
            type01 = z3.And(z3.Not(q[c][0]), q[c][1])
            type11 = z3.And(q[c][0], q[c][1])
            solver.add(z3.Implies(z3.Or(type01, type11), seen10))
            solver.add(z3.Implies(type11, seen01))
            seen10 = z3.Or(seen10, type10)
            seen01 = z3.Or(seen01, type01)
        solver.add(seen10, seen01)
    elif q_rank_case == "10":
        solver.add(z3.Or(*(q[c][0] for c in range(n3))))
        solver.add(*(z3.Not(q[c][1]) for c in range(n3)))
        solver.add(*(z3.Not(w[a][1]) for a in range(n2)))
    elif q_rank_case == "01":
        solver.add(z3.Or(*(q[c][1] for c in range(n3))))
        solver.add(*(z3.Not(q[c][0]) for c in range(n3)))
        solver.add(*(z3.Not(w[a][0]) for a in range(n2)))
    elif q_rank_case == "11":
        solver.add(z3.Or(*(q[c][0] for c in range(n3))))
        solver.add(*(q[c][0] == q[c][1] for c in range(n3)))
        solver.add(*(w[a][0] == w[a][1] for a in range(n2)))
    elif q_rank_case == "0":
        solver.add(*(z3.Not(q[c][r]) for c in range(n3) for r in range(2)))
        solver.add(*(z3.Not(w[a][r]) for a in range(n2) for r in range(2)))
    else:
        raise ValueError(q_rank_case)
    for a in range(n2):
        for x in range(n1):
            q3, q4 = products21[a][x]
            left = xor_z3(z3, (value(q3, 3), value(q4, 4)))
            right = xor_z3(z3, list(
                z3.And(u[a][r], v21[r][x]) for r in range(2)
            ) + list(
                z3.And(w[a][r], z[r][x]) for r in range(2)
            ))
            solver.add(left == right)

    target3, target4 = jet.filtered_pair_coordinates(reduced.targets[target_index])
    solver.add(xor_z3(z3, (value(target3, 3), value(target4, 4))) == z3.BoolVal(True))
    for generator in range(15):
        _, row4 = jet.filtered_pair_coordinates(
            multiply(reduced.targets[target_index], variable(generator))
        )
        solver.add(value(row4, 4) == z3.BoolVal(False))
    solver.add(z3.Or(*lambda4))

    payload = solver.sexpr().encode()
    digest = hashlib.sha256(payload).hexdigest()
    started = time.time()
    verdict = solver.check()
    elapsed = time.time() - started
    answer = {
        "scope": "full_filtered_pair_rank_condition",
        "M31_factor_rank_stratum": q_rank_case,
        "target": target_index,
        "A1_dimension": n1,
        "A2_dimension": n2,
        "A3_dimension": n3,
        "A4_dimension": len(free4),
        "boolean_unknowns_declared": 4100,
        "assertions": len(solver.assertions()),
        "smt_sha256": digest,
        "verdict": str(verdict),
        "seconds": elapsed,
    }
    if verdict == z3.sat:
        model = solver.model()
        lambda3_mask = sum(
            1 << i for i, bit in enumerate(lambda3)
            if z3.is_true(model.eval(bit, model_completion=True))
        )
        lambda4_mask = sum(
            1 << i for i, bit in enumerate(lambda4)
            if z3.is_true(model.eval(bit, model_completion=True))
        )

        def numeric_value(mask: int, degree: int) -> int:
            compact = compact_mask(mask, free3 if degree == 3 else free4)
            functional = lambda3_mask if degree == 3 else lambda4_mask
            return (compact & functional).bit_count() & 1

        m22_rows = []
        for row in products22:
            packed = sum(numeric_value(mask, 4) << b for b, mask in enumerate(row))
            m22_rows.append(packed)
        m31_rows = []
        for row in products31:
            packed = sum(numeric_value(mask, 4) << x for x, mask in enumerate(row))
            m31_rows.append(packed)
        m21_rows = []
        for row in products21:
            packed = 0
            for x, (q3, q4) in enumerate(row):
                if numeric_value(q3, 3) ^ numeric_value(q4, 4):
                    packed ^= 1 << x
            m21_rows.append(packed)
        block_rows = [
            m22_rows[a] | (m21_rows[a] << n2) for a in range(n2)
        ] + [row << n2 for row in m31_rows]
        target_value = numeric_value(target3, 3) ^ numeric_value(target4, 4)
        socle_values = []
        for generator in range(15):
            _, row4 = jet.filtered_pair_coordinates(
                multiply(reduced.targets[target_index], variable(generator))
            )
            socle_values.append(numeric_value(row4, 4))
        answer.update({
            "lambda3_support": lambda3_mask.bit_count(),
            "lambda3_sha256": mask_digest(lambda3_mask),
            "lambda4_support": lambda4_mask.bit_count(),
            "lambda4_sha256": mask_digest(lambda4_mask),
            "M22_rank": plain_rank(m22_rows),
            "M31_rank": plain_rank(m31_rows),
            "filtered_block_rank": plain_rank(block_rows),
            "filtered_h2": plain_rank(block_rows) - plain_rank(m31_rows),
            "target_value": target_value,
            "target_socle_values": socle_values,
        })
        if answer["filtered_h2"] > 2 or target_value != 1 or any(socle_values):
            raise AssertionError(answer)
    elif verdict == z3.unknown:
        answer["reason_unknown"] = solver.reason_unknown()
    return answer


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--target", type=int, choices=range(9), default=2)
    parser.add_argument("--emit-products", action="store_true")
    parser.add_argument("--search-homogeneous", action="store_true")
    parser.add_argument("--search-filtered", action="store_true")
    parser.add_argument("--timeout-ms", type=int, default=60000)
    parser.add_argument("--q-rank-case", choices=("2", "10", "01", "11", "0"), default="2")
    args = parser.parse_args()
    if args.search_filtered:
        result = search_filtered_rank_two(args.target, args.timeout_ms, args.q_rank_case)
    elif args.search_homogeneous:
        result = search_homogeneous_rank_two(args.target, args.timeout_ms)
    else:
        result = run(args.target, args.emit_products)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
