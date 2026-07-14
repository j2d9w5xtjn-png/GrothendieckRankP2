#!/usr/bin/env python3
"""Rank-4 cubic dual and global rank<=3 exclusion for the mixed a2a2 chart.

Requires z3-solver.  The audit run used a temporary installation at
``/tmp/rank4_z3``; the script automatically checks that location.
"""

from __future__ import annotations

import hashlib
import sys
import time
from itertools import combinations_with_replacement
from pathlib import Path

sys.path.insert(0, str(Path.cwd()))

try:
    import z3
except ModuleNotFoundError:
    sys.path.insert(0, "/tmp/rank4_z3")
    import z3

import scripts.audit_universal_rank4_quadratic as audit


def xor(expressions):
    out = z3.BoolVal(False)
    for expression in expressions:
        out = z3.Xor(out, expression)
    return out


def build_cubic_relations():
    chart = audit.build_chart(0)
    equations = chart.equations_z
    nvars = 46
    linear_mons = audit.monomials(nvars, 1)
    linear_lookup = {m: i for i, m in enumerate(linear_mons)}
    quad_mons = audit.monomials(nvars, 2)
    quad_lookup = {m: i for i, m in enumerate(quad_mons)}
    cubic_mons = audit.monomials(nvars, 3)
    cubic_lookup = {m: i for i, m in enumerate(cubic_mons)}

    def layer(poly, degree, lookup):
        return audit.poly_mask(
            audit.homogeneous_layer(poly, degree, "mixed"), lookup
        )

    linear_pivots, linear_kernel = audit.echelon_with_combos(
        [layer(f, 1, linear_lookup) for f in equations]
    )
    free = [v for v in range(nvars) if v not in linear_pivots]
    free_position = {v: i for i, v in enumerate(free)}
    variable_images = [0] * nvars
    for v in free:
        variable_images[v] = 1 << free_position[v]
    for pivot, (row, _) in linear_pivots.items():
        image = 0
        for v in audit.bit_indices(row ^ (1 << pivot)):
            image ^= 1 << free_position[v]
        variable_images[pivot] = image

    def actual_parameter(v):
        return audit.const(2) if v == 45 else audit.var(v)

    degree2_elements = []
    for _, (_, selector) in sorted(linear_pivots.items()):
        lift = audit.exact_sum(equations, selector)
        for v in range(nvars):
            degree2_elements.append(audit.mul(actual_parameter(v), lift))
    for selector in linear_kernel:
        degree2_elements.append(audit.exact_sum(equations, selector))
    degree2_pivots, degree2_kernel = audit.echelon_with_combos(
        [layer(f, 2, quad_lookup) for f in degree2_elements]
    )

    def quad_times_variable(row, v):
        out = 0
        for qi in audit.bit_indices(row):
            mon = tuple(sorted(quad_mons[qi] + (v,)))
            out ^= 1 << cubic_lookup[mon]
        return out

    cubic_candidates = [
        quad_times_variable(row, v)
        for row, _ in degree2_pivots.values()
        for v in range(nvars)
    ]
    cubic_candidates += [
        layer(audit.exact_sum(degree2_elements, selector), 3, cubic_lookup)
        for selector in degree2_kernel
    ]

    free_cubics = list(combinations_with_replacement(range(15), 3))
    free_cubic_lookup = {m: i for i, m in enumerate(free_cubics)}

    def expand(mon):
        terms = {()}
        for v in mon:
            new_terms = set()
            for old in terms:
                for j in audit.bit_indices(variable_images[v]):
                    new = tuple(sorted(old + (j,)))
                    if new in new_terms:
                        new_terms.remove(new)
                    else:
                        new_terms.add(new)
            terms = new_terms
        out = 0
        for term in terms:
            out ^= 1 << free_cubic_lookup[term]
        return out

    relation_pivots = {}
    for row in cubic_candidates:
        reduced = 0
        for ci in audit.bit_indices(row):
            reduced ^= expand(cubic_mons[ci])
        audit.insert_plain(relation_pivots, reduced)

    # Normal representative u*c111*(c112+c121).
    target13 = (
        1 << free_cubic_lookup[tuple(sorted((
            free_position[0], free_position[18], free_position[19]
        )))]
    ) ^ (
        1 << free_cubic_lookup[tuple(sorted((
            free_position[0], free_position[18], free_position[21]
        )))]
    )
    target23 = (
        1 << free_cubic_lookup[tuple(sorted((
            free_position[0], free_position[18], free_position[28]
        )))]
    ) ^ (
        1 << free_cubic_lookup[tuple(sorted((
            free_position[0], free_position[18], free_position[30]
        )))]
    )
    return free, free_cubics, relation_pivots, target13, target23


def rank4_certificate(free_cubics, relations, target):
    # On the common free variables, use p0,p18 -> X; p1 -> Y; p10 -> Z;
    # p21,p31 -> Y+Z; p30 -> D, and send all other free variables to zero.
    # The cubic inverse system is X^[2]Z + XYD + YD^[2] + Z^[3].
    free_ambient = [0, 1, 3, 4, 5, 9, 10, 18, 19, 21, 22, 27, 28, 30, 31]
    q_by_ambient = {0: 1, 1: 2, 10: 4, 18: 1, 21: 6, 30: 8, 31: 6}
    qmap = [q_by_ambient.get(v, 0) for v in free_ambient]
    q_cubics = list(combinations_with_replacement(range(4), 3))
    q_lookup = {m: i for i, m in enumerate(q_cubics)}
    G = {(0, 0, 2), (0, 1, 3), (1, 3, 3), (2, 2, 2)}

    def value(mon):
        terms = {()}
        for v in mon:
            new_terms = set()
            for old in terms:
                for j in range(4):
                    if (qmap[v] >> j) & 1:
                        new = tuple(sorted(old + (j,)))
                        if new in new_terms:
                            new_terms.remove(new)
                        else:
                            new_terms.add(new)
            terms = new_terms
        return len(terms & G) & 1

    lam = 0
    for i, mon in enumerate(free_cubics):
        if value(mon):
            lam |= 1 << i
    assert all((lam & row).bit_count() % 2 == 0 for row in relations.values())
    assert (lam & target).bit_count() % 2 == 1

    quadrics = list(combinations_with_replacement(range(15), 2))
    quad_lookup = {m: i for i, m in enumerate(quadrics)}
    cubic_lookup = {m: i for i, m in enumerate(free_cubics)}
    cat_pivots = {}
    for i in range(15):
        row = 0
        for q, jk in enumerate(quadrics):
            if (lam >> cubic_lookup[tuple(sorted((i,) + jk))]) & 1:
                row ^= 1 << q
        audit.insert_plain(cat_pivots, row)
    assert len(cat_pivots) == 4
    return lam, len(cat_pivots)


def exclude_rank_three(free_cubics, relations, targets):
    quadrics = list(combinations_with_replacement(range(15), 2))
    quad_lookup = {m: i for i, m in enumerate(quadrics)}
    U = [[z3.Bool(f"u_{i}_{r}") for r in range(3)] for i in range(15)]
    V = [[z3.Bool(f"v_{r}_{q}") for q in range(120)] for r in range(3)]
    C = [
        [xor(z3.And(U[i][r], V[r][q]) for r in range(3)) for q in range(120)]
        for i in range(15)
    ]

    def coefficient(mon):
        i, j, k = mon
        return C[i][quad_lookup[(j, k)]]

    solver = z3.Solver()
    solver.set(timeout=120000)
    # Keep the audit bounded on a laptop; the canonical run uses much less.
    solver.set(max_memory=1024)
    for i, j, k in free_cubics:
        entry = C[i][quad_lookup[(j, k)]]
        if j != i:
            solver.add(entry == C[j][quad_lookup[tuple(sorted((i, k)))]] )
        if k != j:
            solver.add(entry == C[k][quad_lookup[(i, j)]])
    for row in relations.values():
        solver.add(xor(
            coefficient(free_cubics[t]) for t in audit.bit_indices(row)
        ) == False)
    target_values = [
        xor(coefficient(free_cubics[t]) for t in audit.bit_indices(target))
        for target in targets
    ]
    solver.add(z3.Or(*target_values))
    payload = solver.sexpr().encode()
    digest = hashlib.sha256(payload).hexdigest()
    started = time.time()
    verdict = solver.check()
    elapsed = time.time() - started
    assert verdict == z3.unsat, (verdict, solver.reason_unknown())
    return len(solver.assertions()), digest, elapsed


def main():
    free, cubics, relations, target13, target23 = build_cubic_relations()
    assert free == [0, 1, 3, 4, 5, 9, 10, 18, 19, 21, 22, 27, 28, 30, 31]
    assert len(relations) == 171
    lam, rank = rank4_certificate(cubics, relations, target13)
    assertions, digest, elapsed = exclude_rank_three(
        cubics, relations, (target13, target23)
    )
    print("free tangent variables", free)
    print("nonlinear cubic relation rank", len(relations))
    print("rank-4 lambda support/rank/target", lam.bit_count(), rank,
          (lam & target13).bit_count() & 1,
          (lam & target23).bit_count() & 1)
    print("rank<=3 SMT assertions/SHA256", assertions, digest)
    print("rank<=3 verdict UNSAT for either nonzero [4] target; seconds", elapsed)
    print("PASS: minimum catalecticant rank is 4; apolar Hilbert=(1,4,4,1)")


if __name__ == "__main__":
    main()
