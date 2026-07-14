#!/usr/bin/env python3
"""Verify elementary invariants of the rank-four counterexample base.

The input is the exact integral ``alpha2^2`` export produced by
``m2/universal_local_rank4.m2``.  We reuse the independently audited filtered
linear-algebra primitives, but ask two new membership questions in

    P = Z_(2)[p_0,...,p_44],  q = (2,p_0,...,p_44):

* ``2 not in I + q^4``;
* ``4 in I + q^4``.

Together they prove that the finite Artin local base has characteristic four.
The script also records its length from the three filtered ranks.
"""

from __future__ import annotations

import argparse
import hashlib

import independent_audit_mixed_a2a2_export as audit


def bit_terms(mask: int, monomials: list[tuple[int, ...]]) -> list[tuple[int, ...]]:
    return [monomials[i] for i in range(len(monomials)) if (mask >> i) & 1]


def run(export_path: str) -> None:
    equations, _ = audit.read_export(export_path)
    monomial_data = {degree: audit.monomial_data(degree) for degree in (1, 2, 3)}

    basis1, relations1 = audit.filtered_basis(
        equations, 1, monomial_data[1][1]
    )
    candidates2 = [
        audit.multiply_q_generator(poly, generator)
        for _, poly in (basis1[pivot] for pivot in sorted(basis1))
        for generator in range(audit.N + 1)
    ] + relations1
    basis2, relations2 = audit.filtered_basis(
        candidates2, 2, monomial_data[2][1]
    )
    candidates3 = [
        audit.multiply_q_generator(poly, generator)
        for _, poly in (basis2[pivot] for pivot in sorted(basis2))
        for generator in range(audit.N + 1)
    ] + relations2
    basis3, _ = audit.filtered_basis(candidates3, 3, monomial_data[3][1])

    assert (len(basis1), len(basis2), len(basis3)) == (31, 974, 16787)
    assert (len(candidates2), len(candidates3)) == (1584, 45414)

    # The coefficient of e_1 tensor e_2 - e_2 tensor e_1 in Delta(e_1) is
    # p_19-p_21.  Its nonzero linear class proves that the resulting group
    # law is genuinely noncommutative.
    plain_basis1 = {pivot: row_poly[0] for pivot, row_poly in basis1.items()}
    nc_row = audit.initial_mask({(19,): 1, (21,): -1}, 1, monomial_data[1][1])
    nc_remainder = audit.reduce_plain(plain_basis1, nc_row)
    assert bit_terms(nc_remainder, monomial_data[1][0]) == [(19,), (21,)]
    nc_dual = audit.dual_for_remainder(plain_basis1, nc_remainder)
    assert bit_terms(nc_dual, monomial_data[1][0]) == [(21,), (41,)]
    assert all(
        not (audit.initial_mask(equation, 1, monomial_data[1][1]) & nc_dual)
        .bit_count()
        % 2
        for equation in equations
    )
    assert (nc_row & nc_dual).bit_count() % 2 == 1

    # Cancel the degree-one initial form of 2 by exact lifts from I.  The
    # resulting degree-two class is then tested against the exhaustive
    # degree-two initial ideal.
    two_residual = audit.cancel_exact(
        {(): 2}, 1, monomial_data[1][1], basis1
    )
    two_row = audit.initial_mask(two_residual, 2, monomial_data[2][1])
    plain_basis2 = {pivot: row_poly[0] for pivot, row_poly in basis2.items()}
    two_remainder = audit.reduce_plain(plain_basis2, two_row)
    assert two_remainder
    two_dual = audit.dual_for_remainder(plain_basis2, two_remainder)
    assert all(
        not (
            audit.initial_mask(candidate, 2, monomial_data[2][1]) & two_dual
        ).bit_count()
        % 2
        for candidate in candidates2
    )
    assert (two_row & two_dual).bit_count() % 2 == 1

    remainder_terms = bit_terms(two_remainder, monomial_data[2][0])
    assert remainder_terms == [(0, 18), (1, 27)]
    dual_terms = bit_terms(two_dual, monomial_data[2][0])
    assert dual_terms == [
        (1, 27),
        (10, 31),
        (10, 41),
        (10, 43),
        (14, 31),
        (14, 41),
        (14, 43),
    ]
    dual_bytes = two_dual.to_bytes(
        max(1, (two_dual.bit_length() + 7) // 8), "little"
    )
    dual_hash = hashlib.sha256(dual_bytes).hexdigest()
    assert dual_hash == "19adb92126a6c8f844cb7d4b217e7a099dadbd4cfe0025cea2ea0b4419e60478"

    # Exact filtered cancellation of 4 through degree three leaves only
    # q-order at least four, which is zero in B=P/(I+q^4).
    four_residual = audit.cancel_exact(
        {(): 4}, 2, monomial_data[2][1], basis2
    )
    four_residual = audit.cancel_exact(
        four_residual, 3, monomial_data[3][1], basis3
    )
    assert not four_residual

    graded_dimensions = (
        1,
        46 - len(basis1),
        1081 - len(basis2),
        17296 - len(basis3),
    )
    assert graded_dimensions == (1, 15, 107, 509)
    assert sum(graded_dimensions) == 632

    print("2 NONMEMBER modulo I+q^4")
    print("2 degree-two remainder", remainder_terms)
    print(
        "2 dual support/hash",
        len(dual_terms),
        dual_hash,
        "rows_checked",
        len(candidates2),
    )
    print("4 MEMBER modulo I+q^4")
    print("c112-c121 NONMEMBER; coproduct is noncocommutative")
    print("graded dimensions", graded_dimensions, "length", sum(graded_dimensions))
    print("VERDICT characteristic(B)=4; |B|=2^632")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("export", help="integral branch-0 M2 export")
    run(parser.parse_args().export)
