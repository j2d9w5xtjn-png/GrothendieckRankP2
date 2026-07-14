#!/usr/bin/env python3
"""Evaluate the universal 189 equations on the explicit length-10 base.

This is a cross-check complementary to
``verify_rank4_length10_counterexample_20260710.py``: that program verifies
the Hopf identities directly, whereas this one parses the independent exact
Macaulay2 export and substitutes the displayed 45 parameter values.
"""

from __future__ import annotations

import argparse

import independent_audit_mixed_a2a2_export as universal
import verify_rank4_length10_counterexample_20260710 as example


def monomial_value(monomial: tuple[int, ...], values: list[example.R]) -> example.R:
    out = example.ONE
    for variable in monomial:
        out = example.rmul(out, values[variable])
    return out


def polynomial_value(poly: universal.Poly, values: list[example.R]) -> example.R:
    out = example.ZERO
    for monomial, coefficient in poly.items():
        out = example.radd(
            out, example.rscale(coefficient, monomial_value(monomial, values))
        )
    return out


def parameter_values() -> list[example.R]:
    values = [example.ZERO for _ in range(45)]
    xs = example.radd(example.XSTAR, example.DSTAR)
    yz = example.radd(example.Y, example.Z)
    table = {
        0: example.X,
        1: example.Y,
        8: example.X,
        10: example.Z,
        14: example.Z,
        17: example.XSTAR,
        18: example.X,
        21: yz,
        24: xs,
        30: example.D,
        31: yz,
        32: xs,
        38: example.X,
        39: example.radd((2, 0, 0, 0), example.YSTAR),
        40: xs,
        41: example.SOCLE,
        42: example.radd(example.X, example.D),
        43: example.radd(yz, example.SOCLE),
        44: xs,
    }
    for index, value in table.items():
        values[index] = value
    return values


def run(export_path: str) -> None:
    equations, targets = universal.read_export(export_path)
    values = parameter_values()
    equation_values = [polynomial_value(equation, values) for equation in equations]
    target_values = [polynomial_value(target, values) for target in targets]
    assert len(equations) == 189 and all(value == example.ZERO for value in equation_values)
    assert target_values == [
        example.ZERO,
        example.ZERO,
        example.SOCLE,
        example.ZERO,
        example.ZERO,
        example.ZERO,
        example.ZERO,
        example.ZERO,
        example.ZERO,
    ]
    print("UNIVERSAL SPECIALIZATION PASS: 189/189 equations vanish")
    print("TARGETS PASS: [0,0,s,0,0,0,0,0,0], s=2Z!=0")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("export", help="integral branch-0 M2 polynomial export")
    run(parser.parse_args().export)
