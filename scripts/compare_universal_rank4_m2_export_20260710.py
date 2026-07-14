#!/usr/bin/env python3
"""Compare an exact M2 polynomial export with the independent Python chart.

Generate the mixed alpha2^2 export by setting RANK4_BRANCH=0,
RANK4_INTEGRAL=1, and RANK4_EXPORT_POLYS=1 when running
m2/universal_local_rank4.m2.

The Macaulay2 source prints fully expanded integer polynomials.  This auditor
parses that independent output, truncates only after complete integer sums
have been read, and compares every coefficient through deformation degree
three with audit_universal_rank4_quadratic.py.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re

from audit_universal_rank4_quadratic import build_chart


VARIABLE = re.compile(r"p_(\d+)(?:\^(\d+))?$")


def parse_polynomial(source: str):
    source = source.strip()
    if source == "0":
        return {}
    normalized = source.replace("-", "+-")
    answer = {}
    for raw_term in normalized.split("+"):
        if not raw_term:
            continue
        coefficient = -1 if raw_term.startswith("-") else 1
        if raw_term.startswith("-"):
            raw_term = raw_term[1:]
        variables = []
        for factor in raw_term.split("*"):
            if not factor:
                continue
            match = VARIABLE.fullmatch(factor)
            if match:
                index = int(match.group(1))
                exponent = int(match.group(2) or "1")
                variables.extend([index] * exponent)
            else:
                coefficient *= int(factor)
        monomial = tuple(sorted(variables))
        answer[monomial] = answer.get(monomial, 0) + coefficient
        if answer[monomial] == 0:
            del answer[monomial]
    return answer


def truncate(polynomial, degree=3):
    return {
        monomial: coefficient
        for monomial, coefficient in polynomial.items()
        if len(monomial) <= degree and coefficient
    }


def canonical_payload(equations, targets):
    def encode(polynomial):
        return [
            [list(monomial), coefficient]
            for monomial, coefficient in sorted(polynomial.items())
        ]

    return {
        "equations": [encode(polynomial) for polynomial in equations],
        "targets": [encode(polynomial) for polynomial in targets],
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("export")
    args = parser.parse_args()

    equations = {}
    targets = {}
    with open(args.export, encoding="utf-8") as handle:
        for line in handle:
            if line.startswith("E "):
                _, index, polynomial = line.rstrip("\n").split(" ", 2)
                equations[int(index)] = truncate(parse_polynomial(polynomial))
            elif line.startswith("T "):
                _, index, polynomial = line.rstrip("\n").split(" ", 2)
                targets[int(index)] = truncate(parse_polynomial(polynomial))

    if sorted(equations) != list(range(189)):
        raise AssertionError(f"expected equation indices 0..188, got {sorted(equations)}")
    if sorted(targets) != list(range(9)):
        raise AssertionError(f"expected target indices 0..8, got {sorted(targets)}")

    exported_equations = [equations[index] for index in range(189)]
    exported_targets = [targets[index] for index in range(9)]
    chart = build_chart(0)

    if exported_equations != chart.equations_z:
        mismatches = [
            index
            for index, (left, right) in enumerate(
                zip(exported_equations, chart.equations_z)
            )
            if left != right
        ]
        raise AssertionError(f"equation mismatch at indices {mismatches[:20]}")
    if exported_targets != chart.targets_z:
        mismatches = [
            index
            for index, (left, right) in enumerate(
                zip(exported_targets, chart.targets_z)
            )
            if left != right
        ]
        raise AssertionError(f"target mismatch at indices {mismatches}")

    encoded = json.dumps(
        canonical_payload(exported_equations, exported_targets),
        sort_keys=True,
        separators=(",", ":"),
    ).encode()
    print("M2/Python exact coefficient comparison through degree 3: PASS")
    print("equations=189 targets=9 branch=alpha2^2 mode=mixed")
    print("canonical jet SHA-256", hashlib.sha256(encoded).hexdigest())


if __name__ == "__main__":
    main()
