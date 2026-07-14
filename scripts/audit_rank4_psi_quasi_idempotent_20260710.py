#!/usr/bin/env python3
"""Exact filtered certificate for psi^2=2 psi on the universal cubic base."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path.cwd()))

import scripts.audit_universal_rank4_quadratic as audit


def main() -> None:
    chart = audit.build_chart(0)
    differences = []
    for i in range(1, 4):
        for r in range(1, 4):
            target = chart.targets_z[3 * (i - 1) + (r - 1)]
            twice_phi = audit.mul(audit.const(2), chart.phi_z[i][r])
            differences.append(audit.add(target, twice_phi, -1))

    test_chart = audit.Chart(
        chart.name,
        chart.equations_z,
        chart.equations_f2,
        differences,
        chart.phi_z,
    )
    report = audit.audit_filtered_degree3(test_chart, "mixed")
    verdicts = [
        row["member_through_degree3"]
        for row in report["filtered_degree3_targets"]
    ]
    remainders = [
        row["cubic_remainder_terms"]
        for row in report["filtered_degree3_targets"]
    ]
    assert verdicts == [True] * 9
    assert remainders == [[] for _ in range(9)]
    print("degree2 rank", report["filtered_degree2_rank"])
    print("degree3 candidates/rank", report["filtered_degree3_candidate_rows"],
          report["filtered_degree3_rank"])
    print("T_ir - 2 phi_i^r memberships", verdicts)
    print("cubic remainders", remainders)
    print("PASS: psi^2=2 psi in End_B(A), where psi=[2]^#-unit*epsilon")


if __name__ == "__main__":
    main()
