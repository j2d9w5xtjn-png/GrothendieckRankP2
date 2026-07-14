#!/usr/bin/env python3
"""Extract a sparse noncocommutative alpha_2 x mu_2 deformation.

The base is R_N=Z[pi]/(pi^2-2,pi^N).  The full 45-parameter bialgebra system
from order4sat.build is used, the special coproduct is pinned to
alpha_2 x mu_2, and noncocommutativity is required.  Lexicographic objectives
minimize deviations first from the tensor product of the alpha-type
Oort--Tate group (a=b=pi) and mu_2, then at the raw bit level.

At N=4 the query is UNSAT.  At N=5 it is SAT and gives a compact explicit
noncommutative deformation; the separate [4]!=e query remains UNSAT.
"""

import argparse

from z3 import BitVec, Extract, If, Optimize, Or, Sum, sat

from explicit_bilinear_ramified_sat import RamifiedQuadratic
from order4sat import build


def c_number(i, j, k):
    return (i - 1) * 9 + (j - 1) * 3 + k


def d_entries():
    number = 28
    out = []
    for i in range(1, 4):
        for j in range(i, 4):
            for k in range(1, 4):
                out.append((i, j, k, number))
                number += 1
    return out


def model_pair(model, value):
    return tuple(model.eval(part, model_completion=True).as_long() for part in value)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=5)
    parser.add_argument("--timeout-ms", type=int, default=300000)
    args = parser.parse_args()

    R = RamifiedQuadratic(args.n)
    base, _anti, _p4nz, ncc = build(R, {(1, 2, 3): 1}, with_antipode=False)
    solver = Optimize()
    solver.set(timeout=args.timeout_ms)
    solver.add(*base, ncc)

    # Full tensor-OT coproduct baseline.  Missing entries are zero.
    c_expected = {
        (1, 1, 1): R.neg(R.pi()),
        (2, 2, 2): R.integer(1),
        (3, 1, 2): R.integer(1),
        (3, 2, 1): R.integer(1),
        (3, 3, 2): R.integer(1),
        (3, 2, 3): R.integer(1),
        (3, 3, 1): R.neg(R.pi()),
        (3, 1, 3): R.neg(R.pi()),
        (3, 3, 3): R.neg(R.pi()),
    }
    c_total = {}
    c_deformed = []
    raw_nonzero = []
    fiber_ones = {(2, 2, 2), (3, 1, 2), (3, 2, 1), (3, 3, 2), (3, 2, 3)}
    for i in range(1, 4):
        for j in range(1, 4):
            for k in range(1, 4):
                number = c_number(i, j, k)
                value = (
                    BitVec(f"c{i}{j}{k}_{number}_a", R.wa),
                    BitVec(f"c{i}{j}{k}_{number}_b", R.wb),
                )
                c_total[(i, j, k)] = value
                expected = c_expected.get((i, j, k), R.zero())
                # Pin only the residue, leaving every higher correction free.
                solver.add(Extract(0, 0, value[0]) == (1 if (i, j, k) in fiber_ones else 0))
                c_deformed.append(If(R.neq0(R.sub(value, expected)), 1, 0))
                raw_nonzero.extend(If(part != 0, 1, 0) for part in value)

    # Tensor-OT multiplication baseline in basis 1,x,y,z=xy.
    m_expected = {
        (1, 1, 1): R.pi(),
        (1, 2, 3): R.integer(1),
        (1, 3, 3): R.pi(),
        (2, 2, 2): R.integer(-2),
        (2, 3, 3): R.integer(-2),
        (3, 3, 3): R.mul(R.integer(-2), R.pi()),
    }
    m_total = {}
    m_deformed = []
    for i, j, k, number in d_entries():
        raw = (
            BitVec(f"d{i}{j}{k}_{number}_a", R.wa),
            BitVec(f"d{i}{j}{k}_{number}_b", R.wb),
        )
        fiber = R.integer(1 if (i, j, k) == (1, 2, 3) else 0)
        value = R.add(fiber, R.mul(R.pi(), raw))
        m_total[(i, j, k)] = value
        expected = m_expected.get((i, j, k), R.zero())
        m_deformed.append(If(R.neq0(R.sub(value, expected)), 1, 0))
        raw_nonzero.extend(If(part != 0, 1, 0) for part in raw)

    solver.minimize(Sum(*m_deformed))
    solver.minimize(Sum(*c_deformed))
    solver.minimize(Sum(*raw_nonzero))
    result = solver.check()
    print("result", result)
    if result != sat:
        return
    model = solver.model()
    print("multiplication deviations from tensor OT", model.eval(Sum(*m_deformed)))
    print("coproduct deviations from tensor OT", model.eval(Sum(*c_deformed)))
    print("multiplication table (nonzero entries)")
    for key, value in sorted(m_total.items()):
        concrete = model_pair(model, value)
        if concrete != (0, 0):
            print(" ", key, concrete)
    print("coproduct I tensor I coefficients (nonzero entries)")
    for key, value in sorted(c_total.items()):
        concrete = model_pair(model, value)
        if concrete != (0, 0):
            print(" ", key, concrete)
if __name__ == "__main__":
    main()
