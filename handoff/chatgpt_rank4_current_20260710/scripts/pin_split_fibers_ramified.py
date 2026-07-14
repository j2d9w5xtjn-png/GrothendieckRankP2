#!/usr/bin/env python3
"""Exact full-bialgebra tests for the four split xy fibers over ramified R_N.

Pinning is implemented in the ring representation itself: when order4sat asks
for a coproduct coefficient ``cijk``, ``PinnedRamified.var`` returns the chosen
residue coefficient plus pi times a fresh variable.  Thus the computation does
not depend on guessing Z3's generated symbol names.
"""

import argparse

from z3 import Solver, unknown

from explicit_bilinear_ramified_sat import RamifiedEisenstein, RamifiedQuadratic
from order4sat import build


CASES = {
    "a2a2": {(3, 1, 2), (3, 2, 1)},
    "W2F": {(2, 1, 1), (3, 1, 2), (3, 2, 1)},
    "mu2mu2": {
        (1, 1, 1),
        (2, 2, 2),
        (3, 1, 2),
        (3, 2, 1),
        (3, 1, 3),
        (3, 3, 1),
        (3, 2, 3),
        (3, 3, 2),
        (3, 3, 3),
    },
    "mu2a2": {(1, 1, 1), (3, 1, 2), (3, 2, 1), (3, 1, 3), (3, 3, 1)},
}


class PinnedRamified(RamifiedQuadratic):
    def __init__(self, N, pins, case):
        super().__init__(N)
        self.pins = pins
        self.case = case
        self.name += f" [{case}]"

    def _raw_var(self, tag):
        return super().var(tag)

    def var(self, tag):
        if len(tag) == 4 and tag[0] == "c" and tag[1:].isdigit():
            key = tuple(int(character) for character in tag[1:])
            residue = self.integer(1 if key in self.pins else 0)
            return self.add(residue, self.mul(self.pi(), self._raw_var(tag + "lift")))
        return self._raw_var(tag)

    def deform(self, tag):
        return self.mul(self.pi(), self._raw_var(tag))


class PinnedEisenstein(RamifiedEisenstein):
    def __init__(self, N, e, alpha_r, pins, case):
        super().__init__(N, e, alpha_r)
        self.pins = pins
        self.case = case
        self.name += f" [{case}]"

    def _raw_var(self, tag):
        return super().var(tag)

    def var(self, tag):
        if len(tag) == 4 and tag[0] == "c" and tag[1:].isdigit():
            key = tuple(int(character) for character in tag[1:])
            residue = self.integer(1 if key in self.pins else 0)
            return self.add(residue, self.mul(self.pi(), self._raw_var(tag + "lift")))
        return self._raw_var(tag)

    def deform(self, tag):
        return self.mul(self.pi(), self._raw_var(tag))


def check(base, extras, timeout_ms):
    solver = Solver()
    solver.set(timeout=timeout_ms)
    solver.add(*base, *extras)
    return solver.check()


def run(N, case, timeout_ms, e=2, alpha_r=1, only="all"):
    R = (
        PinnedRamified(N, CASES[case], case)
        if e == 2
        else PinnedEisenstein(N, e, alpha_r, CASES[case], case)
    )
    base, _anti, p4nz, ncc = build(R, {(1, 2, 3): 1}, with_antipode=False)
    gate = check(base, [], timeout_ms)
    noncomm = check(base, [ncc], timeout_ms) if only in ("all", "noncomm") else "skipped"
    p4 = check(base, [p4nz], timeout_ms) if only in ("all", "p4") else "skipped"
    both = "skipped"
    if p4 == unknown:
        both = check(base, [ncc, p4nz], timeout_ms)
    print(
        f"N={N} case={case}: gate={gate}; noncomm={noncomm}; [4]!=e={p4}; noncomm+[4]!=e={both}",
        flush=True,
    )


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=5)
    parser.add_argument("--case", choices=list(CASES) + ["all"], default="all")
    parser.add_argument("--timeout-ms", type=int, default=300000)
    parser.add_argument("--e", type=int, default=2)
    parser.add_argument("--alpha-r", type=int, default=1)
    parser.add_argument("--only", choices=("all", "p4", "noncomm"), default="all")
    args = parser.parse_args()
    cases = CASES if args.case == "all" else (args.case,)
    for case in cases:
        run(args.n, case, args.timeout_ms, e=args.e, alpha_r=args.alpha_r, only=args.only)


if __name__ == "__main__":
    main()
