#!/usr/bin/env python3
r"""Fiber-stratified S' search on ramified principal rings.

This is equivalent to the unpinned query over residue F_2, but replaces the
27 arbitrary residue coproduct coefficients by the complete finite list of
six rational xy Hopf fibers and the four (c1,c4) t^4 normal forms.  All higher
base-ring digits of multiplication and coproduct remain free.
"""

import argparse
import itertools
import sys
import time

from z3 import Solver, sat, set_param

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_embdim2_len6_20260709 import PinCoproductResidue
from order4sat_ramified_towers_20260709 import EisensteinTrunc, exhaustive_ring_gates, value
from s2check import build_blocks, sp_constraints


XY_MULT = {(1, 2, 3): 1}
T4_MULT = {(1, 1, 2): 1, (1, 2, 3): 1}


def t4_pins(c1, c4):
    pins = {(3, 1, 2): 1, (3, 2, 1): 1}
    if c1:
        for key in ((1, 1, 2), (1, 2, 1), (1, 2, 3), (1, 3, 2),
                    (3, 2, 3), (3, 3, 2)):
            pins[key] = 1
    if c4:
        pins[(1, 2, 2)] = 1
    return pins


def solve(label, constraints, timeout):
    s = Solver()
    s.set("timeout", timeout * 1000)
    s.add(*constraints)
    t0 = time.monotonic()
    ans = s.check()
    print(f"    [{label}] -> {ans} ({time.monotonic()-t0:.2f}s)", flush=True)
    return ans


def run_model(base, p, ann, fib, pins, label, timeout):
    print(f"  --- {label} ---", flush=True)
    R = PinCoproductResidue(base, pins)
    A, M, C, F, phi, _, _ = build_blocks(R, fib)
    holds, fails = sp_constraints(R, phi, p, ann, "st")
    core = A + M + C + F
    s1 = solve("S1 axioms+fiber2+S'-HOLDS", core + [holds], timeout)
    if s1 != sat:
        raise RuntimeError(f"nonvacuity gate failed in {label}: {s1}")
    return solve("S2 axioms+fiber2+S'-FAILS", core + [fails], timeout)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--e", type=int, required=True)
    ap.add_argument("--N", type=int, default=5)
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--xy-models", nargs="+", choices=tuple(XY_MODELS),
                    default=tuple(XY_MODELS))
    ap.add_argument("--skip-t4", action="store_true")
    args = ap.parse_args()
    set_param("parallel.enable", True)

    base = EisensteinTrunc(args.e, args.N)
    exhaustive_ring_gates(base)
    p = base.pi()
    els = list(base.elements())
    ann = [x for x in els if value(base.mul(p, x)) == value(base.zero())]
    print(f"S' STRATIFIED base {base.name}; |ann(pi)|={len(ann)}", flush=True)

    results = []
    for name in args.xy_models:
        pins = XY_MODELS[name]
        results.append((f"xy/{name}", run_model(
            base, p, ann, XY_MULT, pins, f"xy split fiber {name}", args.timeout)))
    if not args.skip_t4:
        for c1, c4 in itertools.product((0, 1), repeat=2):
            name = f"t4/c1={c1},c4={c4}"
            results.append((name, run_model(
                base, p, ann, T4_MULT, t4_pins(c1, c4), name, args.timeout)))

    print("===== STRATIFIED SUMMARY =====", flush=True)
    for name, ans in results:
        print(f"  {name}: {ans}", flush=True)
    print("DONE sprime_ramified_principal_depth5_stratified_20260709", flush=True)


if __name__ == "__main__":
    main()
