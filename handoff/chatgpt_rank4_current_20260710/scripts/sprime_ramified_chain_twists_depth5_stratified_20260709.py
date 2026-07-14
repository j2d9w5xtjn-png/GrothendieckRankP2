#!/usr/bin/env python3
"""Fiber-stratified S' queries on the four e=2 length-five chain carries."""

import argparse
import itertools
import sys

from z3 import set_param

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_chain_twists_len5_20260709 import TwistedChainLen5, ring_gates
from order4sat_ramified_towers_20260709 import value
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT, XY_MULT, run_model, t4_pins,
)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--xy-models", nargs="+", choices=tuple(XY_MODELS),
                    default=tuple(XY_MODELS))
    ap.add_argument("--skip-t4", action="store_true")
    args = ap.parse_args()
    set_param("parallel.enable", True)

    grand = []
    for c, d in itertools.product((0, 1), repeat=2):
        base = TwistedChainLen5(c, d)
        print(f"===== S' STRATIFIED base {base.name} =====", flush=True)
        ring_gates(base)
        p = base.concrete(0, 1)
        els = base.elements()
        ann = [x for x in els if value(base.mul(p, x)) == value(base.zero())]
        assert len(ann) == 2
        for name in args.xy_models:
            pins = XY_MODELS[name]
            label = f"xy/{name}"
            grand.append((c, d, label, run_model(
                base, p, ann, XY_MULT, pins, label, args.timeout)))
        if not args.skip_t4:
            for c1, c4 in itertools.product((0, 1), repeat=2):
                label = f"t4/c1={c1},c4={c4}"
                grand.append((c, d, label, run_model(
                    base, p, ann, T4_MULT, t4_pins(c1, c4), label, args.timeout)))

    print("===== CHAIN-TWIST STRATIFIED SUMMARY =====", flush=True)
    for c, d, label, ans in grand:
        print(f"  R({c},{d}) {label}: {ans}", flush=True)
    print("DONE sprime_ramified_chain_twists_depth5_stratified_20260709", flush=True)


if __name__ == "__main__":
    main()
