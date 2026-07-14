#!/usr/bin/env python3
"""Exact S' queries on the three pure ramified principal length-five rings."""

import argparse
import sys

from z3 import set_param

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat_ramified_towers_20260709 import EisensteinTrunc, exhaustive_ring_gates
from sprime_ramified_length4_six_20260709 import run_principal


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--es", nargs="+", type=int, choices=(2, 3, 4), default=(2, 3, 4))
    ap.add_argument("--timeout", type=int, default=7200)
    args = ap.parse_args()
    set_param("parallel.enable", True)
    print("S' DEPTH-FIVE PRINCIPAL RAMIFIED SEARCH", flush=True)
    for e in args.es:
        R = EisensteinTrunc(e, 5)
        exhaustive_ring_gates(R)
        run_principal(R, R.pi(), args.timeout)
    print("DONE sprime_ramified_principal_depth5_20260709", flush=True)
