#!/usr/bin/env python3
"""Memory-bounded full-deformation search on the missing F_8 ``xy`` form.

The exact orbit audit in ``f8_xy_semilinear_orbits_20260710.py`` finds one
F_8-rational killed-by-two Hopf fiber not represented by the six F_2-defined
pins used previously.  Its restricted-Lie semilinear matrix is

                         [[0, 1],
                          [1, w]].

This script pins precisely that residue coproduct over
W(F_8)[pi]/(pi^2-2,pi^3), while leaving every higher multiplication and
coproduct digit free.  It asks first for a bialgebra sanity point and then
for [4]^# != e.  A SAT main result is checked again with a literal antipode.

Z3 parallelism is disabled and ``memory_max_size`` is set before construction.
An ``unknown`` (including timeout or memory exhaustion) has no mathematical
polarity.
"""

from __future__ import annotations

import argparse
import gc
import resource
import sys
import time

from z3 import BitVecVal, Solver, sat, set_param

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from f8_xy_semilinear_orbits_20260710 import (
    KNOWN,
    enumerate_orbits,
    finite_hopf_gates,
    matrix_to_coproduct,
)
from order4sat import Rram, build
from order4sat_f8 import Ext3
from order4sat_ramified_embdim2_len6_20260709 import XY_MULT


MISSING_MATRIX = (0, 1, 1, 2)  # 2 is w in the polynomial-basis encoding.


def rss_mib():
    n = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    # macOS reports bytes; Linux reports KiB.
    return n / (1024 * 1024) if sys.platform == "darwin" else n / 1024


class F8ResiduePin:
    """Fix each c_ijk modulo the maximal ideal to an arbitrary F_8 value."""

    def __init__(self, ring, residue_c):
        self.R = ring
        self.residue_c = residue_c
        self.name = ring.name + " [F8 missing xy orbit pinned]"

    def __getattr__(self, key):
        return getattr(self.R, key)

    def residue_lift(self, value):
        # Ext3(Rram) polynomial coordinates 1,w,w^2.  A Teichmueller lift is
        # unnecessary: any coefficientwise lift with the right residue works,
        # because all higher digits are supplied independently by deform().
        return tuple(
            (BitVecVal((value >> i) & 1, 2), BitVecVal(0, 1))
            for i in range(3)
        )

    def var(self, tag):
        if len(tag) == 4 and tag[0] == "c" and tag[1:].isdigit():
            key = tuple(map(int, tag[1:]))
            z = self.residue_lift(self.residue_c.get(key, 0))
            return self.R.add(z, self.R.deform(tag))
        return self.R.var(tag)


def check(label, constraints, extra, timeout_ms):
    solver = Solver()
    solver.set("timeout", timeout_ms)
    solver.add(*constraints)
    solver.add(*extra)
    started = time.monotonic()
    verdict = solver.check()
    elapsed = time.monotonic() - started
    reason = solver.reason_unknown() if str(verdict) == "unknown" else ""
    print(
        f"{label}: {verdict} elapsed={elapsed:.2f}s "
        f"max_rss={rss_mib():.1f}MiB reason={reason or '-'}",
        flush=True,
    )
    return verdict, solver


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--timeout", type=int, default=900, help="seconds per query")
    ap.add_argument("--memory-mb", type=int, default=1536, help="Z3 hard memory ceiling")
    ap.add_argument("--sanity-only", action="store_true")
    args = ap.parse_args()
    assert args.timeout > 0 and args.memory_mb >= 256

    set_param("parallel.enable", False)
    set_param("memory_max_size", args.memory_mb)
    print(
        f"CONFIG single_threaded=true timeout={args.timeout}s "
        f"z3_memory_max={args.memory_mb}MiB",
        flush=True,
    )

    # Recompute the exact classification gate, rather than trusting a label.
    orbits = enumerate_orbits()
    owner = {A: i for i, O in enumerate(orbits) for A in O}
    known = {owner[A] for A in KNOWN.values()}
    missing = [i for i in range(len(orbits)) if i not in known]
    assert missing == [owner[MISSING_MATRIX]]
    assert MISSING_MATRIX in orbits[missing[0]]
    pins = finite_hopf_gates(MISSING_MATRIX)
    print(
        f"GATE orbit_count={len(orbits)} missing_orbits={missing} "
        f"missing_orbit_size={len(orbits[missing[0]])} finite_hopf=[2]=0 passed",
        flush=True,
    )
    print(f"PIN_MATRIX {MISSING_MATRIX}", flush=True)
    print(f"PIN_TABLE {sorted(pins.items())}", flush=True)

    R = F8ResiduePin(Ext3(Rram()), pins)
    started = time.monotonic()
    # Keep the expensive antipode variables/identities out of H0 and MAIN.
    # A finite flat bialgebra seed is rebuilt with a literal antipode only if
    # MAIN is SAT.  This materially lowers the live expression DAG and makes
    # the overwhelmingly likely UNSAT/UNKNOWN path the memory-cheapest one.
    base, _anti, p4nz, _ncc = build(R, XY_MULT, with_antipode=False)
    print(
        f"BUILT base_constraints={len(base)} antipode_constraints_deferred=true "
        f"elapsed={time.monotonic()-started:.2f}s max_rss={rss_mib():.1f}MiB",
        flush=True,
    )

    sanity, solver = check(
        "H0 bialgebra+fiber2 sanity", base, (), args.timeout * 1000
    )
    if sanity != sat:
        print("STOP sanity did not return SAT; no mathematical verdict", flush=True)
        return 2
    del solver
    gc.collect()
    if args.sanity_only:
        print("DONE sanity-only", flush=True)
        return 0

    main_verdict, solver = check(
        "MAIN bialgebra+[4]!=e", base, (p4nz,), args.timeout * 1000
    )
    if main_verdict == sat:
        del solver
        del base, p4nz, R
        gc.collect()
        print("POSTCHECK rebuilding with literal antipode constraints", flush=True)
        R = F8ResiduePin(Ext3(Rram()), pins)
        base, anti, p4nz, _ncc = build(R, XY_MULT, with_antipode=True)
        hopf, solver = check(
            "POSTCHECK Hopf+[4]!=e", base, (p4nz, *anti), args.timeout * 1000
        )
        if hopf == sat:
            print("COUNTEREXAMPLE_CANDIDATE SAT; export and independently verify model", flush=True)
        else:
            print("BIALGEBRA_SEED_ONLY: antipode postcheck was not SAT", flush=True)
    elif str(main_verdict) == "unsat":
        print("EXACT RESULT: no [4]-defect in the missing F8 xy stratum", flush=True)
    else:
        print("OPEN RESULT: timeout/memory/unknown has no mathematical polarity", flush=True)
    print("DONE order4sat_f8ram_xy_missing_orbit_20260710", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
