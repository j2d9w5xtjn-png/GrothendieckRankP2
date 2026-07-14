#!/usr/bin/env python3
"""order4sat_f8nofib.py -- the F_8 analogue of Theorem B' (HANDOFF §B.0b).

Theorem B' (order4sat --nofiber2, complete 2026-07-08) removed the
"fiber killed by 2" hypothesis over the six length-3 rings with residue
field F_2 and F_4.  The residue-field-F_8 rings have so far been run with
fiber2=True only (order4sat_f8.py), except the ramified one, whose
no-fiber2 pass is already inside order4sat_f8ram.py.  This script supplies
the two missing no-fiber2 runs:

    W(F_8)/8       ==  Ext3(Z8)
    F_8[eps]/eps^3 ==  Ext3(F2eps3)

All 12 (ring, fiber) queries UNSAT here + in f8ram would give the F_8
analogue of Theorem B', making the F_8 case unconditional on the fiber.

Both ring classes are ringcheck.py-validated (no ring class added or
edited here -- golden rule 1b satisfied by inheritance).  Level-1 sanity
(expect sat) is built into run().

Run:  <z3venv>/bin/python scripts/order4sat_f8nofib.py
NOTE: the 512-element F_8 rings are the slowest bases in the project;
launch only when the box has spare cores.
"""
from z3 import set_param

from order4sat import Z8, F2eps3, run
from order4sat_f8 import Ext3

if __name__ == "__main__":
    set_param("parallel.enable", True)
    fibs = [("F_q[x,y]/(x^2,y^2)", {(1, 2, 3): 1}),
            ("F_q[t]/t^4", {(1, 1, 2): 1, (1, 2, 3): 1})]
    for R in [Ext3(Z8()), Ext3(F2eps3())]:
        for fn, fib in fibs:
            run(R, fn, fib, use_fiber2=False)
    print("DONE order4sat_f8nofib", flush=True)
