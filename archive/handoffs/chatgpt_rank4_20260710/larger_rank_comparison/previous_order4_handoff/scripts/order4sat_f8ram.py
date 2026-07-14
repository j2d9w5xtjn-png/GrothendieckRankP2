#!/usr/bin/env python3
"""order4sat_f8ram.py -- the last length-3 base ring with residue field F_8.

Corollary C of REPORT_order4.md upgrades the SAT/ideal-membership results to
"every finite locally free group scheme of order 4 over an Artin local ring of
length <= 3 with residue field k is killed by 4", by classifying such rings:
for m^2 != 0 the maximal ideal is principal and R is one of

    k[eps]/eps^3,        W(k)/8,        W(k)[pi]/(pi^2 - 2, pi^3).

For k = F_2 and F_4 all three are already UNSAT (Theorem B).  For k = F_8,
`order4sat_f8.py` covers the first two (W(F_8)/8 and F_8[eps]/eps^3); this
script supplies the missing RAMIFIED one,

    W(F_8)[pi]/(pi^2 - 2, pi^3)  ==  Ext3(Rram),

for both fiber shapes, with and without the "fiber killed by 2" hypothesis.
Together with the other two, UNSAT here extends Corollary C to residue field F_8.

The base-ring arithmetic of Ext3(Rram) is machine-validated by `ringcheck.py`
(ring axioms, locality, m nilpotent, residue field F_8 via the minimal polynomial
of w reducing to an irreducible cubic mod m).

Run:  <z3venv>/bin/python scripts/order4sat_f8ram.py
"""
from z3 import set_param

from order4sat import Rram, run
from order4sat_f8 import Ext3

if __name__ == "__main__":
    set_param("parallel.enable", True)
    fibs = [("F_q[x,y]/(x^2,y^2)", {(1, 2, 3): 1}),
            ("F_q[t]/t^4", {(1, 1, 2): 1, (1, 2, 3): 1})]
    R = Ext3(Rram())
    for use_fiber2 in (True, False):
        for fn, fib in fibs:
            run(R, fn, fib, use_fiber2=use_fiber2)
    print("DONE order4sat_f8ram", flush=True)
