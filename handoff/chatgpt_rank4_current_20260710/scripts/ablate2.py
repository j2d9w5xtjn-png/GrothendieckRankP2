#!/usr/bin/env python3
"""
ablate2.py -- follow-up to ablate.py (session 3): minimal axiom sets.

ablate.py showed over F2[eps]/eps^3 (both fibers): each of A+M+F, M+C+F, A+M+C
forces [4]^# = 0, while A+C+F does not (Delta-multiplicativity M is
load-bearing).  This run descends the lattice below M:

  q1: M alone      + [4]!=0
  q2: M+F          + [4]!=0
  q3: M+A          + [4]!=0
  q4: M+C          + [4]!=0

An `unsat` at q1 would mean: multiplicativity of a counital Delta with respect
to ANY commutative (not even associative) deformed product of the given fiber
shape already forces [4]^# = 0 at length 3 -- the sharpest possible target for
a hand proof.  Gates: reproduce gate1 (A+M+C+F + [4]!=0 -> unsat) once per
fiber to validate bookkeeping.
"""
from ablate import F2eps3, build_blocks, check
from z3 import set_param

if __name__ == "__main__":
    set_param("parallel.enable", True)
    R = F2eps3()
    fibs = [("F_q[x,y]/(x^2,y^2)", {(1,2,3):1}),
            ("F_q[t]/t^4", {(1,1,2):1, (1,2,3):1})]
    for fn, fib in fibs:
        print(f"===== base {R.name}, fiber {fn} =====", flush=True)
        A, M, C, F, p4nz = build_blocks(R, fib)
        check("gate1: A+M+C+F + [4]!=0", A+M+C+F+[p4nz], expect="unsat")
        check("q1: M     + [4]!=0", M+[p4nz])
        check("q2: M+F   + [4]!=0", M+F+[p4nz])
        check("q3: M+A   + [4]!=0", M+A+[p4nz])
        check("q4: M+C   + [4]!=0", M+C+[p4nz])
    print("DONE ablate2", flush=True)
