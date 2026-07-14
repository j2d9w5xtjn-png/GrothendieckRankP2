#!/usr/bin/env python3
r"""t^4 normal-form search on W(F_8)[pi]/(pi^2-2,pi^3).

For every killed-by-two t^4 Hopf fiber over a perfect field, the reduced
coproduct is, in a suitable basis, the two-parameter (c1,c4) normal form used
in THEORY_order4.md 12.3/14.9.  Here c1 and c4 are left as arbitrary F_8
variables while every higher deformation digit remains free.  This replaces
27 arbitrary residue coproduct coefficients by six residue bits without
discarding an isomorphism class.
"""

import sys

from z3 import BitVec, BitVecVal, ZeroExt, set_param

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat import Rram, fresh, run
from order4sat_f8 import Ext3


T4_MULT = {(1, 1, 2): 1, (1, 2, 3): 1}


class T4NormalFormRing:
    def __init__(self, ring):
        self.R = ring
        self.name = ring.name + " [t4 killed-2 normal form c1,c4]"
        self.c1 = self._residue_var("fiber_c1")
        self.c4 = self._residue_var("fiber_c4")
        self.c1sq = ring.mul(self.c1, self.c1)

    def _residue_var(self, tag):
        nm = fresh(tag)
        # Ext3(Rram): three polynomial-basis coefficients; each coefficient
        # is a+b*pi with a mod 4, b mod 2.  A residue-field lift has one free
        # low bit in a and zero in every other digit.
        return tuple((ZeroExt(1, BitVec(nm + f"_{i}", 1)), BitVecVal(0, 1))
                     for i in range(3))

    def __getattr__(self, key):
        return getattr(self.R, key)

    def var(self, tag):
        if len(tag) == 4 and tag[0] == "c" and tag[1:].isdigit():
            key = tuple(map(int, tag[1:]))
            if key in {(1, 1, 2), (1, 2, 1)}:
                target = self.c1
            elif key in {(1, 2, 3), (1, 3, 2)}:
                target = self.c1sq
            elif key == (1, 2, 2):
                target = self.c4
            elif key in {(3, 1, 2), (3, 2, 1)}:
                target = self.R.one()
            elif key in {(3, 2, 3), (3, 3, 2)}:
                target = self.c1
            else:
                target = self.R.zero()
            return self.R.add(target, self.R.deform(tag))
        return self.R.var(tag)


if __name__ == "__main__":
    set_param("parallel.enable", True)
    R = T4NormalFormRing(Ext3(Rram()))
    run(R, "all killed-by-2 t^4 fibers over F_8", T4_MULT, use_fiber2=True)
    print("DONE order4sat_f8ram_t4_normalform_20260709", flush=True)
