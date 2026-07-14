#!/usr/bin/env python3
"""Split-xy-fiber searches on the unresolved ramified F_8 length-3 base."""

import argparse
import sys

from z3 import set_param

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat import Rram, run
from order4sat_f8 import Ext3
from order4sat_ramified_embdim2_len6_20260709 import PinCoproductResidue, XY_MULT


MODELS = {
    "a2a2": {(3, 1, 2): 1, (3, 2, 1): 1},
    "W2F": {(2, 1, 1): 1, (3, 1, 2): 1, (3, 2, 1): 1},
    "mu2mu2": {
        (1, 1, 1): 1, (2, 2, 2): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
    "mu2a2": {
        (1, 1, 1): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
    },
    # The last two are the nonsplit F_2-rational forms of mu2^2.  They are
    # geometrically split but are not F_2-isomorphic to any of the four rows
    # above, so exact F_2 searches must include them separately.
    "mu2mu2_unipotent": {
        (1, 1, 1): 1, (1, 2, 2): 1, (1, 2, 3): 1,
        (1, 3, 2): 1, (1, 3, 3): 1,
        (2, 2, 2): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
    "mu2mu2_irreducible": {
        (1, 2, 2): 1, (1, 1, 3): 1, (1, 3, 1): 1, (1, 3, 3): 1,
        (2, 1, 1): 1, (2, 2, 2): 1,
        (2, 1, 3): 1, (2, 3, 1): 1,
        (2, 2, 3): 1, (2, 3, 2): 1, (2, 3, 3): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
}


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", choices=tuple(MODELS) + ("all",), default="mu2a2")
    args = ap.parse_args()
    set_param("parallel.enable", True)
    base = Ext3(Rram())
    names = tuple(MODELS) if args.model == "all" else (args.model,)
    for name in names:
        R = PinCoproductResidue(base, MODELS[name])
        run(R, f"{name} over F_8 (xy algebra)", XY_MULT, use_fiber2=True)
    print("DONE order4sat_f8ram_alpha2mu2_pinned_20260709", flush=True)
