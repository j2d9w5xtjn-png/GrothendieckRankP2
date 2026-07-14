#!/usr/bin/env python3
"""S' on a ramified type-two h=(1,2,2) length-five quotient."""

import argparse
import itertools
import sys

from z3 import set_param

sys.path.insert(0, __file__.rsplit("/",1)[0])
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_embdim2_len6_20260709 import RamifiedThickening, validate
from sprime_ramified_nonprincipal_depth5_stratified_20260709 import (
    residual_syzygy_basis, run_model,
)
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT, XY_MULT, t4_pins,
)


def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--timeout",type=int,default=600)
    ap.add_argument("--unroll",action="store_true")
    args=ap.parse_args(); set_param("parallel.enable",True)
    # Q is the socle quotient of the length-six Gorenstein ring
    # O_{2,4}[u]/(pi^2u,u^2-pi^2).
    Q=RamifiedThickening(N=3,L=2,theta_degree=2)
    print(f"===== S' h=(1,2,2) quotient {Q.name} =====",flush=True)
    validate(Q)
    pi=(Q.O.monomial(1),Q.M.zero()); u=(Q.O.zero(),Q.M.one())
    gens=[pi,u]
    _,basis=residual_syzygy_basis(Q,gens)
    results=[]
    for name,pins in XY_MODELS.items():
        results.append((f"xy/{name}",run_model(
            Q,gens,basis,XY_MULT,pins,f"xy/{name}",args.timeout,
            unroll=args.unroll)))
    for c1,c4 in itertools.product((0,1),repeat=2):
        label=f"t4/c1={c1},c4={c4}"
        results.append((label,run_model(
            Q,gens,basis,T4_MULT,t4_pins(c1,c4),label,args.timeout,
            unroll=args.unroll)))
    print("SUMMARY",flush=True)
    for label,out in results: print(f"  {label}: {','.join(map(str,out))}",flush=True)
    print("DONE sprime_length5_q122_ramified_20260709",flush=True)


if __name__=="__main__": main()
