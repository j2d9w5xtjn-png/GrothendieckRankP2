#!/usr/bin/env python3
r"""S' on the mixed-characteristic square-zero length-five quotient.

R = Z/4[x,y,z]/(2x,2y,2z,(x,y,z)^2) has m=(2,x,y,z), m^2=0,
length 5 and 32 elements.  Since the four displayed generators are an F2
basis of m, Syz(2,x,y,z)=m^4=Soc(R)^4.  Socle shifts change neither division
nor kernel membership under fiber2, so there is no residual syzygy to quantify.
"""

import argparse
import itertools
import sys
import time

from z3 import And, BitVec, BitVecVal, Extract, Not, Or, Solver, sat, set_param

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat import fresh
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_embdim2_len6_20260709 import PinCoproductResidue
from order4sat_ramified_towers_20260709 import value
from sprime_ramified_length4_six_20260709 import in_kernel, module_div_eqs, sp_nonprincipal_holds
from sprime_ramified_principal_depth5_stratified_20260709 import T4_MULT, XY_MULT, t4_pins
from s2check import build_blocks


class MixedSquareZeroLength5:
    name = "Z/4[x,y,z]/(2x,2y,2z,(x,y,z)^2)"
    def zero(self):
        return (BitVecVal(0,2), BitVecVal(0,1), BitVecVal(0,1), BitVecVal(0,1))
    def one(self):
        return (BitVecVal(1,2), BitVecVal(0,1), BitVecVal(0,1), BitVecVal(0,1))
    def var(self, tag):
        n = fresh(tag)
        return (BitVec(n+"_a",2), BitVec(n+"_x",1),
                BitVec(n+"_y",1), BitVec(n+"_z",1))
    def add(self, u, v):
        return (u[0]+v[0], u[1]^v[1], u[2]^v[2], u[3]^v[3])
    def sub(self, u, v):
        return (u[0]-v[0], u[1]^v[1], u[2]^v[2], u[3]^v[3])
    def mul(self, u, v):
        a, x, y, z = u; b, X, Y, Z = v
        al, bl = Extract(0,0,a), Extract(0,0,b)
        return (a*b, (al&X)^(x&bl), (al&Y)^(y&bl), (al&Z)^(z&bl))
    def eq0(self, u): return And(*[q==0 for q in u])
    def neq0(self, u): return Or(*[q!=0 for q in u])
    def lowzero(self, u): return Extract(0,0,u[0])==0
    def deform(self, tag):
        v=self.var(tag)
        return (BitVecVal(2,2)*v[0], v[1], v[2], v[3])
    def concrete(self,a,x,y,z):
        return (BitVecVal(a,2),BitVecVal(x,1),BitVecVal(y,1),BitVecVal(z,1))
    def elements(self):
        return [self.concrete(a,x,y,z) for a in range(4)
                for x,y,z in itertools.product((0,1),repeat=3)]


def ring_gate(R, gens):
    els=R.elements(); zero=R.zero(); one=R.one()
    for a,b,c in itertools.product(els,repeat=3):
        assert value(R.mul(a,one))==value(a)
        assert value(R.mul(a,b))==value(R.mul(b,a))
        assert value(R.mul(R.mul(a,b),c))==value(R.mul(a,R.mul(b,c)))
        assert value(R.mul(a,R.add(b,c)))==value(R.add(R.mul(a,b),R.mul(a,c)))
    m=[a for a in els if value(R.mul(a,a))==value(zero)]
    # Here m is exactly the 16-element square-zero ideal.
    assert len(m)==16 and all(value(R.mul(a,b))==value(zero) for a in m for b in m)
    assert {value(g) for g in gens} <= {value(a) for a in m}
    # A relation sum g_j a_j=0 depends only on the four residue coefficients.
    # Check that its kernel over F2 is zero; coefficients in m=Soc are then
    # exactly the full syzygy module Soc^4.
    for bits in itertools.product((0,1),repeat=4):
        total=zero
        for g,bit in zip(gens,bits):
            if bit: total=R.add(total,g)
        assert (value(total)==value(zero)) == (bits==(0,0,0,0))
    print("  [ring/syzygy gate] |R|=32, |m|=|Soc|=16, m^2=0, "
          "Syz(gens)=Soc^4 -> PASS",flush=True)


def fail_i(R,phi,gens,tag,i):
    vecs=[[R.var(f"{tag}_{i}_{j}_{r}") for r in range(3)] for j in range(4)]
    division=And(*module_div_eqs(R,phi[i],vecs,gens))
    # Socle shifts exhaust the remaining division coset and do not change
    # kernel membership, so this single representative is exact.
    return And(division, Not(And(*[in_kernel(R,phi,v) for v in vecs])))


def solve(label,constraints,timeout):
    s=Solver(); s.set("timeout",timeout*1000); s.add(*constraints)
    t=time.monotonic(); ans=s.check()
    print(f"    [{label}] -> {ans} ({time.monotonic()-t:.2f}s)",flush=True)
    return ans


def run_model(base,gens,fib,pins,label,timeout):
    print(f"  --- {label} ---",flush=True)
    R=PinCoproductResidue(base,pins)
    A,M,C,F,phi,_,_=build_blocks(R,fib); core=A+M+C+F
    h0=solve("H0 axioms+fiber2 sanity",core,timeout)
    if h0 != sat:
        print("    [row vacuous: this residue Hopf fiber has no lift over R]",flush=True)
        return [h0]
    holds=sp_nonprincipal_holds(R,phi,gens,"sq5")
    solve("S1 axioms+fiber2+S'-HOLDS",core+[holds],timeout)
    out=[]
    for i in range(1,4):
        out.append(solve(f"S2.{i} axioms+fiber2+S'-FAIL_i",
                         core+[fail_i(R,phi,gens,"sq5",i)],timeout))
    return out


def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--timeout",type=int,default=600)
    args=ap.parse_args(); set_param("parallel.enable",True)
    R=MixedSquareZeroLength5()
    gens=[R.concrete(2,0,0,0),R.concrete(0,1,0,0),
          R.concrete(0,0,1,0),R.concrete(0,0,0,1)]
    print(f"===== S' base {R.name} =====",flush=True); ring_gate(R,gens)
    results=[]
    for name,pins in XY_MODELS.items():
        results.append((f"xy/{name}",run_model(R,gens,XY_MULT,pins,f"xy/{name}",args.timeout)))
    for c1,c4 in itertools.product((0,1),repeat=2):
        label=f"t4/c1={c1},c4={c4}"
        results.append((label,run_model(R,gens,T4_MULT,t4_pins(c1,c4),label,args.timeout)))
    print("SUMMARY",flush=True)
    for label,out in results: print(f"  {label}: {','.join(map(str,out))}",flush=True)
    print("DONE sprime_mixed_squarezero_length5_20260709",flush=True)


if __name__=="__main__": main()
