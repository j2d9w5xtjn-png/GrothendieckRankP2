#!/usr/bin/env python3
r"""Exact S' on the seven length-six rank-one stretched quotients (§6).

The seven rings are the five fiber products

    P x_F2 F2[u,v]/(u,v)^2

for the five principal length-four rings P, together with Q0 and Q1 after
adjoining one extra annihilated tangent direction.  Each explicit
64-element table is exhaustively gated for the ring axioms, presentation,
locality, (1,3,1,1) filtration, exact type-three socle, maximal-ideal
generator ideal, and deformation range.

For the natural three generators, naive full syzygy enumeration has 64^3
coefficient tuples.  The exact efficient gate instead partitions R into the
eight additive cosets of Soc(R) and tests all 8^3=512 coefficient-coset
tuples.  Exactly sixteen are residual syzygies.  Soc*m=0 and the coset
partition prove that these represent the complete 8192-element full
syzygy, since 16*8^3=64^3/32.

Fiber2 puts every entry of phi=[2]^# in m, so Soc shifts affect neither a
division nor kernel membership.  Every split FAIL_i is therefore unrolled
over all 16^3=4096 residual choices, exactly and quantifier-free.  The sweep
uses all six F2-rational xy Hopf fibers and four t4 normal forms, separates
H0-vacuous rows, and independently validates any SAT failure seed against
all equations, its division, and all 4096 residual representatives.
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time

from z3 import (
    And, BitVec, BitVecVal, Extract, Not, Or, Solver, ZeroExt, is_true, sat,
    set_param, unknown, unsat,
)

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat import fresh
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_embdim2_len6_20260709 import PinCoproductResidue
from order4sat_ramified_towers_20260709 import value
from ringcheck import Tab, add_closure, check_axioms, check_locality, ev
from sprime_ramified_length4_six_20260709 import (
    in_kernel, module_div_eqs, sp_nonprincipal_holds,
)
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT, XY_MULT, t4_pins,
)
from s2check import build_blocks, phi_of_coords


def cast(x, width):
    old = x.size()
    if old == width: return x
    if old < width: return ZeroExt(width-old, x)
    return Extract(width-1, 0, x)


class StretchedTableRing:
    def __init__(self, key, name, widths, products, generators, socle, presentation):
        self.key, self.name, self.widths = key, name, tuple(widths)
        self.products = {(0,i): {i:1} for i in range(len(widths))}
        for pair, image in products.items(): self.products[tuple(sorted(pair))] = dict(image)
        self.generator_coords = tuple(generators)
        self.socle_values = set(socle)
        self.presentation = presentation
    def zero(self): return tuple(BitVecVal(0,w) for w in self.widths)
    def one(self):
        out=list(self.zero()); out[0]=BitVecVal(1,self.widths[0]); return tuple(out)
    def var(self, tag):
        nm=fresh(tag); return tuple(BitVec(f"{nm}_{i}",w) for i,w in enumerate(self.widths))
    def concrete(self,*coords): return tuple(BitVecVal(a,w) for a,w in zip(coords,self.widths))
    def add(self,a,b): return tuple(x+y for x,y in zip(a,b))
    def sub(self,a,b): return tuple(x-y for x,y in zip(a,b))
    def mul(self,a,b):
        out=[BitVecVal(0,w) for w in self.widths]
        for i,ai in enumerate(a):
            for j,bj in enumerate(b):
                for k,c in self.products.get(tuple(sorted((i,j))),{}).items():
                    w=self.widths[k]
                    out[k]=out[k]+cast(ai,w)*cast(bj,w)*BitVecVal(c,w)
        return tuple(out)
    def eq0(self,a): return And(*[x==0 for x in a])
    def neq0(self,a): return Or(*[x!=0 for x in a])
    def lowzero(self,a): return (a[0]&1)==0
    def deform(self,tag):
        x=self.var(tag); return (2*x[0],)+x[1:]
    def elements(self):
        return [self.concrete(*c) for c in itertools.product(
            *[range(1<<w) for w in self.widths])]
    def generators(self): return [self.concrete(*c) for c in self.generator_coords]


def all_rings():
    f2_soc={(0,0,0,a,b,c) for a,b,c in itertools.product((0,1),repeat=3)}
    Bf2=StretchedTableRing(
        "B_F2x4_2rad", "F2[x,u,v]/(x^4,xu,xv,(u,v)^2)",
        (1,1,1,1,1,1), {(1,1):{2:1},(1,2):{3:1}},
        ((0,1,0,0,0,0),(0,0,0,0,1,0),(0,0,0,0,0,1)), f2_soc,"Bf2")

    z16_soc={(8*a,u,v) for a,u,v in itertools.product((0,1),repeat=3)}
    Bz16=StretchedTableRing(
        "B_Z16_2rad", "Z/16[u,v]/(2u,2v,(u,v)^2)",
        (4,1,1), {}, ((2,0,0),(0,1,0),(0,0,1)), z16_soc,"Bz16")

    q0_soc={(0,2*a,u,v) for a,u,v in itertools.product((0,1),repeat=3)}
    Bq0=StretchedTableRing(
        "B_quad0_2rad", "B(Z/4[x]/(x^2-2)) with two radical tangents",
        (2,2,1,1), {(1,1):{0:2}},
        ((0,1,0,0),(0,0,1,0),(0,0,0,1)), q0_soc,"Bquad0")
    Bq1=StretchedTableRing(
        "B_quad1_2rad", "B(Z/4[x]/(x^2-2x-2)) with two radical tangents",
        (2,2,1,1), {(1,1):{0:2,1:2}},
        ((0,1,0,0),(0,0,1,0),(0,0,0,1)), q0_soc,"Bquad1")

    cubic_soc={(2*a,0,0,u,v) for a,u,v in itertools.product((0,1),repeat=3)}
    Bcub=StretchedTableRing(
        "B_cubic_2rad", "B(Z/4[x]/(x^3-2,x^4)) with two radical tangents",
        (2,1,1,1,1), {(1,1):{2:1},(1,2):{0:2}},
        ((0,1,0,0,0),(0,0,0,1,0),(0,0,0,0,1)), cubic_soc,"Bcubic")

    nq0_soc={(2*a,0,0,b,c) for a,b,c in itertools.product((0,1),repeat=3)}
    NQ0=StretchedTableRing(
        "Q0_plus_dual", "Q0 x_F2 F2[v]/v^2",
        (2,1,1,1,1), {(1,1):{2:1},(1,2):{3:1}},
        ((2,0,0,0,0),(0,1,0,0,0),(0,0,0,0,1)), nq0_soc,"Q0dual")

    nq1_soc={(2*b,2*a,b,c) for a,b,c in itertools.product((0,1),repeat=3)}
    NQ1=StretchedTableRing(
        "Q1_plus_dual", "Q1 x_F2 F2[v]/v^2",
        (2,2,1,1), {(1,1):{2:1},(1,2):{1:2}},
        ((2,0,0,0),(0,1,0,0),(0,0,0,1)), nq1_soc,"Q1dual")
    return {R.key:R for R in (Bf2,Bz16,Bq0,Bq1,Bcub,NQ0,NQ1)}


def val(x): return value(x)
def cpow(R,x,n):
    y=R.one()
    for _ in range(n): y=R.mul(y,x)
    return y


def validate_presentation(R):
    z=R.zero(); two=R.add(R.one(),R.one()); g=R.generators()
    if R.presentation=="Bf2":
        x,u,vv=g
        assert val(two)==val(z) and val(cpow(R,x,3))!=val(z) and val(cpow(R,x,4))==val(z)
        assert all(val(R.mul(a,b))==val(z) for a,b in ((x,u),(x,vv),(u,u),(u,vv),(vv,vv)))
    elif R.presentation=="Bz16":
        p,u,vv=g
        assert val(p)==val(two) and val(cpow(R,p,3))!=val(z) and val(cpow(R,p,4))==val(z)
        assert all(val(R.mul(a,b))==val(z) for a,b in ((p,u),(p,vv),(u,u),(u,vv),(vv,vv)))
    elif R.presentation in ("Bquad0","Bquad1"):
        x,u,vv=g; rhs=two
        if R.presentation=="Bquad1": rhs=R.add(two,R.mul(two,x))
        assert val(R.mul(x,x))==val(rhs) and val(cpow(R,x,3))!=val(z) and val(cpow(R,x,4))==val(z)
        assert all(val(R.mul(a,b))==val(z) for a,b in ((x,u),(x,vv),(u,u),(u,vv),(vv,vv)))
    elif R.presentation=="Bcubic":
        x,u,vv=g
        assert val(cpow(R,x,3))==val(two) and val(cpow(R,x,4))==val(z)
        assert all(val(R.mul(a,b))==val(z) for a,b in ((x,u),(x,vv),(u,u),(u,vv),(vv,vv)))
    elif R.presentation=="Q0dual":
        p,x,vv=g
        assert val(p)==val(two) and val(R.mul(two,x))==val(z)
        assert val(cpow(R,x,3))!=val(z) and val(cpow(R,x,4))==val(z)
        assert val(R.mul(vv,vv))==val(z) and val(R.mul(vv,x))==val(z) and val(R.mul(vv,two))==val(z)
    elif R.presentation=="Q1dual":
        p,x,vv=g
        assert val(p)==val(two) and val(R.mul(two,x))==val(cpow(R,x,3))
        assert val(cpow(R,x,3))!=val(z) and val(cpow(R,x,4))==val(z)
        assert val(R.mul(vv,vv))==val(z) and val(R.mul(vv,x))==val(z) and val(R.mul(vv,two))==val(z)
    else: raise ValueError(R.presentation)


def validate_ring(R):
    started=time.monotonic(); els=R.elements(); vals=[ev(x) for x in els]
    assert len(els)==len(set(vals))==64
    T=Tab(R,els); check_axioms(T,vals,triple_cap=64)
    nm,residue,powers=check_locality(T,expect_residue_deg=1)
    assert (nm,residue,powers)==(32,2,[32,4,2,1])
    maximal={x for x in vals if T.lowzero(x)}
    raw={T.mul(ev(g),a) for g in R.generators() for a in vals}
    assert add_closure(T,raw)==maximal
    soc={ev(a) for a in els if all(val(R.mul(a,g))==val(R.zero()) for g in R.generators())}
    assert soc==R.socle_values and len(soc)==8
    assert all(T.mul(s,a)==T.zero for s in soc for a in maximal)
    validate_presentation(R)
    print(f"  [ring/presentation/locality/type gate] {R.key}: |R|=64, "
          f"|m^k|=32,4,2,1, |Soc|=8, type=3 -> PASS "
          f"({time.monotonic()-started:.2f}s)",flush=True)
    return [T.by_val[x] for x in sorted(soc)]


def tuple_add(R,a,b): return tuple(R.add(x,y) for x,y in zip(a,b))
def tuple_key(a): return tuple(val(x) for x in a)


def exact_residual_syzygies(R,gens,soc):
    els=R.elements(); z=R.zero(); covered=set(); qreps=[]
    for a in els:
        if val(a) in covered: continue
        coset={val(R.add(a,s)) for s in soc}
        assert len(coset)==8 and not(coset&covered)
        qreps.append(a); covered|=coset
    assert len(qreps)==8 and covered=={val(a) for a in els}
    assert all(val(R.mul(s,g))==val(z) for s in soc for g in gens)
    residual=[]
    for coeffs in itertools.product(qreps,repeat=3):
        total=z
        for a,g in zip(coeffs,gens): total=R.add(total,R.mul(a,g))
        if val(total)==val(z): residual.append(coeffs)
    assert len(residual)==16 and len({tuple_key(x) for x in residual})==16
    socvals={val(x) for x in soc}
    orders=[]
    for a in residual:
        y=tuple(z for _ in range(3))
        for n in range(1,9):
            y=tuple_add(R,y,a)
            if all(val(x) in socvals for x in y): orders.append(n); break
        else: raise AssertionError("residual order >8")
    for a,b in itertools.product(residual,repeat=2):
        c=tuple_add(R,a,b)
        assert any(all(val(R.sub(x,y)) in socvals for x,y in zip(c,r)) for r in residual)
    group="has order-4 classes" if 4 in orders else "C2^4"
    full=len(residual)*(len(soc)**3)
    assert full==(len(els)**3)//32==8192
    print(f"  [exact full-syzygy/coset gate] |R/Soc|=8; tested 8^3=512 "
          f"coefficient cosets; |Syz/Soc^3|=16 ({group}); |Syz|=8192 -> PASS",flush=True)
    print("    residual representatives: "+repr([[val(x) for x in row] for row in residual]),flush=True)
    return residual


def fail_i_unrolled(R,phi,gens,residual,tag,i):
    vecs=[[R.var(f"{tag}_{i}_{j}_{r}") for r in range(3)] for j in range(3)]
    division=And(*module_div_eqs(R,phi[i],vecs,gens)); misses=[]
    # A literal expansion recomputes phi(vec_j+shift_j) for every one of the
    # 4096 combined residual choices.  Cache by the three-coordinate shift
    # seen by each individual coefficient vector.  This shares ASTs only: the
    # final conjunction below still contains every combined residual tuple.
    kernel_cache=[{} for _ in range(3)]
    def cached_kernel(j,shiftvec):
        key=tuple(val(x) for x in shiftvec)
        if key not in kernel_cache[j]:
            shifted=[R.add(vecs[j][r],shiftvec[r]) for r in range(3)]
            kernel_cache[j][key]=in_kernel(R,phi,shifted)
        return kernel_cache[j][key]
    for shifts in itertools.product(residual,repeat=3):
        per_j=[[shifts[r][j] for r in range(3)] for j in range(3)]
        misses.append(Not(And(*[cached_kernel(j,per_j[j]) for j in range(3)])))
    assert len(misses)==4096
    print("      [unroll cache] 4096 combined representatives; distinct "
          f"coefficient shifts={','.join(str(len(c)) for c in kernel_cache)}",flush=True)
    return And(division,*misses),vecs


def concrete_term(model,x):
    if isinstance(x,tuple): return tuple(concrete_term(model,y) for y in x)
    y=model.eval(x,model_completion=True); return BitVecVal(y.as_long(),x.size())
def model_value(model,x): return val(concrete_term(model,x))
def concrete_kernel(R,phi,vec): return all(val(x)==val(R.zero()) for x in phi_of_coords(R,phi,vec))


def validate_sat(R,model,asserted,phi,gens,residual,vecs,i,c,mtab):
    assert all(is_true(model.eval(a,model_completion=True)) for a in asserted)
    cphi=[[concrete_term(model,x) for x in row] for row in phi]
    cvecs=[[concrete_term(model,x) for x in row] for row in vecs]
    for r in range(3):
        total=R.zero()
        for g,row in zip(gens,cvecs): total=R.add(total,R.mul(g,row[r]))
        assert val(total)==val(cphi[i][r+1])
    checked=0
    for shifts in itertools.product(residual,repeat=3):
        shifted=[list(row) for row in cvecs]
        for r,shift in enumerate(shifts):
            for j in range(3): shifted[j][r]=R.add(shifted[j][r],shift[j])
        assert not all(concrete_kernel(R,cphi,row) for row in shifted); checked+=1
    assert checked==4096
    print("      [independent SAT seed validation] equations, division, all 4096 residual choices -> PASS",flush=True)
    ms={str(k):model_value(model,x) for k,x in sorted(mtab.items()) if model_value(model,x)!=val(R.zero())}
    cs={str(k):model_value(model,x) for k,x in sorted(c.items()) if model_value(model,x)!=val(R.zero())}
    ds=[[model_value(model,x) for x in row] for row in vecs]
    print(f"      SAT_SEED multiplication_nonzero={ms}",flush=True)
    print(f"      SAT_SEED coproduct_nonzero={cs}",flush=True)
    print(f"      SAT_SEED FAIL_{i}_division={ds}",flush=True)


def solve(label,constraints,timeout,on_sat=None):
    s=Solver(); s.set("timeout",timeout*1000); s.add(*constraints)
    t=time.monotonic(); ans=s.check(); elapsed=time.monotonic()-t
    reason=f" reason={s.reason_unknown()}" if ans==unknown else ""
    print(f"    [{label}] -> {ans} ({elapsed:.2f}s){reason}",flush=True)
    if ans==sat and on_sat is not None: on_sat(s.model(),constraints)
    return ans


def run_row(base,gens,residual,fib,pins,label,timeout,only_i):
    print(f"  --- {label} ---",flush=True); R=PinCoproductResidue(base,pins)
    A,M,C,F,phi,c,mtab=build_blocks(R,fib); core=A+M+C+F
    h0=solve("H0 axioms+fiber2 sanity",core,timeout)
    out={"H0":str(h0),"S1":"not-run","S2":{},"class":"unknown"}
    if h0==unsat:
        out["class"]="H0-vacuous"; print("    [H0-VACUOUS: no bialgebra lift]",flush=True); return out
    if h0==unknown: return out
    holds=sp_nonprincipal_holds(R,phi,gens,"rsH")
    s1=solve("S1 axioms+fiber2+S'-HOLDS",core+[holds],timeout); out["S1"]=str(s1)
    if s1!=sat: print("    [S1 sanity did not return SAT; FAIL_i still run]",flush=True)
    cls="UNSAT" if set(only_i)=={1,2,3} else "partial-UNSAT"
    for i in only_i:
        failure,vecs=fail_i_unrolled(base,phi,gens,residual,"rsF",i); asserted=core+[failure]
        def on_sat(model,constraints,i=i,vecs=vecs):
            validate_sat(base,model,constraints,phi,gens,residual,vecs,i,c,mtab)
        ans=solve(f"S2.{i} axioms+fiber2+S'-FAIL_i",asserted,timeout,on_sat)
        out["S2"][str(i)]=str(ans)
        if ans==sat: cls="SAT S'-failure"
        elif ans==unknown and cls!="SAT S'-failure": cls="unknown"
    out["class"]=cls; print(f"    [ROW CLASS] {cls}",flush=True); return out


def main():
    rings=all_rings(); ap=argparse.ArgumentParser()
    ap.add_argument("--rings",nargs="+",choices=tuple(rings)+("all",),default=("all",))
    ap.add_argument("--fibers",choices=("xy","t4","all"),default="all")
    ap.add_argument("--xy-models",nargs="+",choices=tuple(XY_MODELS),default=tuple(XY_MODELS))
    ap.add_argument("--t4-forms",nargs="+",choices=("00","01","10","11"),default=("00","01","10","11"))
    ap.add_argument("--only-i",nargs="+",type=int,choices=(1,2,3),default=(1,2,3))
    ap.add_argument("--timeout",type=int,default=600); ap.add_argument("--validate-only",action="store_true")
    args=ap.parse_args(); set_param("parallel.enable",True)
    selected=list(rings) if "all" in args.rings else args.rings; allrows=[]
    print("EXACT S' SWEEP -- SEVEN LENGTH-SIX RANK-ONE STRETCHED QUOTIENTS",flush=True)
    print("Results are S' verdicts, not direct [4] verdicts.",flush=True)
    for key in selected:
        R=rings[key]; print(f"===== LENGTH6 RANK-ONE STRETCHED {key}: {R.name} =====",flush=True)
        soc=validate_ring(R); gens=R.generators(); residual=exact_residual_syzygies(R,gens,soc)
        if args.validate_only: continue
        rows=[]
        if args.fibers in ("xy","all"):
            for name in args.xy_models:
                rows.append((f"xy/{name}",run_row(R,gens,residual,XY_MULT,XY_MODELS[name],f"xy/{name}",args.timeout,tuple(args.only_i))))
        if args.fibers in ("t4","all"):
            for form in args.t4_forms:
                c1,c4=int(form[0]),int(form[1]); label=f"t4/c1={c1},c4={c4}"
                rows.append((label,run_row(R,gens,residual,T4_MULT,t4_pins(c1,c4),label,args.timeout,tuple(args.only_i))))
        print("SUMMARY",flush=True)
        for label,row in rows:
            s2=",".join(f"{i}:{x}" for i,x in sorted(row["S2"].items())) or "not-run"
            print(f"  {label}: class={row['class']}; H0={row['H0']}; S1={row['S1']}; S2={s2}",flush=True)
        print(f"DONE {key}",flush=True); allrows.extend((key,label,row) for label,row in rows)
    print("===== LENGTH6 RANK-ONE STRETCHED TERMINAL SUMMARY =====",flush=True)
    counts={"H0-vacuous":0,"SAT S'-failure":0,"UNSAT":0,"partial-UNSAT":0,"unknown":0}
    for _,_,row in allrows: counts[row["class"]]=counts.get(row["class"],0)+1
    print("COUNTS "+", ".join(f"{k}={x}" for k,x in counts.items()),flush=True)
    print("DONE sprime_length6_rankone_stretched_seven_stratified_20260710",flush=True)


if __name__=="__main__": main()
