#!/usr/bin/env python3
r"""Exact S' sweep on the seventeen length-six radical extensions (§7).

Fourteen rings are obtained by adjoining one annihilated dual tangent to the
audited pointed-quadratic length-five tables.  The remaining three are

    Z/4[x,y]/(2x,2y,q,(x,y)^3),  q=x^2,xy,x^2+xy+y^2,

where the tangent class of 2 is the added radical direction.  Every explicit
64-element table receives exhaustive ring, presentation, locality,
filtration, type-three socle, generator-ideal, and deformation-range gates.

The exact efficient syzygy and Hopf machinery is shared with the completed
seven-ring rank-one-stretched sweep: R/Soc has eight elements, all 8^3=512
coefficient cosets are tested, sixteen residual syzygies are derived, and
the full 8192-element syzygy is proved.  Each split FAIL_i retains all
16^3=4096 combined residual choices with cached shared kernel ASTs.  Any SAT
failure is independently checked against the complete equations, division,
and all 4096 representatives.
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time

from z3 import is_true, set_param

sys.path.insert(0, __file__.rsplit("/",1)[0])
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_towers_20260709 import value
from ringcheck import Tab, add_closure, check_axioms, check_locality, ev
from sprime_length5_pointed_quadratic_sweep_20260710 import (
    AdditiveTableRing, all_rings as pointed_rings,
)
from sprime_length6_rankone_stretched_seven_stratified_20260710 import (
    exact_residual_syzygies, run_row,
)
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT, XY_MULT, t4_pins,
)


def val(x): return value(x)


def embed_coords(x, tail=0): return tuple(val(x))+(tail,)


def build_extended_rings():
    out={}
    for base_key,(base,base_gens) in pointed_rings().items():
        products={pair:dict(image) for pair,image in base.products.items() if pair[0]!=0}
        R=AdditiveTableRing(f"RadExt({base.name})",base.widths+(1,),products)
        key=f"ext_{base_key}"; R.key=key; R.base_key=base_key
        R.base_ring=base; R.base_gens=base_gens
        gens=[R.concrete(*embed_coords(g)) for g in base_gens]
        zcoords=[0]*len(R.widths); zcoords[-1]=1; gens.append(R.concrete(*zcoords))
        base_soc=[a for a in base.elements() if all(
            val(base.mul(a,g))==val(base.zero()) for g in base_gens)]
        R.socle_values={tuple(val(s))+(z,) for s in base_soc for z in (0,1)}
        out[key]=(R,gens)

    # Three Z/4 fiber products over the equal-characteristic q-types.
    cases={
        "x2": {(1,1):{},(1,2):{3:1},(2,2):{4:1}},
        "xy": {(1,1):{3:1},(1,2):{},(2,2):{4:1}},
        "irr": {(1,1):{3:1},(1,2):{4:1},(2,2):{3:1,4:1}},
    }
    for q,products in cases.items():
        R=AdditiveTableRing(f"Z/4 x_F2 C({q};0)",(2,1,1,1,1),products)
        key=f"rad2_{q}"; R.key=key; R.base_key=None; R.radical_q=q
        gens=[R.concrete(2,0,0,0,0),R.concrete(0,1,0,0,0),R.concrete(0,0,1,0,0)]
        R.socle_values={(2*a,0,0,b,c) for a,b,c in itertools.product((0,1),repeat=3)}
        out[key]=(R,gens)
    assert len(out)==17
    return out


def original_xy(R,gens):
    """Recover the displayed x,y inside an extended pointed table."""
    key=R.base_key; a,b=gens[:2]
    if key.startswith("eq_") or key.startswith("deg2_"): return a,b
    if key=="tan_x2_x": return a,b
    if key=="tan_x2_y": return b,a
    if key=="tan_xy_x": return a,b
    if key=="tan_xy_x+y": return b,R.sub(a,b)
    if key=="tan_irr_x": return a,b
    raise ValueError(key)


def q_value(R,q,x,y):
    x2,xy,y2=R.mul(x,x),R.mul(x,y),R.mul(y,y)
    if q=="x2": return x2
    if q=="xy": return xy
    if q=="irr": return R.add(R.add(x2,xy),y2)
    raise ValueError(q)


def validate_extended_presentation(R,gens):
    z=R.zero(); two=R.add(R.one(),R.one())
    if R.base_key is None:
        radical,x,y=gens
        assert val(radical)==val(two)
        assert val(R.mul(two,x))==val(z) and val(R.mul(two,y))==val(z)
        assert val(q_value(R,R.radical_q,x,y))==val(z)
        # m^3=0 is independently implied by the gated filtration, but check
        # all displayed cubic monomials directly as a presentation audit.
        assert all(val(R.mul(a,R.mul(b,c)))==val(z)
                   for a,b,c in itertools.product((x,y),repeat=3))
        return

    x,y=original_xy(R,gens); dual=gens[2]
    q=R.base_key.split("_")[1]
    assert val(q_value(R,q,x,y))==val(z)
    if R.base_key.startswith("eq_"):
        assert val(two)==val(z)
    elif R.base_key.startswith("tan_"):
        point={
            "tan_x2_x":x,"tan_x2_y":y,"tan_xy_x":x,
            "tan_xy_x+y":R.add(x,y),"tan_irr_x":x,
        }[R.base_key]
        assert val(two)==val(point)
    else:
        wname=R.base_key.split("_",2)[2]
        x2,xy,y2=R.mul(x,x),R.mul(x,y),R.mul(y,y)
        point={"y2":y2,"xy":xy,"xy+y2":R.add(xy,y2),
               "x2":x2,"x2+y2":R.add(x2,y2)}[wname]
        assert val(two)==val(point)
    assert all(val(R.mul(dual,g))==val(z) for g in gens)


def validate_ring(R,gens):
    started=time.monotonic(); els=R.elements(); vals=[ev(a) for a in els]
    assert len(els)==len(set(vals))==64
    T=Tab(R,els); check_axioms(T,vals,triple_cap=64)
    nm,residue,powers=check_locality(T,expect_residue_deg=1)
    assert (nm,residue,powers)==(32,2,[32,4,1])
    maximal={a for a in vals if T.lowzero(a)}
    raw={T.mul(ev(g),a) for g in gens for a in vals}
    assert add_closure(T,raw)==maximal
    soc={ev(a) for a in els if all(val(R.mul(a,g))==val(R.zero()) for g in gens)}
    assert soc==R.socle_values and len(soc)==8
    assert all(T.mul(s,a)==T.zero for s in soc for a in maximal)
    validate_extended_presentation(R,gens)

    # For the fourteen wrappers, independently cross-check the entire
    # embedded 32-element table against the already-audited source table.
    if R.base_key is not None:
        B=R.base_ring
        for a,b in itertools.product(B.elements(),repeat=2):
            ea=R.concrete(*embed_coords(a)); eb=R.concrete(*embed_coords(b))
            want=R.concrete(*embed_coords(B.mul(a,b)))
            assert val(R.mul(ea,eb))==val(want)
    print(f"  [ring/presentation/locality/type gate] {R.key}: |R|=64, "
          f"|m^k|=32,4,1, |Soc|=8, type=3 -> PASS "
          f"({time.monotonic()-started:.2f}s)",flush=True)
    return [T.by_val[x] for x in sorted(soc)]


def main():
    rings=build_extended_rings(); ap=argparse.ArgumentParser()
    ap.add_argument("--rings",nargs="+",choices=tuple(rings)+("all",),default=("all",))
    ap.add_argument("--fibers",choices=("xy","t4","all"),default="all")
    ap.add_argument("--xy-models",nargs="+",choices=tuple(XY_MODELS),default=tuple(XY_MODELS))
    ap.add_argument("--t4-forms",nargs="+",choices=("00","01","10","11"),default=("00","01","10","11"))
    ap.add_argument("--only-i",nargs="+",type=int,choices=(1,2,3),default=(1,2,3))
    ap.add_argument("--timeout",type=int,default=600); ap.add_argument("--validate-only",action="store_true")
    args=ap.parse_args(); set_param("parallel.enable",True)
    selected=list(rings) if "all" in args.rings else args.rings; allrows=[]
    print("EXACT S' SWEEP -- SEVENTEEN LENGTH-SIX RADICAL EXTENSIONS",flush=True)
    print("Results are S' verdicts, not direct [4] verdicts.",flush=True)
    for key in selected:
        R,gens=rings[key]; print(f"===== LENGTH6 RADICAL EXTENSION {key}: {R.name} =====",flush=True)
        soc=validate_ring(R,gens); residual=exact_residual_syzygies(R,gens,soc)
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
    print("===== LENGTH6 RADICAL EXTENSIONS TERMINAL SUMMARY =====",flush=True)
    counts={"H0-vacuous":0,"SAT S'-failure":0,"UNSAT":0,"partial-UNSAT":0,"unknown":0}
    for _,_,row in allrows: counts[row["class"]]=counts.get(row["class"],0)+1
    print("COUNTS "+", ".join(f"{k}={x}" for k,x in counts.items()),flush=True)
    print("DONE sprime_length6_radical_extensions_seventeen_stratified_20260710",flush=True)


if __name__=="__main__": main()
