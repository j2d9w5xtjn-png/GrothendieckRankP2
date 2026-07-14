#!/usr/bin/env python3
"""s4xy_case_reduction_gates.py
Exploratory F2[eps]/eps^4 gates for a hand proof of the s=4 divided-[4]
identity in the xy fiber.  These gates refine s4probe.py's one-line X2g endpoint
into per-split-model linear-algebra reductions.

They are not arbitrary-k' Groebner certificates.  They are a map of the hand proof:
  * alpha2^2 and mu2^2 reduce to an operator identity for N=Psi1, M=Psi2, L=Psi3
    with N image in k z.
  * W2[F] and mu2 x alpha2 reduce to rank-one matrix identities.
All negated identities below are UNSAT over F2[eps]/eps^4.
"""
import sys
sys.path.insert(0,'/mnt/data/groth_handoff_v2/scripts')
from z3 import Solver, Or, set_param
from order4sat_beyond import F2epsN
from s2check import build_blocks
from s3gates import KF2, digit

XY={(1,2,3):1}
CASES={
 'a2a2':{(3,1,2),(3,2,1)},
 'W2F':{(2,1,1),(3,1,2),(3,2,1)},
 'mu2mu2':{(1,1,1),(2,2,2),(3,1,2),(3,2,1),(3,1,3),(3,3,1),(3,2,3),(3,3,2),(3,3,3)},
 'mu2a2':{(1,1,1),(3,1,2),(3,2,1),(3,1,3),(3,3,1)},
}
R=F2epsN(4); K=KF2()
A,Mb,C,F,phi,c,Mtab=build_blocks(R,XY)
base=A+Mb+C+F

def d(x,l): return digit(R,x,l)
def add(*xs):
    out=xs[0]
    for x in xs[1:]: out=K.add(out,x)
    return out
def mul(a,b): return K.mul(a,b)
def keq(x,y): return K.eq0(add(x,y))
def pin_of(case):
    out=[]; pins=CASES[case]
    for i in range(1,4):
        for j in range(1,4):
            for k in range(1,4):
                out.append(keq(d(c[(i,j,k)],0), K.one() if (i,j,k) in pins else K.zero()))
    return out
P={n:{(i,r):d(phi[i][r],n) for i in range(1,4) for r in range(1,4)} for n in (1,2,3)}
w={n:{(i,j,k):d(c[(i,j,k)],n) for i in range(1,4) for j in range(1,4) for k in range(1,4)} for n in (1,2,3)}
Mcoef=lambda i,j,r,n: d(Mtab[(min(i,j),max(i,j),r)],n)

def comp(a,b,i,ss):
    return add(*[mul(P[a][(i,r)],P[b][(r,ss)]) for r in (1,2,3)])
def d4_all():
    return [add(comp(1,3,i,j),comp(2,2,i,j),comp(3,1,i,j)) for i in (1,2,3) for j in (1,2,3)]
def gate(s,label,exprs):
    s.push(); s.add(Or(*[K.neq0(e) for e in exprs])); r=s.check(); s.pop()
    print(f"  [{label}] -> {r}", flush=True)

def run_image_z_case(case):
    extra=pin_of(case)
    s=Solver(); s.set('timeout',120000)
    for e in base+extra: s.add(e)
    print(f"===== {case} over F2[eps]/eps^4 =====", flush=True)
    print("  [Q0 axioms sat] ->", s.check(), flush=True)
    cx,cy=P[1][(1,3)],P[1][(2,3)]
    gate(s,'N has image in kz and N(z)=0',
         [P[1][(1,1)],P[1][(1,2)],P[1][(2,1)],P[1][(2,2)],P[1][(3,1)],P[1][(3,2)],P[1][(3,3)]])
    if case=='mu2mu2':
        gate(s,'M(z)=0', [P[2][(3,1)],P[2][(3,2)],P[2][(3,3)]])
        gate(s,'L(z)=0', [P[3][(3,1)],P[3][(3,2)],P[3][(3,3)]])
    else:
        gate(s,'M(z) in kz', [P[2][(3,1)],P[2][(3,2)]])
    for g,cg in [(1,cx),(2,cy),(3,K.zero())]:
        for ss in (1,2):
            gate(s,f'M^2({g})_{ss} + N({g})*L(z)_{ss}=0',
                 [add(comp(2,2,g,ss),mul(cg,P[3][(3,ss)]))])
        ellLg=add(mul(cx,P[3][(g,1)]),mul(cy,P[3][(g,2)]))
        gate(s,f'z-component identity for input {g}',
             [add(comp(2,2,g,3),mul(cg,P[3][(3,3)]),ellLg)])
    gate(s,'endpoint D4=0',d4_all())

def run_rank_one_case(case):
    extra=pin_of(case)
    s=Solver(); s.set('timeout',120000)
    for e in base+extra: s.add(e)
    print(f"===== {case} over F2[eps]/eps^4 =====", flush=True)
    print("  [Q0 axioms sat] ->", s.check(), flush=True)
    if case=='W2F':
        lam=Mcoef(1,1,1,1); nu=Mcoef(2,2,1,1); m=Mcoef(1,2,2,1)
        alpha=w[1][(1,1,1)]; delta=w[1][(1,2,2)]
        rho=add(mul(lam,alpha),mul(nu,delta)); Cfree=P[2][(2,3)]
        gate(s,'Psi1: x->0, y->lambda x, z->0',
             [P[1][(1,r)] for r in (1,2,3)]+[add(P[1][(2,1)],lam),P[1][(2,2)],P[1][(2,3)]]+[P[1][(3,r)] for r in (1,2,3)])
        gate(s,'Psi2(x)=rho x', [add(P[2][(1,1)],rho),P[2][(1,2)],P[2][(1,3)]])
        gate(s,'(Psi2 y)_y=rho', [add(P[2][(2,2)],rho)])
        gate(s,'Psi2(z)=m lambda x', [add(P[2][(3,1)],mul(m,lam)),P[2][(3,2)],P[2][(3,3)]])
        gate(s,'lambda (Psi3 x)_y=rho^2', [add(mul(lam,P[3][(1,2)]),mul(rho,rho))])
        gate(s,'lambda (Psi3 x)_z=rho (Psi2 y)_z', [add(mul(lam,P[3][(1,3)]),mul(rho,Cfree))])
        gate(s,'(Psi3 z)_y=m rho', [add(P[3][(3,2)],mul(m,rho))])
        gate(s,'lambda((Psi3 y)_y+(Psi3 x)_x+m(Psi2 y)_z)=0',
             [mul(lam,add(P[3][(2,2)],P[3][(1,1)],mul(m,Cfree)))])
    else:
        lam=Mcoef(1,1,2,1); nu=Mcoef(2,2,2,1); m=Mcoef(1,2,1,1)
        alpha=w[1][(2,1,1)]; delta=w[1][(2,2,2)]
        rho=add(mul(lam,alpha),mul(nu,delta)); Cfree=P[2][(1,3)]
        gate(s,'Psi1: x->lambda y, y->0, z->0',
             [P[1][(1,1)],add(P[1][(1,2)],lam),P[1][(1,3)]]+[P[1][(2,r)] for r in (1,2,3)]+[P[1][(3,r)] for r in (1,2,3)])
        gate(s,'Psi2(y)=rho y', [P[2][(2,1)],add(P[2][(2,2)],rho),P[2][(2,3)]])
        gate(s,'(Psi2 x)_x=rho', [add(P[2][(1,1)],rho)])
        gate(s,'Psi2(z)=m lambda y', [P[2][(3,1)],add(P[2][(3,2)],mul(m,lam)),P[2][(3,3)]])
        gate(s,'lambda (Psi3 y)_x=rho^2', [add(mul(lam,P[3][(2,1)]),mul(rho,rho))])
        gate(s,'lambda (Psi3 y)_z=rho (Psi2 x)_z', [add(mul(lam,P[3][(2,3)]),mul(rho,Cfree))])
        gate(s,'(Psi3 z)_x=m rho', [add(P[3][(3,1)],mul(m,rho))])
        gate(s,'lambda((Psi3 x)_x+(Psi3 y)_y+m(Psi2 x)_z)=0',
             [mul(lam,add(P[3][(1,1)],P[3][(2,2)],mul(m,Cfree)))])
    gate(s,'endpoint D4=0',d4_all())

if __name__=='__main__':
    set_param('parallel.enable', True)
    run_image_z_case('a2a2')
    run_rank_one_case('W2F')
    run_image_z_case('mu2mu2')
    run_rank_one_case('mu2a2')
