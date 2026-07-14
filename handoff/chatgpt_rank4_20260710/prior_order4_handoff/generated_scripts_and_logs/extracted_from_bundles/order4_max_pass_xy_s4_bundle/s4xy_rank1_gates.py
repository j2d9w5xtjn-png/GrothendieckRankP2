#!/usr/bin/env python3
"""s4xy_rank1_gates.py
New exploratory gates for the s=4 xy-fiber hand proof.
They isolate the rank-one split cases W2[F] and mu2 x alpha2 into matrix identities
which imply D4=0 by linear algebra once the s<=3 identities are banked.

These are F2[eps]/eps^4 gates only (like s4probe.py); they are discovery/proof-audit
for the proposed hand lemmas, not arbitrary-coefficient ideal-membership certificates.
"""
import sys
sys.path.insert(0,'/mnt/data/groth_handoff_v2/scripts')
from z3 import Solver, Or, And, set_param
from order4sat_beyond import F2epsN
from s2check import build_blocks
from s3gates import KF2, digit

XY={(1,2,3):1}
CASES={
 'W2F':{(2,1,1),(3,1,2),(3,2,1)},
 'mu2a2':{(1,1,1),(3,1,2),(3,2,1),(3,1,3),(3,3,1)},}
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
M=lambda i,j,r,n: d(Mtab[(min(i,j),max(i,j),r)],n)

def d4_component(i,ss):
    terms=[]
    for r in (1,2,3):
        terms += [mul(P[1][(i,r)],P[3][(r,ss)]),
                  mul(P[2][(i,r)],P[2][(r,ss)]),
                  mul(P[3][(i,r)],P[1][(r,ss)])]
    return add(*terms)

def run_case(case):
    extra=pin_of(case)
    s=Solver(); s.set('timeout',120000)
    for e in base+extra: s.add(e)
    print(f"===== {case} over F2[eps]/eps^4 =====", flush=True)
    print("  [Q0 axioms sat] ->", s.check(), flush=True)
    def gate(label, exprs):
        s.push(); s.add(Or(*[K.neq0(e) for e in exprs])); r=s.check(); s.pop()
        print(f"  [{label}] -> {r}", flush=True)
        return str(r)
    if case=='W2F':
        lam=M(1,1,1,1); nu=M(2,2,1,1)
        m2=M(1,2,2,1)
        alpha=w[1][(1,1,1)]; delta=w[1][(1,2,2)]
        rho=add(mul(lam,alpha),mul(nu,delta))
        Cc=P[2][(2,3)]
        gate('W-Mx: Psi2(x)=rho x', [add(P[2][(1,1)],rho),P[2][(1,2)],P[2][(1,3)]])
        gate('W-My-y: (Psi2 y)_y=rho', [add(P[2][(2,2)],rho)])
        gate('W-Mz: Psi2(z)=m2*lambda*x', [add(P[2][(3,1)],mul(m2,lam)),P[2][(3,2)],P[2][(3,3)]])
        gate('W-Lx-y: lambda*(Psi3 x)_y=rho^2', [add(mul(lam,P[3][(1,2)]),mul(rho,rho))])
        gate('W-Lx-z: lambda*(Psi3 x)_z=rho*(Psi2 y)_z', [add(mul(lam,P[3][(1,3)]),mul(rho,Cc))])
        gate('W-Lz-y: (Psi3 z)_y=m2*rho', [add(P[3][(3,2)],mul(m2,rho))])
        gate('W-xcomp: lambda*((Psi3 y)_y+(Psi3 x)_x+m2*(Psi2 y)_z)=0',
             [mul(lam,add(P[3][(2,2)],P[3][(1,1)],mul(m2,Cc)))])
    else:
        lam=M(1,1,2,1); nu=M(2,2,2,1)
        m1=M(1,2,1,1)
        alpha=w[1][(2,1,1)]; delta=w[1][(2,2,2)]
        rho=add(mul(lam,alpha),mul(nu,delta))
        Cc=P[2][(1,3)]
        gate('E-My: Psi2(y)=rho y', [P[2][(2,1)],add(P[2][(2,2)],rho),P[2][(2,3)]])
        gate('E-Mx-x: (Psi2 x)_x=rho', [add(P[2][(1,1)],rho)])
        gate('E-Mz: Psi2(z)=m1*lambda*y', [P[2][(3,1)],add(P[2][(3,2)],mul(m1,lam)),P[2][(3,3)]])
        gate('E-Ly-x: lambda*(Psi3 y)_x=rho^2', [add(mul(lam,P[3][(2,1)]),mul(rho,rho))])
        gate('E-Ly-z: lambda*(Psi3 y)_z=rho*(Psi2 x)_z', [add(mul(lam,P[3][(2,3)]),mul(rho,Cc))])
        gate('E-Lz-x: (Psi3 z)_x=m1*rho', [add(P[3][(3,1)],mul(m1,rho))])
        gate('E-xcomp-dual: lambda*((Psi3 x)_x+(Psi3 y)_y+m1*(Psi2 x)_z)=0',
             [mul(lam,add(P[3][(1,1)],P[3][(2,2)],mul(m1,Cc)))])
    gate('endpoint D4=0', [d4_component(i,j) for i in (1,2,3) for j in (1,2,3)])

if __name__=='__main__':
    set_param('parallel.enable', True)
    run_case('W2F')
    run_case('mu2a2')
