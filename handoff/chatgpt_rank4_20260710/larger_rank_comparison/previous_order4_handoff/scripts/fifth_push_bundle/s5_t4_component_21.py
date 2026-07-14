#!/usr/bin/env python3
"""Partial exact-F2 probe for the next curvilinear t^4 layer.
Checks selected D5 components over F2[eps]/eps^5 with Delta0 pinned to the
(c1,c4) normal form and D2-D4 added as already-banked constraints.
"""
import sys
from z3 import Solver, BitVec, BitVecVal, set_param
sys.path.insert(0,'/mnt/data/v3/scripts')
from order4sat_beyond import F2epsN
from s2check import build_blocks
from s3gates import KF2, digit
T4={(1,1,2):1,(1,2,3):1}; K=KF2()
def ksum(xs):
    out=K.zero()
    for x in xs: out=K.add(out,x)
    return out
def dmat(P,s):
    out={}
    for i in range(1,4):
        for ss in range(1,4):
            terms=[]
            for n in range(1,s):
                m=s-n
                if n in P and m in P:
                    for r in range(1,4): terms.append(K.mul(P[n][(i,r)],P[m][(r,ss)]))
            out[(i,ss)]=ksum(terms)
    return out
R=F2epsN(5)
A,Mb,C,F,phi,c,Mtab=build_blocks(R,T4); base=A+Mb+C+F
c1=BitVec('pin_c1_partial',1); c4=BitVec('pin_c4_partial',1)
def pin0(i,j,k):
    if i==1:
        if (j,k) in [(1,2),(2,1),(2,3),(3,2)]: return c1
        if (j,k)==(2,2): return c4
        return BitVecVal(0,1)
    if i==2: return BitVecVal(0,1)
    if (j,k) in [(1,2),(2,1)]: return BitVecVal(1,1)
    if (j,k) in [(2,3),(3,2)]: return c1
    return BitVecVal(0,1)
for i in range(1,4):
    for j in range(1,4):
        for k in range(1,4): base.append(digit(R,c[(i,j,k)],0)==pin0(i,j,k))
P={n:{(i,r):digit(R,phi[i][r],n) for i in range(1,4) for r in range(1,4)} for n in range(1,5)}
known=list(dmat(P,2).values())+list(dmat(P,3).values())+list(dmat(P,4).values())
D5=dmat(P,5)
print('Partial s=5 t^4 probe over F2[eps]/eps^5')
print('Base constraints including pinned Delta0:', len(base))
selected=[(2,1)]
for key in selected:
    s=Solver(); s.set('timeout',90000)
    for e in base: s.add(e)
    for x in known: s.add(K.eq0(x))
    s.add(K.neq0(D5[key]))
    print('D5%s negation:'%(key,), s.check(), flush=True)
print('Skipped hard components: (1,3), (3,3).')
