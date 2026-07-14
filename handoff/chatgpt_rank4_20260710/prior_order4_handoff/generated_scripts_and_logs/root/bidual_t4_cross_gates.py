#!/usr/bin/env python3
from z3 import Solver, Or, BitVecVal
from order4sat_beyond import BiDual
from s2check import build_blocks
from s3gates import digit, KF2
T4={(1,1,2):1,(1,2,3):1}
R=BiDual; K=KF2()
A,Mb,C,F,phi,c,Mtab=build_blocks(R,T4)
base=A+Mb+C+F
# R basis: 0=1, 1=u, 2=v, 3=uv.
def dig(x,n): return digit(R,x,n)
P={(i,j):dig(phi[i][j],1) for i in range(1,4) for j in range(1,4)}
Q={(i,j):dig(phi[i][j],2) for i in range(1,4) for j in range(1,4)}
T={(i,j):dig(phi[i][j],3) for i in range(1,4) for j in range(1,4)}
mu_u=lambda i,j,r: dig(Mtab[(min(i,j),max(i,j),r)],1)
mu_v=lambda i,j,r: dig(Mtab[(min(i,j),max(i,j),r)],2)
p=mu_u(1,1,1); q=mu_u(1,2,1); r=mu_v(1,1,1); s=mu_v(1,2,1)
BP=P[(1,2)]; CP=P[(1,3)]; BQ=Q[(1,2)]; CQ=Q[(1,3)]

def add(*xs):
    z=BitVecVal(0,1)
    for x in xs: z = z ^ x
    return z

def mul(a,b): return a & b

def neq(x): return x != 0
# vector identities
ids=[]
# P,Q shape for sanity
for row in [2,3]:
    for col in [1,2,3]:
        ids.append((f'P kills row {row},{col}', P[(row,col)]))
        ids.append((f'Q kills row {row},{col}', Q[(row,col)]))
ids += [('P t has no t', P[(1,1)]), ('Q t has no t', Q[(1,1)])]
# T(t^2) = p Q(t)+r P(t), T(t^3)=q Q(t)+s P(t)
for col in [1,2,3]:
    ids.append((f'Tt2 col{col}', add(T[(2,col)], mul(p,Q[(1,col)]), mul(r,P[(1,col)]))))
    ids.append((f'Tt3 col{col}', add(T[(3,col)], mul(q,Q[(1,col)]), mul(s,P[(1,col)]))))
# cross Step6 identity for T(t)_t
ids.append(('Tt_t cross formula', add(T[(1,1)], mul(p,BQ), mul(q,CQ), mul(r,BP), mul(s,CP))))
# S' solvability trace identity (same)
ids.append(('trace equation', add(T[(1,1)], mul(BQ,p), mul(CQ,q), mul(BP,r), mul(CP,s))))

print('BiDual t4 cross gates')
for name, expr in ids:
    ss=Solver(); ss.add(*base); ss.add(expr != 0)
    print(f'[{name}] -> {ss.check()}')
