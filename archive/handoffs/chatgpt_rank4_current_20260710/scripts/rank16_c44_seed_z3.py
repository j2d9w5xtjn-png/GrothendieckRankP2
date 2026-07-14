#!/usr/bin/env python3
"""Z3 full-deformation lift test for rank-16 c44 carry seeds.

Default fiber c44_ca1_cb1:
  A0 = F2[a,b]/(a^4,b^4)
  Delta(a)=a⊗1+1⊗a+a^2⊗a^2
  Delta(b)=b⊗1+1⊗b+a^2⊗a^2

The first-order linear scanner finds cotangent matrices with L^4 != 0.
This script asks whether such a direction exists under full Hopf axioms over
F2[e]/e^NE.  NE=2 reproduces the first-order seed; NE=3 asks for a
second-order lift while keeping Psi_1^4 nonzero.
"""
from __future__ import annotations
import argparse, time, itertools, sys
from z3 import Solver, BitVec, BitVecVal, Or, set_param, sat
set_param('parallel.enable', True)
T0=time.time()

def build(NE=2, ca=1, cb=1):
    caps=(4,4); r=2
    strides=[1,4]; DIM=16; I=list(range(1,DIM)); G=[1,4]
    def idx(e): return e[0]+4*e[1]
    def exps(m): return ((m//1)%4,(m//4)%4)
    MUL=[[-1]*DIM for _ in range(DIM)]
    for x in range(DIM):
        ex=exps(x)
        for y in range(DIM):
            ey=exps(y); ez=(ex[0]+ey[0],ex[1]+ey[1])
            if ez[0]<4 and ez[1]<4: MUL[x][y]=idx(ez)
    def mul(x,y):
        m=MUL[x][y]; return None if m<0 else m
    def t2(x,y): return x*DIM+y
    def u2(i): return divmod(i,DIM)
    def t3(x,y,z): return (x*DIM+y)*DIM+z
    def band(x,y):
        if isinstance(x,int): return y if x else 0
        if isinstance(y,int): return x if y else 0
        return x & y
    def bxor(x,y):
        if isinstance(x,int): return y if x==0 else bnot(y)
        if isinstance(y,int): return x if y==0 else bnot(x)
        return x ^ y
    def bnot(x):
        if isinstance(x,int): return 1-x
        return x ^ BitVecVal(1,1)
    def isz(x): return isinstance(x,int) and x==0
    a,b=G; a2=idx((2,0)); b2=idx((0,2))
    carry_basis=[[(a2,a2)],[(b2,b2)],[(a2,b2),(b2,a2)]]
    dg={a:[(a,0),(0,a)], b:[(b,0),(0,b)]}
    for i,terms in enumerate(carry_basis):
        if (ca>>i)&1: dg[a].extend(terms)
        if (cb>>i)&1: dg[b].extend(terms)
    def vmul_t2_const(u,v):
        out=0; uu=u
        while uu:
            l=uu&-uu; ii=l.bit_length()-1; uu^=l
            x,y=u2(ii); vv=v
            while vv:
                l2=vv&-vv; jj=l2.bit_length()-1; vv^=l2
                p,q=u2(jj); xp=mul(x,p); yq=mul(y,q)
                if xp is not None and yq is not None: out ^= 1<<t2(xp,yq)
        return out
    DG={}
    for g,terms in dg.items():
        v=0
        for p,q in terms: v ^= 1<<t2(p,q)
        DG[g]=v
    def dmono(m):
        out=1<<t2(0,0)
        ee=exps(m)
        for slot,e in enumerate(ee):
            g=G[slot]
            for _ in range(e): out=vmul_t2_const(out,DG[g])
        return out
    D0=[dmono(m) for m in range(DIM)]
    # quick killed/coassoc gates
    def mu_t2(v):
        out=0; vv=v
        while vv:
            l=vv&-vv; ii=l.bit_length()-1; vv^=l
            p,q=u2(ii); m=mul(p,q)
            if m is not None: out ^= 1<<m
        return out
    assert all(mu_t2(D0[x])==0 for x in I)
    # variables
    layers=list(range(1,NE)); MU={}; WV={}
    for l in layers:
        for ii,x in enumerate(I):
            for y in I[ii:]:
                MU[(l,x,y)]=[0]+[BitVec(f'm{l}_{x}_{y}_{o}',1) for o in I]
        for x in I:
            v=[0]*(DIM*DIM)
            for p in I:
                for q in I:
                    v[t2(p,q)]=BitVec(f'w{l}_{x}_{p}_{q}',1)
            WV[(l,x)]=v
    def muvar(l,x,y):
        if x>y: x,y=y,x
        return MU[(l,x,y)]
    def leg_mul(l,p,q):
        if l==0:
            m=mul(p,q); return [] if m is None else [(m,1)]
        if p==0 or q==0: return []
        mv=muvar(l,p,q); return [(o,mv[o]) for o in I]
    def basis(x):
        X=[[0]*DIM for _ in range(NE)]; X[0][x]=1; return X
    def A_mul(X,Y):
        Z=[[0]*DIM for _ in range(NE)]
        for i in range(NE):
            for j in range(NE-i):
                r0=i+j
                x0,y0=X[i][0],Y[j][0]
                if not isz(x0):
                    for c in range(DIM): Z[r0][c]=bxor(Z[r0][c], band(x0,Y[j][c]))
                if not isz(y0):
                    for c in range(DIM): Z[r0][c]=bxor(Z[r0][c], band(y0,X[i][c]))
                if not (isz(x0) or isz(y0)): Z[r0][0]=bxor(Z[r0][0], band(x0,y0))
                for x in I:
                    xx=X[i][x]
                    if isz(xx): continue
                    for y in I:
                        yy=Y[j][y]
                        if isz(yy): continue
                        xy=band(xx,yy); m=mul(x,y)
                        if m is not None: Z[r0][m]=bxor(Z[r0][m],xy)
                        for l in range(1,NE-i-j):
                            mv=muvar(l,x,y)
                            for o in I: Z[r0+l][o]=bxor(Z[r0+l][o], band(xy,mv[o]))
        return Z
    def Delta_apply(X):
        R=[[0]*(DIM*DIM) for _ in range(NE)]
        for i in range(NE):
            if not isz(X[i][0]): R[i][t2(0,0)]=bxor(R[i][t2(0,0)],X[i][0])
            for x in I:
                xx=X[i][x]
                if isz(xx): continue
                vv=D0[x]
                while vv:
                    lb=vv&-vv; k=lb.bit_length()-1; vv^=lb
                    R[i][k]=bxor(R[i][k],xx)
                for l in range(1,NE-i):
                    wv=WV[(l,x)]
                    for k,e in enumerate(wv):
                        if not isz(e): R[i+l][k]=bxor(R[i+l][k], band(xx,e))
        return R
    def T2_mul(U,V):
        Z=[[0]*(DIM*DIM) for _ in range(NE)]
        for i in range(NE):
            for iu,f in enumerate(U[i]):
                if isz(f): continue
                p,q=u2(iu)
                for j in range(NE-i):
                    for iv,g0 in enumerate(V[j]):
                        if isz(g0): continue
                        pp,qq=u2(iv); fg=band(f,g0)
                        for l1 in range(NE-i-j):
                            L=leg_mul(l1,p,pp)
                            if not L: continue
                            for l2 in range(NE-i-j-l1):
                                Rl=leg_mul(l2,q,qq)
                                if not Rl: continue
                                rr=i+j+l1+l2
                                for c1,e1 in L:
                                    fe=band(fg,e1)
                                    if isz(fe): continue
                                    for c2,e2 in Rl:
                                        tt=band(fe,e2)
                                        if isz(tt): continue
                                        Z[rr][t2(c1,c2)]=bxor(Z[rr][t2(c1,c2)],tt)
        return Z
    def coassoc_defect(x):
        U=Delta_apply(basis(x)); L=[[0]*(DIM**3) for _ in range(NE)]; R=[[0]*(DIM**3) for _ in range(NE)]
        for i in range(NE):
            for idx2,f in enumerate(U[i]):
                if isz(f): continue
                p,q=u2(idx2)
                # Delta on p in left leg
                if p==0: L[i][t3(0,0,q)]=bxor(L[i][t3(0,0,q)],f)
                else:
                    vv=D0[p]
                    while vv:
                        lb=vv&-vv; k=lb.bit_length()-1; vv^=lb
                        p1,p2=u2(k); L[i][t3(p1,p2,q)]=bxor(L[i][t3(p1,p2,q)],f)
                    for l in range(1,NE-i):
                        for k,e in enumerate(WV[(l,p)]):
                            if not isz(e):
                                p1,p2=u2(k); L[i+l][t3(p1,p2,q)]=bxor(L[i+l][t3(p1,p2,q)],band(f,e))
                if q==0: R[i][t3(p,0,0)]=bxor(R[i][t3(p,0,0)],f)
                else:
                    vv=D0[q]
                    while vv:
                        lb=vv&-vv; k=lb.bit_length()-1; vv^=lb
                        q1,q2=u2(k); R[i][t3(p,q1,q2)]=bxor(R[i][t3(p,q1,q2)],f)
                    for l in range(1,NE-i):
                        for k,e in enumerate(WV[(l,q)]):
                            if not isz(e):
                                q1,q2=u2(k); R[i+l][t3(p,q1,q2)]=bxor(R[i+l][t3(p,q1,q2)],band(f,e))
        return [[bxor(L[r][c],R[r][c]) for c in range(DIM**3)] for r in range(NE)]
    S=Solver(); neq=0
    def assert0(x):
        nonlocal_neq[0]+=1
        if isinstance(x,int):
            assert x==0
        else: S.add(x==0)
    nonlocal_neq=[0]
    print('building assoc',flush=True)
    PRODS={(x,y):A_mul(basis(x),basis(y)) for x in I for y in I}
    for x,y,z in itertools.product(I,repeat=3):
        A1=A_mul(PRODS[(x,y)],basis(z)); A2=A_mul(basis(x),PRODS[(y,z)])
        for rr in layers:
            for o in range(DIM): assert0(bxor(A1[rr][o],A2[rr][o]))
    print('building Delta-mult',nonlocal_neq[0],flush=True)
    for ii,x in enumerate(I):
        for y in I[ii:]:
            LHS=Delta_apply(A_mul(basis(x),basis(y)))
            RHS=T2_mul(Delta_apply(basis(x)),Delta_apply(basis(y)))
            for rr in layers:
                for o in range(DIM*DIM): assert0(bxor(LHS[rr][o],RHS[rr][o]))
    print('building coassoc',nonlocal_neq[0],flush=True)
    for x in I:
        C=coassoc_defect(x)
        for rr in layers:
            for o in range(DIM**3): assert0(C[rr][o])
    print('built equations',nonlocal_neq[0], 'time', time.time()-T0, flush=True)
    # Psi maps
    PSI={n:{} for n in range(NE)}
    for x in I:
        Dr=Delta_apply(basis(x)); Ph=[[0]*DIM for _ in range(NE)]
        for i in range(NE):
            for idx2,f in enumerate(Dr[i]):
                if isz(f): continue
                p,q=u2(idx2)
                for l in range(NE-i):
                    for cc,e in leg_mul(l,p,q): Ph[i+l][cc]=bxor(Ph[i+l][cc], band(f,e))
        for n in range(NE): PSI[n][x]=Ph[n]
    def psi_apply(n,vec):
        out=[0]*DIM
        for x in I:
            vx=vec[x]
            if isz(vx): continue
            Px=PSI[n][x]
            for c in range(DIM):
                if not isz(Px[c]): out[c]=bxor(out[c], band(vx,Px[c]))
        return out
    def psi_pow(x, K):
        v=[1 if c==x else 0 for c in range(DIM)]
        for _ in range(K): v=psi_apply(1,v)
        return v
    GEN=set(G)                                  # generator monomial indices (a,b)
    def nonzero_cond(K, coords=None):
        # coords=None -> full map; coords='gen' -> only generator (degree-1) outputs
        lits=[]
        outset = GEN if coords=='gen' else range(DIM)
        for x in I:
            v=psi_pow(x, K)
            for c in outset:
                if not isz(v[c]):
                    if isinstance(v[c],int): return True
                    lits.append(v[c]==BitVecVal(1,1))
        return Or(lits) if lits else False
    return S, nonzero_cond

if __name__=='__main__':
    ap=argparse.ArgumentParser(); ap.add_argument('--NE',type=int,default=2); ap.add_argument('--ca',type=int,default=1); ap.add_argument('--cb',type=int,default=1); ap.add_argument('--timeout-ms',type=int,default=0)
    ap.add_argument('--powers',type=str,default='4')     # comma list of K to test Psi_1^K != 0
    args=ap.parse_args()
    S, nonzero_cond = build(args.NE,args.ca,args.cb)
    if args.timeout_ms: S.set('timeout',args.timeout_ms)
    def ask(label, cond):
        if cond is True: print(f'{label} : trivially sat',flush=True); return
        if cond is False: print(f'{label} : trivially unsat (identically 0)',flush=True); return
        S.push(); S.add(cond); t=time.time(); r=S.check(); S.pop()
        print(f'{label} : {r}   solve_time {time.time()-t:.1f}s',flush=True)
    for K in [int(x) for x in args.powers.split(',')]:
        ask(f'Psi_1^{K} != 0 (full map)', nonzero_cond(K))
        ask(f'Psi_1^{K} != 0 (generator/deg-1 output only = L^{K} mod I^2)',
            nonzero_cond(K, coords='gen'))
