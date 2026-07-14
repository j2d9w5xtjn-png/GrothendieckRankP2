from __future__ import annotations
import time, itertools
# Fixed algebra A=F2[t]/t^8; exact comultiplication deformations of mu_8 over F2[e]/e^4.
# Search for coassociative Δ(t)=u0+eU1+e^2U2+e^3U3 with [8]^#(t)=phi^3(t) nonzero.
N=8; M=4; I=list(range(1,N)); T2=N*N; T3=N**3; NP=len(I)*len(I)
def bit(i): return 1<<i
def mul_exp(a,b):
    s=a+b; return s if s<N else None
def t2_index(a,b): return a*N+b
def t2_unindex(i): return divmod(i,N)
def t3_index(a,b,c): return (a*N+b)*N+c
def t3_unindex(i):
    a,r=divmod(i,N*N); b,c=divmod(r,N); return a,b,c
def vec_mul_A(u,v):
    res=0; uu=u
    while uu:
        l=uu&-uu; a=l.bit_length()-1; uu^=l
        vv=v
        while vv:
            l2=vv&-vv; b=l2.bit_length()-1; vv^=l2
            c=mul_exp(a,b)
            if c is not None: res^=bit(c)
    return res
def vec_mul_t2(u,v):
    res=0; uu=u
    while uu:
        l=uu&-uu; idx=l.bit_length()-1; uu^=l
        a,b=t2_unindex(idx); vv=v
        while vv:
            l2=vv&-vv; j=l2.bit_length()-1; vv^=l2
            c,d=t2_unindex(j); ac=mul_exp(a,c); bd=mul_exp(b,d)
            if ac is not None and bd is not None: res^=bit(t2_index(ac,bd))
    return res
def vec_mul_t3(u,v):
    res=0; uu=u
    while uu:
        l=uu&-uu; idx=l.bit_length()-1; uu^=l
        a,b,c=t3_unindex(idx); vv=v
        while vv:
            l2=vv&-vv; j=l2.bit_length()-1; vv^=l2
            d,e,f=t3_unindex(j); ad=mul_exp(a,d); be=mul_exp(b,e); cf=mul_exp(c,f)
            if ad is not None and be is not None and cf is not None: res^=bit(t3_index(ad,be,cf))
    return res
def rmul(kind,a,b):
    mul = vec_mul_t2 if kind==2 else vec_mul_t3 if kind==3 else vec_mul_A
    out=[0]*M
    for i in range(M):
        if not a[i]: continue
        for j in range(M-i):
            if b[j]: out[i+j]^=mul(a[i],b[j])
    return tuple(out)
def radd(a,b): return tuple(a[i]^b[i] for i in range(M))
u0=bit(t2_index(1,0))^bit(t2_index(0,1))^bit(t2_index(1,1))
PARAMS=[t2_index(p,q) for p in I for q in I]
def mask_to_U(mask):
    U=0
    for j,idx in enumerate(PARAMS):
        if (mask>>j)&1: U^=bit(idx)
    return U
def U_to_mask(U):
    m=0
    for j,idx in enumerate(PARAMS):
        if (U>>idx)&1: m^=1<<j
    return m
def Delta_powers(Us):
    u=tuple([u0]+list(Us))
    D=[None]*N; D[0]=tuple([bit(t2_index(0,0))]+[0]*(M-1))
    for a in range(1,N): D[a]=rmul(2,D[a-1],u)
    return D
def Delta_id(vR,D):
    out=[0]*M
    for deg,v in enumerate(vR):
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            a,b=t2_unindex(idx); Da=D[a]
            emb=[0]*M
            for e,u in enumerate(Da):
                res=0; uu=u
                while uu:
                    l2=uu&-uu; j=l2.bit_length()-1; uu^=l2
                    p,q=t2_unindex(j); res^=bit(t3_index(p,q,b))
                emb[e]=res
            for e in range(M-deg): out[e+deg]^=emb[e]
    return tuple(out)
def id_Delta(vR,D):
    out=[0]*M
    for deg,v in enumerate(vR):
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            a,b=t2_unindex(idx); Db=D[b]
            emb=[0]*M
            for e,u in enumerate(Db):
                res=0; uu=u
                while uu:
                    l2=uu&-uu; j=l2.bit_length()-1; uu^=l2
                    p,q=t2_unindex(j); res^=bit(t3_index(a,p,q))
                emb[e]=res
            for e in range(M-deg): out[e+deg]^=emb[e]
    return tuple(out)
def coassoc_defect(Us):
    D=Delta_powers(Us); u=tuple([u0]+list(Us))
    L=Delta_id(u,D); R=id_Delta(u,D)
    return tuple(L[i]^R[i] for i in range(M))
def mu_t2(v):
    res=0; vv=v
    while vv:
        l=vv&-vv; idx=l.bit_length()-1; vv^=l
        a,b=t2_unindex(idx); c=mul_exp(a,b)
        if c is not None: res^=bit(c)
    return res
def phi_map(Us):
    D=Delta_powers(Us); Phi=[]
    for a in range(N): Phi.append(tuple(mu_t2(D[a][i]) for i in range(M)))
    return Phi
def compose_phi(Phi,val):
    out=[0]*M
    for deg,v in enumerate(val):
        vv=v
        while vv:
            l=vv&-vv; a=l.bit_length()-1; vv^=l
            pa=Phi[a]
            for e in range(M-deg): out[e+deg]^=pa[e]
    return tuple(out)
def phi3_t(Us):
    Phi=phi_map(Us); val=tuple([bit(1)]+[0]*(M-1))
    for _ in range(3): val=compose_phi(Phi,val)
    return val
# Linear algebra over F2 rows length NP
def rref_trans(rows,ncols):
    rows=rows[:]; trans=[1<<i for i in range(len(rows))]; piv=[]; r=0
    for c in range(ncols):
        p=None
        for i in range(r,len(rows)):
            if (rows[i]>>c)&1: p=i; break
        if p is None: continue
        rows[r],rows[p]=rows[p],rows[r]; trans[r],trans[p]=trans[p],trans[r]
        for i in range(len(rows)):
            if i!=r and ((rows[i]>>c)&1): rows[i]^=rows[r]; trans[i]^=trans[r]
        piv.append(c); r+=1
    return rows,trans,piv,r
def kernel_from_rref(rows,piv,ncols):
    pivset=set(piv); free=[c for c in range(ncols) if c not in pivset]; ker=[]
    for f in free:
        x=1<<f
        for row,p in zip(rows,piv):
            if (row>>f)&1: x|=1<<p
        ker.append(x)
    return ker
def parity(x): return x.bit_count()&1
# L rows for top layer variable
Lrows=[0]*T3
for j,idx in enumerate(PARAMS):
    Us=[0,0,bit(idx)]
    d=coassoc_defect(Us)[3]
    vv=d
    while vv:
        l=vv&-vv; i=l.bit_length()-1; vv^=l
        Lrows[i]^=1<<j
Lr,Ltrans,Lpiv,rank=rref_trans(Lrows,NP)
zero_trans=[Ltrans[i] for i in range(rank,T3) if Lr[i]==0]
K=kernel_from_rref(Lr[:rank],Lpartial_piv if False else Lpiv,NP)
# fix typo by recomputing K above works
print('NP',NP,'L rank',rank,'kerdim',len(K),'zero',len(zero_trans), flush=True)
def solve_L(rhs):
    for tr in zero_trans:
        if parity(tr&rhs): return None
    sol=0
    # transformed RHS for pivot rows gives pivot values when free=0
    for row_i,p in enumerate(Lpiv):
        if parity(Ltrans[row_i]&rhs): sol^=1<<p
    return sol
def lin_F_top():
    F=[0]*N
    for j,idx in enumerate(PARAMS):
        q=phi3_t([0,0,bit(idx)])[3]
        vv=q
        while vv:
            l=vv&-vv; o=l.bit_length()-1; vv^=l
            F[o]^=1<<j
    return F
F=lin_F_top()
Fker=[]
for km in K:
    U=mask_to_U(km); q=phi3_t([0,0,U])[3]
    Fker.append(q)
print('F nonzero outputs',[(i,bin(f)) for i,f in enumerate(F) if f],'Fker nonzero',[(i,bin(q)) for i,q in enumerate(Fker) if q], flush=True)

# Q-only enumeration: since F(U3)=0 in the previous setup, [8] top does not depend on U3.
# Check q=phi^3(t)_e3 for every U1 and every U2 solving layer2; this is stronger than layer3 coassoc.
t0=time.time(); cand=None; total=0
for m1sel in range(1<<len(K)):
    m1=0
    for i,k in enumerate(K):
        if (m1sel>>i)&1: m1^=k
    U1=mask_to_U(m1)
    rhs2=coassoc_defect([U1,0,0])[2]
    p2=solve_L(rhs2)
    if p2 is None:
        print('unexpected no U2')
        continue
    for m2sel in range(1<<len(K)):
        m2=p2
        for i,k in enumerate(K):
            if (m2sel>>i)&1: m2^=k
        U2=mask_to_U(m2)
        q=phi3_t([U1,U2,0])[3]
        total+=1
        if q:
            cand=(m1,m2,q); break
    if cand: break
    if m1sel%16==0: print('m1sel',m1sel,'total',total,'elapsed',time.time()-t0, flush=True)
print('qonly done total',total,'cand',cand,'elapsed',time.time()-t0, flush=True)
