from __future__ import annotations
import random, time, sys
# Random exact search for full algebra+coalgebra deformations of mu_8 over F2[e]/e^3.
# Solves second-layer linear equations for random first-order bialgebra cocycles and tests [8].
N=8; M=3; I=list(range(1,N)); T2=N*N; T3=N**3

def bit(i): return 1<<i
def mul0_exp(a,b):
    s=a+b; return s if s<N else None
def t2_index(a,b): return a*N+b
def t2_unindex(i): return divmod(i,N)
def t3_index(a,b,c): return (a*N+b)*N+c
def t3_unindex(i):
    a,r=divmod(i,N*N); b,c=divmod(r,N); return a,b,c
# Δ0 for mu_8
def vec_mul_t2_0(u,v):
    res=0; uu=u
    while uu:
        l=uu&-uu; idx=l.bit_length()-1; uu^=l
        a,b=t2_unindex(idx); vv=v
        while vv:
            l2=vv&-vv; j=l2.bit_length()-1; vv^=l2
            c,d=t2_unindex(j); ac=mul0_exp(a,c); bd=mul0_exp(b,d)
            if ac is not None and bd is not None: res^=bit(t2_index(ac,bd))
    return res
DELTA_T=bit(t2_index(1,0))^bit(t2_index(0,1))^bit(t2_index(1,1))
DELTA0=[0]*N; DELTA0[0]=bit(t2_index(0,0))
for a in range(1,N): DELTA0[a]=vec_mul_t2_0(DELTA0[a-1],DELTA_T)
# variables per layer: symmetric mu(a,b)->out and D(a)->p,q, normalized
pairs=[]
for ii,a in enumerate(I):
    for b in I[ii:]: pairs.append((a,b))
var=[]; vid={}
for a,b in pairs:
    for out in I:
        vid[('m',a,b,out)]=len(var); var.append(('m',a,b,out))
for a in I:
    for p in I:
        for q in I:
            vid[('d',a,p,q)]=len(var); var.append(('d',a,p,q))
NV=len(var)
print('NV',NV, flush=True)
def split_mask(mask):
    mu={}; D={}
    # mu key (a,b) with a<=b -> A bitset
    for a,b in pairs:
        v=0
        for out in I:
            j=vid[('m',a,b,out)]
            if (mask>>j)&1: v^=bit(out)
        mu[(a,b)]=v
    for a in I:
        v=0
        for p in I:
            for q in I:
                j=vid[('d',a,p,q)]
                if (mask>>j)&1: v^=bit(t2_index(p,q))
        D[a]=v
    D[0]=0
    return mu,D
ZERO_MU={(a,b):0 for a,b in pairs}; ZERO_D={a:0 for a in range(N)}
def get_mu_layer(mu,a,b):
    if a==0 or b==0: return 0
    if a>b: a,b=b,a
    return mu[(a,b)]
def mu_basis(a,b,mu1,mu2):
    v0=bit(mul0_exp(a,b)) if mul0_exp(a,b) is not None else 0
    return (v0,get_mu_layer(mu1,a,b),get_mu_layer(mu2,a,b))
def A_mul_vec_layer(u,v,mu1,mu2):
    # u,v are A bitsets (one layer vectors); product as R-bilinear? This returns product using full mu layers? Not here.
    raise NotImplementedError
# Full R multiplication in A: inputs len3 A-bitsets, output len3.
def A_mul_R(x,y,mu1,mu2):
    out=[0,0,0]
    for i,ui in enumerate(x):
        if not ui: continue
        for j,vj in enumerate(y):
            if not vj or i+j>=M: continue
            # multiply layer vectors with mu0/mu1/mu2, shifted by i+j
            uu=ui
            while uu:
                l=uu&-uu; a=l.bit_length()-1; uu^=l
                vv=vj
                while vv:
                    l2=vv&-vv; b=l2.bit_length()-1; vv^=l2
                    mb=mu_basis(a,b,mu1,mu2)
                    for k in range(M-(i+j)):
                        out[i+j+k]^=mb[k]
    return tuple(out)
def T2_mul_R(x,y,mu1,mu2):
    out=[0,0,0]
    for i,ui in enumerate(x):
        if not ui: continue
        for j,vj in enumerate(y):
            if not vj or i+j>=M: continue
            uu=ui
            while uu:
                l=uu&-uu; idx=l.bit_length()-1; uu^=l
                a,b=t2_unindex(idx); vv=vj
                while vv:
                    l2=vv&-vv; jdx=l2.bit_length()-1; vv^=l2
                    c,d=t2_unindex(jdx)
                    left=mu_basis(a,c,mu1,mu2); right=mu_basis(b,d,mu1,mu2)
                    # tensor product of A products; combine layer k+l
                    for k in range(M-(i+j)):
                        if not left[k]: continue
                        for ldeg in range(M-(i+j)-k):
                            if not right[ldeg]: continue
                            # tensor product of A bitsets left[k] ⊗ right[ldeg]
                            res=0; aa=left[k]
                            while aa:
                                la=aa&-aa; p=la.bit_length()-1; aa^=la
                                bb=right[ldeg]
                                while bb:
                                    lb=bb&-bb; q=lb.bit_length()-1; bb^=lb
                                    res^=bit(t2_index(p,q))
                            out[i+j+k+ldeg]^=res
    return tuple(out)
def T3_mul_R(x,y,mu1,mu2):
    out=[0,0,0]
    for i,ui in enumerate(x):
        if not ui: continue
        for j,vj in enumerate(y):
            if not vj or i+j>=M: continue
            uu=ui
            while uu:
                l=uu&-uu; idx=l.bit_length()-1; uu^=l
                a,b,c=t3_unindex(idx); vv=vj
                while vv:
                    l2=vv&-vv; jdx=l2.bit_length()-1; vv^=l2
                    d,e,f=t3_unindex(jdx)
                    A=mu_basis(a,d,mu1,mu2); B=mu_basis(b,e,mu1,mu2); C=mu_basis(c,f,mu1,mu2)
                    for ka in range(M-(i+j)):
                        if not A[ka]: continue
                        for kb in range(M-(i+j)-ka):
                            if not B[kb]: continue
                            for kc in range(M-(i+j)-ka-kb):
                                if not C[kc]: continue
                                res=0; aa=A[ka]
                                while aa:
                                    la=aa&-aa; p=la.bit_length()-1; aa^=la
                                    bb=B[kb]
                                    while bb:
                                        lb=bb&-bb; q=lb.bit_length()-1; bb^=lb
                                        cc=C[kc]
                                        while cc:
                                            lc=cc&-cc; r=lc.bit_length()-1; cc^=lc
                                            res^=bit(t3_index(p,q,r))
                                out[i+j+ka+kb+kc]^=res
    return tuple(out)
def Delta_basis(a,D1,D2):
    if a==0: return (bit(t2_index(0,0)),0,0)
    return (DELTA0[a],D1[a],D2[a])
def Delta_A_R(x,D1,D2):
    out=[0,0,0]
    for deg,v in enumerate(x):
        vv=v
        while vv:
            l=vv&-vv; a=l.bit_length()-1; vv^=l
            Da=Delta_basis(a,D1,D2)
            for k in range(M-deg): out[deg+k]^=Da[k]
    return tuple(out)
def Delta_id_T2_R(x,D1,D2):
    out=[0,0,0]
    for deg,v in enumerate(x):
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            a,b=t2_unindex(idx); Da=Delta_basis(a,D1,D2)
            for k in range(M-deg):
                res=0; uu=Da[k]
                while uu:
                    l2=uu&-uu; j=l2.bit_length()-1; uu^=l2
                    p,q=t2_unindex(j); res^=bit(t3_index(p,q,b))
                out[deg+k]^=res
    return tuple(out)
def id_Delta_T2_R(x,D1,D2):
    out=[0,0,0]
    for deg,v in enumerate(x):
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            a,b=t2_unindex(idx); Db=Delta_basis(b,D1,D2)
            for k in range(M-deg):
                res=0; uu=Db[k]
                while uu:
                    l2=uu&-uu; j=l2.bit_length()-1; uu^=l2
                    p,q=t2_unindex(j); res^=bit(t3_index(a,p,q))
                out[deg+k]^=res
    return tuple(out)
# equation positions
assoc_pos={}; mult_pos={}; coassoc_pos={}; pos=0
for a in I:
  for b in I:
   for c in I:
    for out in range(N): assoc_pos[(a,b,c,out)]=pos; pos+=1
for a in I:
  for b in I:
   for idx in range(T2): mult_pos[(a,b,idx)]=pos; pos+=1
for a in I:
  for idx in range(T3): coassoc_pos[(a,idx)]=pos; pos+=1
EQ=pos
print('EQ',EQ, flush=True)
def defects_bits(mu1,D1,mu2,D2,layer):
    bits=0
    # assoc
    for a in I:
      for b in I:
       for c in I:
        left=A_mul_R(mu_basis(a,b,mu1,mu2),(bit(c),0,0),mu1,mu2)
        left=A_mul_R(mu_basis(a,b,mu1,mu2),(bit(c),0,0),mu1,mu2)
        # Actually need (a*b)*c and a*(b*c)
        left=A_mul_R(mu_basis(a,b,mu1,mu2),(bit(c),0,0),mu1,mu2)
        right=A_mul_R((bit(a),0,0),mu_basis(b,c,mu1,mu2),mu1,mu2)
        v=left[layer]^right[layer]
        vv=v
        while vv:
            l=vv&-vv; out=l.bit_length()-1; vv^=l
            bits^=1<<assoc_pos[(a,b,c,out)]
    # Delta multiplicativity
    for a in I:
      for b in I:
        left=Delta_A_R(mu_basis(a,b,mu1,mu2),D1,D2)
        right=T2_mul_R(Delta_basis(a,D1,D2),Delta_basis(b,D1,D2),mu1,mu2)
        v=left[layer]^right[layer]
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            bits^=1<<mult_pos[(a,b,idx)]
    # coassoc
    for a in I:
        left=Delta_id_T2_R(Delta_basis(a,D1,D2),D1,D2)
        right=id_Delta_T2_R(Delta_basis(a,D1,D2),D1,D2)
        v=left[layer]^right[layer]
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            bits^=1<<coassoc_pos[(a,idx)]
    return bits
# Build columns for layer variable
def varmask_to_struct(mask): return split_mask(mask)
def column_bits(j,layer=1):
    mask=1<<j; mu,D=split_mask(mask)
    if layer==1: return defects_bits(mu,D,ZERO_MU,ZERO_D,1)
    else: return defects_bits(ZERO_MU,ZERO_D,mu,D,2)
print('building columns', flush=True)
t0=time.time(); cols=[]
for j in range(NV):
    cols.append(column_bits(j,1))
print('columns built',time.time()-t0, flush=True)
# transpose to rows
rows=[0]*EQ
for j,c in enumerate(cols):
    cc=c
    while cc:
        l=cc&-cc; i=l.bit_length()-1; cc^=l
        rows[i]^=1<<j
rows=[r for r in rows if r]
print('nonzero rows',len(rows), flush=True)
def rref(rows,ncols):
    rows=rows[:]; piv=[]; r=0
    for c in range(ncols):
        p=None
        for i in range(r,len(rows)):
            if (rows[i]>>c)&1: p=i; break
        if p is None: continue
        rows[r],rows[p]=rows[p],rows[r]
        for i in range(len(rows)):
            if i!=r and ((rows[i]>>c)&1): rows[i]^=rows[r]
        piv.append(c); r+=1
    return rows[:r],piv
def nullspace(rows,ncols):
    rr,piv=rref(rows,ncols); pivset=set(piv); free=[c for c in range(ncols) if c not in pivset]
    basis=[]
    for f in free:
        x=1<<f
        for row,p in zip(rr,piv):
            if (row>>f)&1: x|=1<<p
        basis.append(x)
    return basis,rr,piv
basis,rr,piv=nullspace(rows,NV)
print('rank',len(piv),'kerdim',len(basis), flush=True)
# Need transform for solving. Recompute rows full with transforms over EQ rows.
def rref_trans(fullrows,ncols):
    rows=fullrows[:]; trans=[1<<i for i in range(len(rows))]; piv=[]; r=0
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
# Use full rows including zeros for consistency transforms
fullrows=[0]*EQ
for j,c in enumerate(cols):
    cc=c
    while cc:
        l=cc&-cc; i=l.bit_length()-1; cc^=l
        fullrows[i]^=1<<j
Lr,Ltrans,Lpiv,rank=rref_trans(fullrows,NV)
zero_trans=[Ltrans[i] for i in range(rank,EQ) if Lr[i]==0]
print('trans rank',rank,'zero',len(zero_trans), flush=True)
def parity(x): return x.bit_count()&1
def solve(rhs):
    for tr in zero_trans:
        if parity(tr&rhs): return None
    sol=0
    for i,p in enumerate(Lpiv):
        if parity(Ltrans[i]&rhs): sol^=1<<p
    return sol
# kernel for layer2 solutions = basis
# phi map and compose for full structure
def mu_t2_R(vR,mu1,mu2):
    # multiply tensor components via algebra multiplication and then multiply the two factors? μ: A⊗A->A.
    out=[0,0,0]
    for deg,v in enumerate(vR):
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            a,b=t2_unindex(idx); mb=mu_basis(a,b,mu1,mu2)
            for k in range(M-deg): out[deg+k]^=mb[k]
    return tuple(out)
def phi_basis(a,mu1,D1,mu2,D2): return mu_t2_R(Delta_basis(a,D1,D2),mu1,mu2)
def phi_map(mu1,D1,mu2,D2): return [phi_basis(a,mu1,D1,mu2,D2) for a in range(N)]
def compose_phi(Phi,val):
    out=[0,0,0]
    for deg,v in enumerate(val):
        vv=v
        while vv:
            l=vv&-vv; a=l.bit_length()-1; vv^=l
            pa=Phi[a]
            for k in range(M-deg): out[deg+k]^=pa[k]
    return tuple(out)
def phi3_t(mu1,D1,mu2,D2):
    Phi=phi_map(mu1,D1,mu2,D2); val=(bit(1),0,0)
    for _ in range(3): val=compose_phi(Phi,val)
    return val
# random search
rng=random.Random(1)
def rand_span(basis):
    m=0
    for b in basis:
        if rng.getrandbits(1): m^=b
    return m
ntest=int(sys.argv[1]) if len(sys.argv)>1 else 200
found=None; tried=0; solv=0
t0=time.time()
for s in range(ntest):
    m1=rand_span(basis); mu1,D1=split_mask(m1)
    rhs=defects_bits(mu1,D1,ZERO_MU,ZERO_D,2)
    p2=solve(rhs)
    if p2 is None: continue
    solv+=1
    # try several layer2 choices
    for _ in range(10):
        m2=p2^rand_span(basis); mu2,D2=split_mask(m2)
        # validate layer2 maybe
        v=defects_bits(mu1,D1,mu2,D2,2)
        if v:
            print('solver bug',v.bit_count()); sys.exit()
        q=phi3_t(mu1,D1,mu2,D2)[2]
        if q:
            found=(m1,m2,q); break
    if found: break
    tried+=1
    if s%20==0: print('sample',s,'solv',solv,'elapsed',time.time()-t0, flush=True)
print('done tried',tried,'solv',solv,'found',found,'elapsed',time.time()-t0, flush=True)
