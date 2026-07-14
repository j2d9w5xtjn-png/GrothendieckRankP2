from __future__ import annotations
import random, time, sys
# Fixed exterior algebra rank 8 over F2[e]/e^N; search comultiplication deformations
# of a selected special fiber for [8]=phi^3 nonzero.
DIM=8; GENS=[1,2,4]; I_BASIS=list(range(1,8)); T2_DIM=64; T3_DIM=512

def bit(i): return 1<<i
def mul_monom(a,b): return None if (a&b) else (a|b)
def t2_index(a,b): return a*8+b
def t2_unindex(i): return divmod(i,8)
def t3_index(a,b,c): return (a*8+b)*8+c
def t3_unindex(i):
    a,r=divmod(i,64); b,c=divmod(r,8); return a,b,c

def vec_mul_t2(u,v):
    res=0; uu=u
    while uu:
        l=uu&-uu; i=l.bit_length()-1; uu^=l
        a,b=t2_unindex(i); vv=v
        while vv:
            l2=vv&-vv; j=l2.bit_length()-1; vv^=l2
            c,d=t2_unindex(j); ac=mul_monom(a,c); bd=mul_monom(b,d)
            if ac is not None and bd is not None: res^=bit(t2_index(ac,bd))
    return res

def vec_mul_t3(u,v):
    res=0; uu=u
    while uu:
        l=uu&-uu; i=l.bit_length()-1; uu^=l
        a,b,c=t3_unindex(i); vv=v
        while vv:
            l2=vv&-vv; j=l2.bit_length()-1; vv^=l2
            d,e,f=t3_unindex(j); ad=mul_monom(a,d); be=mul_monom(b,e); cf=mul_monom(c,f)
            if ad is not None and be is not None and cf is not None: res^=bit(t3_index(ad,be,cf))
    return res

def delta0_W3F(g):
    if g==1: terms=[(1,0),(0,1)]
    elif g==2: terms=[(2,0),(0,2),(1,1)]
    elif g==4: terms=[(4,0),(0,4),(3,1),(1,3),(2,2)]
    else: raise ValueError
    v=0
    for a,b in terms: v^=bit(t2_index(a,b))
    return v

def delta0_W2A(g):
    if g==1: terms=[(1,0),(0,1)]
    elif g==2: terms=[(2,0),(0,2),(1,1)]
    elif g==4: terms=[(4,0),(0,4)]
    else: raise ValueError
    v=0
    for a,b in terms: v^=bit(t2_index(a,b))
    return v

def delta0_alpha(g): return bit(t2_index(g,0))^bit(t2_index(0,g))

def delta0_heis(g):
    if g==1 or g==2: return bit(t2_index(g,0))^bit(t2_index(0,g))
    if g==4: return bit(t2_index(4,0))^bit(t2_index(0,4))^bit(t2_index(1,2))
    raise ValueError
SPECIALS={'W3F':delta0_W3F,'W2A':delta0_W2A,'alpha':delta0_alpha,'heis':delta0_heis}
name=sys.argv[1] if len(sys.argv)>1 else 'W3F'
N=int(sys.argv[2]) if len(sys.argv)>2 else 5
DELTA0_G={g:SPECIALS[name](g) for g in GENS}
def delta0_monom(m):
    res=bit(t2_index(0,0))
    for g in GENS:
        if m&g: res=vec_mul_t2(res,DELTA0_G[g])
    return res
DELTA0=[delta0_monom(m) for m in range(8)]
# ring vector operations length N for T2/T3/A

def rmul_t2(a,b):
    out=[0]*N
    for i in range(N):
        if not a[i]: continue
        for j in range(N-i):
            if b[j]: out[i+j]^=vec_mul_t2(a[i],b[j])
    return tuple(out)
def rmul_t3(a,b):
    out=[0]*N
    for i in range(N):
        if not a[i]: continue
        for j in range(N-i):
            if b[j]: out[i+j]^=vec_mul_t3(a[i],b[j])
    return tuple(out)

def build_delta(D_layers):
    # D_layers list length N, D_layers[0] ignored/zero? each dict g->T2 vec for coefficient degree s.
    genR={}
    for g in GENS:
        arr=[0]*N; arr[0]=DELTA0_G[g]
        for s in range(1,N): arr[s]=D_layers[s].get(g,0)
        genR[g]=tuple(arr)
    Delta=[None]*8; zero=tuple([0]*N)
    one=[0]*N; one[0]=bit(t2_index(0,0)); Delta[0]=tuple(one)
    for m in range(1,8):
        res=tuple(one)
        for g in GENS:
            if m&g: res=rmul_t2(res,genR[g])
        Delta[m]=res
    return Delta

def embed_Delta_id_T2_R(vR, Delta):
    out=[0]*N
    for deg,v in enumerate(vR):
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            a,b=t2_unindex(idx); Da=Delta[a]
            for s in range(N-deg):
                u=Da[s]; uu=u
                while uu:
                    ll=uu&-uu; j=ll.bit_length()-1; uu^=ll
                    p,q=t2_unindex(j); out[deg+s]^=bit(t3_index(p,q,b))
    return tuple(out)

def embed_id_Delta_T2_R(vR, Delta):
    out=[0]*N
    for deg,v in enumerate(vR):
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            a,b=t2_unindex(idx); Db=Delta[b]
            for s in range(N-deg):
                u=Db[s]; uu=u
                while uu:
                    ll=uu&-uu; j=ll.bit_length()-1; uu^=ll
                    p,q=t2_unindex(j); out[deg+s]^=bit(t3_index(a,p,q))
    return tuple(out)

def coassoc_defect(D_layers):
    Delta=build_delta(D_layers)
    defs=[]
    for g in GENS:
        L=embed_Delta_id_T2_R(Delta[g],Delta)
        R=embed_id_Delta_T2_R(Delta[g],Delta)
        defs.append(tuple(L[i]^R[i] for i in range(N)))
    return defs
# parameter masks for D_s
PARAMS=[]
for g in GENS:
    for a in I_BASIS:
        for b in I_BASIS: PARAMS.append((g,t2_index(a,b)))
NP=len(PARAMS)
def D_from_mask(mask):
    D={g:0 for g in GENS}
    for j,(g,idx) in enumerate(PARAMS):
        if (mask>>j)&1: D[g]^=bit(idx)
    return D

def layer_bits(defs,s):
    out=0
    for gi,d in enumerate(defs):
        v=d[s]; vv=v
        while vv:
            l=vv&-vv; c=l.bit_length()-1; vv^=l
            out^=1<<(gi*T3_DIM+c)
    return out

def build_L_rows():
    rows=[0]*(3*T3_DIM)
    for j,(g,idx) in enumerate(PARAMS):
        D_layers=[{gg:0 for gg in GENS} for _ in range(N)]
        D_layers[1][g]=bit(idx)
        bits=layer_bits(coassoc_defect(D_layers),1)
        bb=bits
        while bb:
            l=bb&-bb; i=l.bit_length()-1; bb^=l
            rows[i]^=1<<j
    return [r for r in rows if r]

def gf2_rref(rows,ncols):
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
        if r==len(rows): break
    return rows[:r],piv

def nullspace_basis(rows,ncols):
    rref,piv=gf2_rref(rows,ncols); pivset=set(piv); free=[c for c in range(ncols) if c not in pivset]
    basis=[]
    for f in free:
        x=1<<f
        for row,p in zip(rref,piv):
            if (row>>f)&1: x|=1<<p
        basis.append(x)
    return basis,rref,piv

def solve_aug(Lr,piv,rhs_bits):
    # rhs row vector length M; use equations rows original? Need reduce augmented by recomputing rows with RHS? Simpler use full rows with RHS.
    # We'll use prebuilt full Lrows_full length M and RREF with transforms below instead.
    pass
# Build full L rows and rref with transforms for solving RHS quickly
M=3*T3_DIM
def build_L_full():
    rows=[0]*M
    for j,(g,idx) in enumerate(PARAMS):
        D_layers=[{gg:0 for gg in GENS} for _ in range(N)]
        D_layers[1][g]=bit(idx)
        bits=layer_bits(coassoc_defect(D_layers),1)
        bb=bits
        while bb:
            l=bb&-bb; i=l.bit_length()-1; bb^=l
            rows[i]^=1<<j
    return rows

def rref_transform(rows,ncols):
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
        if r==len(rows): break
    return rows,trans,piv,r

def parity(x): return x.bit_count()&1
print('special',name,'N',N,'building L')
t0=time.time(); Lfull=build_L_full(); Lr,Ltrans,Lpiv,rank=rref_transform(Lfull,NP)
zero_trans=[Ltrans[i] for i in range(rank,M) if Lr[i]==0]
free=[c for c in range(NP) if c not in set(Lpiv)]
ker=[]
for f in free:
    x=1<<f
    for row,p in zip(Lr[:rank],Lpiv):
        if (row>>f)&1: x|=1<<p
    ker.append(x)
print('rank',rank,'kerdim',len(ker),'zero_cons',len(zero_trans),'time',time.time()-t0)

def solve_rhs(rhs):
    for tr in zero_trans:
        if parity(tr&rhs): return None
    sol=0
    for i,p in enumerate(Lpiv):
        if parity(Ltrans[i]&rhs): sol|=1<<p
    return sol

def randomize(sol):
    for b in ker:
        if random.getrandbits(1): sol^=b
    return sol
# phi computation length N

def mu_t2(v):
    res=0; vv=v
    while vv:
        l=vv&-vv; i=l.bit_length()-1; vv^=l
        a,b=t2_unindex(i); c=mul_monom(a,b)
        if c is not None: res^=bit(c)
    return res

def mul_A_vec(u,v):
    res=0; uu=u
    while uu:
        l=uu&-uu; i=l.bit_length()-1; uu^=l
        vv=v
        while vv:
            l2=vv&-vv; j=l2.bit_length()-1; vv^=l2
            c=mul_monom(i,j)
            if c is not None: res^=bit(c)
    return res

def rmul_A(a,b):
    out=[0]*N
    for i in range(N):
        if not a[i]: continue
        for j in range(N-i):
            if b[j]: out[i+j]^=mul_A_vec(a[i],b[j])
    return tuple(out)

def phi_map(D_layers):
    Delta=build_delta(D_layers)
    genPhi={g:tuple(mu_t2(Delta[g][s]) for s in range(N)) for g in GENS}
    Phi=[None]*8; one=[0]*N; one[0]=bit(0); Phi[0]=tuple(one)
    for m in range(1,8):
        res=tuple(one)
        for g in GENS:
            if m&g: res=rmul_A(res,genPhi[g])
        Phi[m]=res
    return Phi

def compose_phi(Phi,val):
    out=[0]*N
    for deg,v in enumerate(val):
        vv=v
        while vv:
            l=vv&-vv; a=l.bit_length()-1; vv^=l
            pa=Phi[a]
            for s in range(N-deg): out[deg+s]^=pa[s]
    return tuple(out)

def phi3_nonzero(D_layers):
    Phi=phi_map(D_layers)
    vals=[]
    for g in GENS:
        v=[0]*N; v[0]=bit(g); v=tuple(v)
        for _ in range(3): v=compose_phi(Phi,v)
        vals.append(v)
    return any(any(v[s] for s in range(N)) for v in vals), vals
# sample recursively
trials=int(sys.argv[3]) if len(sys.argv)>3 else 2000
found=None; bad=0
for tr in range(trials):
    D_layers=[{g:0 for g in GENS} for _ in range(N)]
    # choose D1 from kernel
    sol=0
    for b in ker:
        if random.getrandbits(1): sol^=b
    D_layers[1]=D_from_mask(sol)
    ok=True
    for s in range(2,N):
        # compute defect with Ds=0 at layer s; need solve L(Ds)=defect (char2)
        defs=coassoc_defect(D_layers)
        rhs=layer_bits(defs,s)
        base=solve_rhs(rhs)
        if base is None:
            ok=False; bad+=1; break
        sol_s=randomize(base)
        D_layers[s]=D_from_mask(sol_s)
        # optional verify lower layers zero
    if not ok: continue
    defs=coassoc_defect(D_layers)
    if any(layer_bits(defs,s) for s in range(1,N)):
        print('BUG coassoc fail'); sys.exit(1)
    nz,vals=phi3_nonzero(D_layers)
    if nz:
        print('FOUND tr',tr,'vals',vals)
        found=D_layers; break
    if tr and tr%100==0: print('tr',tr,'bad',bad,'elapsed',time.time()-t0)
print('done found',bool(found),'bad',bad,'elapsed',time.time()-t0)
