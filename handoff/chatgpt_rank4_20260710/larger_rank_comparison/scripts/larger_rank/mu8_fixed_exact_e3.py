from __future__ import annotations
import time
# Fixed algebra A=F2[t]/t^8. Deform only comultiplication of mu_8 over F2[e]/e^3.
# Δ(t)=u0+e U1+e^2 U2, Ui in I⊗I. Coassoc and test [8]=[2]^3 on t.
N=8; I=list(range(1,N)); T2=N*N; T3=N**3; NP=len(I)*len(I)
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
def radd(a,b): return tuple(x^y for x,y in zip(a,b))
def rmul_t2(a,b):
    return (vec_mul_t2(a[0],b[0]),
            vec_mul_t2(a[0],b[1])^vec_mul_t2(a[1],b[0]),
            vec_mul_t2(a[0],b[2])^vec_mul_t2(a[1],b[1])^vec_mul_t2(a[2],b[0]))
def rmul_t3(a,b):
    return (vec_mul_t3(a[0],b[0]),
            vec_mul_t3(a[0],b[1])^vec_mul_t3(a[1],b[0]),
            vec_mul_t3(a[0],b[2])^vec_mul_t3(a[1],b[1])^vec_mul_t3(a[2],b[0]))
def rvec_mul_A(a,b):
    return (vec_mul_A(a[0],b[0]),
            vec_mul_A(a[0],b[1])^vec_mul_A(a[1],b[0]),
            vec_mul_A(a[0],b[2])^vec_mul_A(a[1],b[1])^vec_mul_A(a[2],b[0]))
# u0 for mu_8 on t=T-1
u0=bit(t2_index(1,0))^bit(t2_index(0,1))^bit(t2_index(1,1))
# precompute Delta powers from u=(u0,U1,U2)
def Delta_powers(U1:int,U2:int):
    u=(u0,U1,U2)
    D=[None]*N
    D[0]=(bit(t2_index(0,0)),0,0)
    for a in range(1,N): D[a]=rmul_t2(D[a-1],u)
    return D
# embeddings T2 R vector -> T3 R vector using Delta powers
def Delta_id(vR,D):
    out=(0,0,0)
    for deg,v in enumerate(vR):
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            a,b=t2_unindex(idx); Da=D[a]
            emb=[0,0,0]
            for e,u in enumerate(Da):
                res=0; uu=u
                while uu:
                    l2=uu&-uu; j=l2.bit_length()-1; uu^=l2
                    p,q=t2_unindex(j); res^=bit(t3_index(p,q,b))
                emb[e]=res
            cur=[0,0,0]
            for e in range(3-deg): cur[e+deg]=emb[e]
            out=(out[0]^cur[0],out[1]^cur[1],out[2]^cur[2])
    return out
def id_Delta(vR,D):
    out=(0,0,0)
    for deg,v in enumerate(vR):
        vv=v
        while vv:
            l=vv&-vv; idx=l.bit_length()-1; vv^=l
            a,b=t2_unindex(idx); Db=D[b]
            emb=[0,0,0]
            for e,u in enumerate(Db):
                res=0; uu=u
                while uu:
                    l2=uu&-uu; j=l2.bit_length()-1; uu^=l2
                    p,q=t2_unindex(j); res^=bit(t3_index(a,p,q))
                emb[e]=res
            cur=[0,0,0]
            for e in range(3-deg): cur[e+deg]=emb[e]
            out=(out[0]^cur[0],out[1]^cur[1],out[2]^cur[2])
    return out
def coassoc_defect(U1,U2):
    D=Delta_powers(U1,U2); u=(u0,U1,U2)
    L=Delta_id(u,D); R=id_Delta(u,D)
    return (L[0]^R[0],L[1]^R[1],L[2]^R[2])
PARAMS=[t2_index(p,q) for p in I for q in I]
def mask_to_U(mask):
    U=0
    for j,idx in enumerate(PARAMS):
        if (mask>>j)&1: U^=bit(idx)
    return U
def bits_T3(v): return v
# linear rows for layer1 U1
def rows_layer1():
    rows=[0]*T3
    for j,idx in enumerate(PARAMS):
        d=coassoc_defect(bit(idx),0)[1]
        vv=d
        while vv:
            l=vv&-vv; i=l.bit_length()-1; vv^=l
            rows[i]^=1<<j
    return [r for r in rows if r]
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
# L for U2 full rows and transform
def L_rows_full():
    rows=[0]*T3
    for j,idx in enumerate(PARAMS):
        d=coassoc_defect(0,bit(idx))[2]
        vv=d
        while vv:
            l=vv&-vv; i=l.bit_length()-1; vv^=l
            rows[i]^=1<<j
    return rows
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
def reduce_coeff(f,Lr,rank):
    rem=f; coeff=0
    for i in range(rank):
        row=Lr[i]; p=(row&-row).bit_length()-1
        if (rem>>p)&1: rem^=row; coeff^=1<<i
    return rem,coeff
def parity(x): return x.bit_count()&1
# phi and [8]
def mu_t2(v):
    res=0; vv=v
    while vv:
        l=vv&-vv; idx=l.bit_length()-1; vv^=l
        a,b=t2_unindex(idx); c=mul_exp(a,b)
        if c is not None: res^=bit(c)
    return res
def phi_map(U1,U2):
    D=Delta_powers(U1,U2)
    # phi(t^a)=mu(D[a]) but also algebra hom by v=mu(u); using D ok
    Phi=[]
    for a in range(N): Phi.append((mu_t2(D[a][0]),mu_t2(D[a][1]),mu_t2(D[a][2])))
    return Phi
def compose_phi(Phi,val):
    out=(0,0,0)
    for deg,v in enumerate(val):
        vv=v
        while vv:
            l=vv&-vv; a=l.bit_length()-1; vv^=l
            pa=Phi[a]
            cur=[0,0,0]
            for e in range(3-deg): cur[e+deg]=pa[e]
            out=(out[0]^cur[0],out[1]^cur[1],out[2]^cur[2])
    return out
def phi3_t(U1,U2):
    Phi=phi_map(U1,U2)
    val=(bit(1),0,0)
    for _ in range(3): val=compose_phi(Phi,val)
    return val

def vals_bits_A(val,deg=2): return val[deg]
print('NP',NP)
t=time.time(); rows1=rows_layer1(); basis,rr,piv=nullspace(rows1,NP); print('layer1 rank',len(piv),'kerdim',len(basis),'rows',len(rows1),'time',time.time()-t)
L=L_rows_full(); Lr,Ltrans,Lpiv,rank=rref_trans(L,NP); zero_trans=[Ltrans[i] for i in range(rank,T3) if Lr[i]==0]
print('L rank',rank,'zero rows',len(zero_trans))
# U2 contribution to phi3 e2
F_cols=[0]*N
for j,idx in enumerate(PARAMS):
    v=phi3_t(0,bit(idx))[2]
    vv=v
    while vv:
        l=vv&-vv; o=l.bit_length()-1; vv^=l
        F_cols[o]^=1<<j
notin=[]; fcoeff=[]
for o,f in enumerate(F_cols):
    rem,coeff=reduce_coeff(f,Lr,rank); fcoeff.append(coeff)
    if rem: notin.append((o,rem))
print('F nonzero cols',sum(1 for f in F_cols if f),'notin',[(o,hex(r)) for o,r in notin[:5]])
# quadratic in U1 for rhs and phi3 e2
D=len(basis)
rhs_diag=[]; q_diag=[]
for i,b in enumerate(basis):
    U=mask_to_U(b)
    rhs_diag.append(coassoc_defect(U,0)[2])
    q_diag.append(phi3_t(U,0)[2])
print('q_diag nonzero',[(i,bin(x)) for i,x in enumerate(q_diag) if x])
rhs_cross=[[0]*(D-i-1) for i in range(D)]; q_cross=[[0]*(D-i-1) for i in range(D)]
qc=[]; rc=0
for i in range(D):
    for jj in range(D-i-1):
        j=i+1+jj; U=mask_to_U(basis[i]^basis[j])
        r=coassoc_defect(U,0)[2]^rhs_diag[i]^rhs_diag[j]
        q=phi3_t(U,0)[2]^q_diag[i]^q_diag[j]
        rhs_cross[i][jj]=r; q_cross[i][jj]=q
        if r: rc+=1
        if q: qc.append((i,j,q))
print('rhs diag nonzero',sum(1 for x in rhs_diag if x),'rhs cross nonzero',rc,'qcross',len(qc),qc[:10])
# consistency polynomials
bad=[]
for ti,tr in enumerate(zero_trans):
    for i,x in enumerate(rhs_diag):
        if parity(tr&x): bad.append(('diag',ti,i)); break
    if bad and bad[-1][1]==ti: continue
    for i in range(D):
        stop=False
        for jj,x in enumerate(rhs_cross[i]):
            if parity(tr&x): bad.append(('cross',ti,i,i+1+jj)); stop=True; break
        if stop: break
print('consistency bad coeffs',len(bad),bad[:10])
# expression coefficients after choosing any U2 solution: q + F(particular) = q + ftrans(rhs)
ftrans=[]
for coeff in fcoeff:
    tr=0; cc=coeff
    while cc:
        l=cc&-cc; i=l.bit_length()-1; cc^=l
        tr^=Ltrans[i]
    ftrans.append(tr)
expr=[]
for o,tr in enumerate(ftrans):
    for i,x in enumerate(q_diag):
        if ((x>>o)&1) ^ (parity(tr&rhs_diag[i]) if tr else 0): expr.append(('diag',o,i)); break
    if expr and expr[-1][1]==o: continue
    for i in range(D):
        stop=False
        for jj,x in enumerate(q_cross[i]):
            if ((x>>o)&1) ^ (parity(tr&x) if tr else 0): expr.append(('cross',o,i,i+1+jj)); stop=True; break
        if stop: break
print('expr nonzero coeffs',len(expr),expr[:20])
