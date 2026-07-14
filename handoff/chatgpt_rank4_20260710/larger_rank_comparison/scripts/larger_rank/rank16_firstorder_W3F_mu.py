from __future__ import annotations
import itertools, time, sys
# Online first-order deformation equations for W_4[F] special fiber (rank 16) over F2.
# A=k[x0,x1,x2,x3]/(xi^2). Delta0 from 2-typical Witt addition, kernel of Frobenius.
d=4
DIM=1<<d
GENS=[1<<i for i in range(d)]
I_BASIS=list(range(1,DIM))
def bit(i): return 1<<i
def mul_monom(a,b): return None if (a&b) else (a|b)
def t2_index(a,b): return a*DIM+b
def t2_unindex(i): return divmod(i,DIM)
def t3_index(a,b,c): return (a*DIM+b)*DIM+c
def t3_unindex(i):
    a,r=divmod(i,DIM*DIM); b,c=divmod(r,DIM); return a,b,c
T2_DIM=DIM*DIM; T3_DIM=DIM**3
# T2 multiplication constant
def vec_mul_t2_0(u,v):
    res=0; uu=u
    while uu:
        l=uu & -uu; i=l.bit_length()-1; uu^=l
        a,b=t2_unindex(i); vv=v
        while vv:
            l2=vv & -vv; j=l2.bit_length()-1; vv^=l2
            c,d=t2_unindex(j); ac=mul_monom(a,c); bd=mul_monom(b,d)
            if ac is not None and bd is not None: res ^= bit(t2_index(ac,bd))
    return res
# W4F generator images from squarefree Witt addition mod 2.
def delta0_gen(g):
    if g==1:
        terms=[(1,0),(0,1)]
    elif g==2:
        terms=[(2,0),(0,2),(1,1)]
    elif g==4:
        terms=[(4,0),(0,4),(3,1),(1,3),(2,2)]
    elif g==8:
        terms=[(8,0),(0,8),(8,8)]
    else: raise ValueError(g)
    v=0
    for a,b in terms: v ^= bit(t2_index(a,b))
    return v
DELTA0_G={g:delta0_gen(g) for g in GENS}
def delta0_monom(m):
    res=bit(t2_index(0,0))
    for g in GENS:
        if m&g: res=vec_mul_t2_0(res,DELTA0_G[g])
    return res
DELTA0=[delta0_monom(m) for m in range(DIM)]
def mu_t2_0(v):
    res=0; vv=v
    while vv:
        l=vv & -vv; i=l.bit_length()-1; vv^=l
        a,b=t2_unindex(i); c=mul_monom(a,b)
        if c is not None: res ^= bit(c)
    return res
assert all(mu_t2_0(DELTA0[i])==0 for i in I_BASIS), 'fiber not killed by 2'
# Variables
var_index={}; vars=[]
pairs=[]
for ii,a in enumerate(I_BASIS):
    for b in I_BASIS[ii:]: pairs.append((a,b))
for a,b in pairs:
    for out in I_BASIS:
        var_index[('m',a,b,out)]=len(vars); vars.append(('m',a,b,out))
for a in I_BASIS:
    for p in I_BASIS:
        for q in I_BASIS:
            var_index[('d',a,p,q)]=len(vars); vars.append(('d',a,p,q))
NV=len(vars)
print('DIM',DIM,'NV',NV,'mu',len(pairs)*len(I_BASIS),'D',len(I_BASIS)**3, flush=True)
# Online row basis over F2, low-pivot.
class RowBasis:
    def __init__(self): self.basis={}; self.rank=0
    def reduce(self,row:int)->int:
        while row:
            p=(row & -row).bit_length()-1
            b=self.basis.get(p)
            if b is None: return row
            row ^= b
        return 0
    def add(self,row:int):
        row=self.reduce(row)
        if row:
            p=(row & -row).bit_length()-1
            self.basis[p]=row; self.rank+=1
            return True
        return False
RB=RowBasis()

def add_forms(vec):
    for f in vec:
        if f: RB.add(f)
# Linear vector funcs
def A_add(u,v): return [u[i]^v[i] for i in range(DIM)]
def T2_add(u,v): return [u[i]^v[i] for i in range(T2_DIM)]
def T3_add(u,v): return [u[i]^v[i] for i in range(T3_DIM)]
def mu1_var_vec(a,b):
    if a==0 or b==0: return [0]*DIM
    if a>b: a,b=b,a
    res=[0]*DIM
    for out in I_BASIS: res[out]=bit(var_index[('m',a,b,out)])
    return res
def D1_var_t2(a):
    res=[0]*T2_DIM
    if a==0: return res
    base=('d',a)
    for p in I_BASIS:
        for q in I_BASIS:
            res[t2_index(p,q)] = bit(var_index[('d',a,p,q)])
    return res
# Cache D1 var maybe large 15*256 arrays; okay
D1_CACHE={a:D1_var_t2(a) for a in [0]+I_BASIS}
MU1_CACHE={}
def mu1_cached(a,b):
    if a>b: a,b=b,a
    key=(a,b)
    v=MU1_CACHE.get(key)
    if v is None:
        v=mu1_var_vec(a,b); MU1_CACHE[key]=v
    return v

def A_const_mul_left(m,U):
    res=[0]*DIM
    if m==0: return U[:]  # 1*U
    for i,form in enumerate(U):
        if form:
            c=mul_monom(m,i)
            if c is not None: res[c]^=form
    return res
def A_const_mul_right(U,m): return A_const_mul_left(m,U)
def mu1_on_const_vecs(u_bits,v_bits):
    res=[0]*DIM; uu=u_bits
    while uu:
        l=uu & -uu; a=l.bit_length()-1; uu^=l
        vv=v_bits
        while vv:
            l2=vv & -vv; b=l2.bit_length()-1; vv^=l2
            if a and b: res=A_add(res,mu1_cached(a,b))
    return res
def Delta0_on_A_linear(U):
    res=[0]*T2_DIM
    for a,form in enumerate(U):
        if form:
            vv=DELTA0[a]
            while vv:
                l=vv & -vv; idx=l.bit_length()-1; vv^=l
                res[idx]^=form
    return res
def t2_const_mul_linear_left(c_bits,U):
    res=[0]*T2_DIM; cc=c_bits
    while cc:
        l=cc & -cc; idx=l.bit_length()-1; cc^=l
        a,b=t2_unindex(idx)
        for j,form in enumerate(U):
            if form:
                p,q=t2_unindex(j); ap=mul_monom(a,p); bq=mul_monom(b,q)
                if ap is not None and bq is not None: res[t2_index(ap,bq)]^=form
    return res
def t2_const_mul_linear_right(U,c_bits): return t2_const_mul_linear_left(c_bits,U)
def mu1_tensor_on_const_t2s(U_bits,V_bits):
    res=[0]*T2_DIM; uu=U_bits
    while uu:
        l=uu & -uu; i=l.bit_length()-1; uu^=l
        a,b=t2_unindex(i); vv=V_bits
        while vv:
            l2=vv & -vv; j=l2.bit_length()-1; vv^=l2
            c,d2=t2_unindex(j)
            bd=mul_monom(b,d2)
            if bd is not None:
                mvec=mu1_on_const_vecs(bit(a),bit(c))
                for out,form in enumerate(mvec):
                    if form: res[t2_index(out,bd)]^=form
            ac=mul_monom(a,c)
            if ac is not None:
                mvec=mu1_on_const_vecs(bit(b),bit(d2))
                for out,form in enumerate(mvec):
                    if form: res[t2_index(ac,out)]^=form
    return res
def Delta0_tensor_id_on_T2_linear(U):
    res=[0]*T3_DIM
    for idx,form in enumerate(U):
        if form:
            a,b=t2_unindex(idx); Da=DELTA0[a]; vv=Da
            while vv:
                l=vv & -vv; j=l.bit_length()-1; vv^=l
                p,q=t2_unindex(j); res[t3_index(p,q,b)]^=form
    return res
def id_tensor_Delta0_on_T2_linear(U):
    res=[0]*T3_DIM
    for idx,form in enumerate(U):
        if form:
            a,b=t2_unindex(idx); Db=DELTA0[b]; vv=Db
            while vv:
                l=vv & -vv; j=l.bit_length()-1; vv^=l
                p,q=t2_unindex(j); res[t3_index(a,p,q)]^=form
    return res
def D1_tensor_id_on_const_T2(C):
    res=[0]*T3_DIM; cc=C
    while cc:
        l=cc & -cc; idx=l.bit_length()-1; cc^=l
        a,b=t2_unindex(idx); Da=D1_CACHE[a]
        for j,form in enumerate(Da):
            if form:
                p,q=t2_unindex(j); res[t3_index(p,q,b)]^=form
    return res
def id_tensor_D1_on_const_T2(C):
    res=[0]*T3_DIM; cc=C
    while cc:
        l=cc & -cc; idx=l.bit_length()-1; cc^=l
        a,b=t2_unindex(idx); Db=D1_CACHE[b]
        for j,form in enumerate(Db):
            if form:
                p,q=t2_unindex(j); res[t3_index(a,p,q)]^=form
    return res
# Generate equations
t0=time.time(); count=0
print('assoc...', flush=True)
for a,b,c in itertools.product(I_BASIS, repeat=3):
    res=[0]*DIM
    ab=mul_monom(a,b)
    if ab is not None and ab!=0: res=A_add(res,mu1_cached(ab,c))
    res=A_add(res,A_const_mul_right(mu1_cached(a,b),c))
    bc=mul_monom(b,c)
    if bc is not None and bc!=0: res=A_add(res,mu1_cached(a,bc))
    res=A_add(res,A_const_mul_left(a,mu1_cached(b,c)))
    add_forms(res); count+=len([f for f in res if f])
print('rank after assoc',RB.rank,'time',time.time()-t0, flush=True)
print('Delta mult...', flush=True)
for idx,(a,b) in enumerate(itertools.product(I_BASIS, repeat=2)):
    ab=mul_monom(a,b)
    left=[0]*T2_DIM
    if ab is not None and ab!=0: left=T2_add(left,D1_CACHE[ab])
    left=T2_add(left,Delta0_on_A_linear(mu1_cached(a,b)))
    right=[0]*T2_DIM
    right=T2_add(right,t2_const_mul_linear_right(D1_CACHE[a],DELTA0[b]))
    right=T2_add(right,t2_const_mul_linear_left(DELTA0[a],D1_CACHE[b]))
    right=T2_add(right,mu1_tensor_on_const_t2s(DELTA0[a],DELTA0[b]))
    add_forms(T2_add(left,right))
print('rank after mult',RB.rank,'time',time.time()-t0, flush=True)
print('coassoc...', flush=True)
for a in I_BASIS:
    left=T3_add(D1_tensor_id_on_const_T2(DELTA0[a]),Delta0_tensor_id_on_T2_linear(D1_CACHE[a]))
    right=T3_add(id_tensor_D1_on_const_T2(DELTA0[a]),id_tensor_Delta0_on_T2_linear(D1_CACHE[a]))
    add_forms(T3_add(left,right))
    print(' coassoc a',a,'rank',RB.rank,'time',time.time()-t0, flush=True)
print('final rank',RB.rank,'dim',NV-RB.rank,'time',time.time()-t0, flush=True)
# Symbol cotangent forms (16 forms input gens/output gens)
def psi_linear_A(a):
    res=[0]*DIM
    D=D1_CACHE[a]
    for idx,form in enumerate(D):
        if form:
            p,q=t2_unindex(idx); m=mul_monom(p,q)
            if m is not None: res[m]^=form
    vv=DELTA0[a]
    while vv:
        l=vv & -vv; idx=l.bit_length()-1; vv^=l
        p,q=t2_unindex(idx)
        if p and q: res=A_add(res,mu1_cached(p,q))
    return res
forms=[]
for a in GENS:
    psi=psi_linear_A(a)
    for out in GENS: forms.append(psi[out])
# Reduce forms modulo equations
rems=[]
for f in forms: rems.append(RB.reduce(f))
print('nonzero reduced forms',sum(1 for r in rems if r), flush=True)
# Find relations among 16 remainders: combinations c with xor rem_i=0
# Row-reduce remainders as vectors, keeping transform in 16-bit output coord space.
def relations_remainders(rems):
    rows=rems[:]; trans=[1<<i for i in range(len(rows))]
    rank=0; piv=[]
    # pivot by variable column low up to NV
    # only 16 rows, simple
    for c in range(NV):
        p=None
        for i in range(rank,len(rows)):
            if (rows[i]>>c)&1: p=i; break
        if p is None: continue
        rows[rank],rows[p]=rows[p],rows[rank]
        trans[rank],trans[p]=trans[p],trans[rank]
        for i in range(len(rows)):
            if i!=rank and ((rows[i]>>c)&1):
                rows[i]^=rows[rank]; trans[i]^=trans[rank]
        piv.append(c); rank+=1
        if rank==len(rows): break
    rel=[trans[i] for i in range(rank,len(rows)) if rows[i]==0]
    return rank,rel,rows,trans
mrank,rels,_,_=relations_remainders(rems)
print('matrix image dim',mrank,'relations',len(rels),[bin(r) for r in rels], flush=True)
def mat_from_bits(bits):
    M=[[0]*d for _ in range(d)]; pos=0
    for j in range(d):
        for i in range(d):
            M[i][j]=(bits>>pos)&1; pos+=1
    return M
def matmul(A,B):
    C=[[0]*d for _ in range(d)]
    for i in range(d):
        for j in range(d):
            s=0
            for k in range(d): s^=A[i][k]&B[k][j]
            C[i][j]=s
    return C
def mnz(A): return any(A[i][j] for i in range(d) for j in range(d))
found=[]; total=0
for bits in range(1<<(d*d)):
    ok=True
    for r in rels:
        if ((bits&r).bit_count()&1): ok=False; break
    if not ok: continue
    total+=1
    M=mat_from_bits(bits); P=M
    for _ in range(3): P=matmul(P,M)  # M^4
    if mnz(P): found.append((bits,M,P)); break
print('possible matrices',total,'L^4 nonzero?',bool(found), flush=True)
if found:
    print('bits',bin(found[0][0]),'M',found[0][1],'M4',found[0][2], flush=True)
