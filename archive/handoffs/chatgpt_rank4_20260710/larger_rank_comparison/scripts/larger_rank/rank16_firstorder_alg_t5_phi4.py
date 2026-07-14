from __future__ import annotations
import itertools, time
# First-order deformations of the rank-16 algebra group 1 + (t)/(t^5) over F2.
# Coordinate algebra A=F2[x1,x2,x3,x4]/(xi^2).  Delta encodes multiplication
# (1+u)(1+v)=1+u+v+uv in the 4-dim nilpotent algebra tF2[t]/t^5.
# We test whether a first-order bialgebra deformation over F2[e]/e^2 can have
# derivative of [16]^# = phi^4 nonzero.
d=4; DIM=1<<d; GENS=[1<<i for i in range(d)]; I_BASIS=list(range(1,DIM))
def bit(i): return 1<<i
def mul_monom(a,b): return None if (a&b) else (a|b)
def t2_index(a,b): return a*DIM+b
def t2_unindex(i): return divmod(i,DIM)
def t3_index(a,b,c): return (a*DIM+b)*DIM+c
def t3_unindex(i):
    a,r=divmod(i,DIM*DIM); b,c=divmod(r,DIM); return a,b,c
T2_DIM=DIM*DIM; T3_DIM=DIM**3

def vec_mul_t2_0(u,v):
    res=0; uu=u
    while uu:
        l=uu & -uu; i=l.bit_length()-1; uu^=l
        a,b=t2_unindex(i); vv=v
        while vv:
            l2=vv & -vv; j=l2.bit_length()-1; vv^=l2
            c,d2=t2_unindex(j); ac=mul_monom(a,c); bd=mul_monom(b,d2)
            if ac is not None and bd is not None: res ^= bit(t2_index(ac,bd))
    return res
# basis variable x_i corresponds to t^(i+1), i=0..3. Product t^a*t^b=t^(a+b) if <=4.
def delta0_gen(g):
    idx=GENS.index(g)+1 # degree 1..4
    terms=[(g,0),(0,g)]
    for a in range(1,idx):
        b=idx-a
        if 1 <= b <= 4:
            terms.append((GENS[a-1], GENS[b-1]))
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
PHI0=[mu_t2_0(DELTA0[a]) for a in range(DIM)]
print('PHI0 on gens', {g:PHI0[g] for g in GENS}, flush=True)
def apply_const_map(F, v_bits):
    res=0; vv=v_bits
    while vv:
        l=vv & -vv; a=l.bit_length()-1; vv^=l
        res ^= F[a]
    return res
# show nilpotency of phi0
for k in range(1,5):
    vals=[]
    for g in GENS:
        v=bit(g)
        for _ in range(k): v=apply_const_map(PHI0,v)
        vals.append(v)
    print('PHI0^%d gens'%k, vals, flush=True)
assert all((lambda v: v==0)([apply_const_map(PHI0, apply_const_map(PHI0, apply_const_map(PHI0, bit(a)))) for a in I_BASIS][0]) for _ in [0])
# Variables
var_index={}; vars=[]; pairs=[]
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
print('NV',NV,'mu',len(pairs)*len(I_BASIS),'D',len(I_BASIS)**3, flush=True)
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
            self.basis[p]=row; self.rank+=1; return True
        return False
RB=RowBasis()
def add_forms(vec):
    for f in vec:
        if f: RB.add(f)
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
    for p in I_BASIS:
        for q in I_BASIS:
            res[t2_index(p,q)] = bit(var_index[('d',a,p,q)])
    return res
D1_CACHE={a:D1_var_t2(a) for a in [0]+I_BASIS}
MU1_CACHE={}
def mu1_cached(a,b):
    if a>b: a,b=b,a
    key=(a,b); v=MU1_CACHE.get(key)
    if v is None:
        v=mu1_var_vec(a,b); MU1_CACHE[key]=v
    return v
def A_const_mul_left(m,U):
    if m==0: return U[:]
    res=[0]*DIM
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
# Generate first-order equations
print('assoc...', flush=True); t0=time.time()
for a,b,c in itertools.product(I_BASIS, repeat=3):
    res=[0]*DIM
    ab=mul_monom(a,b)
    if ab is not None and ab!=0: res=A_add(res,mu1_cached(ab,c))
    res=A_add(res,A_const_mul_right(mu1_cached(a,b),c))
    bc=mul_monom(b,c)
    if bc is not None and bc!=0: res=A_add(res,mu1_cached(a,bc))
    res=A_add(res,A_const_mul_left(a,mu1_cached(b,c)))
    add_forms(res)
print('rank after assoc',RB.rank,'time',time.time()-t0, flush=True)
print('Delta mult...', flush=True)
for a,b in itertools.product(I_BASIS, repeat=2):
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
print('final rank',RB.rank,'dim',NV-RB.rank,'time',time.time()-t0, flush=True)
# derivative T of phi=[2]^#
def T_linear_A(a):
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
T=[T_linear_A(a) for a in range(DIM)]
def apply_const_to_linear(U,F):
    res=[0]*DIM
    for a,form in enumerate(U):
        if form:
            fv=F[a]; vv=fv
            while vv:
                l=vv & -vv; b=l.bit_length()-1; vv^=l
                res[b]^=form
    return res
def apply_T_to_const(v_bits):
    res=[0]*DIM; vv=v_bits
    while vv:
        l=vv & -vv; a=l.bit_length()-1; vv^=l
        res=A_add(res,T[a])
    return res
def Npow_const(v_bits,k):
    v=v_bits
    for _ in range(k): v=apply_const_map(PHI0,v)
    return v
# D(phi^4)=sum_{i=0}^3 N^i T N^(3-i)
forms=[]
for a in I_BASIS:
    term=[0]*DIM
    for i in range(4):
        before=Npow_const(bit(a),3-i)
        mid=apply_T_to_const(before)
        after=mid
        for _ in range(i): after=apply_const_to_linear(after, PHI0)
        term=A_add(term, after)
    for out in I_BASIS: forms.append(term[out])
rems=[RB.reduce(f) for f in forms]
nonzero=[(idx,r) for idx,r in enumerate(rems) if r]
print('D(phi^4) nonzero reduced coordinates',len(nonzero), flush=True)
print(nonzero[:50], flush=True)
# Also reduce only generator inputs and basis outputs for clarity
for ai,a in enumerate(GENS):
    outs=[]
    for out in I_BASIS:
        idx=(a-1)*len(I_BASIS)+(out-1) # not correct for nonconsecutive a? we'll direct below
    
# Print coordinate labels
if nonzero:
    for idx,r in nonzero[:20]:
        a=I_BASIS[idx//len(I_BASIS)]; out=I_BASIS[idx%len(I_BASIS)]
        print(' target input',a,'output',out,'rem_lsb',(r & -r).bit_length()-1, flush=True)
