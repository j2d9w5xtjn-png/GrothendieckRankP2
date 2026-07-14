from __future__ import annotations
import itertools, sys, time

# First-order bialgebra deformations of H=F2[t]/t^N with either multiplicative
# (mu_N, t=T-1) or additive primitive coalgebra. Tests linearized [2^r].
# Usage: python firstorder_tpower.py 8 mult|prim [nocoassoc]

N=int(sys.argv[1]) if len(sys.argv)>1 else 8
kind=sys.argv[2] if len(sys.argv)>2 else 'mult'
DO_COASSOC= not (len(sys.argv)>3 and sys.argv[3]=='nocoassoc')
I_BASIS=list(range(1,N))
DIM=N
def bit(i): return 1<<i
def mul_exp(a,b):
    s=a+b
    return s if s<N else None
def t2_index(a,b): return a*N+b
def t2_unindex(i): return divmod(i,N)
def t3_index(a,b,c): return (a*N+b)*N+c
def t3_unindex(i):
    a,r=divmod(i,N*N); b,c=divmod(r,N); return a,b,c
T2_DIM=N*N; T3_DIM=N**3

def vec_mul_t2(u,v):
    res=0; uu=u
    while uu:
        l=uu&-uu; i=l.bit_length()-1; uu^=l
        a,b=t2_unindex(i); vv=v
        while vv:
            l2=vv&-vv; j=l2.bit_length()-1; vv^=l2
            c,d=t2_unindex(j); ac=mul_exp(a,c); bd=mul_exp(b,d)
            if ac is not None and bd is not None: res ^= bit(t2_index(ac,bd))
    return res
# Delta0(t)
if kind=='mult':
    DELTA_T=bit(t2_index(1,0)) ^ bit(t2_index(0,1)) ^ bit(t2_index(1,1))
elif kind=='prim':
    DELTA_T=bit(t2_index(1,0)) ^ bit(t2_index(0,1))
else:
    raise SystemExit('kind must be mult or prim')
def delta0_exp(e):
    res=bit(t2_index(0,0))
    for _ in range(e): res=vec_mul_t2(res, DELTA_T)
    return res
DELTA0=[delta0_exp(i) for i in range(N)]
def mu_t2(v):
    res=0; vv=v
    while vv:
        l=vv&-vv; idx=l.bit_length()-1; vv^=l
        a,b=t2_unindex(idx); c=mul_exp(a,b)
        if c is not None: res ^= bit(c)
    return res
# phi0=[2]^#
PHI0=[mu_t2(DELTA0[i]) for i in range(N)]
# For mult, PHI0(t^i)=t^(2i). For prim char2, zero on I.
print('N',N,'kind',kind,'T2',T2_DIM,'T3',T3_DIM,'phi0',[PHI0[i] for i in range(N)], flush=True)
# variables
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
            p=(row&-row).bit_length()-1
            b=self.basis.get(p)
            if b is None: return row
            row^=b
        return 0
    def add(self,row:int):
        row=self.reduce(row)
        if row:
            self.basis[(row&-row).bit_length()-1]=row; self.rank+=1; return True
        return False
RB=RowBasis()
def add_forms(vec):
    for f in vec:
        if f: RB.add(f)
def Vadd(u,v): return [u[i]^v[i] for i in range(len(u))]
def A_const_mul_left(a,U):
    if a==0: return U[:]
    res=[0]*N
    for i,f in enumerate(U):
        if f:
            c=mul_exp(a,i)
            if c is not None: res[c]^=f
    return res
def A_const_mul_right(U,a): return A_const_mul_left(a,U)
def mu1_var_vec(a,b):
    if a==0 or b==0: return [0]*N
    if a>b: a,b=b,a
    res=[0]*N
    for out in I_BASIS: res[out]=bit(var_index[('m',a,b,out)])
    return res
MU1_CACHE={}
def mu1_cached(a,b):
    if a>b: a,b=b,a
    key=(a,b); v=MU1_CACHE.get(key)
    if v is None:
        v=mu1_var_vec(a,b); MU1_CACHE[key]=v
    return v
def D1_var_t2(a):
    res=[0]*T2_DIM
    if a==0: return res
    for p in I_BASIS:
        for q in I_BASIS:
            res[t2_index(p,q)] = bit(var_index[('d',a,p,q)])
    return res
D1_CACHE={a:D1_var_t2(a) for a in range(N)}
def mu1_on_const_vecs(u_bits,v_bits):
    res=[0]*N; uu=u_bits
    while uu:
        l=uu&-uu; a=l.bit_length()-1; uu^=l
        vv=v_bits
        while vv:
            l2=vv&-vv; b=l2.bit_length()-1; vv^=l2
            if a and b: res=Vadd(res,mu1_cached(a,b))
    return res
def Delta0_on_A_linear(U):
    res=[0]*T2_DIM
    for a,f in enumerate(U):
        if f:
            vv=DELTA0[a]
            while vv:
                l=vv&-vv; idx=l.bit_length()-1; vv^=l
                res[idx]^=f
    return res
def t2_const_mul_linear_left(c_bits,U):
    res=[0]*T2_DIM; cc=c_bits
    while cc:
        l=cc&-cc; idx=l.bit_length()-1; cc^=l
        a,b=t2_unindex(idx)
        for j,f in enumerate(U):
            if f:
                p,q=t2_unindex(j); ap=mul_exp(a,p); bq=mul_exp(b,q)
                if ap is not None and bq is not None: res[t2_index(ap,bq)]^=f
    return res
def t2_const_mul_linear_right(U,c_bits): return t2_const_mul_linear_left(c_bits,U)
def mu1_tensor_on_const_t2s(U_bits,V_bits):
    res=[0]*T2_DIM; uu=U_bits
    while uu:
        l=uu&-uu; i=l.bit_length()-1; uu^=l
        a,b=t2_unindex(i); vv=V_bits
        while vv:
            l2=vv&-vv; j=l2.bit_length()-1; vv^=l2
            c,d=t2_unindex(j)
            bd=mul_exp(b,d)
            if bd is not None:
                mvec=mu1_on_const_vecs(bit(a),bit(c))
                for out,f in enumerate(mvec):
                    if f: res[t2_index(out,bd)]^=f
            ac=mul_exp(a,c)
            if ac is not None:
                mvec=mu1_on_const_vecs(bit(b),bit(d))
                for out,f in enumerate(mvec):
                    if f: res[t2_index(ac,out)]^=f
    return res
def Delta0_tensor_id_on_T2_linear(U):
    res=[0]*T3_DIM
    for idx,f in enumerate(U):
        if f:
            a,b=t2_unindex(idx); vv=DELTA0[a]
            while vv:
                l=vv&-vv; j=l.bit_length()-1; vv^=l
                p,q=t2_unindex(j); res[t3_index(p,q,b)]^=f
    return res
def id_tensor_Delta0_on_T2_linear(U):
    res=[0]*T3_DIM
    for idx,f in enumerate(U):
        if f:
            a,b=t2_unindex(idx); vv=DELTA0[b]
            while vv:
                l=vv&-vv; j=l.bit_length()-1; vv^=l
                p,q=t2_unindex(j); res[t3_index(a,p,q)]^=f
    return res
def D1_tensor_id_on_const_T2(C):
    res=[0]*T3_DIM; cc=C
    while cc:
        l=cc&-cc; idx=l.bit_length()-1; cc^=l
        a,b=t2_unindex(idx); Da=D1_CACHE[a]
        for j,f in enumerate(Da):
            if f:
                p,q=t2_unindex(j); res[t3_index(p,q,b)]^=f
    return res
def id_tensor_D1_on_const_T2(C):
    res=[0]*T3_DIM; cc=C
    while cc:
        l=cc&-cc; idx=l.bit_length()-1; cc^=l
        a,b=t2_unindex(idx); Db=D1_CACHE[b]
        for j,f in enumerate(Db):
            if f:
                p,q=t2_unindex(j); res[t3_index(a,p,q)]^=f
    return res
# Equations
start=time.time(); print('assoc...', flush=True)
for a,b,c in itertools.product(I_BASIS, repeat=3):
    res=[0]*N
    ab=mul_exp(a,b)
    if ab is not None and ab!=0: res=Vadd(res,mu1_cached(ab,c))
    res=Vadd(res,A_const_mul_right(mu1_cached(a,b),c))
    bc=mul_exp(b,c)
    if bc is not None and bc!=0: res=Vadd(res,mu1_cached(a,bc))
    res=Vadd(res,A_const_mul_left(a,mu1_cached(b,c)))
    add_forms(res)
print('rank after assoc',RB.rank,'time',time.time()-start, flush=True)
print('Delta mult...', flush=True)
for idx,(a,b) in enumerate(itertools.product(I_BASIS, repeat=2)):
    ab=mul_exp(a,b)
    left=[0]*T2_DIM
    if ab is not None and ab!=0: left=Vadd(left,D1_CACHE[ab])
    left=Vadd(left,Delta0_on_A_linear(mu1_cached(a,b)))
    right=[0]*T2_DIM
    right=Vadd(right,t2_const_mul_linear_right(D1_CACHE[a],DELTA0[b]))
    right=Vadd(right,t2_const_mul_linear_left(DELTA0[a],D1_CACHE[b]))
    right=Vadd(right,mu1_tensor_on_const_t2s(DELTA0[a],DELTA0[b]))
    add_forms(Vadd(left,right))
print('rank after mult',RB.rank,'time',time.time()-start, flush=True)
if DO_COASSOC:
    print('coassoc...', flush=True)
    for a in I_BASIS:
        left=Vadd(D1_tensor_id_on_const_T2(DELTA0[a]),Delta0_tensor_id_on_T2_linear(D1_CACHE[a]))
        right=Vadd(id_tensor_D1_on_const_T2(DELTA0[a]),id_tensor_Delta0_on_T2_linear(D1_CACHE[a]))
        add_forms(Vadd(left,right))
        print(' coassoc a',a,'rank',RB.rank,'time',time.time()-start, flush=True)
else:
    print('coassoc skipped', flush=True)
print('final rank',RB.rank,'dim',NV-RB.rank,'time',time.time()-start, flush=True)
# Linearized phi1: μ0 D1(a) + μ1 applied to each pair in DELTA0[a]
def phi1_linear_A(a):
    res=[0]*N
    D=D1_CACHE[a]
    for idx,f in enumerate(D):
        if f:
            p,q=t2_unindex(idx); m=mul_exp(p,q)
            if m is not None: res[m]^=f
    vv=DELTA0[a]
    while vv:
        l=vv&-vv; idx=l.bit_length()-1; vv^=l
        p,q=t2_unindex(idx)
        if p and q: res=Vadd(res,mu1_cached(p,q))
    return res
PHI1=[phi1_linear_A(a) for a in range(N)]
# apply phi0 to a linear vector of forms: phi0 basis map is constant bitset, so output forms
def phi0_on_linear(U):
    res=[0]*N
    for a,f in enumerate(U):
        if f:
            vv=PHI0[a]
            while vv:
                l=vv&-vv; b=l.bit_length()-1; vv^=l
                res[b]^=f
    return res
# apply phi1 to constant basis bitset/value
def phi1_on_const(vbits):
    res=[0]*N; vv=vbits
    while vv:
        l=vv&-vv; a=l.bit_length()-1; vv^=l
        res=Vadd(res,PHI1[a])
    return res
# compose linearized kth power for k=log2(order)=r? For order N=2^r, [N]=phi^r.
r=N.bit_length()-1
# linearization sum_{i=0}^{r-1} phi0^i phi1 phi0^{r-1-i}
def phi0_power_const(a, e):
    v=bit(a)
    for _ in range(e):
        out=0; vv=v
        while vv:
            l=vv&-vv; x=l.bit_length()-1; vv^=l
            out ^= PHI0[x]
        v=out
    return v
lin_power=[]
for a in I_BASIS:
    total=[0]*N
    for i in range(r):
        v=phi0_power_const(a, r-1-i)
        U=phi1_on_const(v)
        for _ in range(i): U=phi0_on_linear(U)
        total=Vadd(total,U)
    lin_power.append(total)
# Reduce all output forms modulo equations.
non=[]
for ai,a in enumerate(I_BASIS):
    for out,f in enumerate(lin_power[ai]):
        rem=RB.reduce(f)
        if rem: non.append((a,out,rem))
print(f'linearized [2^{r}] nonzero reduced coeffs',len(non), flush=True)
print('first nonzero',[(a,o,hex(rem & ((1<<80)-1))) for a,o,rem in non[:10]], flush=True)
# Also report phi1 cotangent matrix forms for output t^1 only? Cotangent dim 1 for tpower.
ct=[]
for a in [1]:
    pass
# Save enough info? no.
