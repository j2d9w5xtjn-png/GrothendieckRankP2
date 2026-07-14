from __future__ import annotations
import itertools, time
# First-order deformations of H=mu_2^3 over F2, A=k[x,y,z]/squares,
# Delta0(x_i)=x_i⊗1+1⊗x_i+x_i⊗x_i. Compute possible cotangent symbols psi on V=I/I^2.
DIM=8; GENS=[1,2,4]; I_BASIS=[1,2,3,4,5,6,7]
def bit(i): return 1<<i
def mul_monom(a,b): return None if (a&b) else (a|b)
def mul_A_vec(u,v):
    res=0; uu=u
    while uu:
        l=uu & -uu; i=l.bit_length()-1; uu^=l
        vv=v
        while vv:
            l2=vv & -vv; j=l2.bit_length()-1; vv^=l2
            c=mul_monom(i,j)
            if c is not None: res ^= bit(c)
    return res
def t2_index(a,b): return a*8+b
def t2_unindex(i): return divmod(i,8)
def t3_index(a,b,c): return (a*8+b)*8+c
def t3_unindex(i):
    a,r=divmod(i,64); b,c=divmod(r,8); return a,b,c

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

def delta0_gen(g):
    if g==1:
        return bit(t2_index(1,0)) ^ bit(t2_index(0,1))
    if g==2:
        return bit(t2_index(2,0)) ^ bit(t2_index(0,2)) ^ bit(t2_index(1,1))
    if g==4:
        return bit(t2_index(4,0)) ^ bit(t2_index(0,4))
    raise ValueError
DELTA0_G={g:delta0_gen(g) for g in GENS}
def delta0_monom(m):
    res=bit(t2_index(0,0))
    for g in GENS:
        if m&g: res=vec_mul_t2_0(res,DELTA0_G[g])
    return res
DELTA0=[delta0_monom(m) for m in range(8)]
# sanity phi0=0 on I
def mu_t2_0(v):
    res=0; vv=v
    while vv:
        l=vv & -vv; i=l.bit_length()-1; vv^=l
        a,b=t2_unindex(i); c=mul_monom(a,b)
        if c is not None: res ^= bit(c)
    return res
assert all(mu_t2_0(DELTA0[i])==0 for i in I_BASIS)

# Variables: mu1 unordered pairs I_BASIS x I_BASIS -> I_BASIS; D1(a) for each a in I_BASIS -> I⊗I.
var_index={}; vars=[]
# pair key sorted by basis index order value monom mask maybe sort numeric
pairs=[]
for idx,a in enumerate(I_BASIS):
    for b in I_BASIS[idx:]: pairs.append((a,b))
for a,b in pairs:
    for out in I_BASIS:
        var_index[('m',a,b,out)]=len(vars); vars.append(('m',a,b,out))
for a in I_BASIS:
    for p in I_BASIS:
        for q in I_BASIS:
            var_index[('d',a,p,q)]=len(vars); vars.append(('d',a,p,q))
NV=len(vars)
print('NV',NV,'mu',len(pairs)*7,'D',7*49)

def mu1_var_vec(a,b):
    if a==0 or b==0: return [0]*DIM  # no variables? not used
    if a>b: a,b=b,a
    coeff=[0]*DIM
    for out in I_BASIS:
        coeff[out]=1<<var_index[('m',a,b,out)]
    return coeff  # vector of coefficient bitsets per A basis

def D1_var_t2(a):
    coeff=[0]*64
    if a==0: return coeff
    for p in I_BASIS:
        for q in I_BASIS:
            coeff[t2_index(p,q)] = 1<<var_index[('d',a,p,q)]
    return coeff

# Linear-vector representations: A-vector with each basis coefficient a bitset of variables plus constant? For equations only variable coeff.
# We'll represent linear forms bitset NV for each target coordinate.
def A_add(u,v): return [u[i]^v[i] for i in range(8)]
def T2_add(u,v): return [u[i]^v[i] for i in range(64)]
def T3_add(u,v): return [u[i]^v[i] for i in range(512)]

def A_const_mul_left(m, U):
    # m monom constant times linear A-vector U
    res=[0]*8
    for i,form in enumerate(U):
        if form:
            c=mul_monom(m,i)
            if c is not None: res[c]^=form
    return res
def A_const_mul_right(U,m): return A_const_mul_left(m,U)

def mu1_on_const_vecs(u_bits,v_bits):
    # u,v constant A vectors bitset; output linear A coeffs
    res=[0]*8
    uu=u_bits
    while uu:
        l=uu & -uu; a=l.bit_length()-1; uu^=l
        vv=v_bits
        while vv:
            l2=vv & -vv; b=l2.bit_length()-1; vv^=l2
            if a==0 or b==0: continue
            mv=mu1_var_vec(a,b)
            res=A_add(res,mv)
    return res

def Delta0_on_A_linear(U):
    # U linear A-vector -> T2 linear by applying constant Delta0 to basis
    res=[0]*64
    for a,form in enumerate(U):
        if form:
            vv=DELTA0[a]
            while vv:
                l=vv & -vv; idx=l.bit_length()-1; vv^=l
                res[idx]^=form
    return res

def D1_on_const_A(u_bits):
    res=[0]*64
    uu=u_bits
    while uu:
        l=uu & -uu; a=l.bit_length()-1; uu^=l
        D=D1_var_t2(a)
        res=T2_add(res,D)
    return res

def t2_const_mul_linear_left(c_bits, U):
    # multiply constant T2 vector c_bits by linear T2 U using μ0 in both legs
    res=[0]*64
    cc=c_bits
    while cc:
        l=cc & -cc; idx=l.bit_length()-1; cc^=l
        a,b=t2_unindex(idx)
        for j,form in enumerate(U):
            if form:
                p,q=t2_unindex(j); ap=mul_monom(a,p); bq=mul_monom(b,q)
                if ap is not None and bq is not None: res[t2_index(ap,bq)]^=form
    return res
def t2_const_mul_linear_right(U,c_bits):
    # commutative μ0 so same but componentwise commutative
    return t2_const_mul_linear_left(c_bits,U)

def mu1_tensor_on_const_t2s(U_bits,V_bits):
    # e coefficient of product in A⊗A of constant U,V: μ1 in first leg + μ1 in second leg.
    res=[0]*64
    uu=U_bits
    while uu:
        l=uu & -uu; i=l.bit_length()-1; uu^=l
        a,b=t2_unindex(i)
        vv=V_bits
        while vv:
            l2=vv & -vv; j=l2.bit_length()-1; vv^=l2
            c,d=t2_unindex(j)
            # μ1(a,c) ⊗ b*d
            bd=mul_monom(b,d)
            if bd is not None:
                mvec=mu1_on_const_vecs(bit(a),bit(c))
                for out,form in enumerate(mvec):
                    if form: res[t2_index(out,bd)]^=form
            # a*c ⊗ μ1(b,d)
            ac=mul_monom(a,c)
            if ac is not None:
                mvec=mu1_on_const_vecs(bit(b),bit(d))
                for out,form in enumerate(mvec):
                    if form: res[t2_index(ac,out)]^=form
    return res

def Delta0_tensor_id_on_T2_linear(U):
    res=[0]*512
    for idx,form in enumerate(U):
        if form:
            a,b=t2_unindex(idx); Da=DELTA0[a]
            vv=Da
            while vv:
                l=vv & -vv; j=l.bit_length()-1; vv^=l
                p,q=t2_unindex(j); res[t3_index(p,q,b)]^=form
    return res

def id_tensor_Delta0_on_T2_linear(U):
    res=[0]*512
    for idx,form in enumerate(U):
        if form:
            a,b=t2_unindex(idx); Db=DELTA0[b]
            vv=Db
            while vv:
                l=vv & -vv; j=l.bit_length()-1; vv^=l
                p,q=t2_unindex(j); res[t3_index(a,p,q)]^=form
    return res

def D1_tensor_id_on_const_T2(C):
    res=[0]*512; cc=C
    while cc:
        l=cc & -cc; idx=l.bit_length()-1; cc^=l
        a,b=t2_unindex(idx); Da=D1_var_t2(a)
        for j,form in enumerate(Da):
            if form:
                p,q=t2_unindex(j); res[t3_index(p,q,b)]^=form
    return res

def id_tensor_D1_on_const_T2(C):
    res=[0]*512; cc=C
    while cc:
        l=cc & -cc; idx=l.bit_length()-1; cc^=l
        a,b=t2_unindex(idx); Db=D1_var_t2(b)
        for j,form in enumerate(Db):
            if form:
                p,q=t2_unindex(j); res[t3_index(a,p,q)]^=form
    return res

def collect_rows(vec):
    return [form for form in vec if form]

rows=[]
# associativity for all triples in I_BASIS: μ1(ab,c)+ μ0(μ1(a,b),c) + μ1(a,bc)+ μ0(a,μ1(b,c)) =0
for a,b,c in itertools.product(I_BASIS, repeat=3):
    res=[0]*8
    ab=mul_monom(a,b)
    if ab is not None and ab!=0: res=A_add(res, mu1_var_vec(ab,c))
    # μ0(μ1(a,b),c)
    res=A_add(res, A_const_mul_right(mu1_var_vec(a,b), c))
    bc=mul_monom(b,c)
    if bc is not None and bc!=0: res=A_add(res, mu1_var_vec(a,bc))
    res=A_add(res, A_const_mul_left(a, mu1_var_vec(b,c)))
    rows += collect_rows(res)
# Delta multiplicativity for all pairs a,b in I_BASIS: first-order equality.
for a,b in itertools.product(I_BASIS, repeat=2):
    ab=mul_monom(a,b)
    left=[0]*64
    if ab is not None and ab!=0: left=T2_add(left,D1_var_t2(ab))
    left=T2_add(left, Delta0_on_A_linear(mu1_var_vec(a,b)))
    right=[0]*64
    right=T2_add(right, t2_const_mul_linear_right(D1_var_t2(a), DELTA0[b]))
    right=T2_add(right, t2_const_mul_linear_left(DELTA0[a], D1_var_t2(b)))
    right=T2_add(right, mu1_tensor_on_const_t2s(DELTA0[a], DELTA0[b]))
    rows += collect_rows(T2_add(left,right))
# Coassoc for all a in I_BASIS: (D1⊗id + Δ0⊗id D1)Δ0? formula
for a in I_BASIS:
    left=T3_add(D1_tensor_id_on_const_T2(DELTA0[a]), Delta0_tensor_id_on_T2_linear(D1_var_t2(a)))
    right=T3_add(id_tensor_D1_on_const_T2(DELTA0[a]), id_tensor_Delta0_on_T2_linear(D1_var_t2(a)))
    rows += collect_rows(T3_add(left,right))
# Remove zero rows, rref
rows=[r for r in rows if r]
print('raw rows',len(rows))
def gf2_rref(rows,ncols):
    rows=rows[:]; r=0; piv=[]
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
rref,piv=gf2_rref(rows,NV); print('rank',len(piv),'dim',NV-len(piv))
# Compute possible cotangent matrix entries as linear forms on variables. psi(a)=mu0(D1a)+mu1(Delta0a)
# We only need a=x,y,z outputs mod I^2 (basis x,y,z).
def psi_linear_A(a):
    # mu0(D1(a))
    res=[0]*8
    D=D1_var_t2(a)
    for idx,form in enumerate(D):
        if form:
            p,q=t2_unindex(idx); m=mul_monom(p,q)
            if m is not None: res[m]^=form
    # μ1 on each tensor term of Delta0[a]
    vv=DELTA0[a]
    while vv:
        l=vv & -vv; idx=l.bit_length()-1; vv^=l
        p,q=t2_unindex(idx)
        if p!=0 and q!=0:
            res=A_add(res, mu1_var_vec(p,q))
    return res
forms=[]
for a in GENS:
    psi=psi_linear_A(a)
    for out in GENS:  # cotangent coordinates x,y,z (order columns by input, rows by output?)
        forms.append(psi[out])
print('cotangent forms nonzero',sum(1 for f in forms if f))
# Determine subspace of possible 9-bit matrices by evaluating forms on nullspace basis.
def nullspace_basis_from_rref(rref,piv,ncols):
    pivset=set(piv); free=[c for c in range(ncols) if c not in pivset]; basis=[]
    for f in free:
        x=1<<f
        for row,p in zip(rref,piv):
            if (row>>f)&1: x|=1<<p
        basis.append(x)
    return basis
solbasis=nullspace_basis_from_rref(rref,piv,NV)
mat_basis=[]
for v in solbasis:
    mb=0
    for i,f in enumerate(forms):
        if ((f & v).bit_count()&1): mb|=1<<i
    if mb: mat_basis.append(mb)
# rref mat_basis over 9 dims to get unique basis
mr,mp=gf2_rref(mat_basis,9); mat_basis=mr
print('matrix subspace dim',len(mat_basis),'basis',[bin(m) for m in mat_basis])
def mat_from_bits(bits):
    # form list: input a loops x,y,z; output x,y,z. Matrix M[out][in]
    M=[[0]*3 for _ in range(3)]
    pos=0
    for j in range(3):
        for i in range(3):
            M[i][j]=(bits>>pos)&1; pos+=1
    return M
def matmul(A,B):
    C=[[0]*3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            s=0
            for k in range(3): s^=A[i][k]&B[k][j]
            C[i][j]=s
    return C
def mat_nonzero(A): return any(A[i][j] for i in range(3) for j in range(3))
found=[]
for mask in range(1<<len(mat_basis)):
    bits=0
    for i,b in enumerate(mat_basis):
        if (mask>>i)&1: bits^=b
    M=mat_from_bits(bits); M2=matmul(M,M); M3=matmul(M2,M)
    if mat_nonzero(M3):
        found.append((bits,M,M2,M3)); break
print('L^3 nonzero exists?',bool(found))
if found:
    bits,M,M2,M3=found[0]
    print('bits',bin(bits),'M',M,'M2',M2,'M3',M3)
