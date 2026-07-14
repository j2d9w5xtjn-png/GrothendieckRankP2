# Targeted deformation search for rank-8 Heisenberg alpha_2^3 over F2[e]/e^3
# Fixed algebra A=R[x,y,z]/(x^2,y^2,z^2), standard U3 coalgebra.
from __future__ import annotations
import random, itertools, sys, time

# A basis monomials represented by bit mask 0..7 (x=1,y=2,z=4); multiplication zero if overlap.
DIM=8
GENS=[1,2,4]
I_BASIS=[1,2,3,4,5,6,7]
T2_DIM=64
T3_DIM=512

def mul_monom(a,b):
    if a & b: return None
    return a|b

def t2_index(a,b): return a*8+b
def t2_unindex(i): return divmod(i,8)
def t3_index(a,b,c): return (a*8+b)*8+c
def t3_unindex(i):
    a, r = divmod(i,64); b,c=divmod(r,8); return a,b,c

# vectors over F2 as Python int bitset. For T2 dim64, T3 dim512.
def bit(i): return 1<<i

def vec_add(*vs):
    r=0
    for v in vs: r ^= v
    return r

def vec_mul_t2(u,v):
    # componentwise algebra product in A⊗A
    res=0
    uu=u
    while uu:
        lsb=uu & -uu; i=lsb.bit_length()-1; uu^=lsb
        a,b=t2_unindex(i)
        vv=v
        while vv:
            lsb2=vv & -vv; j=lsb2.bit_length()-1; vv^=lsb2
            c,d=t2_unindex(j)
            ac=mul_monom(a,c); bd=mul_monom(b,d)
            if ac is not None and bd is not None:
                res ^= bit(t2_index(ac,bd))
    return res

def vec_mul_t3(u,v):
    res=0
    uu=u
    while uu:
        lsb=uu & -uu; i=lsb.bit_length()-1; uu^=lsb
        a,b,c=t3_unindex(i)
        vv=v
        while vv:
            lsb2=vv & -vv; j=lsb2.bit_length()-1; vv^=lsb2
            d,e,f=t3_unindex(j)
            ad=mul_monom(a,d); be=mul_monom(b,e); cf=mul_monom(c,f)
            if ad is not None and be is not None and cf is not None:
                res ^= bit(t3_index(ad,be,cf))
    return res

# Standard Δ0 on gens: x primitive, y primitive, z primitive + x⊗y
def delta0_gen(g):
    if g==1:
        return bit(t2_index(1,0)) ^ bit(t2_index(0,1))
    if g==2:
        return bit(t2_index(2,0)) ^ bit(t2_index(0,2))
    if g==4:
        return bit(t2_index(4,0)) ^ bit(t2_index(0,4)) ^ bit(t2_index(1,2))
    raise ValueError

DELTA0_G={g:delta0_gen(g) for g in GENS}

def delta0_monom(m):
    res=bit(t2_index(0,0))
    for g in GENS:
        if m & g:
            res=vec_mul_t2(res, DELTA0_G[g])
    return res
DELTA0=[delta0_monom(m) for m in range(8)]

# R=e^3 elements represented as tuple/list of 3 T2 vectors or T3 vectors.
def radd(a,b): return (a[0]^b[0], a[1]^b[1], a[2]^b[2])
def rmul_t2(a,b):
    # multiply in T2 over F2[e]/e^3
    return (vec_mul_t2(a[0],b[0]),
            vec_mul_t2(a[0],b[1]) ^ vec_mul_t2(a[1],b[0]),
            vec_mul_t2(a[0],b[2]) ^ vec_mul_t2(a[1],b[1]) ^ vec_mul_t2(a[2],b[0]))

def rmul_t3(a,b):
    return (vec_mul_t3(a[0],b[0]),
            vec_mul_t3(a[0],b[1]) ^ vec_mul_t3(a[1],b[0]),
            vec_mul_t3(a[0],b[2]) ^ vec_mul_t3(a[1],b[1]) ^ vec_mul_t3(a[2],b[0]))

# Linear maps: apply Δ_R to one tensor factor of T2 coefficient vector -> T3 R-vector.
# Need Δ_R on monomials, given generator D1/D2.
def build_deltaR(D1_g, D2_g):
    # D*_g dict g->T2 vector, return list m-> R(T2) tuple
    genR={}
    for g in GENS:
        genR[g]=(DELTA0_G[g], D1_g.get(g,0), D2_g.get(g,0))
    Delta=[None]*8
    Delta[0]=(bit(t2_index(0,0)),0,0)
    for m in range(1,8):
        res=(bit(t2_index(0,0)),0,0)
        for g in GENS:
            if m & g:
                res=rmul_t2(res, genR[g])
        Delta[m]=res
    return Delta

def tensor_Delta_id_on_t2_R(vR, Delta):
    # vR tuple of T2 vecs. For each basis a⊗b map to Δ(a)⊗b.
    out=(0,0,0)
    for deg, v in enumerate(vR):
        vv=v
        while vv:
            lsb=vv & -vv; i=lsb.bit_length()-1; vv ^= lsb
            a,b=t2_unindex(i)
            Da=Delta[a]
            # embed each T2 basis p⊗q to p⊗q⊗b
            emb=[0,0,0]
            for d in range(3):
                u=Da[d]; res=0
                uu=u
                while uu:
                    l=uu & -uu; j=l.bit_length()-1; uu^=l
                    p,q=t2_unindex(j)
                    res ^= bit(t3_index(p,q,b))
                emb[d]=res
            # multiply by e^deg => shift degrees
            cur=[0,0,0]
            for d in range(3-deg):
                cur[d+deg]=emb[d]
            out=(out[0]^cur[0], out[1]^cur[1], out[2]^cur[2])
    return out

def tensor_id_Delta_on_t2_R(vR, Delta):
    out=(0,0,0)
    for deg,v in enumerate(vR):
        vv=v
        while vv:
            lsb=vv & -vv; i=lsb.bit_length()-1; vv^=lsb
            a,b=t2_unindex(i)
            Db=Delta[b]
            emb=[0,0,0]
            for d in range(3):
                u=Db[d]; res=0
                uu=u
                while uu:
                    l=uu & -uu; j=l.bit_length()-1; uu^=l
                    p,q=t2_unindex(j)
                    res ^= bit(t3_index(a,p,q))
                emb[d]=res
            cur=[0,0,0]
            for d in range(3-deg): cur[d+deg]=emb[d]
            out=(out[0]^cur[0], out[1]^cur[1], out[2]^cur[2])
    return out

def coassoc_defect(D1_g,D2_g):
    Delta=build_deltaR(D1_g,D2_g)
    defects=[]
    for g in GENS:
        left=tensor_Delta_id_on_t2_R(Delta[g], Delta)
        right=tensor_id_Delta_on_t2_R(Delta[g], Delta)
        defects.append((left[0]^right[0], left[1]^right[1], left[2]^right[2]))
    return defects

# μ: T2 vector -> A vector bitset dim8 (component multiply)
def mu_t2(v):
    res=0
    vv=v
    while vv:
        l=vv & -vv; i=l.bit_length()-1; vv^=l
        a,b=t2_unindex(i)
        c=mul_monom(a,b)
        if c is not None: res ^= bit(c)
    return res

def mul_A_vec(u,v):
    res=0
    uu=u
    while uu:
        l=uu & -uu; i=l.bit_length()-1; uu^=l
        vv=v
        while vv:
            l2=vv & -vv; j=l2.bit_length()-1; vv^=l2
            c=mul_monom(i,j)
            if c is not None: res ^= bit(c)
    return res

def phi_map_R(D1_g,D2_g):
    Delta=build_deltaR(D1_g,D2_g)
    # map A -> R(A) tuple len3, algebra hom by φ(g)=μΔ(g)
    genPhi={g:(mu_t2(Delta[g][0]), mu_t2(Delta[g][1]), mu_t2(Delta[g][2])) for g in GENS}
    Phi=[None]*8
    Phi[0]=(bit(0),0,0)  # φ(1)=1
    for m in range(1,8):
        res=(bit(0),0,0)
        for g in GENS:
            if m & g:
                # multiply R(A)
                a=res; b=genPhi[g]
                res=(mul_A_vec(a[0],b[0]),
                     mul_A_vec(a[0],b[1]) ^ mul_A_vec(a[1],b[0]),
                     mul_A_vec(a[0],b[2]) ^ mul_A_vec(a[1],b[1]) ^ mul_A_vec(a[2],b[0]))
        Phi[m]=res
    return Phi

def compose_phi(Phi, val):
    # Phi: A basis -> R(A). val: R(A). return R(A) applying algebra map R-linearly to A coeffs
    out=(0,0,0)
    for deg,v in enumerate(val):
        vv=v
        while vv:
            l=vv & -vv; i=l.bit_length()-1; vv^=l
            pi=Phi[i]
            cur=[0,0,0]
            for d in range(3-deg): cur[d+deg]=pi[d]
            out=(out[0]^cur[0], out[1]^cur[1], out[2]^cur[2])
    return out

def phi_power3_nonzero(D1_g,D2_g):
    Phi=phi_map_R(D1_g,D2_g)
    vals=[]
    for g in GENS:
        v=(bit(g),0,0)
        v1=compose_phi(Phi,v)
        v2=compose_phi(Phi,v1)
        v3=compose_phi(Phi,v2)
        vals.append(v3)
    return any(v!=(0,0,0) for v in vals), vals

# Parameter indexing: D values only in I⊗I (49) for each of 3 gens.
PARAMS=[]
for g in GENS:
    for a in I_BASIS:
        for b in I_BASIS:
            PARAMS.append((g,t2_index(a,b)))
NP=len(PARAMS)
print('NP per layer', NP)

def D_from_mask(mask):
    D={g:0 for g in GENS}
    for j,(g,idx) in enumerate(PARAMS):
        if (mask>>j)&1:
            D[g] ^= bit(idx)
    return D

# Build linear equations for D1: coassoc e coefficient, by columns.
def lin_rows_for_layer1():
    base=coassoc_defect({g:0 for g in GENS},{g:0 for g in GENS})
    assert all(d==(0,0,0) for d in base), 'Delta0 not coassoc'
    # row bitsets length NP, for each T3 coordinate in e coeff of each gen.
    rows=[0]*(3*T3_DIM)
    for j,(g,idx) in enumerate(PARAMS):
        D={gg:0 for gg in GENS}; D[g]=bit(idx)
        defs=coassoc_defect(D,{gg:0 for gg in GENS})
        for gi,d in enumerate(defs):
            v=d[1]  # epsilon coeff
            vv=v
            while vv:
                l=vv & -vv; c=l.bit_length()-1; vv^=l
                rows[gi*T3_DIM+c] ^= (1<<j)
    rows=[r for r in rows if r]
    return rows

def gf2_rref(rows, ncols):
    rows=rows[:]
    pivots=[]; r=0
    # use dictionary pivot highest? We need efficient. We'll pivot by col increasing.
    for c in range(ncols):
        pivot=None
        for i in range(r,len(rows)):
            if (rows[i]>>c)&1:
                pivot=i; break
        if pivot is None: continue
        rows[r],rows[pivot]=rows[pivot],rows[r]
        for i in range(len(rows)):
            if i!=r and ((rows[i]>>c)&1):
                rows[i]^=rows[r]
        pivots.append(c); r+=1
        if r==len(rows): break
    return rows[:r], pivots

def nullspace_basis(rows, ncols):
    rref,pivots=gf2_rref(rows,ncols)
    pivset=set(pivots)
    free=[c for c in range(ncols) if c not in pivset]
    basis=[]
    # In rref, row i has pivot pivots[i]; pivot var = sum row free vars (since row dot x=0)
    for f in free:
        x=1<<f
        for row,p in zip(rref,pivots):
            if (row>>f)&1:
                x |= 1<<p
        basis.append(x)
    return basis,pivots,rref

def random_span(basis):
    x=0
    for b in basis:
        if random.getrandbits(1): x^=b
    return x

# Linear solver for D2: coassoc e2 equations = 0 for fixed D1.
# L same as layer1 differential on D2 at epsilon2. Build columns for D2 coefficient of e2 with D1=0.
# Then RHS is defect e2 with D2=0.
def build_L_rows_aug(rhs_vecs=None):
    # rows as coefficients for D2 vars, and optional rhs bits appended at bit NP
    rows=[0]*(3*T3_DIM)
    for j,(g,idx) in enumerate(PARAMS):
        D2={gg:0 for gg in GENS}; D2[g]=bit(idx)
        defs=coassoc_defect({gg:0 for gg in GENS},D2)
        for gi,d in enumerate(defs):
            v=d[2]
            vv=v
            while vv:
                l=vv & -vv; c=l.bit_length()-1; vv^=l
                rows[gi*T3_DIM+c] ^= (1<<j)
    if rhs_vecs is not None:
        for gi,d in enumerate(rhs_vecs):
            v=d[2]
            vv=v
            while vv:
                l=vv & -vv; c=l.bit_length()-1; vv^=l
                rows[gi*T3_DIM+c] ^= (1<<NP)
    rows=[r for r in rows if r]
    return rows

def solve_linear_aug(rows, nvars):
    # rows bitset nvars coeffs plus rhs at nvars. Return (consistent, particular, kernel_basis)
    # RREF by coeff columns; include RHS untouched.
    rows=rows[:]
    r=0; pivots=[]
    for c in range(nvars):
        pivot=None
        for i in range(r,len(rows)):
            if (rows[i]>>c)&1:
                pivot=i; break
        if pivot is None: continue
        rows[r],rows[pivot]=rows[pivot],rows[r]
        for i in range(len(rows)):
            if i!=r and ((rows[i]>>c)&1): rows[i]^=rows[r]
        pivots.append(c); r+=1
        if r==len(rows): break
    # inconsistent row: coeffs zero rhs 1
    coeffmask=(1<<nvars)-1
    for row in rows:
        if (row & coeffmask)==0 and ((row>>nvars)&1):
            return False,0,[]
    rref=rows[:r]
    pivset=set(pivots); free=[c for c in range(nvars) if c not in pivset]
    part=0
    for row,p in zip(rref,pivots):
        if (row>>nvars)&1: part |= 1<<p
    ker=[]
    for f in free:
        x=1<<f
        for row,p in zip(rref,pivots):
            if (row>>f)&1: x|=1<<p
        ker.append(x)
    return True,part,ker

if __name__=='__main__':
    t=time.time()
    rows=lin_rows_for_layer1()
    print('layer1 nonzero rows',len(rows),'build',time.time()-t)
    basis,pivots,rref=nullspace_basis(rows,NP)
    print('D1 cocycle dim',len(basis),'rank',len(pivots))
    # sample D1 with D2=0 satisfying full coassoc
    ntest=2000; found=0; valid2=0
    for i in range(ntest):
        m=random_span(basis)
        D1=D_from_mask(m); D0={g:0 for g in GENS}
        defs=coassoc_defect(D1,D0)
        if all(d[2]==0 for d in defs):
            valid2+=1
            nz,vals=phi_power3_nonzero(D1,D0)
            if nz:
                print('FOUND D2=0 counter candidate mask',m, 'vals',vals)
                found=1; break
    print('sample D2=0 valid2',valid2,'found',found)
    # sample D1, solve D2, random D2 solutions test [8]
    for i in range(200):
        m=random_span(basis)
        D1=D_from_mask(m); D0={g:0 for g in GENS}
        rhs=coassoc_defect(D1,D0)  # need L(D2)=rhs (since defect=D2linear+rhs; char2 same)
        rows_aug=build_L_rows_aug(rhs)
        ok,part,ker=solve_linear_aug(rows_aug,NP)
        if not ok: continue
        for trial in range(50):
            sol=part
            for b in ker:
                if random.getrandbits(1): sol^=b
            D2=D_from_mask(sol)
            defs=coassoc_defect(D1,D2)
            if not all(d==(0,0,0) for d in defs):
                print('solver bug'); sys.exit()
            nz,vals=phi_power3_nonzero(D1,D2)
            if nz:
                print('FOUND candidate D1mask',m,'D2mask',sol,'kerdim',len(ker),'vals',vals)
                sys.exit()
        if i%10==0: print('sample solve',i,'kerdim',len(ker),'elapsed',time.time()-t)
    print('no candidate in samples')
