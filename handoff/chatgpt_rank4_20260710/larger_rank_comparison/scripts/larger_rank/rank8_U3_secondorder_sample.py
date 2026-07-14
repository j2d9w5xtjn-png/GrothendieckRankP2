from __future__ import annotations
import itertools, random, time, sys
# Rank-8 U3/Heisenberg fiber over F2; full commutative algebra + coalgebra
# deformations over F2[e]/e^3. Random/linalg second-order search for [8]!=0.
DIM=8; GENS=[1,2,4]; I=list(range(1,8)); T2=64; T3=512
def bit(i): return 1<<i
def mul_monom(a,b): return None if a&b else a|b
def t2(a,b): return a*8+b
def u2(i): return divmod(i,8)
def t3(a,b,c): return (a*8+b)*8+c
def u3(i):
    a,r=divmod(i,64); b,c=divmod(r,8); return a,b,c
# special fiber Delta0 U3
def vec_mul_t2_0(u,v):
    res=0
    while u:
        l=u&-u; i=l.bit_length()-1; u^=l; a,b=u2(i); vv=v
        while vv:
            l2=vv&-vv; j=l2.bit_length()-1; vv^=l2; c,d=u2(j)
            ac=mul_monom(a,c); bd=mul_monom(b,d)
            if ac is not None and bd is not None: res^=bit(t2(ac,bd))
    return res
def delta0_gen(g):
    if g==1: terms=[(1,0),(0,1)]
    elif g==2: terms=[(2,0),(0,2)]
    elif g==4: terms=[(4,0),(0,4),(1,2)]
    else: raise ValueError
    v=0
    for a,b in terms: v^=bit(t2(a,b))
    return v
DG0={g:delta0_gen(g) for g in GENS}
def delta0_monom(m):
    res=bit(t2(0,0))
    for g in GENS:
        if m&g: res=vec_mul_t2_0(res,DG0[g])
    return res
DELTA0=[delta0_monom(a) for a in range(DIM)]
# variables
pairs=[]
for ii,a in enumerate(I):
    for b in I[ii:]: pairs.append((a,b))
vars=[]; vindex={}
for a,b in pairs:
    for out in I:
        vindex[('m',a,b,out)]=len(vars); vars.append(('m',a,b,out))
for a in I:
    for p in I:
        for q in I:
            vindex[('d',a,p,q)]=len(vars); vars.append(('d',a,p,q))
NV=len(vars); print('NV',NV, flush=True)
# mu0 table bitsets
MU0=[[0]*DIM for _ in range(DIM)]
for a in range(DIM):
    for b in range(DIM):
        c=mul_monom(a,b)
        if c is not None: MU0[a][b]=bit(c)
ZERO_A=(0,0,0); ZERO_T2=(0,0,0); ZERO_T3=(0,0,0)
def tables_from_mask(mask:int, degree:int=1):
    # returns (mu1,D1) if degree=1; use same shape for degree2
    MU=[[0]*DIM for _ in range(DIM)]
    DD=[0]*DIM
    for j,v in enumerate(vars):
        if ((mask>>j)&1)==0: continue
        if v[0]=='m':
            _,a,b,out=v; MU[a][b]^=bit(out)
            if a!=b: MU[b][a]^=bit(out)
        else:
            _,a,p,q=v; DD[a]^=bit(t2(p,q))
    return MU,DD
MUZERO=[[0]*DIM for _ in range(DIM)]; DZERO=[0]*DIM
def mu_apply_table(MU,u:int,v:int)->int:
    res=0; uu=u
    while uu:
        l=uu&-uu; a=l.bit_length()-1; uu^=l; vv=v
        while vv:
            l2=vv&-vv; b=l2.bit_length()-1; vv^=l2; res^=MU[a][b]
    return res
def muR_A(U,V,MU1,MU2):
    # U,V tuples deg0,1,2 Abits
    out=[0,0,0]
    MUs=[MU0,MU1,MU2]
    for i in range(3):
        if U[i]==0: continue
        for j in range(3-i):
            if V[j]==0: continue
            for k in range(3-i-j):
                val=mu_apply_table(MUs[k],U[i],V[j])
                out[i+j+k]^=val
    return tuple(out)
def delta_table(D1,D2):
    return [(DELTA0[a], D1[a], D2[a]) for a in range(DIM)]
def Delta_on_AR(U,D1,D2):
    Delta=delta_table(D1,D2); out=[0,0,0]
    for deg in range(3):
        v=U[deg]
        while v:
            l=v&-v; a=l.bit_length()-1; v^=l
            Da=Delta[a]
            for k in range(3-deg): out[deg+k]^=Da[k]
    return tuple(out)
def embed_Delta_id(Da,b):
    # Da tuple T2 -> T3 tuple, no external degree
    out=[0,0,0]
    for k in range(3):
        v=Da[k]
        while v:
            l=v&-v; idx=l.bit_length()-1; v^=l; p,q=u2(idx)
            out[k]^=bit(t3(p,q,b))
    return tuple(out)
def embed_id_Delta(a,Db):
    out=[0,0,0]
    for k in range(3):
        v=Db[k]
        while v:
            l=v&-v; idx=l.bit_length()-1; v^=l; p,q=u2(idx)
            out[k]^=bit(t3(a,p,q))
    return tuple(out)
def Delta_id_on_T2R(U,D1,D2):
    Delta=delta_table(D1,D2); out=[0,0,0]
    for deg in range(3):
        v=U[deg]
        while v:
            l=v&-v; idx=l.bit_length()-1; v^=l; a,b=u2(idx)
            emb=embed_Delta_id(Delta[a],b)
            for k in range(3-deg): out[deg+k]^=emb[k]
    return tuple(out)
def id_Delta_on_T2R(U,D1,D2):
    Delta=delta_table(D1,D2); out=[0,0,0]
    for deg in range(3):
        v=U[deg]
        while v:
            l=v&-v; idx=l.bit_length()-1; v^=l; a,b=u2(idx)
            emb=embed_id_Delta(a,Delta[b])
            for k in range(3-deg): out[deg+k]^=emb[k]
    return tuple(out)
def tensor_from_A_pair(a,b): return (bit(t2(a,b)),0,0)
def t2_tensor_product(U,V,MU1,MU2):
    # product in A⊗A over R using deformed mu in each factor
    out=[0,0,0]; MUs=[MU0,MU1,MU2]
    for du in range(3):
        uv=U[du]
        while uv:
            l=uv&-uv; idx=l.bit_length()-1; uv^=l; a,b=u2(idx)
            for dv in range(3-du):
                vv=V[dv]
                while vv:
                    l2=vv&-vv; j=l2.bit_length()-1; vv^=l2; c,d=u2(j)
                    # choose deformation degree k in first leg, ldeg in second leg
                    for k in range(3-du-dv):
                        ac=MU0[a][c] if k==0 else MUs[k][a][c]
                        if ac==0: continue
                        for ldeg in range(3-du-dv-k):
                            bd=MUs[ldeg][b][d]
                            if bd==0: continue
                            # tensor all basis terms in ac and bd
                            aa=ac
                            while aa:
                                la=aa&-aa; ia=la.bit_length()-1; aa^=la
                                bb=bd
                                while bb:
                                    lb=bb&-bb; ib=lb.bit_length()-1; bb^=lb
                                    out[du+dv+k+ldeg]^=bit(t2(ia,ib))
    return tuple(out)
def phi_images(MU1,MU2,D1,D2):
    Phi=[]
    for a in range(DIM):
        res=[0,0,0]
        Delta=(DELTA0[a],D1[a],D2[a])
        for deg in range(3):
            v=Delta[deg]
            while v:
                l=v&-v; idx=l.bit_length()-1; v^=l; p,q=u2(idx)
                # apply mu0/mu1/mu2 to p,q
                vals=[MU0[p][q], MU1[p][q], MU2[p][q]]
                for k in range(3-deg): res[deg+k]^=vals[k]
        Phi.append(tuple(res))
    return Phi
def compose_phi(Phi,U):
    out=[0,0,0]
    for deg in range(3):
        v=U[deg]
        while v:
            l=v&-v; a=l.bit_length()-1; v^=l
            Pa=Phi[a]
            for k in range(3-deg): out[deg+k]^=Pa[k]
    return tuple(out)
def equations_bits(MU1,MU2,D1,D2,deg:int)->int:
    pos=0; bits=0
    # associativity
    for a,b,c in itertools.product(I, repeat=3):
        left=muR_A(muR_A((bit(a),0,0),(bit(b),0,0),MU1,MU2),(bit(c),0,0),MU1,MU2)
        right=muR_A((bit(a),0,0),muR_A((bit(b),0,0),(bit(c),0,0),MU1,MU2),MU1,MU2)
        v=left[deg]^right[deg]
        for out in range(DIM):
            if (v>>out)&1: bits^=1<<pos
            pos+=1
    # Delta multiplicativity
    for a,b in itertools.product(I, repeat=2):
        mab=muR_A((bit(a),0,0),(bit(b),0,0),MU1,MU2)
        left=Delta_on_AR(mab,D1,D2)
        right=t2_tensor_product((DELTA0[a],D1[a],D2[a]),(DELTA0[b],D1[b],D2[b]),MU1,MU2)
        v=left[deg]^right[deg]
        for out in range(T2):
            if (v>>out)&1: bits^=1<<pos
            pos+=1
    # coassoc
    for a in I:
        U=(DELTA0[a],D1[a],D2[a])
        left=Delta_id_on_T2R(U,D1,D2); right=id_Delta_on_T2R(U,D1,D2)
        v=left[deg]^right[deg]
        for out in range(T3):
            if (v>>out)&1: bits^=1<<pos
            pos+=1
    return bits
M=343*8+49*T2+7*T3
assert M==9464
def target_bits(MU1,MU2,D1,D2,deg:int)->int:
    Phi=phi_images(MU1,MU2,D1,D2)
    bits=0; pos=0
    for a in I:
        U=(bit(a),0,0)
        U=compose_phi(Phi,U); U=compose_phi(Phi,U); U=compose_phi(Phi,U)
        v=U[deg]
        for out in I:
            if (v>>out)&1: bits^=1<<pos
            pos+=1
    return bits
Q=7*7
# Build L rows for degree1 equations.
def build_rows_and_F():
    rows=[0]*M; F=[0]*Q
    t=time.time()
    for j in range(NV):
        MU1,D1=tables_from_mask(1<<j)
        eb=equations_bits(MU1,MUZERO,D1,DZERO,1)
        b=eb
        while b:
            l=b&-b; i=l.bit_length()-1; b^=l; rows[i]^=1<<j
        tb=target_bits(MUZERO,MU1,DZERO,D1,2)  # wait: for second variables, pass as MU2,D2 not MU1,D1
        # wrong call patched below
    return rows,F
# We'll build rows and F separately to avoid confusion.
print('building L and F columns...', flush=True)
rows=[0]*M; F=[0]*Q
t0=time.time()
for j in range(NV):
    MUj,Dj=tables_from_mask(1<<j)
    eb=equations_bits(MUj,MUZERO,Dj,DZERO,1)
    b=eb
    while b:
        l=b&-b; i=l.bit_length()-1; b^=l; rows[i]^=1<<j
    tb=target_bits(MUZERO,MUj,DZERO,Dj,2)  # variable as second-order
    b=tb
    while b:
        l=b&-b; q=l.bit_length()-1; b^=l; F[q]^=1<<j
    if j and j%100==0: print(' col',j,'time',time.time()-t0, flush=True)
print('built columns time',time.time()-t0,'nonzero rows',sum(1 for r in rows if r),'nonzero F',sum(1 for f in F if f), flush=True)
# RREF with transform.
def rref_with_transform(rows,ncols):
    rows=rows[:]; trans=[1<<i for i in range(len(rows))]; r=0; piv=[]
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
def nullspace_from_rref(rrows,piv,ncols):
    ps=set(piv); basis=[]
    for f in range(ncols):
        if f in ps: continue
        x=1<<f
        for row,p in zip(rrows,piv):
            if (row>>f)&1: x|=1<<p
        basis.append(x)
    return basis
def parity(x): return x.bit_count()&1
print('rref L...', flush=True)
Lr,Ltrans,Lpiv,rank=rref_with_transform(rows,NV)
zero_trans=[Ltrans[i] for i in range(rank,len(rows)) if Lr[i]==0]
print('rank',rank,'dim',NV-rank,'zero rows',len(zero_trans), flush=True)
first_basis=nullspace_from_rref(Lr[:rank],Lpiv,NV)
print('first basis',len(first_basis), flush=True)
# Target F row-span coeffs
f_coeff=[]; not_in=[]
for q,f in enumerate(F):
    rem=f; coeff=0
    for i in range(rank):
        row=Lr[i]; p=(row&-row).bit_length()-1
        if (rem>>p)&1:
            rem^=row; coeff^=1<<i
    f_coeff.append(coeff)
    if rem: not_in.append(q)
print('F not in row span',not_in,'nonzero F rows',sum(1 for f in F if f), flush=True)
f_trans=[]
for coeff in f_coeff:
    tr=0; c=coeff
    while c:
        l=c&-c; i=l.bit_length()-1; c^=l; tr^=Ltrans[i]
    f_trans.append(tr)
def random_first():
    m=0
    for b in first_basis:
        if random.getrandbits(1): m^=b
    return m
# sample random first-order deformations and test second-order lift/target

if len(sys.argv)>1 and sys.argv[1]=='quad':
    print('quadratic identity check on first-order basis...', flush=True)
    qd=[]; ed=[]
    nonq=[]
    for i,b in enumerate(first_basis):
        MU1,D1=tables_from_mask(b)
        q=target_bits(MU1,MUZERO,D1,DZERO,2)
        qd.append(q)
        if q: nonq.append(('diag',i,q)); print('q diag nonzero',i,q, flush=True)
    noncross=[]
    for i in range(len(first_basis)):
        for j in range(i+1,len(first_basis)):
            MU1,D1=tables_from_mask(first_basis[i]^first_basis[j])
            q=target_bits(MU1,MUZERO,D1,DZERO,2)^qd[i]^qd[j]
            if q:
                noncross.append((i,j,q)); print('q cross nonzero',i,j,q, flush=True); raise SystemExit
    print('q diag count',sum(1 for x in qd if x),'q cross count',len(noncross), flush=True)
    # consistency conditions quadratic: test diagonals/crosses against zero-row transforms.
    bad=[]
    rhsd=[]
    for i,b in enumerate(first_basis):
        MU1,D1=tables_from_mask(b); rhs=equations_bits(MU1,MUZERO,D1,DZERO,2); rhsd.append(rhs)
        if any(parity(tr&rhs) for tr in zero_trans): bad.append(('diag',i))
    print('bad consistency diag',len(bad), flush=True)
    for i in range(len(first_basis)):
        for j in range(i+1,len(first_basis)):
            MU1,D1=tables_from_mask(first_basis[i]^first_basis[j]); rhs=equations_bits(MU1,MUZERO,D1,DZERO,2)^rhsd[i]^rhsd[j]
            if any(parity(tr&rhs) for tr in zero_trans):
                bad.append(('cross',i,j)); print('first bad consistency cross',i,j, flush=True); break
        if len(bad)> (0 if not any(x[0]=='cross' for x in bad) else 1): break
    print('bad consistency total/first',bad[:5], flush=True)
    raise SystemExit

N=int(sys.argv[1]) if len(sys.argv)>1 else 2000
print('sampling',N, flush=True)
found=None; lift=0; bad=0
for s in range(N):
    m=random_first(); MU1,D1=tables_from_mask(m)
    rhs=equations_bits(MU1,MUZERO,D1,DZERO,2)  # L(second)=rhs (char2)
    incons=False
    for tr in zero_trans:
        if parity(tr&rhs): incons=True; break
    if incons:
        bad+=1; continue
    lift+=1
    qbits=target_bits(MU1,MUZERO,D1,DZERO,2)
    expr=qbits
    for q,tr in enumerate(f_trans):
        if tr and parity(tr&rhs): expr ^= 1<<q
    if expr or not_in:
        found=(m,expr,qbits,rhs.bit_count()); print('FOUND',found,'sample',s, flush=True); break
    if s and s%100==0: print('sample',s,'lift',lift,'bad',bad,'elapsed',time.time()-t0, flush=True)
print('done lift',lift,'bad',bad,'found',found, flush=True)
