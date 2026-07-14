import sys, time, random
sys.path.append('/mnt/data')
import rank8_search as rs

NP=rs.NP; M=3*rs.T3_DIM
DZERO={g:0 for g in rs.GENS}

def defects_to_bits(defs, deg):
    out=0
    for gi,d in enumerate(defs):
        v=d[deg]
        vv=v
        while vv:
            l=vv & -vv; c=l.bit_length()-1; vv^=l
            out ^= 1<<(gi*rs.T3_DIM+c)
    return out

def vals_to_bits(vals):
    # vals list for gens: each tuple (A bits e0,e1,e2). output 3*3*8 bits
    out=0
    pos=0
    for val in vals:
        for deg in range(3):
            v=val[deg]
            for a in range(8):
                if (v>>a)&1: out ^= 1<<pos
                pos+=1
    return out
QDIM=3*3*8

def build_L_full():
    rows=[0]*M
    for j,(g,idx) in enumerate(rs.PARAMS):
        D2={gg:0 for gg in rs.GENS}; D2[g]=1<<idx
        defs=rs.coassoc_defect(DZERO,D2)
        bits=defects_to_bits(defs,2)
        bb=bits
        while bb:
            l=bb & -bb; i=l.bit_length()-1; bb^=l
            rows[i] ^= 1<<j
    return rows

def rref_with_transform(rows, ncols):
    # rows list length M, trans tracks original coordinates. Full elimination.
    rows=rows[:]
    trans=[1<<i for i in range(len(rows))]
    r=0; pivots=[]
    for c in range(ncols):
        pivot=None
        for i in range(r,len(rows)):
            if (rows[i]>>c)&1:
                pivot=i; break
        if pivot is None: continue
        rows[r],rows[pivot]=rows[pivot],rows[r]
        trans[r],trans[pivot]=trans[pivot],trans[r]
        for i in range(len(rows)):
            if i!=r and ((rows[i]>>c)&1):
                rows[i]^=rows[r]
                trans[i]^=trans[r]
        pivots.append(c); r+=1
        if r==len(rows): break
    return rows, trans, pivots, r

def reduce_f_get_coeffs(f, rref_rows, rank):
    # rref pivot rows have unique pivots, but use leading bit low? Need pivot col = lsb of row? due col increasing and eliminated all.
    coeff=0
    rem=f
    for i in range(rank):
        row=rref_rows[i]
        # pivot = lowest set bit? Since row may have free bits > pivot, no lower bits.
        p=(row & -row).bit_length()-1
        if (rem>>p)&1:
            rem ^= row; coeff ^= 1<<i
    return rem, coeff

def parity(x): return x.bit_count() & 1

print('building D1 cocycle basis')
rows1=rs.lin_rows_for_layer1()
basis,pivots,rref=rs.nullspace_basis(rows1,NP)
print('D1 dim',len(basis))
assert len(basis)<=25
print('building L')
Lrows=build_L_full()
print('nonzero L rows',sum(1 for r in Lrows if r))
print('rref L')
t0=time.time(); Lr, Ltrans, Lpiv, rank = rref_with_transform(Lrows, NP)
print('rank',rank,'kerdim',NP-rank,'time',time.time()-t0)
# consistency transforms are trans for rows rank..M, whose coeff rows are zero.
zero_trans=[Ltrans[i] for i in range(rank,M) if Lr[i]==0]
# In fact all after rank coeff zero. Some trans may be zero? no.
print('zero consistency rows',len(zero_trans))

# D2-output linear map f for phi^3 at D1=0
F_cols=[0]*QDIM  # bitset NP for each output coordinate
for j,(g,idx) in enumerate(rs.PARAMS):
    D2={gg:0 for gg in rs.GENS}; D2[g]=1<<idx
    nz,vals=rs.phi_power3_nonzero(DZERO,D2)
    bits=vals_to_bits(vals)
    bb=bits
    while bb:
        l=bb & -bb; q=l.bit_length()-1; bb^=l
        F_cols[q] ^= 1<<j
# Reduce f's
f_coeff=[]
not_in=[]
for q,f in enumerate(F_cols):
    rem,coeff=reduce_f_get_coeffs(f,Lr,rank)
    f_coeff.append(coeff)
    if rem: not_in.append((q,rem))
print('nonzero F outputs',sum(1 for f in F_cols if f),'not in row span',len(not_in))
if not_in:
    print('F not in row span -> any consistent D1 would yield candidate for q',not_in[:5])

# Build quadratic tables for RHS(D1) and qbits(D1)
d=len(basis)
print('building quadratic tables over',d,'D1 vars')
def D_from_basis_mask(mask):
    parammask=0
    for i,b in enumerate(basis):
        if (mask>>i)&1: parammask ^= b
    return rs.D_from_mask(parammask)

rhs_diag=[0]*d; q_diag=[0]*d
rhs_cross=[[0]*d for _ in range(d)]; q_cross=[[0]*d for _ in range(d)]
for i in range(d):
    D=rs.D_from_mask(basis[i])
    rhs_diag[i]=defects_to_bits(rs.coassoc_defect(D,DZERO),2)
    q_diag[i]=vals_to_bits(rs.phi_power3_nonzero(D,DZERO)[1])
for i in range(d):
    Di=rs.D_from_mask(basis[i])
    for j in range(i+1,d):
        D=rs.D_from_mask(basis[i]^basis[j])
        rhs=defects_to_bits(rs.coassoc_defect(D,DZERO),2)
        q=vals_to_bits(rs.phi_power3_nonzero(D,DZERO)[1])
        rhs_cross[i][j]=rhs ^ rhs_diag[i] ^ rhs_diag[j]
        q_cross[i][j]=q ^ q_diag[i] ^ q_diag[j]
print('tables built')

def eval_quad(mask,diag,cross):
    out=0
    # diag
    mm=mask
    bits=[]
    while mm:
        l=mm & -mm; i=l.bit_length()-1; mm^=l; bits.append(i); out ^= diag[i]
    for aa in range(len(bits)):
        i=bits[aa]
        for j in bits[aa+1:]: out ^= cross[i][j]
    return out

# Precompute for each output q: contribution from L equations = dot(coeff_i, rref_rhs_i)
# For a given RHS bits, rref_rhs_i = parity(Ltrans[i]&RHS). f contribution = parity( xor selected trans & RHS)
f_trans=[0]*QDIM
for q,coeff in enumerate(f_coeff):
    tr=0; cc=coeff
    while cc:
        l=cc & -cc; i=l.bit_length()-1; cc^=l
        tr ^= Ltrans[i]
    f_trans[q]=tr

# Exact enumeration all D1 basis masks.
N=1<<d
bad_cons=0; good=0; cand=[]
# To speed: for each output coordinate expression bit = qbit ^ parity(f_trans&q)
# Could combine into QDIM bits by loop.
print('enumerating',N)
t0=time.time()
for mask in range(N):
    rhs=eval_quad(mask,rhs_diag,rhs_cross)
    # consistency: all zero rows dot rhs=0
    inconsistent=False
    for tr in zero_trans:
        if parity(tr & rhs):
            inconsistent=True; break
    if inconsistent:
        bad_cons+=1; continue
    good+=1
    qbits=eval_quad(mask,q_diag,q_cross)
    # expression on all solutions, assuming F in row span; if F not in span then candidate anyway.
    expr=qbits
    for q,tr in enumerate(f_trans):
        if tr and parity(tr & rhs): expr ^= 1<<q
    if expr or not_in:
        cand.append((mask,expr))
        print('candidate mask',mask,'expr',expr,'rhsbits',rhs.bit_count(),'qbits',qbits)
        break
    if mask and mask%100000==0:
        print(mask,'good',good,'bad',bad_cons,'elapsed',time.time()-t0)
print('done good',good,'bad_cons',bad_cons,'cand',cand[:1],'elapsed',time.time()-t0)
