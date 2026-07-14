import sys, time
sys.path.append('/mnt/data')
import rank8_search as rs
NP=rs.NP; M=3*rs.T3_DIM; DZERO={g:0 for g in rs.GENS}

def defects_to_bits(defs, deg):
    out=0
    for gi,d in enumerate(defs):
        v=d[deg]
        while v:
            l=v & -v; c=l.bit_length()-1; v^=l
            out ^= 1<<(gi*rs.T3_DIM+c)
    return out

def vals_to_bits(vals):
    out=0; pos=0
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
    rows=rows[:]; trans=[1<<i for i in range(len(rows))]
    r=0; piv=[]
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

def reduce_f_get_coeffs(f, rref_rows, rank):
    coeff=0; rem=f
    for i in range(rank):
        row=rref_rows[i]; p=(row & -row).bit_length()-1
        if (rem>>p)&1: rem^=row; coeff^=1<<i
    return rem,coeff

def parity(x): return x.bit_count()&1
print('basis')
rows1=rs.lin_rows_for_layer1(); basis,pivots,rref=rs.nullspace_basis(rows1,NP); d=len(basis)
print('d',d)
print('L')
Lrows=build_L_full(); Lr,Ltrans,Lpiv,rank=rref_with_transform(Lrows,NP)
zero_trans=[Ltrans[i] for i in range(rank,M) if Lr[i]==0]
print('rank',rank,'zero_trans',len(zero_trans))
# F cols zero?
F_cols=[0]*QDIM
for j,(g,idx) in enumerate(rs.PARAMS):
    D2={gg:0 for gg in rs.GENS}; D2[g]=1<<idx
    vals=rs.phi_power3_nonzero(DZERO,D2)[1]
    bits=vals_to_bits(vals)
    bb=bits
    while bb:
        l=bb & -bb; q=l.bit_length()-1; bb^=l
        F_cols[q]^=1<<j
notin=[]; f_coeff=[]
for q,f in enumerate(F_cols):
    rem,coeff=reduce_f_get_coeffs(f,Lr,rank); f_coeff.append(coeff)
    if rem: notin.append(q)
print('F nonzero',sum(1 for f in F_cols if f),'notin',notin[:5])
# quadratic diag/cross for rhs/q
rhs_diag=[]; q_diag=[]
for i,b in enumerate(basis):
    D=rs.D_from_mask(b)
    rhs_diag.append(defects_to_bits(rs.coassoc_defect(D,DZERO),2))
    q_diag.append(vals_to_bits(rs.phi_power3_nonzero(D,DZERO)[1]))
print('q_diag nonzero',[(i,x) for i,x in enumerate(q_diag) if x])
rhs_cross=[]; q_cross=[]; qc_non=[]; rc_non=0
for i in range(d):
    row=[]; qrow=[]
    for j in range(i+1,d):
        D=rs.D_from_mask(basis[i]^basis[j])
        rhs=defects_to_bits(rs.coassoc_defect(D,DZERO),2)^rhs_diag[i]^rhs_diag[j]
        q=vals_to_bits(rs.phi_power3_nonzero(D,DZERO)[1])^q_diag[i]^q_diag[j]
        row.append(rhs); qrow.append(q)
        if rhs: rc_non+=1
        if q: qc_non.append((i,j,q))
    rhs_cross.append(row); q_cross.append(qrow)
print('rhs_diag nonzero',sum(1 for x in rhs_diag if x),'rhs_cross nonzero',rc_non)
print('q_cross nonzero count',len(qc_non),'first',qc_non[:10])
# Check consistency polynomials by composing each zero_trans with rhs diag/cross
bad_diag=[]; bad_cross=[]
for ti,tr in enumerate(zero_trans):
    for i,x in enumerate(rhs_diag):
        if parity(tr&x): bad_diag.append((ti,i)); break
    if bad_diag and bad_diag[-1][0]==ti: continue
    idx=0
    for i in range(d):
        for jj,x in enumerate(rhs_cross[i]):
            j=i+1+jj
            if parity(tr&x): bad_cross.append((ti,i,j)); break
        if bad_cross and bad_cross[-1][0]==ti: break
print('bad consistency diag',len(bad_diag),'cross',len(bad_cross),'first',bad_diag[:5],bad_cross[:5])
# expression q + f_trans(rhs); F zero so f_trans zero? Check f_trans nonzero count
f_trans=[]
for q,coeff in enumerate(f_coeff):
    tr=0; cc=coeff
    while cc:
        l=cc&-cc; i=l.bit_length()-1; cc^=l
        tr^=Ltrans[i]
    f_trans.append(tr)
print('f_trans nonzero',sum(1 for x in f_trans if x))
# Compute expression polynomial coefficients for each q coordinate; report any nonzero
expr_diag=[0]*d; expr_cross=[[0]*(d-i-1) for i in range(d)]
expr_non=[]
for out in range(QDIM):
    tr=f_trans[out]
    # bit coefficient packed per monomial? compute if any
    for i,x in enumerate(q_diag):
        coeff=((x>>out)&1) ^ (parity(tr&rhs_diag[i]) if tr else 0)
        if coeff: expr_non.append(('diag',out,i)); break
    if expr_non and expr_non[-1][1]==out: continue
    for i in range(d):
        for jj,x in enumerate(q_cross[i]):
            coeff=((x>>out)&1) ^ (parity(tr&x) if tr else 0)
            if coeff: expr_non.append(('cross',out,i,i+1+jj)); break
        if expr_non and expr_non[-1][1]==out: break
print('expr nonzero coeff count outputs/first',len(expr_non),expr_non[:20])
