"""Fast certificate companion to rank8_exact.py.

Checks the rank-8 fixed-algebra Heisenberg/U3 second-order search without
enumerating all 2^20 first-order masks. The key point is that the target
[8]^#=[2]^#^3 expression is identically zero as a quadratic polynomial in the
first-order cocycle parameters and has no linear dependence on D2.
"""
import sys, time
sys.path.append('/mnt/data')
import rank8_search as rs

NP = rs.NP
DZERO = {g: 0 for g in rs.GENS}
QDIM = 3 * 3 * 8
M = 3 * rs.T3_DIM

def defects_to_bits(defs, deg):
    out = 0
    for gi, d in enumerate(defs):
        v = d[deg]
        while v:
            l = v & -v
            c = l.bit_length() - 1
            v ^= l
            out ^= 1 << (gi * rs.T3_DIM + c)
    return out

def vals_to_bits(vals):
    out = 0
    pos = 0
    for val in vals:
        for deg in range(3):
            v = val[deg]
            for a in range(8):
                if (v >> a) & 1:
                    out ^= 1 << pos
                pos += 1
    return out

def build_L_rows():
    rows = [0] * M
    for j, (g, idx) in enumerate(rs.PARAMS):
        D2 = {gg: 0 for gg in rs.GENS}
        D2[g] = 1 << idx
        bits = defects_to_bits(rs.coassoc_defect(DZERO, D2), 2)
        while bits:
            l = bits & -bits
            i = l.bit_length() - 1
            bits ^= l
            rows[i] ^= 1 << j
    return rows

def rank_rows(rows):
    basis = {}
    rank = 0
    for row in rows:
        while row:
            p = (row & -row).bit_length() - 1
            b = basis.get(p)
            if b is None:
                basis[p] = row
                rank += 1
                break
            row ^= b
    return rank

print('NP per layer', NP, flush=True)
t0 = time.time()
rows1 = rs.lin_rows_for_layer1()
basis, pivots, rref = rs.nullspace_basis(rows1, NP)
print('D1 dim', len(basis), 'linear rank', len(pivots), 'time', time.time()-t0, flush=True)

Lrows = build_L_rows()
print('D2 coassoc linear rank', rank_rows(Lrows), 'nonzero rows', sum(1 for r in Lrows if r), flush=True)

F_cols = [0] * QDIM
for j, (g, idx) in enumerate(rs.PARAMS):
    D2 = {gg: 0 for gg in rs.GENS}
    D2[g] = 1 << idx
    bits = vals_to_bits(rs.phi_power3_nonzero(DZERO, D2)[1])
    while bits:
        l = bits & -bits
        q = l.bit_length() - 1
        bits ^= l
        F_cols[q] ^= 1 << j
print('D2 contribution to phi^3 nonzero output coordinates', sum(1 for f in F_cols if f), flush=True)

q_diag = []
q_cross_nonzero = []
for i, b in enumerate(basis):
    q = vals_to_bits(rs.phi_power3_nonzero(rs.D_from_mask(b), DZERO)[1])
    if q:
        q_diag.append((i, q))
for i in range(len(basis)):
    for j in range(i+1, len(basis)):
        D = rs.D_from_mask(basis[i] ^ basis[j])
        qij = vals_to_bits(rs.phi_power3_nonzero(D, DZERO)[1])
        qi = 0
        qj = 0
        # recompute directly to avoid storing all values; dimension is only 20.
        qi = vals_to_bits(rs.phi_power3_nonzero(rs.D_from_mask(basis[i]), DZERO)[1])
        qj = vals_to_bits(rs.phi_power3_nonzero(rs.D_from_mask(basis[j]), DZERO)[1])
        cross = qij ^ qi ^ qj
        if cross:
            q_cross_nonzero.append((i, j, cross))
            break
    if q_cross_nonzero:
        break
print('phi^3 quadratic diagonal nonzero count', len(q_diag), 'first', q_diag[:3], flush=True)
print('phi^3 quadratic cross nonzero count', len(q_cross_nonzero), 'first', q_cross_nonzero[:1], flush=True)
if sum(1 for f in F_cols if f) == 0 and not q_diag and not q_cross_nonzero:
    print('CERTIFICATE: phi^3 is identically zero for all first-order D1 and all second-layer D2 in this fixed-algebra U3 search.', flush=True)
else:
    print('NOT CERTIFIED: target polynomial has nonzero coefficients.', flush=True)
print('elapsed', time.time()-t0, flush=True)
