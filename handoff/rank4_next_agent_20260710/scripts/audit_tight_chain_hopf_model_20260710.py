#!/usr/bin/env python3
"""Exact finite audit of the nonprincipal tight-chain Hopf model.

The coefficient ring is F2[u,v]/(u^2,v^2), represented on the basis
1,u,v,uv.  All bialgebra identities are checked on basis elements, which is
exhaustive by multilinearity.  No solver is used.
"""

from itertools import product


# Ring elements are four-bit coefficient vectors, packed into an integer.
# Bit m is the coefficient of u^(m&1) v^((m>>1)&1).
ZERO, ONE, U, V, C = 0, 1, 2, 4, 8


def radd(a, b):
    return a ^ b


def rmul(a, b):
    out = 0
    for i in range(4):
        if not ((a >> i) & 1):
            continue
        for j in range(4):
            if not ((b >> j) & 1):
                continue
            if i & j:  # a repeated u or v gives u^2 or v^2
                continue
            out ^= 1 << (i | j)
    return out


assert rmul(U, U) == rmul(V, V) == 0
assert rmul(U, V) == C and rmul(C, U) == rmul(C, V) == 0


def vzero(n):
    return [ZERO] * n


def vadd(a, b):
    return [radd(x, y) for x, y in zip(a, b)]


def vscale(a, x):
    return [rmul(a, y) for y in x]


def basis(i, n=4):
    out = vzero(n)
    out[i] = ONE
    return out


# D basis: 1,X,Y,Z=XY.  Put a=u+uv and c=uv.
A = radd(U, C)
M = [[vzero(4) for _ in range(4)] for _ in range(4)]
for i in range(4):
    M[0][i] = basis(i)
    M[i][0] = basis(i)
M[1][1] = vscale(A, basis(1))                 # X^2=aX
M[1][2] = basis(3)                            # XY=Z
M[2][1] = vadd(basis(3), vscale(C, basis(2))) # YX=Z+cY
M[2][2] = vzero(4)                            # Y^2=0
M[1][3] = vscale(A, basis(3))                 # XZ=aZ
M[3][1] = vscale(U, basis(3))                 # ZX=uZ
M[2][3] = M[3][2] = M[3][3] = vzero(4)


def dmul(x, y):
    out = vzero(4)
    for i, xi in enumerate(x):
        for j, yj in enumerate(y):
            out = vadd(out, vscale(rmul(xi, yj), M[i][j]))
    return out


# Tensor index is 4*i+j.
def tidx(i, j):
    return 4 * i + j


DELTA = [vzero(16) for _ in range(4)]
DELTA[0][tidx(0, 0)] = ONE
DELTA[1][tidx(1, 0)] = DELTA[1][tidx(0, 1)] = ONE
DELTA[2][tidx(2, 0)] = DELTA[2][tidx(0, 2)] = ONE
DELTA[2][tidx(1, 1)] = V
DELTA[3][tidx(3, 0)] = DELTA[3][tidx(0, 3)] = ONE
DELTA[3][tidx(1, 2)] = DELTA[3][tidx(2, 1)] = ONE


def delta(x):
    out = vzero(16)
    for i, xi in enumerate(x):
        out = vadd(out, vscale(xi, DELTA[i]))
    return out


def tmul(x, y):
    out = vzero(16)
    for i, j, k, ell in product(range(4), repeat=4):
        co = rmul(x[tidx(i, j)], y[tidx(k, ell)])
        if not co:
            continue
        left = M[i][k]
        right = M[j][ell]
        for p, lp in enumerate(left):
            for q, rq in enumerate(right):
                out[tidx(p, q)] ^= rmul(co, rmul(lp, rq))
    return out


def delta_left(x):
    out = vzero(64)
    for i, j in product(range(4), repeat=2):
        co = x[tidx(i, j)]
        for p, q in product(range(4), repeat=2):
            out[16 * p + 4 * q + j] ^= rmul(co, DELTA[i][tidx(p, q)])
    return out


def delta_right(x):
    out = vzero(64)
    for i, j in product(range(4), repeat=2):
        co = x[tidx(i, j)]
        for q, r in product(range(4), repeat=2):
            out[16 * i + 4 * q + r] ^= rmul(co, DELTA[j][tidx(q, r)])
    return out


# Antipode: S(X)=X, S(Y)=Y+cX, S(Z)=Z+cY.
ANTIPODE = [basis(0), basis(1), vadd(basis(2), vscale(C, basis(1))),
            vadd(basis(3), vscale(C, basis(2)))]


def apply_s(x):
    out = vzero(4)
    for i, xi in enumerate(x):
        out = vadd(out, vscale(xi, ANTIPODE[i]))
    return out


def convolution_on_basis(i, left=True):
    out = vzero(4)
    for p, q in product(range(4), repeat=2):
        co = DELTA[i][tidx(p, q)]
        a, b = (apply_s(basis(p)), basis(q)) if left else (basis(p), apply_s(basis(q)))
        out = vadd(out, vscale(co, dmul(a, b)))
    return out


# Algebra, coalgebra, bialgebra, counit, and antipode checks.
for i, j, k in product(range(4), repeat=3):
    assert dmul(dmul(basis(i), basis(j)), basis(k)) == dmul(basis(i), dmul(basis(j), basis(k)))

for i, j in product(range(4), repeat=2):
    assert delta(dmul(basis(i), basis(j))) == tmul(DELTA[i], DELTA[j])

for i in range(4):
    assert delta_left(DELTA[i]) == delta_right(DELTA[i])
    left_counit = [DELTA[i][tidx(0, j)] for j in range(4)]
    right_counit = [DELTA[i][tidx(j, 0)] for j in range(4)]
    assert left_counit == right_counit == basis(i)
    target = basis(0) if i == 0 else vzero(4)
    assert convolution_on_basis(i, True) == target
    assert convolution_on_basis(i, False) == target

# P_2=mu Delta: X->0, Y->uv X, Z->uv Y, hence P_2^2=0.
P = []
for i in range(4):
    out = vzero(4)
    for p, q in product(range(4), repeat=2):
        out = vadd(out, vscale(DELTA[i][tidx(p, q)], M[p][q]))
    P.append(out)
assert P[0] == basis(0)
assert P[1] == vzero(4)
assert P[2] == vscale(C, basis(1))
assert P[3] == vscale(C, basis(2))
for i in range(1, 4):
    out = vzero(4)
    for j, co in enumerate(P[i]):
        out = vadd(out, vscale(co, P[j]))
    assert out == vzero(4)

# Dual coordinate map phi=P^vee on (x,y,z): x->uv y, y->uv z, z->0.
PHI = [vscale(C, basis(2)), vscale(C, basis(3)), vzero(4)]


def phi_i(x):
    out = vzero(4)
    for i in range(1, 4):
        out = vadd(out, vscale(x[i], PHI[i - 1]))
    return out


# Exact S' witnesses over m=(u,v): uv*y=v*(u*y), uv*z=u*(v*z).
uy = vscale(U, basis(2))
vz = vscale(V, basis(3))
assert phi_i(uy) == vzero(4)
assert phi_i(vz) == vzero(4)
assert PHI[0] == vscale(V, uy)
assert PHI[1] == vscale(U, vz)
assert PHI[2] == vzero(4)

# The tempting division by the socle element c gives a literal length-three
# chain x->y->z, but c is not a generator of m and this is not the S' test.
SOCLE_DIVIDED = [basis(2), basis(3), vzero(4)]
assert SOCLE_DIVIDED[1] == basis(3)  # C^2(x)=z != 0

# Noncommutativity and special-fiber checks.
assert dmul(basis(2), basis(1)) != dmul(basis(1), basis(2))
for i in range(1, 4):
    assert all((co & 1) == 0 for co in P[i])  # killed-by-two special fiber


def residue_vec(x):
    return [co & 1 for co in x]


special_m = [[vzero(4) for _ in range(4)] for _ in range(4)]
for i in range(4):
    special_m[0][i] = basis(i)
    special_m[i][0] = basis(i)
special_m[1][2] = special_m[2][1] = basis(3)
for i, j in product(range(4), repeat=2):
    assert residue_vec(M[i][j]) == special_m[i][j]

special_delta = [vzero(16) for _ in range(4)]
special_delta[0][tidx(0, 0)] = ONE
special_delta[1][tidx(1, 0)] = special_delta[1][tidx(0, 1)] = ONE
special_delta[2][tidx(2, 0)] = special_delta[2][tidx(0, 2)] = ONE
special_delta[3][tidx(3, 0)] = special_delta[3][tidx(0, 3)] = ONE
special_delta[3][tidx(1, 2)] = special_delta[3][tidx(2, 1)] = ONE
for i in range(4):
    assert residue_vec(DELTA[i]) == special_delta[i]

print("associativity: PASS (64 basis triples)")
print("bialgebra and coassociativity: PASS")
print("antipode: PASS")
print("P2: X->0, Y->uv*X, Z->uv*Y; P2^2=0: PASS")
print("dual phi: x->uv*y, y->uv*z, z->0")
print("S': uv*y=v*(u*y), uv*z=u*(v*z), with u*y and v*z in ker(phi): PASS")
print("noncommutative total group and alpha_2^2 special fiber: PASS")
print("AUDIT PASS")
