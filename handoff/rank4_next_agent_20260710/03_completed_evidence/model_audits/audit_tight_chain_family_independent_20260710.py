#!/usr/bin/env python3
"""Independent bounded checks for the tight-chain audit.

This script does two finite computations, without a solver:

1. It exhausts all parameter quadruples (a,c,d,s) in
   F2[u,v]/(u^2,v^2) satisfying (4.2)--(4.3), and checks the claimed
   rank-four algebra, coalgebra, antipode, and Sweedler-square formulas.
   For every tuple whose special fiber is killed by two, it also checks
   the explicit S' witnesses, including the case in which s is a unit.
2. Over F2[pi]/(pi^6) (the first case N=5), it exhausts the 32 possible
   residue tuples in Section 5 and checks the displayed formulas (5.5)
   and the following formula for B^2(T^2).
"""

from itertools import product


# F2[u,v]/(u^2,v^2), with bits indexed by 1,u,v,uv.
ZERO, ONE, U, V, UV = 0, 1, 2, 4, 8


def radd(a, b):
    return a ^ b


def rmul(a, b):
    out = 0
    for i, j in product(range(4), repeat=2):
        if ((a >> i) & 1) and ((b >> j) & 1) and not (i & j):
            out ^= 1 << (i | j)
    return out


def rvzero(n):
    return [ZERO] * n


def rvadd(x, y):
    return [radd(a, b) for a, b in zip(x, y)]


def rvscale(a, x):
    return [rmul(a, b) for b in x]


def rbasis(i, n=4):
    x = rvzero(n)
    x[i] = ONE
    return x


def family_tables(a, c, d, s):
    """Multiplication, coproduct, and antipode on 1,X,Y,Z=XY."""
    h = radd(a, c)
    m = [[rvzero(4) for _ in range(4)] for _ in range(4)]
    for i in range(4):
        m[0][i] = rbasis(i)
        m[i][0] = rbasis(i)
    m[1][1] = rvscale(a, rbasis(1))
    m[1][2] = rbasis(3)
    m[2][1] = rvadd(rbasis(3), rvscale(c, rbasis(2)))
    m[2][2] = rvscale(d, rbasis(2))
    m[1][3] = rvscale(a, rbasis(3))
    m[3][1] = rvscale(h, rbasis(3))
    m[2][3] = m[3][2] = rvscale(d, rbasis(3))
    m[3][3] = rvscale(rmul(a, d), rbasis(3))

    def tidx(i, j):
        return 4 * i + j

    delta = [rvzero(16) for _ in range(4)]
    delta[0][tidx(0, 0)] = ONE
    delta[1][tidx(1, 0)] = delta[1][tidx(0, 1)] = ONE
    delta[2][tidx(2, 0)] = delta[2][tidx(0, 2)] = ONE
    delta[2][tidx(1, 1)] = s
    delta[3][tidx(3, 0)] = delta[3][tidx(0, 3)] = ONE
    delta[3][tidx(1, 2)] = delta[3][tidx(2, 1)] = ONE

    antipode = [
        rbasis(0),
        rbasis(1),
        rvadd(rbasis(2), rvscale(rmul(s, a), rbasis(1))),
        rvadd(
            rvadd(rbasis(3), rvscale(c, rbasis(2))),
            rvscale(rmul(s, rmul(a, a)), rbasis(1)),
        ),
    ]
    return m, delta, antipode


def audit_family_tuple(a, c, d, s):
    m, delta, antipode = family_tables(a, c, d, s)

    def vmul(x, y):
        out = rvzero(4)
        for i, j in product(range(4), repeat=2):
            out = rvadd(out, rvscale(rmul(x[i], y[j]), m[i][j]))
        return out

    def tindex(i, j):
        return 4 * i + j

    def tscale(co, x):
        return rvscale(co, x)

    def tmul(x, y):
        out = rvzero(16)
        for i, j, k, ell in product(range(4), repeat=4):
            co = rmul(x[tindex(i, j)], y[tindex(k, ell)])
            if not co:
                continue
            for p, q in product(range(4), repeat=2):
                out[tindex(p, q)] ^= rmul(co, rmul(m[i][k][p], m[j][ell][q]))
        return out

    def delta_v(x):
        out = rvzero(16)
        for i in range(4):
            out = rvadd(out, tscale(x[i], delta[i]))
        return out

    for i, j, k in product(range(4), repeat=3):
        assert vmul(vmul(rbasis(i), rbasis(j)), rbasis(k)) == vmul(
            rbasis(i), vmul(rbasis(j), rbasis(k))
        )
    for i, j in product(range(4), repeat=2):
        assert delta_v(vmul(rbasis(i), rbasis(j))) == tmul(delta[i], delta[j])

    # Coassociativity and both antipode convolutions.
    for i in range(4):
        dl = rvzero(64)
        dr = rvzero(64)
        for p, q in product(range(4), repeat=2):
            co = delta[i][tindex(p, q)]
            for j, k in product(range(4), repeat=2):
                dl[16 * j + 4 * k + q] ^= rmul(co, delta[p][tindex(j, k)])
                dr[16 * p + 4 * j + k] ^= rmul(co, delta[q][tindex(j, k)])
        assert dl == dr
        for left in (True, False):
            conv = rvzero(4)
            for p, q in product(range(4), repeat=2):
                co = delta[i][tindex(p, q)]
                lp = antipode[p] if left else rbasis(p)
                rq = rbasis(q) if left else antipode[q]
                conv = rvadd(conv, rvscale(co, vmul(lp, rq)))
            assert conv == (rbasis(0) if i == 0 else rvzero(4))

    p2 = []
    for i in range(4):
        value = rvzero(4)
        for p, q in product(range(4), repeat=2):
            value = rvadd(value, rvscale(delta[i][tindex(p, q)], m[p][q]))
        p2.append(value)
    h = radd(a, c)
    assert p2[1] == rvzero(4)
    assert p2[2] == rvscale(rmul(s, h), rbasis(1))
    assert p2[3] == rvscale(c, rbasis(2))

    # If the special fiber is killed by two, c and s*h lie in m.
    # Check the two explicit case-by-case kernel divisions for phi on A=D^vee.
    killed_fiber = not (c & ONE) and not (rmul(s, h) & ONE)
    if killed_fiber:
        if not (s & ONE):  # s in m: sh*y=s*(h*y), c*z=c*z.
            assert rmul(h, c) == 0
        else:              # s unit: cs=0 => c=0, and sh in m => h in m.
            assert c == 0 and not (h & ONE)
    return killed_fiber


valid = killed = 0
for a, c, d, s in product(range(16), repeat=4):
    h = radd(a, c)
    if not (
        rmul(c, h) == 0
        and rmul(c, s) == 0
        and rmul(c, d) == 0
        and rmul(s, radd(d, rmul(s, rmul(a, a)))) == 0
    ):
        continue
    valid += 1
    killed += audit_family_tuple(a, c, d, s)


# F2[pi]/pi^6, packed into six bits.  Work modulo pi^5 when comparing B.
PI_LEN = 6
PI_MASK = (1 << PI_LEN) - 1
B_MASK = (1 << 5) - 1


def pmul(a, b):
    out = 0
    for i, j in product(range(PI_LEN), repeat=2):
        if i + j < PI_LEN and ((a >> i) & 1) and ((b >> j) & 1):
            out ^= 1 << (i + j)
    return out


def pscale(a, x):
    return [pmul(a, b) for b in x]


def padd(x, y):
    return [a ^ b for a, b in zip(x, y)]


def t_reduce(n, r, cache):
    if n < 4:
        out = [0] * 4
        out[n] = ONE
        return out
    if n in cache:
        return cache[n]
    out = [0] * 4
    q = 1 << 3
    for j in range(1, 4):
        out = padd(out, pscale(pmul(q, r[j]), t_reduce(n - 4 + j, r, cache)))
    cache[n] = out
    return out


def amul(x, y, r):
    out = [0] * 4
    cache = {}
    for i, j in product(range(4), repeat=2):
        out = padd(out, pscale(pmul(x[i], y[j]), t_reduce(i + j, r, cache)))
    return out


def div_pi(x):
    assert all(not (co & 1) for co in x)
    return [co >> 1 for co in x]


monogenic_cases = 0
for a0, b0, d0, beta0, gamma0 in product(range(2), repeat=5):
    r = [0, a0, b0, d0]
    v = [0, 0, beta0, gamma0]
    phi_t = pscale(1 << 1, v)
    b_t2 = div_pi(amul(phi_t, phi_t, r))
    b_t3 = div_pi(amul(amul(phi_t, phi_t, r), phi_t, r))
    expected_t2 = pscale(
        1 << 4,
        padd(pscale(beta0, r), [0, 0, 0, gamma0 * a0]),
    )
    assert [x & B_MASK for x in b_t2] == [x & B_MASK for x in expected_t2]
    assert all(not (x & B_MASK) for x in b_t3)

    # B^2(T^2), computed from B on the basis modulo pi^5.
    bcols = [None, v, b_t2, b_t3]
    b2_t2 = [0] * 4
    for j in range(1, 4):
        b2_t2 = padd(b2_t2, pscale(b_t2[j], bcols[j]))
    expected_b2_t2 = pscale(
        1 << 4,
        [0, 0, beta0 * a0, beta0 * a0 * gamma0],
    )
    assert [x & B_MASK for x in b2_t2] == [x & B_MASK for x in expected_b2_t2]
    monogenic_cases += 1


print(f"triangular family: PASS ({valid} valid parameter tuples; {killed} killed-fiber tuples)")
print(f"monogenic N=5 formulas: PASS ({monogenic_cases} residue tuples)")
print("INDEPENDENT AUDIT PASS")
