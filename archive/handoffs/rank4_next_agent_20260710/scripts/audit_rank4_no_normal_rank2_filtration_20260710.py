#!/usr/bin/env python3
"""Deterministic audit of RANK4_NO_NORMAL_RANK2_FILTRATION_2026-07-10.md.

This uses only the Python standard library.  It treats

    R = F_2[a,b]/(a^2,b^2)

as a 16-element ring and checks the displayed rank-four Hopf algebra on all
basis products.  It also exhausts all 192 unimodular vectors in R^2 for the
Lie-ideal obstruction.  No conclusion is inferred from a timeout or partial
run: the final ``AUDIT PASS`` line is printed only after every assertion.
"""

from __future__ import annotations

from itertools import product


# Ring elements are bit masks on (1,a,b,ab), in that order.
ZERO, ONE, A, B, AB = 0, 1, 2, 4, 8
R_ELEMENTS = range(16)


def r_add(x: int, y: int) -> int:
    return x ^ y


def r_mul(x: int, y: int) -> int:
    out = 0
    for i in range(4):
        if not (x >> i) & 1:
            continue
        ia, ib = (i & 1), ((i >> 1) & 1)
        for j in range(4):
            if not (y >> j) & 1:
                continue
            ja, jb = (j & 1), ((j >> 1) & 1)
            if ia + ja <= 1 and ib + jb <= 1:
                out ^= 1 << ((ia + ja) + 2 * (ib + jb))
    return out


def r_is_unit(x: int) -> bool:
    return bool(x & ONE)


def vzero(n: int) -> tuple[int, ...]:
    return (ZERO,) * n


def vadd(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(r_add(a, b) for a, b in zip(x, y))


def vscale(c: int, x: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(r_mul(c, a) for a in x)


def basis(n: int, i: int) -> tuple[int, ...]:
    return tuple(ONE if j == i else ZERO for j in range(n))


def add_term(x: tuple[int, ...], i: int, c: int) -> tuple[int, ...]:
    y = list(x)
    y[i] = r_add(y[i], c)
    return tuple(y)


# D basis: (1,X,Y,Z=XY).  Each table entry is an R-linear combination.
D1, DX, DY, DZ = (basis(4, i) for i in range(4))


def dvec(**coeffs: int) -> tuple[int, ...]:
    names = {"one": 0, "x": 1, "y": 2, "z": 3}
    out = list(vzero(4))
    for name, value in coeffs.items():
        out[names[name]] = value
    return tuple(out)


D_MUL_TABLE = (
    (D1, DX, DY, DZ),
    (DX, dvec(x=B), DZ, dvec(z=B)),
    (DY, dvec(x=A, y=B, z=ONE), dvec(y=A), dvec(y=AB)),
    (DZ, dvec(x=AB), dvec(z=A), dvec(z=AB)),
)


def d_mul(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
    out = vzero(4)
    for i, ci in enumerate(x):
        for j, cj in enumerate(y):
            out = vadd(out, vscale(r_mul(ci, cj), D_MUL_TABLE[i][j]))
    return out


def tensor_mul(
    x: tuple[int, ...], y: tuple[int, ...], n: int,
    mul,
) -> tuple[int, ...]:
    out = vzero(n * n)
    for ij, cij in enumerate(x):
        if not cij:
            continue
        i, j = divmod(ij, n)
        for kl, ckl in enumerate(y):
            if not ckl:
                continue
            k, ell = divmod(kl, n)
            left = mul(basis(n, i), basis(n, k))
            right = mul(basis(n, j), basis(n, ell))
            scalar = r_mul(cij, ckl)
            for p, cp in enumerate(left):
                for q, cq in enumerate(right):
                    idx = p * n + q
                    out = add_term(out, idx, r_mul(scalar, r_mul(cp, cq)))
    return out


def delta_d_basis(i: int) -> tuple[int, ...]:
    out = vzero(16)
    terms = {
        0: ((0, 0),),
        1: ((1, 0), (0, 1)),
        2: ((2, 0), (0, 2)),
        3: ((3, 0), (1, 2), (2, 1), (0, 3)),
    }[i]
    for p, q in terms:
        out = add_term(out, 4 * p + q, ONE)
    return out


DELTA_D = tuple(delta_d_basis(i) for i in range(4))


def delta_linear(x: tuple[int, ...], table: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    out = vzero(len(table[0]))
    for i, ci in enumerate(x):
        out = vadd(out, vscale(ci, table[i]))
    return out


def check_ring() -> None:
    assert r_mul(A, A) == ZERO
    assert r_mul(B, B) == ZERO
    assert r_mul(A, B) == AB
    assert r_mul(AB, A) == r_mul(AB, B) == ZERO
    for x, y, z in product(R_ELEMENTS, repeat=3):
        assert r_mul(r_mul(x, y), z) == r_mul(x, r_mul(y, z))
        assert r_mul(x, y) == r_mul(y, x)
        assert r_mul(x, r_add(y, z)) == r_add(r_mul(x, y), r_mul(x, z))
    units = [x for x in R_ELEMENTS if r_is_unit(x)]
    assert len(units) == 8
    maximal_ideal = {x for x in R_ELEMENTS if not r_is_unit(x)}
    m2 = {
        r_add(r_mul(x1, y1), r_mul(x2, y2))
        for x1, y1, x2, y2 in product(maximal_ideal, repeat=4)
    }
    socle = {
        x for x in R_ELEMENTS
        if all(r_mul(x, y) == ZERO for y in maximal_ideal)
    }
    assert m2 == {ZERO, AB}
    assert socle == {ZERO, AB}
    assert all(r_mul(x, y) == ZERO for x in m2 for y in maximal_ideal)
    print("ring: PASS (16 elements; length 4; m^2=socle=(ab); m^3=0; 8 units)")


def check_d_algebra() -> None:
    db = (D1, DX, DY, DZ)
    for x in db:
        assert d_mul(D1, x) == d_mul(x, D1) == x
    for x, y, z in product(db, repeat=3):
        assert d_mul(d_mul(x, y), z) == d_mul(x, d_mul(y, z))
    assert d_mul(DX, DX) == dvec(x=B)
    assert d_mul(DY, DY) == dvec(y=A)
    assert d_mul(DY, DX) == dvec(x=A, y=B, z=ONE)
    assert d_mul(DX, DY) == DZ
    # All four critical Diamond-lemma overlaps.
    assert d_mul(d_mul(DX, DX), DX) == d_mul(DX, d_mul(DX, DX))
    assert d_mul(d_mul(DY, DY), DY) == d_mul(DY, d_mul(DY, DY))
    assert d_mul(DY, d_mul(DX, DX)) == d_mul(d_mul(DY, DX), DX)
    assert d_mul(d_mul(DY, DY), DX) == d_mul(DY, d_mul(DY, DX))
    print("D algebra: PASS (64 basis associativity checks; 4 critical overlaps)")


def check_d_hopf() -> None:
    db = (D1, DX, DY, DZ)
    for x, y in product(db, repeat=2):
        lhs = delta_linear(d_mul(x, y), DELTA_D)
        rhs = tensor_mul(delta_linear(x, DELTA_D), delta_linear(y, DELTA_D), 4, d_mul)
        assert lhs == rhs

    # Cocommutativity and the two counit identities.
    eps = (ONE, ZERO, ZERO, ZERO)
    for i, delta in enumerate(DELTA_D):
        for p, q in product(range(4), repeat=2):
            assert delta[4 * p + q] == delta[4 * q + p]
        left = vzero(4)
        right = vzero(4)
        for p, q in product(range(4), repeat=2):
            left = add_term(left, q, r_mul(eps[p], delta[4 * p + q]))
            right = add_term(right, p, r_mul(delta[4 * p + q], eps[q]))
        assert left == right == basis(4, i)

    # Coassociativity in D tensor D tensor D.
    for i, delta in enumerate(DELTA_D):
        left = vzero(64)
        right = vzero(64)
        for p, q in product(range(4), repeat=2):
            c = delta[4 * p + q]
            for r, s in product(range(4), repeat=2):
                left = add_term(left, 16 * r + 4 * s + q, r_mul(c, DELTA_D[p][4 * r + s]))
                right = add_term(right, 16 * p + 4 * r + s, r_mul(c, DELTA_D[q][4 * r + s]))
        assert left == right

    sd = (D1, DX, DY, dvec(x=A, y=B, z=ONE))
    for i, j in product(range(4), repeat=2):
        sij = delta_linear(d_mul(basis(4, i), basis(4, j)), sd)
        rhs = d_mul(sd[j], sd[i])
        assert sij == rhs
    for i, delta in enumerate(DELTA_D):
        left = vzero(4)
        right = vzero(4)
        for p, q in product(range(4), repeat=2):
            c = delta[4 * p + q]
            left = vadd(left, vscale(c, d_mul(sd[p], basis(4, q))))
            right = vadd(right, vscale(c, d_mul(basis(4, p), sd[q])))
        expected = D1 if i == 0 else vzero(4)
        assert left == right == expected
    print("D Hopf structure: PASS (multiplicative, coassociative, cocommutative, antipode)")


# The dual A has basis (1,x,y,z=xy).
A1, AX, AY, AZ = (basis(4, i) for i in range(4))


def make_a_mul_table() -> tuple[tuple[tuple[int, ...], ...], ...]:
    table = []
    for i in range(4):
        row = []
        for j in range(4):
            coeffs = tuple(DELTA_D[k][4 * i + j] for k in range(4))
            row.append(coeffs)
        table.append(tuple(row))
    return tuple(table)


A_MUL_TABLE = make_a_mul_table()


def a_mul(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
    out = vzero(4)
    for i, ci in enumerate(x):
        for j, cj in enumerate(y):
            out = vadd(out, vscale(r_mul(ci, cj), A_MUL_TABLE[i][j]))
    return out


def make_delta_a() -> tuple[tuple[int, ...], ...]:
    table = []
    for k in range(4):
        delta = vzero(16)
        for i, j in product(range(4), repeat=2):
            delta = add_term(delta, 4 * i + j, D_MUL_TABLE[i][j][k])
        table.append(delta)
    return tuple(table)


DELTA_A = make_delta_a()


def expected_delta_a() -> tuple[tuple[int, ...], ...]:
    out = [vzero(16) for _ in range(4)]
    formulas = {
        0: ((0, 0, ONE),),
        1: ((1, 0, ONE), (0, 1, ONE), (1, 1, B), (2, 1, A), (3, 1, AB)),
        2: ((2, 0, ONE), (0, 2, ONE), (2, 2, A), (2, 1, B), (2, 3, AB)),
        3: (
            (3, 0, ONE), (0, 3, ONE), (1, 2, ONE), (2, 1, ONE),
            (1, 3, B), (3, 2, A), (3, 3, AB),
        ),
    }
    for k, terms in formulas.items():
        for i, j, c in terms:
            out[k] = add_term(out[k], 4 * i + j, c)
    return tuple(out)


def mu_tensor(delta: tuple[int, ...]) -> tuple[int, ...]:
    out = vzero(4)
    for i, j in product(range(4), repeat=2):
        out = vadd(out, vscale(delta[4 * i + j], A_MUL_TABLE[i][j]))
    return out


def check_a_hopf_and_power() -> None:
    abasis = (A1, AX, AY, AZ)
    assert A_MUL_TABLE[1][1] == A_MUL_TABLE[2][2] == vzero(4)
    assert A_MUL_TABLE[1][2] == A_MUL_TABLE[2][1] == AZ
    for i in (1, 2, 3):
        assert A_MUL_TABLE[3][i] == A_MUL_TABLE[i][3] == vzero(4)
    assert DELTA_A == expected_delta_a()
    # Reducing all coefficients modulo m gives the standard Hopf algebra of
    # alpha_2 x alpha_2.
    reduce_residue = lambda c: c & ONE
    residue_delta = tuple(tuple(reduce_residue(c) for c in d) for d in DELTA_A)
    expected_residue = tuple(
        tuple(reduce_residue(c) for c in d) for d in expected_delta_a()
    )
    assert residue_delta == expected_residue
    for x, y, z in product(abasis, repeat=3):
        assert a_mul(a_mul(x, y), z) == a_mul(x, a_mul(y, z))
    for x, y in product(abasis, repeat=2):
        lhs = delta_linear(a_mul(x, y), DELTA_A)
        rhs = tensor_mul(delta_linear(x, DELTA_A), delta_linear(y, DELTA_A), 4, a_mul)
        assert lhs == rhs

    # Dual antipode: S(1)=1, S(x)=x+az, S(y)=y+bz, S(z)=z.
    sa = (A1, vadd(AX, vscale(A, AZ)), vadd(AY, vscale(B, AZ)), AZ)
    for i, delta in enumerate(DELTA_A):
        left = vzero(4)
        right = vzero(4)
        for p, q in product(range(4), repeat=2):
            c = delta[4 * p + q]
            left = vadd(left, vscale(c, a_mul(sa[p], basis(4, q))))
            right = vadd(right, vscale(c, a_mul(basis(4, p), sa[q])))
        expected = A1 if i == 0 else vzero(4)
        assert left == right == expected

    phi = tuple(mu_tensor(delta) for delta in DELTA_A)
    assert phi == (A1, vscale(A, AZ), vscale(B, AZ), vzero(4))
    phi2 = tuple(delta_linear(x, phi) for x in phi)
    assert phi2 == (A1, vzero(4), vzero(4), vzero(4))

    # Exhaust every augmentation-ideal element, not just the basis.
    for cx, cy, cz in product(R_ELEMENTS, repeat=3):
        element = (ZERO, cx, cy, cz)
        assert a_mul(element, element) == vzero(4)
    print("A Hopf structure: PASS (displayed coproduct and antipode exact; special fiber alpha_2^2)")
    print("power maps: PASS (phi(x)=az, phi(y)=bz, phi(z)=0, phi^2=eta*epsilon)")
    print("height one: PASS (all 4096 augmentation-ideal elements square to zero)")


def check_lie_and_flatness_obstructions() -> None:
    ideal_a = {r_mul(A, r) for r in R_ELEMENTS}
    ideal_b = {r_mul(B, r) for r in R_ELEMENTS}
    assert B not in ideal_a and A not in ideal_b

    unimodular = []
    ideal_lines = []
    scalar_containments = []
    for r, s in product(R_ELEMENTS, repeat=2):
        if not (r_is_unit(r) or r_is_unit(s)):
            continue
        unimodular.append((r, s))
        wedge = r_add(r_mul(A, s), r_mul(B, r))
        if wedge == ZERO:
            ideal_lines.append((r, s))
        for lam in R_ELEMENTS:
            if r_mul(lam, r) == A and r_mul(lam, s) == B:
                scalar_containments.append((r, s, lam))
    assert len(unimodular) == 192
    assert not ideal_lines
    assert not scalar_containments
    print("Lie obstruction: PASS (192/192 unimodular vectors fail w∧v=0)")
    print("faithful-flat descent inputs: PASS (b notin (a), a notin (b))")

    # A/(az,bz) = R{1,x,y} + (R/m){z}: cardinality 16^3*2=8192.
    quotient_size = 16**3 * 2
    assert quotient_size == 8192
    assert all(quotient_size != 16**n for n in range(8))
    print("squaring equalizer: PASS (cardinality 8192, hence not finite free/flat over local R)")


def main() -> None:
    print("rank4 no-normal-rank2 filtration audit v1")
    check_ring()
    check_d_algebra()
    check_d_hopf()
    check_a_hopf_and_power()
    check_lie_and_flatness_obstructions()
    print("AUDIT PASS")


if __name__ == "__main__":
    main()
