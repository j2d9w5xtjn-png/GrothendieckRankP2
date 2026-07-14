#!/usr/bin/env python3
"""Audit the supplementary descriptions of the length-10 rank-4 example.

This script imports the exact tuple implementation used by
``verify_rank4_length10_counterexample_20260710.py`` and checks:

* the displayed regular GL_4 matrix and its GL_3 quotient;
* an explicit recovery of e1,e2,e3 from the GL_3 matrix coefficients;
* the multiplication and coalgebra tables of the dual Hopf algebra;
* the rank-2 Hopf quotient defining the subgroup H_x, and [2]_{H_x}=e.

There is no search here.  All matrices have size at most 4 by 4, and the
script uses far less than 100 MiB of memory.
"""

from __future__ import annotations

from itertools import product

from verify_rank4_length10_counterexample_20260710 import (
    AElement,
    D,
    DELTA,
    IDENTITY,
    ONE,
    PROJECTION,
    R,
    SOCLE,
    X,
    XSTAR,
    Y,
    YSTAR,
    Z,
    ZERO,
    aadd,
    abasis,
    amul,
    ascale,
    azero,
    map_apply,
    mul_basis,
    radd,
    rmul,
    rneg,
    rscale,
    verify_base_ring,
    verify_hopf_algebra,
)


def aneg(a: AElement) -> AElement:
    return tuple(rneg(c) for c in a)  # type: ignore[return-value]


def aterm(c: R, i: int) -> AElement:
    return ascale(c, abasis(i))


def asum(*terms: AElement) -> AElement:
    out = azero()
    for term in terms:
        out = aadd(out, term)
    return out


def universal_translation_matrix() -> list[list[AElement]]:
    """Matrix of (id tensor g)Delta with the universal point g."""
    matrix = [[azero() for _ in range(4)] for _ in range(4)]
    for column, row in product(range(4), repeat=2):
        entry = azero()
        for second in range(4):
            entry = aadd(
                entry,
                aterm(DELTA[column][4 * row + second], second),
            )
        matrix[row][column] = entry
    return matrix


def matrix_mul(
    left: list[list[AElement]], right: list[list[AElement]]
) -> list[list[AElement]]:
    rows = len(left)
    middle = len(right)
    columns = len(right[0])
    assert len(left[0]) == middle
    out = [[azero() for _ in range(columns)] for _ in range(rows)]
    for i, j, k in product(range(rows), range(columns), range(middle)):
        out[i][j] = aadd(out[i][j], amul(left[i][k], right[k][j]))
    return out


def identity_matrix(n: int) -> list[list[AElement]]:
    return [
        [abasis(0) if i == j else azero() for j in range(n)]
        for i in range(n)
    ]


def verify_linear_representations(antipode) -> None:
    q = radd(XSTAR, rmul(X, Y))
    # D*=XY in the imported inverse-system basis.
    omega = rmul(X, Y)
    assert q == radd(XSTAR, omega)
    eta = YSTAR
    sigma = SOCLE
    three_plus_eta = radd(rscale(3, ONE), eta)

    matrix = universal_translation_matrix()
    expected = [[azero() for _ in range(4)] for _ in range(4)]
    expected[0] = [abasis(0), abasis(1), abasis(2), abasis(3)]
    expected[1] = [
        azero(),
        asum(abasis(0), aterm(X, 1)),
        azero(),
        asum(abasis(2), aterm(X, 3)),
    ]
    expected[2] = [
        azero(),
        aterm(radd(Y, Z), 1),
        asum(
            abasis(0), aterm(D, 1), aterm(radd(Y, Z), 2), aterm(q, 3)
        ),
        asum(aterm(three_plus_eta, 1), aterm(q, 2), aterm(sigma, 3)),
    ]
    expected[3] = [
        azero(),
        aterm(q, 1),
        azero(),
        asum(
            abasis(0),
            aterm(radd(X, D), 1),
            aterm(radd(radd(Y, Z), sigma), 2),
            aterm(q, 3),
        ),
    ]
    assert matrix == expected

    # Applying the antipode to every coefficient gives the inverse matrix.
    inverse = [[map_apply(antipode, entry) for entry in row] for row in matrix]
    assert matrix_mul(matrix, inverse) == identity_matrix(4)
    assert matrix_mul(inverse, matrix) == identity_matrix(4)

    quotient = [row[1:] for row in matrix[1:]]
    quotient_inverse = [row[1:] for row in inverse[1:]]
    assert matrix_mul(quotient, quotient_inverse) == identity_matrix(3)
    assert matrix_mul(quotient_inverse, quotient) == identity_matrix(3)

    # Direct scheme-theoretic faithfulness: recover all coordinate generators
    # from U=X_13 and V=X_23 in the quotient matrix.
    u = quotient[0][2]
    v = quotient[1][2]
    assert rmul(q, X) == sigma
    assert rmul(three_plus_eta, three_plus_eta) == ONE
    recovered_e1 = ascale(
        three_plus_eta, aadd(v, aneg(ascale(q, u)))
    )
    assert recovered_e1 == abasis(1)
    t = ascale(X, recovered_e1)
    t2 = amul(t, t)
    t3 = amul(t2, t)
    assert amul(t3, t) == azero()
    geometric_inverse = asum(abasis(0), aneg(t), t2, aneg(t3))
    recovered_e2 = amul(geometric_inverse, u)
    recovered_e3 = amul(recovered_e1, recovered_e2)
    assert recovered_e2 == abasis(2)
    assert recovered_e3 == abasis(3)

    # The middle basis line R*bar(e2) is invariant.
    assert quotient[0][1] == quotient[2][1] == azero()


# An element of the linear dual A^vee is represented by its values on
# 1,e1,e2,e3, hence by four coefficients in R.
DualElement = tuple[R, R, R, R]
DualTensor = tuple[R, ...]


def dzero() -> DualElement:
    return (ZERO, ZERO, ZERO, ZERO)


def dbasis(i: int) -> DualElement:
    return tuple(ONE if i == j else ZERO for j in range(4))  # type: ignore


def dadd(a: DualElement, b: DualElement) -> DualElement:
    return tuple(radd(a[i], b[i]) for i in range(4))  # type: ignore


def dscale(c: R, a: DualElement) -> DualElement:
    return tuple(rmul(c, a[i]) for i in range(4))  # type: ignore


def dsum(*terms: DualElement) -> DualElement:
    out = dzero()
    for term in terms:
        out = dadd(out, term)
    return out


def dmul(a: DualElement, b: DualElement) -> DualElement:
    out = [ZERO for _ in range(4)]
    for target, i, j in product(range(4), repeat=3):
        out[target] = radd(
            out[target],
            rmul(rmul(a[i], b[j]), DELTA[target][4 * i + j]),
        )
    return tuple(out)  # type: ignore


def dtzero() -> DualTensor:
    return tuple(ZERO for _ in range(16))


def dtterm(c: R, i: int, j: int) -> DualTensor:
    out = list(dtzero())
    out[4 * i + j] = c
    return tuple(out)


def dtadd(a: DualTensor, b: DualTensor) -> DualTensor:
    return tuple(radd(a[i], b[i]) for i in range(16))


def dtsum(*terms: DualTensor) -> DualTensor:
    out = dtzero()
    for term in terms:
        out = dtadd(out, term)
    return out


def dual_coproduct(k: int) -> DualTensor:
    out = list(dtzero())
    for i, j in product(range(4), repeat=2):
        out[4 * i + j] = mul_basis(i, j)[k]
    return tuple(out)


def verify_dual_hopf_table() -> None:
    one, u, v, w = (dbasis(i) for i in range(4))
    q = radd(XSTAR, rmul(X, Y))
    eta = YSTAR
    sigma = SOCLE
    yz = radd(Y, Z)
    assert dmul(one, u) == dmul(u, one) == u
    expected_products = {
        (1, 1): dscale(X, u),
        (1, 2): w,
        (2, 1): dsum(
            dscale(yz, u),
            dscale(D, v),
            dscale(radd(rscale(3, ONE), eta), w),
        ),
        (1, 3): dscale(X, w),
        (3, 1): dsum(dscale(q, u), dscale(radd(X, D), w)),
        (2, 2): dsum(dscale(yz, v), dscale(q, w)),
        (2, 3): dsum(dscale(q, v), dscale(sigma, w)),
        (3, 2): dscale(radd(yz, sigma), w),
        (3, 3): dscale(q, w),
    }
    basis = (one, u, v, w)
    for (i, j), expected in expected_products.items():
        assert dmul(basis[i], basis[j]) == expected

    assert dual_coproduct(1) == dtsum(
        dtterm(ONE, 1, 0), dtterm(ONE, 0, 1), dtterm(X, 1, 1)
    )
    assert dual_coproduct(2) == dtsum(
        dtterm(ONE, 2, 0),
        dtterm(ONE, 0, 2),
        dtterm(Y, 1, 1),
        dtterm(Z, 2, 2),
    )
    assert dual_coproduct(3) == dtsum(
        dtterm(ONE, 3, 0),
        dtterm(ONE, 0, 3),
        dtterm(ONE, 1, 2),
        dtterm(ONE, 2, 1),
        dtterm(X, 1, 3),
        dtterm(X, 3, 1),
        dtterm(Z, 2, 3),
        dtterm(Z, 3, 2),
        dtterm(XSTAR, 3, 3),
    )


# B=R[t]/(t^2-Xt), represented on the basis 1,t.
BElement = tuple[R, R]
BTensor = tuple[R, R, R, R]


def badd(a: BElement, b: BElement) -> BElement:
    return (radd(a[0], b[0]), radd(a[1], b[1]))


def bmul(a: BElement, b: BElement) -> BElement:
    constant = rmul(a[0], b[0])
    linear = radd(rmul(a[0], b[1]), rmul(a[1], b[0]))
    linear = radd(linear, rmul(X, rmul(a[1], b[1])))
    return (constant, linear)


def pi(a: AElement) -> BElement:
    return (a[0], a[1])


def pi_tensor(value) -> BTensor:
    # Only tensor indices 0 and 1 survive; the output order is
    # 1x1,1xt,tx1,txt.
    return (
        value[0],
        value[1],
        value[4],
        value[5],
    )


def verify_rank_two_subgroup(antipode) -> None:
    for i, j in product(range(4), repeat=2):
        assert pi(mul_basis(i, j)) == bmul(pi(abasis(i)), pi(abasis(j)))

    delta_t = (ZERO, ONE, ONE, X)
    assert pi_tensor(DELTA[1]) == delta_t
    assert pi_tensor(DELTA[2]) == (ZERO, ZERO, ZERO, ZERO)
    assert pi_tensor(DELTA[3]) == (ZERO, ZERO, ZERO, ZERO)
    assert pi(map_apply(antipode, abasis(1))) == (ZERO, ONE)
    assert pi(map_apply(antipode, abasis(2))) == (ZERO, ZERO)
    assert pi(map_apply(antipode, abasis(3))) == (ZERO, ZERO)

    # Contract Delta(t): [2]^#(t)=(2+X^2)t=0 because X^2=2.
    doubled_coefficient = radd(rscale(2, ONE), rmul(X, X))
    assert doubled_coefficient == ZERO


def main() -> None:
    verify_base_ring()
    _, antipode = verify_hopf_algebra()
    verify_linear_representations(antipode)
    verify_dual_hopf_table()
    verify_rank_two_subgroup(antipode)
    print("GL4 PASS: displayed right-regular matrix and antipode inverse")
    print("GL3 PASS: quotient matrix invertible; e1,e2,e3 recovered exactly")
    print("FLAG PASS: R*bar(e2) is an invariant line in A/R")
    print("DUAL HOPF PASS: all displayed products and coproducts")
    print("SUBGROUP PASS: A -> R[t]/(t^2-Xt) is a Hopf quotient")
    print("SUBGROUP PASS: [2] on H_x is trivial because X^2=2")


if __name__ == "__main__":
    main()
