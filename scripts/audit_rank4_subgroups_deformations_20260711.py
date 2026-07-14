#!/usr/bin/env python3
"""Exact audit of rank-two subgroups and the deformation tower.

The calculation is bounded by a single pass through the 1,024-element base
ring.  It verifies the sixteen normalized rank-two Hopf quotients, the dual
adjoint formulas detecting normality, and the length 6 -> 8 -> 10 tower in
which normality and then the fourth-power relation break.
"""

from __future__ import annotations

from itertools import product

import audit_rank4_descriptions_20260710 as desc
import verify_rank4_length10_counterexample_20260710 as core


R = core.R


def rsum(*terms: R) -> R:
    out = core.ZERO
    for term in terms:
        out = core.radd(out, term)
    return out


def additive_span(generators: list[R]) -> set[R]:
    span = {core.ZERO}
    for generator in generators:
        span |= {core.radd(value, generator) for value in list(span)}
    return span


ELEMENTS = list(core.all_ring_elements())


def ideal(*generators: R) -> set[R]:
    products = [core.rmul(g, value) for g in generators for value in ELEMENTS]
    return additive_span(products)


def ideal_product(left: set[R], right: set[R]) -> set[R]:
    return additive_span([core.rmul(a, b) for a in left for b in right])


def mod_equal(a: R, b: R, modulus: set[R]) -> bool:
    return core.radd(a, core.rneg(b)) in modulus


def tensor_mod_symmetric(value, modulus: set[R]) -> bool:
    for i, j in product(range(4), repeat=2):
        if not mod_equal(value[4 * i + j], value[4 * j + i], modulus):
            return False
    return True


def candidate_valid(r: R, t: R, s: R, c: R) -> bool:
    """Check A -> R[f]/(f^2-tf), ei -> (1,r,s)f as a bialgebra map."""
    x, y, z, d = core.X, core.Y, core.Z, core.D
    xi = core.XSTAR
    eta = core.YSTAR
    q = rsum(core.XSTAR, core.DSTAR)
    sigma = core.SOCLE
    one = core.ONE
    two = core.rscale(2, one)

    def mul(*terms: R) -> R:
        out = one
        for term in terms:
            out = core.rmul(out, term)
        return out

    # Algebra relations.
    equations = [
        (t, rsum(x, core.rmul(y, r))),
        (s, core.rmul(r, t)),
        (core.rmul(s, t), core.rmul(x, s)),
        (mul(r, r, t), core.rmul(z, r)),
        (mul(r, s, t), core.rmul(z, s)),
        (mul(s, s, t), core.rmul(xi, s)),
    ]

    # Reduced coproduct coefficients after applying the quotient to both
    # tensor factors.  The two primitive legs agree automatically.
    equations.extend(
        [
            (c, rsum(x, core.rmul(rsum(y, z), r), core.rmul(q, s))),
            (
                core.rmul(r, c),
                rsum(
                    core.rmul(d, r),
                    mul(rsum(y, z), r, r),
                    mul(q, r, s),
                ),
            ),
            (
                core.rmul(s, c),
                rsum(
                    core.rmul(r, one),
                    core.rmul(r, one),
                    core.rmul(x, s),
                    mul(radd_two_eta := rsum(two, eta), r, one),
                    mul(q, r, r),
                    mul(sigma, r, s),
                    mul(rsum(x, d), s, one),
                    mul(rsum(y, z, sigma), s, r),
                    mul(q, s, s),
                ),
            ),
        ]
    )
    # Keep the named coefficient visibly checked; this also prevents an
    # accidental simplification of the (2+eta)e2 tensor e1 term.
    assert radd_two_eta == rsum(two, eta)
    # A rank-two Hopf algebra in this chart satisfies ct=-2; equivalently,
    # its doubling is zero.  We do not assume c=t here: the enumeration below
    # discovers that extra self-duality in all solutions.
    equations.append((rsum(two, core.rmul(c, t)), core.ZERO))
    return all(left == right for left, right in equations)


def adjoint_certificate(
    r: R, s: R, antipode
) -> tuple[R, ...]:
    """Compute (q_r tensor id)Ad^*(e3-s e1) in B_t tensor A."""
    k3 = core.aadd(core.abasis(3), core.ascale(core.rneg(s), core.abasis(1)))
    triple = core.t3_left(core.delta_apply(k3))
    out = [core.ZERO for _ in range(8)]
    quotient_basis = (
        (core.ONE, core.ZERO),
        (core.ZERO, core.ONE),
        (core.ZERO, r),
        (core.ZERO, s),
    )
    for i, j, k in product(range(4), repeat=3):
        coefficient = triple[16 * i + 4 * j + k]
        if coefficient == core.ZERO:
            continue
        right = core.amul(core.abasis(i), antipode[k])
        for b_index in range(2):
            b_coefficient = quotient_basis[j][b_index]
            for a_index in range(4):
                out[4 * b_index + a_index] = core.radd(
                    out[4 * b_index + a_index],
                    core.rmul(
                        coefficient,
                        core.rmul(b_coefficient, right[a_index]),
                    ),
                )
    return tuple(out)


def verify_sixteen_subgroups(antipode) -> None:
    x, y, z, d = core.X, core.Y, core.Z, core.D
    xi, eta, omega, sigma = (
        core.XSTAR,
        core.YSTAR,
        core.DSTAR,
        core.SOCLE,
    )
    q = rsum(xi, omega)
    expected: set[tuple[R, R, R, R]] = set()
    for eps, alpha, beta, gamma in product(range(2), repeat=4):
        r = rsum(
            d if eps else core.ZERO,
            eta if alpha else core.ZERO,
            q if beta else core.ZERO,
            sigma if gamma else core.ZERO,
        )
        t = rsum(
            x,
            q if eps else core.ZERO,
            sigma if alpha else core.ZERO,
        )
        s = rsum(
            eta if eps else core.ZERO,
            sigma if (eps ^ beta) else core.ZERO,
        )
        assert candidate_valid(r, t, s, t)
        expected.add((r, t, s, t))

        certificate = adjoint_certificate(r, s, antipode)
        expected_certificate = [core.ZERO for _ in range(8)]
        expected_certificate[4 + 2] = rsum(
            eta, sigma if eps else core.ZERO
        )
        assert certificate == tuple(expected_certificate)
        assert certificate != tuple(core.ZERO for _ in range(8))

        unit = rsum(
            core.ONE,
            rsum(y, z) if eps else core.ZERO,
            xi if alpha else core.ZERO,
        )
        assert t == core.rmul(unit, x)
        assert core.rmul(core.rmul(unit, unit), x) == x

    assert len(expected) == 16

    # Exhaust all normalized maps e1 -> f.  The equations derive t,s,c from
    # r, so this is only a 1,024-case pass.
    found: set[tuple[R, R, R, R]] = set()
    for r in ELEMENTS:
        t = rsum(x, core.rmul(y, r))
        s = core.rmul(r, t)
        c = rsum(x, core.rmul(rsum(y, z), r), core.rmul(q, s))
        if candidate_valid(r, t, s, c):
            found.add((r, t, s, c))
    assert found == expected

    # There is no second branch with e2, but not e1, a generator.  After
    # normalizing e2 -> f, e2^2 forces t=z; e1 -> a f with a nonunit would
    # have to satisfy a^2 z=xa+y.
    maximal = ideal(x, y, z, d)
    impossible_branch = [
        a
        for a in maximal
        if core.rmul(core.rmul(a, a), z)
        == rsum(core.rmul(x, a), y)
    ]
    assert impossible_branch == []


def dual_antipode(f: desc.DualElement, antipode) -> desc.DualElement:
    values: list[R] = []
    for basis_index in range(4):
        image = antipode[basis_index]
        value = core.ZERO
        for i in range(4):
            value = core.radd(value, core.rmul(f[i], image[i]))
        values.append(value)
    return tuple(values)  # type: ignore[return-value]


def dual_adjoint(
    h: desc.DualElement, k: desc.DualElement, antipode
) -> desc.DualElement:
    delta_h = [core.ZERO for _ in range(16)]
    for target in range(4):
        for index, coefficient in enumerate(desc.dual_coproduct(target)):
            delta_h[index] = core.radd(
                delta_h[index], core.rmul(h[target], coefficient)
            )
    out = desc.dzero()
    for i, j in product(range(4), repeat=2):
        coefficient = delta_h[4 * i + j]
        if coefficient == core.ZERO:
            continue
        term = desc.dmul(desc.dbasis(i), k)
        term = desc.dmul(term, dual_antipode(desc.dbasis(j), antipode))
        out = desc.dadd(out, desc.dscale(coefficient, term))
    return out


def verify_normality_and_deformation_tower(antipode) -> None:
    one, u, v, w = (desc.dbasis(i) for i in range(4))
    del one
    eta = core.YSTAR
    q = rsum(core.XSTAR, core.DSTAR)
    assert dual_adjoint(u, u, antipode) == desc.dzero()
    assert dual_adjoint(v, u, antipode) == desc.dsum(
        desc.dscale(rsum(core.Y, core.Z), u),
        desc.dscale(core.D, v),
        desc.dscale(eta, w),
    )
    assert dual_adjoint(w, u, antipode) == desc.dsum(
        desc.dscale(q, u), desc.dscale(eta, v)
    )

    i_d = ideal(core.D)
    i_d2 = ideal_product(i_d, i_d)
    i_d3 = ideal_product(i_d2, i_d)
    assert len(i_d) == 2**4
    assert len(i_d2) == 2**2
    assert i_d3 == {core.ZERO}
    assert i_d == ideal(core.D, eta, q, core.SOCLE)
    assert i_d2 == ideal(eta, core.SOCLE)
    assert 10 - 4 == 6 and 10 - 2 == 8

    # Both successive kernels in R_10 -> R_8 -> R_6 are square-zero.
    assert all(core.rmul(a, b) in i_d2 for a in i_d for b in i_d)
    assert all(core.rmul(a, b) == core.ZERO for a in i_d2 for b in i_d2)

    # Modulo d, R{1,e2} is a Hopf subalgebra and gives the quotient rank-two
    # group with parameters (z,y+z).  Its doubling is zero.
    assert core.D in i_d and eta in i_d and q in i_d and core.SOCLE in i_d
    allowed = {(0, 0), (0, 2), (2, 0), (2, 2)}
    for index, coefficient in enumerate(core.DELTA[2]):
        pair = divmod(index, 4)
        if pair not in allowed:
            assert coefficient in i_d
    assert mod_equal(core.DELTA[2][4 * 2 + 2], rsum(core.Y, core.Z), i_d)
    assert mod_equal(antipode[2][2], core.ONE, i_d)
    assert mod_equal(antipode[2][3], core.ZERO, i_d)
    assert rsum(
        core.rscale(2, core.ONE), core.rmul(core.Z, rsum(core.Y, core.Z))
    ) == core.ZERO

    # The length-eight lift keeps d nonzero, so the dual adjoint exits
    # R{1,u}; nevertheless sigma is zero there and [4] still vanishes.
    assert core.D not in i_d2
    assert core.SOCLE in i_d2

    # The final length-ten lift restores the socle class sigma=dq=omega*d,
    # which is exactly the fourth-power coefficient.
    assert core.rmul(core.D, q) == core.SOCLE
    assert core.rmul(core.DSTAR, core.D) == core.SOCLE
    assert core.SOCLE != core.ZERO

    # m-adic version: N is already an injective first-order skew symbol, but
    # the fourth-power class only appears in m^3=(sigma).
    maximal = ideal(core.X, core.Y, core.Z, core.D)
    maximal2 = ideal_product(maximal, maximal)
    maximal3 = ideal_product(maximal2, maximal)
    maximal4 = ideal_product(maximal3, maximal)
    assert (len(maximal), len(maximal2), len(maximal3), len(maximal4)) == (
        2**9,
        2**5,
        2,
        1,
    )
    first_skew_coefficients = [rsum(core.Y, core.Z), core.D]
    assert all(value not in maximal2 for value in first_skew_coefficients)
    assert rsum(first_skew_coefficients[0], first_skew_coefficients[1]) not in maximal2
    assert maximal3 == {core.ZERO, core.SOCLE}

    # Killing exactly the two first skew directions makes the whole
    # coproduct cocommutative.  This quotient has length four.
    commutative_modulus = ideal(core.D, rsum(core.Y, core.Z))
    assert len(commutative_modulus) == 2**6
    assert all(
        tensor_mod_symmetric(core.DELTA[i], commutative_modulus)
        for i in range(4)
    )


def main() -> None:
    core.verify_base_ring()
    _, antipode = core.verify_hopf_algebra()
    verify_sixteen_subgroups(antipode)
    verify_normality_and_deformation_tower(antipode)
    print("SUBGROUP CLASSIFICATION PASS: exactly 16 normalized Hopf quotients")
    print("SUBGROUP ISOMORPHISM PASS: all are Oort-Tate (x,x) forms")
    print("ADJOINT PASS: H_x normal exactly after killing d")
    print("DEFORMATION PASS: lengths 6 -> 8 -> 10 with square-zero steps")
    print("DEFORMATION PASS: normality breaks at length 8; [4] at length 10")
    print("M-ADIC PASS: first skew in degree 1; [4] in socle degree 3")
    print("COMMUTATIVE QUOTIENT PASS: kill d and y+z (length 4)")


if __name__ == "__main__":
    main()
