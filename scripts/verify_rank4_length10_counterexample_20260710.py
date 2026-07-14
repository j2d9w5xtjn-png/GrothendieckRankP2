#!/usr/bin/env python3
"""Exact, dependency-free verification of the length-10 rank-4 example.

The word "length" means composition length over the residue field F_2;
the base ring consequently has 2^10 elements.  This program constructs the
base ring and Hopf algebra directly from the formulas in the accompanying
note.  It does not import the universal-deformation checker or trust a
Groebner-basis output.

All calculations use small tuples of Python integers.  The largest exhaustive
loop visits the 1,024 elements of the base once and uses well under 100 MiB.
"""

from __future__ import annotations

from itertools import product


# ---------------------------------------------------------------------------
# The base ring
# ---------------------------------------------------------------------------

# V has ordered basis X,Y,Z,D.  The independent part of V^* has basis
# X*,Y*,D*; the missing Z* is identified with the scalar 2.
V_NAMES = ("X", "Y", "Z", "D")
H_INDICES = (0, 1, 3)
H_NAMES = ("X*", "Y*", "D*")
Z_INDEX = 2
H_POSITION = {index: position for position, index in enumerate(H_INDICES)}

# F is the symmetric trilinear form whose displayed square-free/repeated
# monomials have coefficient one.
F_SUPPORT = {
    tuple(sorted(t))
    for t in (
        (0, 0, 2),  # X^[2] Z
        (0, 1, 3),  # X Y D
        (1, 3, 3),  # Y D^[2]
        (2, 2, 2),  # Z^[3]
    )
}

# A canonical element is (constant mod 4, V-bitmask, H-bitmask, socle bit).
# The Z-bit has additive order four: adding Z to Z creates the socle s=2Z.
# All other displayed nilpotent coordinates have order two.
R = tuple[int, int, int, int]
ZERO: R = (0, 0, 0, 0)
ONE: R = (1, 0, 0, 0)
SOCLE: R = (0, 0, 0, 1)


def radd(x: R, y: R) -> R:
    c1, v1, h1, s1 = x
    c2, v2, h2, s2 = y
    z_carry = ((v1 >> Z_INDEX) & 1) & ((v2 >> Z_INDEX) & 1)
    return ((c1 + c2) % 4, v1 ^ v2, h1 ^ h2, s1 ^ s2 ^ z_carry)


def rscale(n: int, x: R) -> R:
    out = ZERO
    for _ in range(n % 4):
        out = radd(out, x)
    return out


def rneg(x: R) -> R:
    return rscale(3, x)


def bform(v1: int, v2: int) -> int:
    """Return B_F(v1,v2) as a four-bit vector in V^*."""
    out = 0
    for i in range(4):
        if not ((v1 >> i) & 1):
            continue
        for j in range(4):
            if not ((v2 >> j) & 1):
                continue
            for k in range(4):
                if tuple(sorted((i, j, k))) in F_SUPPORT:
                    out ^= 1 << k
    return out


def h_full(h: int) -> int:
    out = 0
    for position, index in enumerate(H_INDICES):
        if (h >> position) & 1:
            out ^= 1 << index
    return out


def nilpotent_times_constant(v: int, h: int, s: int, c: int) -> R:
    c %= 4
    vv = v if c & 1 else 0
    hh = h if c & 1 else 0
    ss = s if c & 1 else 0
    # 2Z=s; all other V-lifts and all of H have order two.
    if c in (2, 3) and ((v >> Z_INDEX) & 1):
        ss ^= 1
    return (0, vv, hh, ss)


def rmul(x: R, y: R) -> R:
    c1, v1, h1, s1 = x
    c2, v2, h2, s2 = y
    out: R = ((c1 * c2) % 4, 0, 0, 0)
    out = radd(out, nilpotent_times_constant(v2, h2, s2, c1))
    out = radd(out, nilpotent_times_constant(v1, h1, s1, c2))

    dual = bform(v1, v2)
    if (dual >> Z_INDEX) & 1:
        out = radd(out, (2, 0, 0, 0))  # Z*=2
    h = 0
    for index in H_INDICES:
        if (dual >> index) & 1:
            h ^= 1 << H_POSITION[index]
    out = radd(out, (0, 0, h, 0))

    pairing = ((v1 & h_full(h2)).bit_count() ^
               (v2 & h_full(h1)).bit_count()) & 1
    if pairing:
        out = radd(out, SOCLE)
    return out


def v_element(index: int) -> R:
    return (0, 1 << index, 0, 0)


def h_element(index: int) -> R:
    if index == Z_INDEX:
        return (2, 0, 0, 0)
    return (0, 0, 1 << H_POSITION[index], 0)


X, Y, Z, D = (v_element(i) for i in range(4))
XSTAR, YSTAR, DSTAR = (
    h_element(i) for i in H_INDICES
)


def rank_f2(rows: list[int]) -> int:
    pivots: dict[int, int] = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    return len(pivots)


def all_ring_elements():
    for c, v, h, s in product(range(4), range(16), range(8), range(2)):
        yield (c, v, h, s)


def verify_base_ring() -> None:
    additive_generators = [ONE] + [v_element(i) for i in range(4)] + [
        h_element(i) for i in H_INDICES
    ]
    assert len(additive_generators) == 8
    for x, y, z in product(additive_generators, repeat=3):
        assert rmul(rmul(x, y), z) == rmul(x, rmul(y, z))
    for x, y in product(additive_generators, repeat=2):
        assert rmul(x, y) == rmul(y, x)
        assert rmul(ONE, x) == x

    # The four first catalecticant rows are independent.  Equivalently,
    # multiplication Sym^2(V)->V^* is onto and F has Cat_1 rank four.
    cat_rows = []
    for i in range(4):
        row = 0
        for j in range(4):
            dual = bform(1 << i, 1 << j)
            row |= dual << (4 * j)
        cat_rows.append(row)
    assert rank_f2(cat_rows) == 4
    assert rank_f2(
        [bform(1 << i, 1 << j) for i in range(4) for j in range(i, 4)]
    ) == 4

    two = radd(ONE, ONE)
    assert two != ZERO and radd(two, two) == ZERO
    assert rmul(X, X) == two                    # Z*=2
    assert rmul(Z, Z) == two
    assert rscale(2, Z) == SOCLE               # s=2Z
    assert rmul(two, Z) == SOCLE
    # Compact quotient presentation:
    # R=(Z/4)[X,Y,Z,D]/(2X,2Y,2D,X^2-2,Z^2-2,Y^2,YZ,ZD,
    #                         D^2-XD,YD-XZ-XY).
    assert rscale(2, X) == rscale(2, Y) == rscale(2, D) == ZERO
    assert rmul(Y, Y) == rmul(Y, Z) == rmul(Z, D) == ZERO
    assert rmul(D, D) == rmul(X, D)
    assert rmul(Y, D) == radd(rmul(X, Z), rmul(X, Y))
    assert rmul(SOCLE, v_element(0)) == ZERO

    # The formulas give m=(2,V,V^*,s), m^2=(V^*,s), m^3=(s), m^4=0.
    m2 = {
        (c, 0, h, s)
        for c in (0, 2)
        for h in range(8)
        for s in range(2)
    }
    assert len(m2) == 2**5
    for x, y in product([two] + [v_element(i) for i in range(4)], repeat=2):
        assert rmul(x, y) in m2
    for x in m2:
        for y in [two] + [v_element(i) for i in range(4)]:
            assert rmul(x, y) in (ZERO, SOCLE)
    for y in [two] + [v_element(i) for i in range(4)]:
        assert rmul(SOCLE, y) == ZERO

    # Exhaustively certify the order and the one-dimensional socle.  It is
    # enough to test the four V-generators because they generate m as ideal.
    elements = list(all_ring_elements())
    assert len(elements) == 2**10 and len(set(elements)) == 2**10
    # Implementation gate for translations against pairs of additive
    # generators; full distributivity follows from the biadditive formula.
    for x in elements:
        for y, z in product(additive_generators, repeat=2):
            assert rmul(radd(x, y), z) == radd(rmul(x, z), rmul(y, z))
    socle = [
        x for x in elements
        if all(rmul(x, v_element(i)) == ZERO for i in range(4))
    ]
    assert socle == [ZERO, SOCLE]


# ---------------------------------------------------------------------------
# The free rank-four algebra and its coproduct
# ---------------------------------------------------------------------------

AElement = tuple[R, R, R, R]
Tensor2 = tuple[R, ...]  # 16 entries, index 4*i+j
Tensor3 = tuple[R, ...]  # 64 entries, index 16*i+4*j+k


def azero() -> AElement:
    return (ZERO, ZERO, ZERO, ZERO)


def abasis(i: int) -> AElement:
    return tuple(ONE if j == i else ZERO for j in range(4))  # type: ignore


def aadd(x: AElement, y: AElement) -> AElement:
    return tuple(radd(x[i], y[i]) for i in range(4))  # type: ignore


def ascale(c: R, x: AElement) -> AElement:
    return tuple(rmul(c, x[i]) for i in range(4))  # type: ignore


def mul_basis(i: int, j: int) -> AElement:
    if i == 0:
        return abasis(j)
    if j == 0:
        return abasis(i)
    i, j = sorted((i, j))
    out = azero()

    def add_term(coefficient: R, basis_index: int) -> None:
        nonlocal out
        term = list(azero())
        term[basis_index] = coefficient
        out = aadd(out, tuple(term))  # type: ignore

    if (i, j) == (1, 1):
        add_term(X, 1)
        add_term(Y, 2)
    elif (i, j) == (1, 2):
        add_term(ONE, 3)
    elif (i, j) == (1, 3):
        add_term(X, 3)
    elif (i, j) == (2, 2):
        add_term(Z, 2)
    elif (i, j) == (2, 3):
        add_term(Z, 3)
    elif (i, j) == (3, 3):
        add_term(XSTAR, 3)
    else:
        raise AssertionError((i, j))
    return out


def amul(x: AElement, y: AElement) -> AElement:
    out = azero()
    for i, j in product(range(4), repeat=2):
        if x[i] != ZERO and y[j] != ZERO:
            out = aadd(out, ascale(rmul(x[i], y[j]), mul_basis(i, j)))
    return out


def t2zero() -> Tensor2:
    return tuple(ZERO for _ in range(16))


def t2add(x: Tensor2, y: Tensor2) -> Tensor2:
    return tuple(radd(x[i], y[i]) for i in range(16))


def t2term(c: R, i: int, j: int) -> Tensor2:
    out = list(t2zero())
    out[4 * i + j] = c
    return tuple(out)


def t2mul(x: Tensor2, y: Tensor2) -> Tensor2:
    out = list(t2zero())
    for i, j, k, ell in product(range(4), repeat=4):
        c = rmul(x[4 * i + j], y[4 * k + ell])
        if c == ZERO:
            continue
        left = mul_basis(i, k)
        right = mul_basis(j, ell)
        for r, s in product(range(4), repeat=2):
            out[4 * r + s] = radd(
                out[4 * r + s], rmul(c, rmul(left[r], right[s]))
            )
    return tuple(out)


def make_delta() -> tuple[Tensor2, Tensor2, Tensor2, Tensor2]:
    delta = [t2term(ONE, 0, 0)]
    for i in range(1, 4):
        value = t2add(t2term(ONE, i, 0), t2term(ONE, 0, i))
        if i == 3:
            value = t2add(value, t2term(ONE, 1, 2))
            value = t2add(value, t2term(ONE, 2, 1))
        delta.append(value)

    def put(i: int, j: int, k: int, c: R) -> None:
        delta[i] = t2add(delta[i], t2term(c, j, k))

    put(1, 1, 1, X)
    put(1, 2, 1, radd(Y, Z))
    put(1, 3, 1, radd(XSTAR, DSTAR))

    put(2, 2, 1, D)
    put(2, 2, 2, radd(Y, Z))
    put(2, 2, 3, radd(XSTAR, DSTAR))

    put(3, 1, 3, X)
    put(3, 2, 1, radd((2, 0, 0, 0), YSTAR))
    put(3, 2, 2, radd(XSTAR, DSTAR))
    put(3, 2, 3, SOCLE)
    put(3, 3, 1, radd(X, D))
    put(3, 3, 2, radd(radd(Y, Z), SOCLE))
    put(3, 3, 3, radd(XSTAR, DSTAR))
    return tuple(delta)  # type: ignore


DELTA = make_delta()


def delta_apply(x: AElement) -> Tensor2:
    out = t2zero()
    for i in range(4):
        if x[i] == ZERO:
            continue
        out = t2add(out, tuple(rmul(x[i], c) for c in DELTA[i]))
    return out


def t3_left(value: Tensor2) -> Tensor3:
    """Apply Delta to the first tensor factor."""
    out = [ZERO for _ in range(64)]
    for i, j in product(range(4), repeat=2):
        c = value[4 * i + j]
        for a, b in product(range(4), repeat=2):
            out[16 * a + 4 * b + j] = radd(
                out[16 * a + 4 * b + j], rmul(c, DELTA[i][4 * a + b])
            )
    return tuple(out)


def t3_right(value: Tensor2) -> Tensor3:
    """Apply Delta to the second tensor factor."""
    out = [ZERO for _ in range(64)]
    for i, j in product(range(4), repeat=2):
        c = value[4 * i + j]
        for b, k in product(range(4), repeat=2):
            out[16 * i + 4 * b + k] = radd(
                out[16 * i + 4 * b + k], rmul(c, DELTA[j][4 * b + k])
            )
    return tuple(out)


def tensor_contract(value: Tensor2) -> AElement:
    out = azero()
    for i, j in product(range(4), repeat=2):
        out = aadd(out, ascale(value[4 * i + j], mul_basis(i, j)))
    return out


# An R-linear map A->A is stored by its values on 1,e1,e2,e3.
LinearMap = tuple[AElement, AElement, AElement, AElement]


def map_apply(f: LinearMap, x: AElement) -> AElement:
    out = azero()
    for i in range(4):
        out = aadd(out, ascale(x[i], f[i]))
    return out


def map_add(f: LinearMap, g: LinearMap) -> LinearMap:
    return tuple(aadd(f[i], g[i]) for i in range(4))  # type: ignore


def map_neg(f: LinearMap) -> LinearMap:
    return tuple(tuple(rneg(c) for c in f[i]) for i in range(4))  # type: ignore


def map_scale(n: int, f: LinearMap) -> LinearMap:
    return tuple(
        tuple(rscale(n, c) for c in f[i]) for i in range(4)
    )  # type: ignore


def compose(f: LinearMap, g: LinearMap) -> LinearMap:
    """Return f after g."""
    return tuple(map_apply(f, g[i]) for i in range(4))  # type: ignore


def convolution(f: LinearMap, g: LinearMap) -> LinearMap:
    values = []
    for i in range(4):
        out = azero()
        for j, k in product(range(4), repeat=2):
            c = DELTA[i][4 * j + k]
            out = aadd(out, ascale(c, amul(f[j], g[k])))
        values.append(out)
    return tuple(values)  # type: ignore


IDENTITY: LinearMap = tuple(abasis(i) for i in range(4))  # type: ignore
PROJECTION: LinearMap = (abasis(0), azero(), azero(), azero())


def verify_hopf_algebra() -> tuple[LinearMap, LinearMap]:
    # The algebra is commutative and associative.
    for i, j, k in product(range(4), repeat=3):
        assert mul_basis(i, j) == mul_basis(j, i)
        assert amul(mul_basis(i, j), abasis(k)) == amul(
            abasis(i), mul_basis(j, k)
        )

    # Counitality, multiplicativity, and coassociativity of Delta.
    for i in range(4):
        left_counit = tuple(DELTA[i][j] for j in range(4))
        right_counit = tuple(DELTA[i][4 * j] for j in range(4))
        assert left_counit == abasis(i)
        assert right_counit == abasis(i)
        assert t3_left(DELTA[i]) == t3_right(DELTA[i])
    for i, j in product(range(4), repeat=2):
        assert delta_apply(mul_basis(i, j)) == t2mul(DELTA[i], DELTA[j])

    # Construct the antipode, rather than merely invoking the lifting lemma.
    phi = convolution(IDENTITY, IDENTITY)
    n = map_add(phi, map_neg(PROJECTION))
    n2 = convolution(n, n)
    n3 = convolution(n2, n)
    n4 = convolution(n3, n)
    assert n4 == map_scale(0, IDENTITY)
    inverse_phi = map_add(
        map_add(PROJECTION, map_neg(n)), map_add(n2, map_neg(n3))
    )
    assert convolution(phi, inverse_phi) == PROJECTION
    assert convolution(inverse_phi, phi) == PROJECTION
    antipode = convolution(IDENTITY, inverse_phi)
    assert convolution(IDENTITY, antipode) == PROJECTION
    assert convolution(antipode, IDENTITY) == PROJECTION
    return phi, antipode


def format_ring(x: R) -> str:
    c, v, h, s = x
    terms: list[str] = []
    if c:
        terms.append(str(c))
    terms.extend(V_NAMES[i] for i in range(4) if (v >> i) & 1)
    terms.extend(H_NAMES[i] for i in range(3) if (h >> i) & 1)
    if s:
        terms.append("s")
    return "0" if not terms else "+".join(terms)


def format_a(x: AElement) -> str:
    terms = []
    for i, c in enumerate(x):
        if c != ZERO:
            terms.append(f"({format_ring(c)})e{i}")
    return "0" if not terms else " + ".join(terms)


def main() -> None:
    verify_base_ring()
    phi, antipode = verify_hopf_algebra()

    psi = map_add(phi, map_neg(PROJECTION))
    fourth = compose(phi, phi)
    eighth = compose(phi, fourth)
    assert map_add(fourth, map_neg(PROJECTION)) == map_scale(2, psi)
    assert compose(psi, psi) == map_scale(2, psi)
    assert fourth[1] == (ZERO, ZERO, ZERO, SOCLE)
    assert fourth[2] == azero() and fourth[3] == azero()
    assert eighth == PROJECTION

    # The coefficient of e2 tensor e1 in Delta(e1) is Y+Z, while that of
    # e1 tensor e2 is zero, so the group is genuinely noncommutative.
    assert DELTA[1][4 * 2 + 1] == radd(Y, Z)
    assert DELTA[1][4 * 1 + 2] == ZERO
    assert radd(Y, Z) != ZERO

    print("BASE PASS: local characteristic 4; |R|=2^10; length 10")
    print("BASE PASS: Hilbert function (1,4,4,1); socle={0,s}; s=2Z!=0")
    print("BASE PASS: generator-level distributivity gates for the biadditive law")
    print("HOPF PASS: algebra, counit, multiplicativity, coassociativity")
    print("HOPF PASS: explicit two-sided convolution antipode constructed")
    print("POWER IDENTITY PASS: psi^2=2psi for psi=[2]^#-unit*epsilon")
    print("[4]^#(e1)=", format_a(fourth[1]), sep="")
    print("[4]^#(e2)=", format_a(fourth[2]), sep="")
    print("[4]^#(e3)=", format_a(fourth[3]), sep="")
    print("[8]^#=unit*epsilon PASS")
    print("NONCOMMUTATIVE PASS: Delta(e1) is not cocommutative")
    print("antipode values")
    for i in range(1, 4):
        print(f"  S(e{i})={format_a(antipode[i])}")


if __name__ == "__main__":
    main()
