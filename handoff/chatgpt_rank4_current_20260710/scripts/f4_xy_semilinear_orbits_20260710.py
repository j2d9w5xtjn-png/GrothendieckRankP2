#!/usr/bin/env python3
"""Exact F_4 rational-form audit for killed-by-two ``xy`` fibers.

Let H = F_4[x,y]/(x^2,y^2).  By the height-one correspondence, a
commutative group structure on Spec(H) killed by two is dual to an abelian
restricted Lie algebra on a two-dimensional F_4-vector space.  Its
2-operation is Frobenius-semilinear and, after choosing a basis, has the form

    xi(v) = A v^(2),             A in M_2(F_4).

If the new basis is related to the old one by v_old = P v_new, then

    A_new = P^(-1) A P^(2).

This dependency-free script exhausts all 4^4 matrices and all 180 elements
of GL_2(F_4).  It deliberately uses several redundant gates:

* exhaustive finite-field and matrix-group checks;
* the twisted-action identity on a matrix basis;
* a direct orbit partition and an independently recomputed canonical-owner
  partition;
* orbit-stabilizer and Burnside counts;
* direct closure of every reported orbit;
* bialgebra, counit, coassociativity, cocommutativity, and [2]=0 checks for
  all 256 matrices;
* literal comparison with the six older F_2-defined solver pins.

The JSON output includes a sparse coproduct pin for every orbit
representative.  Field elements use the encoding

    0 -> 0, 1 -> 1, 2 -> w, 3 -> w+1,   where w^2+w+1 = 0.

No SMT solver or computer-algebra system is used.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from functools import lru_cache
import json
import resource
import sys
import time


# F_4 = F_2[w]/(w^2+w+1), polynomial-basis bit encoding 1,w.
FIELD_LABELS = ("0", "1", "w", "w+1")


def fadd(a: int, b: int) -> int:
    return a ^ b


def fmul(a: int, b: int) -> int:
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 0b100:
            a ^= 0b111               # w^2 = w+1
    return out & 0b11


def fpow(a: int, n: int) -> int:
    out = 1
    while n:
        if n & 1:
            out = fmul(out, a)
        a = fmul(a, a)
        n >>= 1
    return out


def finv(a: int) -> int:
    assert a
    return fpow(a, 2)


def ffrob(a: int) -> int:
    return fmul(a, a)


# Matrices are row-major tuples (a,b,c,d) = [[a,b],[c,d]].
def madd(A, B):
    return tuple(fadd(a, b) for a, b in zip(A, B))


def mscale(q, A):
    return tuple(fmul(q, a) for a in A)


def mmul(A, B):
    a, b, c, d = A
    e, f, g, h = B
    return (
        fadd(fmul(a, e), fmul(b, g)),
        fadd(fmul(a, f), fmul(b, h)),
        fadd(fmul(c, e), fmul(d, g)),
        fadd(fmul(c, f), fmul(d, h)),
    )


def mfrob(A):
    return tuple(ffrob(x) for x in A)


def mdet(A):
    a, b, c, d = A
    return fadd(fmul(a, d), fmul(b, c))


def minv(A):
    a, b, c, d = A
    q = finv(mdet(A))
    # Minus equals plus in characteristic two.
    return tuple(fmul(q, x) for x in (d, b, c, a))


ALL_MATRICES = tuple(
    (a, b, c, d)
    for a in range(4) for b in range(4) for c in range(4) for d in range(4)
)
GL2 = tuple(A for A in ALL_MATRICES if mdet(A))
IDENTITY = (1, 0, 0, 1)
MATRIX_BASIS = (
    (1, 0, 0, 0),
    (0, 1, 0, 0),
    (0, 0, 1, 0),
    (0, 0, 0, 1),
)


def twisted_conjugate(A, P):
    """P acts by A |-> P^(-1) A P^(2)."""
    return mmul(mmul(minv(P), A), mfrob(P))


def field_and_action_gates():
    # Exhaustive field laws (only 4^3 triples).
    for a in range(4):
        assert fmul(a, 0) == 0 and fmul(a, 1) == a
        assert fpow(a, 4) == a
        assert ffrob(ffrob(a)) == a
        if a:
            assert fmul(a, finv(a)) == 1
        for b in range(4):
            assert fmul(a, b) == fmul(b, a)
            assert ffrob(fadd(a, b)) == fadd(ffrob(a), ffrob(b))
            assert ffrob(fmul(a, b)) == fmul(ffrob(a), ffrob(b))
            for c in range(4):
                assert fmul(a, fadd(b, c)) == fadd(fmul(a, b), fmul(a, c))
                assert fmul(fmul(a, b), c) == fmul(a, fmul(b, c))

    assert len(GL2) == (4**2 - 1) * (4**2 - 4) == 180
    for P in GL2:
        assert mmul(P, minv(P)) == IDENTITY
        assert mmul(minv(P), P) == IDENTITY
        assert mfrob(mfrob(P)) == P

    # The formula is a right action in the convention used here:
    # T_Q(T_P(A)) = T_{P Q}(A).  Matrix-entry linearity means checking a
    # basis checks it for all A; arithmetic linearity was checked above.
    for P in GL2:
        for E in MATRIX_BASIS:
            assert twisted_conjugate(E, IDENTITY) == E
        for Q in GL2:
            PQ = mmul(P, Q)
            assert PQ in GL2
            for E in MATRIX_BASIS:
                assert twisted_conjugate(twisted_conjugate(E, P), Q) == \
                    twisted_conjugate(E, PQ)


def enumerate_orbits():
    """Direct orbit enumeration plus independent partition certificates."""
    unseen = set(ALL_MATRICES)
    orbits = []
    while unseen:
        seed = min(unseen)
        orbit = frozenset(twisted_conjugate(seed, P) for P in GL2)
        assert seed in orbit
        assert orbit <= unseen, "twisted orbit overlaps an earlier orbit"
        unseen.difference_update(orbit)
        orbits.append(tuple(sorted(orbit)))
    orbits.sort(key=lambda orbit: orbit[0])
    orbits = tuple(orbits)

    # Direct disjoint-union gate.
    assert sum(map(len, orbits)) == len(ALL_MATRICES)
    union = set()
    for orbit in orbits:
        assert union.isdisjoint(orbit)
        union.update(orbit)
    assert union == set(ALL_MATRICES)

    # Independent canonical-owner partition: do not reuse ``unseen`` or its
    # owners.  Every matrix is assigned the minimum of its 180 transforms.
    canonical_groups = defaultdict(set)
    for A in ALL_MATRICES:
        canonical_groups[min(twisted_conjugate(A, P) for P in GL2)].add(A)
    independent = tuple(
        tuple(sorted(group))
        for _, group in sorted(canonical_groups.items())
    )
    assert independent == orbits

    # Closure and orbit-stabilizer, separately for each representative.
    stabilizers = []
    for orbit in orbits:
        rep = orbit[0]
        direct = {twisted_conjugate(rep, P) for P in GL2}
        assert direct == set(orbit)
        for A in orbit:
            assert {twisted_conjugate(A, P) for P in GL2} == direct
        stabilizer = tuple(P for P in GL2 if twisted_conjugate(rep, P) == rep)
        assert len(orbit) * len(stabilizer) == len(GL2)
        stabilizer_set = set(stabilizer)
        assert IDENTITY in stabilizer_set
        assert all(minv(P) in stabilizer_set for P in stabilizer)
        assert all(mmul(P, Q) in stabilizer_set
                   for P in stabilizer for Q in stabilizer)
        stabilizers.append(len(stabilizer))

    # Burnside is a third count of the number of orbits.
    fixed_counts = tuple(
        sum(twisted_conjugate(A, P) == A for A in ALL_MATRICES)
        for P in GL2
    )
    assert sum(fixed_counts) % len(GL2) == 0
    assert sum(fixed_counts) // len(GL2) == len(orbits)
    return orbits, tuple(stabilizers), fixed_counts


def put(pin, key, value):
    if value:
        pin[key] = value


def matrix_to_coproduct(A):
    """Dualize u^2=a*u+c*v, v^2=b*u+d*v to Delta on 1,x,y,xy."""
    a, b, c, d = A
    pin = {}

    # Delta(x), with x and y primitive summands suppressed from the pin.
    put(pin, (1, 1, 1), a)
    put(pin, (1, 2, 2), b)
    put(pin, (1, 1, 3), fmul(c, b))
    put(pin, (1, 3, 1), fmul(c, b))
    put(pin, (1, 2, 3), fmul(b, a))
    put(pin, (1, 3, 2), fmul(b, a))
    put(pin, (1, 3, 3), fmul(b, fadd(fmul(a, a), fmul(c, d))))

    # Delta(y).
    put(pin, (2, 1, 1), c)
    put(pin, (2, 2, 2), d)
    put(pin, (2, 1, 3), fmul(c, d))
    put(pin, (2, 3, 1), fmul(c, d))
    put(pin, (2, 2, 3), fmul(b, c))
    put(pin, (2, 3, 2), fmul(b, c))
    put(pin, (2, 3, 3), fmul(c, fadd(fmul(a, b), fmul(d, d))))

    # Delta(xy) = Delta(x) Delta(y).
    put(pin, (3, 1, 2), 1)
    put(pin, (3, 2, 1), 1)
    put(pin, (3, 1, 3), a)
    put(pin, (3, 3, 1), a)
    put(pin, (3, 2, 3), d)
    put(pin, (3, 3, 2), d)
    put(pin, (3, 3, 3), fadd(fmul(a, d), fmul(b, c)))
    return pin


def matrix_to_coproduct_by_duality(A):
    """Independently dualize the restricted enveloping algebra.

    This intentionally does not use the closed formulas above.  Monomials in
    the commutative algebra

        F_4[u,v]/(u^2-a*u-c*v, v^2-b*u-d*v)

    are recursively reduced to the basis 1,u,v,uv.  The coefficient of a
    basis vector in each product is then, by definition, the corresponding
    coproduct coefficient in the dual Hopf algebra.
    """
    a, b, c, d = A

    @lru_cache(maxsize=None)
    def reduce_monomial(i, j):
        if i >= 2:
            left = reduce_monomial(i - 1, j)
            right = reduce_monomial(i - 2, j + 1)
            return tuple(fadd(fmul(a, x), fmul(c, y))
                         for x, y in zip(left, right))
        if j >= 2:
            left = reduce_monomial(i + 1, j - 2)
            right = reduce_monomial(i, j - 1)
            return tuple(fadd(fmul(b, x), fmul(d, y))
                         for x, y in zip(left, right))
        out = [0] * 4
        out[((i, j) == (1, 0)) + 2 * ((i, j) == (0, 1))
            + 3 * ((i, j) == (1, 1))] = 1
        return tuple(out)

    exponents = ((0, 0), (1, 0), (0, 1), (1, 1))
    pin = {}
    for left in range(1, 4):
        for right in range(1, 4):
            i = exponents[left][0] + exponents[right][0]
            j = exponents[left][1] + exponents[right][1]
            product = reduce_monomial(i, j)
            for output in range(1, 4):
                put(pin, (output, left, right), product[output])
    return pin


# Multiplication in F_4[x,y]/(x^2,y^2), basis 1,x,y,xy.
PRODUCT_INDEX = (
    (0, 1, 2, 3),
    (1, None, 3, None),
    (2, 3, None, None),
    (3, None, None, None),
)
BASIS = tuple(tuple(int(i == j) for i in range(4)) for j in range(4))


def vmul(u, v):
    out = [0] * 4
    for i, ui in enumerate(u):
        if not ui:
            continue
        for j, vj in enumerate(v):
            k = PRODUCT_INDEX[i][j]
            if k is not None and vj:
                out[k] ^= fmul(ui, vj)
    return tuple(out)


def tmul(u, v):
    out = [0] * 16
    for i in range(4):
        for j in range(4):
            left_co = u[4 * i + j]
            if not left_co:
                continue
            for k in range(4):
                p = PRODUCT_INDEX[i][k]
                if p is None:
                    continue
                for ell in range(4):
                    q = PRODUCT_INDEX[j][ell]
                    right_co = v[4 * k + ell]
                    if q is not None and right_co:
                        out[4 * p + q] ^= fmul(left_co, right_co)
    return tuple(out)


def coproduct_vectors(pin):
    delta = []
    one = [0] * 16
    one[0] = 1
    delta.append(tuple(one))
    for i in range(1, 4):
        row = [0] * 16
        row[4 * i] ^= 1
        row[i] ^= 1
        for j in range(1, 4):
            for k in range(1, 4):
                row[4 * j + k] ^= pin.get((i, j, k), 0)
        delta.append(tuple(row))
    return tuple(delta)


def delta_vec(v, delta):
    out = [0] * 16
    for i, coefficient in enumerate(v):
        if coefficient:
            for q, x in enumerate(delta[i]):
                out[q] ^= fmul(coefficient, x)
    return tuple(out)


def finite_hopf_gates(A):
    """Check all Hopf identities needed here on the four basis vectors."""
    pin = matrix_to_coproduct(A)
    delta = coproduct_vectors(pin)

    # Cocommutativity and both counit identities.
    for i in range(4):
        for j in range(4):
            for k in range(4):
                assert delta[i][4 * j + k] == delta[i][4 * k + j]
        assert all(delta[i][j] == int(i == j) for j in range(4))
        assert all(delta[i][4 * j] == int(i == j) for j in range(4))

    # Delta is an algebra map.
    for i in range(4):
        for j in range(4):
            assert delta_vec(vmul(BASIS[i], BASIS[j]), delta) == \
                tmul(delta[i], delta[j])

    # Coassociativity.
    for i in range(4):
        lhs = [0] * 64
        rhs = [0] * 64
        for j in range(4):
            for k in range(4):
                coefficient = delta[i][4 * j + k]
                if not coefficient:
                    continue
                for p in range(4):
                    for q in range(4):
                        lhs[16 * p + 4 * q + k] ^= fmul(
                            coefficient, delta[j][4 * p + q]
                        )
                        rhs[16 * j + 4 * p + q] ^= fmul(
                            coefficient, delta[k][4 * p + q]
                        )
        assert lhs == rhs

    # [2]^# = mu o Delta is the augmentation.  Hence the identity map is
    # its own convolution inverse, so this simultaneously supplies the
    # antipode S=id and proves that the bialgebra is a killed-by-two group.
    for i in range(4):
        doubled = [0] * 4
        for j in range(4):
            for k in range(4):
                coefficient = delta[i][4 * j + k]
                product_index = PRODUCT_INDEX[j][k]
                if coefficient and product_index is not None:
                    doubled[product_index] ^= coefficient
        assert doubled == ([1, 0, 0, 0] if i == 0 else [0, 0, 0, 0])
    return pin


# F_2 matrices defining the six older rational pins, embedded in F_4.
KNOWN = {
    "a2a2": (0, 0, 0, 0),
    "W2F": (0, 0, 1, 0),
    "mu2mu2": (1, 0, 0, 1),
    "mu2a2": (1, 0, 0, 0),
    "mu2mu2_unipotent": (1, 1, 0, 1),
    "mu2mu2_irreducible": (0, 1, 1, 1),
}


# Literal sparse tables, copied from the existing solver convention.  This
# catches a transpose or dualization-convention slip in matrix_to_coproduct.
KNOWN_LITERAL_PINS = {
    "a2a2": {(3, 1, 2): 1, (3, 2, 1): 1},
    "W2F": {(2, 1, 1): 1, (3, 1, 2): 1, (3, 2, 1): 1},
    "mu2mu2": {
        (1, 1, 1): 1, (2, 2, 2): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
    "mu2a2": {
        (1, 1, 1): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
    },
    "mu2mu2_unipotent": {
        (1, 1, 1): 1, (1, 2, 2): 1,
        (1, 2, 3): 1, (1, 3, 2): 1, (1, 3, 3): 1,
        (2, 2, 2): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 1, 3): 1, (3, 3, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
    "mu2mu2_irreducible": {
        (1, 2, 2): 1, (1, 1, 3): 1, (1, 3, 1): 1, (1, 3, 3): 1,
        (2, 1, 1): 1, (2, 2, 2): 1,
        (2, 1, 3): 1, (2, 3, 1): 1,
        (2, 2, 3): 1, (2, 3, 2): 1, (2, 3, 3): 1,
        (3, 1, 2): 1, (3, 2, 1): 1,
        (3, 2, 3): 1, (3, 3, 2): 1, (3, 3, 3): 1,
    },
}


def matrix_json(A):
    a, b, c, d = A
    return {
        "encoding": [[a, b], [c, d]],
        "pretty": [[FIELD_LABELS[a], FIELD_LABELS[b]],
                   [FIELD_LABELS[c], FIELD_LABELS[d]]],
    }


def semilinear_square_json(A):
    """Matrix of xi^2, namely A A^(2); it changes by ordinary conjugacy."""
    norm = mmul(A, mfrob(A))
    a, b, c, d = norm
    return {
        **matrix_json(norm),
        "trace_encoding": fadd(a, d),
        "trace_pretty": FIELD_LABELS[fadd(a, d)],
        "determinant_encoding": mdet(norm),
        "determinant_pretty": FIELD_LABELS[mdet(norm)],
    }


def pin_json(pin):
    names = ("1", "x", "y", "xy")
    return [
        {
            "key": f"c{i}{j}{k}",
            "output": names[i],
            "left": names[j],
            "right": names[k],
            "coefficient_encoding": coefficient,
            "coefficient_pretty": FIELD_LABELS[coefficient],
        }
        for (i, j, k), coefficient in sorted(pin.items())
    ]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    started = time.monotonic()

    field_and_action_gates()
    orbits, stabilizers, fixed_counts = enumerate_orbits()
    owner = {A: i for i, orbit in enumerate(orbits) for A in orbit}

    # Check all 256 structures, not merely the representatives.
    pins = {A: finite_hopf_gates(A) for A in ALL_MATRICES}
    assert all(pins[A] == matrix_to_coproduct_by_duality(A)
               for A in ALL_MATRICES)
    assert all(pins[A] == KNOWN_LITERAL_PINS[name]
               for name, A in KNOWN.items())

    known_owner = {name: owner[A] for name, A in KNOWN.items()}
    known_by_orbit = defaultdict(list)
    for name, i in known_owner.items():
        known_by_orbit[i].append(name)
    covered = set(known_owner.values())

    orbit_rows = []
    for i, (orbit, stabilizer_size) in enumerate(zip(orbits, stabilizers)):
        representative = orbit[0]
        orbit_rows.append({
            "index": i,
            "representative": matrix_json(representative),
            "representative_determinant_encoding": mdet(representative),
            "representative_determinant_pretty": FIELD_LABELS[mdet(representative)],
            "xi_squared_linear_invariant": semilinear_square_json(representative),
            "orbit_size": len(orbit),
            "stabilizer_size": stabilizer_size,
            "known_F2_labels": sorted(known_by_orbit[i]),
            "coproduct_sparse_pin": pin_json(pins[representative]),
        })

    result = {
        "field": {
            "definition": "F2[w]/(w^2+w+1)",
            "encoding": {str(i): FIELD_LABELS[i] for i in range(4)},
        },
        "matrix_count": len(ALL_MATRICES),
        "gl2_count": len(GL2),
        "orbit_count": len(orbits),
        "orbit_size_histogram": {
            str(size): count
            for size, count in sorted(Counter(map(len, orbits)).items())
        },
        "burnside_fixed_count_histogram": {
            str(size): count
            for size, count in sorted(Counter(fixed_counts).items())
        },
        "known_F2_pin_orbits": known_owner,
        "all_orbits_covered_by_six_known_F2_pins": len(covered) == len(orbits),
        "missing_orbit_indices": [i for i in range(len(orbits)) if i not in covered],
        "orbits": orbit_rows,
        "gates": {
            "field_and_matrix_group": "passed",
            "twisted_action_identity": "passed",
            "direct_partition": "passed",
            "independent_canonical_partition": "passed",
            "orbit_closure": "passed",
            "orbit_stabilizer": "passed",
            "burnside": "passed",
            "all_256_bialgebra_coassociativity_killed_by_2": "passed",
            "all_256_closed_formula_equals_direct_duality": "passed",
            "literal_six_pin_comparison": "passed",
        },
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "max_rss_mib": round(
            resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            / (1024 * 1024 if sys.platform == "darwin" else 1024),
            3,
        ),
    }

    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print("F4 XY SEMILINEAR ORBIT AUDIT")
        print(json.dumps(result, indent=2, sort_keys=True))
        print("DONE f4_xy_semilinear_orbits_20260710")


if __name__ == "__main__":
    main()
