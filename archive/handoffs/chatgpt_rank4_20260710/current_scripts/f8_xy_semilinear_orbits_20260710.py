#!/usr/bin/env python3
"""Exact F_8 rational-form audit for the killed-by-two ``xy`` fiber.

The coordinate algebra is H = F_8[x,y]/(x^2,y^2).  Height-one commutative
group structures on H are dual to Frobenius-semilinear endomorphisms

    xi(v) = A v^(2),       A in M_2(F_8),

up to the twisted change of basis A |-> P^-1 A P^(2).  This script enumerates
all 4096 matrices and all 3528 elements of GL_2(F_8), proves that the resulting
orbits partition M_2(F_8), converts every orbit representative to a coproduct
table, and independently checks the bialgebra and [2]=0 identities by finite
arithmetic.

It is deliberately dependency-free and has a tiny memory footprint.  Its
purpose is to decide whether the six F_2-defined coproduct pins already used
in the ramified F_8 searches exhaust the F_8-rational forms.
"""

from __future__ import annotations

from collections import Counter
import argparse
import json
import resource
import sys
import time


# F_8 = F_2[w]/(w^3+w+1), encoded in the polynomial basis 1,w,w^2.
def fadd(a: int, b: int) -> int:
    return a ^ b


def fmul(a: int, b: int) -> int:
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 0b1000:
            a ^= 0b1011                 # w^3 = w+1
    return out & 0b111


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
    return fpow(a, 6)


# Matrices are row-major tuples (a,b,c,d) = [[a,b],[c,d]].
def madd(A, B):
    return tuple(fadd(a, b) for a, b in zip(A, B))


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
    return tuple(fmul(x, x) for x in A)


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
    for a in range(8) for b in range(8) for c in range(8) for d in range(8)
)
GL2 = tuple(A for A in ALL_MATRICES if mdet(A))


def twisted_conjugate(A, P):
    return mmul(mmul(minv(P), A), mfrob(P))


def enumerate_orbits():
    unseen = set(ALL_MATRICES)
    orbits = []
    while unseen:
        seed = min(unseen)
        orbit = {twisted_conjugate(seed, P) for P in GL2}
        assert seed in orbit
        assert orbit <= unseen, "twisted orbits overlapped without agreeing"
        unseen.difference_update(orbit)
        orbits.append(tuple(sorted(orbit)))
    orbits.sort(key=lambda O: O[0])
    assert sum(map(len, orbits)) == 8**4
    assert len(set().union(*(set(O) for O in orbits))) == 8**4
    return tuple(orbits)


def put(pin, key, value):
    if value:
        pin[key] = value


def matrix_to_coproduct(A):
    """Dualize u^2=a*u+c*v, v^2=b*u+d*v to Delta on 1,x,y,xy."""
    a, b, c, d = A
    pin = {}

    # Delta(x)-primitive terms.
    put(pin, (1, 1, 1), a)
    put(pin, (1, 2, 2), b)
    put(pin, (1, 1, 3), fmul(c, b))
    put(pin, (1, 3, 1), fmul(c, b))
    put(pin, (1, 2, 3), fmul(b, a))
    put(pin, (1, 3, 2), fmul(b, a))
    put(pin, (1, 3, 3), fmul(b, fadd(fmul(a, a), fmul(c, d))))

    # Delta(y)-primitive terms.
    put(pin, (2, 1, 1), c)
    put(pin, (2, 2, 2), d)
    put(pin, (2, 1, 3), fmul(c, d))
    put(pin, (2, 3, 1), fmul(c, d))
    put(pin, (2, 2, 3), fmul(b, c))
    put(pin, (2, 3, 2), fmul(b, c))
    put(pin, (2, 3, 3), fmul(c, fadd(fmul(a, b), fmul(d, d))))

    # Delta(xy)-primitive terms.
    put(pin, (3, 1, 2), 1)
    put(pin, (3, 2, 1), 1)
    put(pin, (3, 1, 3), a)
    put(pin, (3, 3, 1), a)
    put(pin, (3, 2, 3), d)
    put(pin, (3, 3, 2), d)
    put(pin, (3, 3, 3), fadd(fmul(a, d), fmul(b, c)))
    return pin


def vmul(u, v):
    """Multiply vectors in F_8[x,y]/(x^2,y^2), basis 1,x,y,xy."""
    out = [0] * 4
    # Products of basis indices.  None means zero.
    tab = (
        (0, 1, 2, 3),
        (1, None, 3, None),
        (2, 3, None, None),
        (3, None, None, None),
    )
    for i, ui in enumerate(u):
        for j, vj in enumerate(v):
            k = tab[i][j]
            if k is not None:
                out[k] ^= fmul(ui, vj)
    return tuple(out)


def tmul(u, v):
    out = [0] * 16
    for i in range(4):
        for j in range(4):
            if not u[4 * i + j]:
                continue
            for k in range(4):
                for l in range(4):
                    co = fmul(u[4 * i + j], v[4 * k + l])
                    if not co:
                        continue
                    left = vmul(tuple(int(q == i) for q in range(4)),
                                tuple(int(q == k) for q in range(4)))
                    right = vmul(tuple(int(q == j) for q in range(4)),
                                 tuple(int(q == l) for q in range(4)))
                    for p, lp in enumerate(left):
                        for q, rq in enumerate(right):
                            out[4 * p + q] ^= fmul(co, fmul(lp, rq))
    return tuple(out)


def coproduct_vectors(pin):
    D = []
    one = [0] * 16
    one[0] = 1
    D.append(tuple(one))
    for i in range(1, 4):
        row = [0] * 16
        row[4 * i] ^= 1
        row[i] ^= 1
        for j in range(1, 4):
            for k in range(1, 4):
                row[4 * j + k] ^= pin.get((i, j, k), 0)
        D.append(tuple(row))
    return tuple(D)


def delta_vec(v, D):
    out = [0] * 16
    for i, co in enumerate(v):
        for q, x in enumerate(D[i]):
            out[q] ^= fmul(co, x)
    return tuple(out)


def finite_hopf_gates(A):
    """Independent exhaustive basis check: multiplicativity, coassoc, [2]=0."""
    pin = matrix_to_coproduct(A)
    D = coproduct_vectors(pin)
    basis = tuple(tuple(int(i == j) for i in range(4)) for j in range(4))

    # Cocommutativity and counit.
    for i in range(4):
        for j in range(4):
            for k in range(4):
                assert D[i][4 * j + k] == D[i][4 * k + j]
        assert all(D[i][j] == int(i == j) for j in range(4))
        assert all(D[i][4 * j] == int(i == j) for j in range(4))

    # Delta is an algebra homomorphism.
    for i in range(4):
        for j in range(4):
            assert delta_vec(vmul(basis[i], basis[j]), D) == tmul(D[i], D[j])

    # Coassociativity on the basis.
    for i in range(4):
        lhs = [0] * 64
        rhs = [0] * 64
        for j in range(4):
            for k in range(4):
                co = D[i][4 * j + k]
                for p in range(4):
                    for q in range(4):
                        lhs[16 * p + 4 * q + k] ^= fmul(co, D[j][4 * p + q])
                        rhs[16 * j + 4 * p + q] ^= fmul(co, D[k][4 * p + q])
        assert lhs == rhs

    # [2]^# = mu Delta is augmentation on every augmentation generator.
    for i in range(1, 4):
        phi = [0] * 4
        for j in range(4):
            for k in range(4):
                prod = vmul(basis[j], basis[k])
                for q, x in enumerate(prod):
                    phi[q] ^= fmul(D[i][4 * j + k], x)
        assert phi == [0, 0, 0, 0]
    return pin


# Matrices underlying the six F_2-defined tables already used by the solver.
KNOWN = {
    "a2a2": (0, 0, 0, 0),
    "W2F": (0, 0, 1, 0),
    "mu2mu2": (1, 0, 0, 1),
    "mu2a2": (1, 0, 0, 0),
    "mu2mu2_unipotent": (1, 1, 0, 1),
    "mu2mu2_irreducible": (0, 1, 1, 1),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--json", action="store_true", help="print the exact audit as JSON")
    args = ap.parse_args()
    started = time.monotonic()

    # Exhaustive field gates.
    assert len(GL2) == (8**2 - 1) * (8**2 - 8) == 3528
    for a in range(8):
        assert fmul(a, 1) == a and fmul(a, 0) == 0
        assert fpow(a, 8) == a
        if a:
            assert fmul(a, finv(a)) == 1
        for b in range(8):
            assert fmul(a, b) == fmul(b, a)
            for c in range(8):
                assert fmul(a, b ^ c) == (fmul(a, b) ^ fmul(a, c))
                assert fmul(fmul(a, b), c) == fmul(a, fmul(b, c))

    orbits = enumerate_orbits()
    owner = {A: i for i, O in enumerate(orbits) for A in O}
    known_owner = {name: owner[A] for name, A in KNOWN.items()}
    for A in KNOWN.values():
        finite_hopf_gates(A)
    for O in orbits:
        finite_hopf_gates(O[0])

    known_tables_match = True
    try:
        from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS
        for name, A in KNOWN.items():
            known_tables_match &= matrix_to_coproduct(A) == MODELS[name]
    except ImportError:
        known_tables_match = None

    covered = set(known_owner.values())
    result = {
        "field": "F2[w]/(w^3+w+1)",
        "matrices": len(ALL_MATRICES),
        "gl2": len(GL2),
        "orbit_count": len(orbits),
        "orbit_sizes": [len(O) for O in orbits],
        "orbit_representatives": [list(O[0]) for O in orbits],
        "known_orbits": known_owner,
        "known_tables_match_literal_solver_pins": known_tables_match,
        "all_orbits_covered_by_six_known_pins": len(covered) == len(orbits),
        "missing_orbits": [i for i in range(len(orbits)) if i not in covered],
        "finite_bialgebra_and_killed_by_2_gates": "passed",
        "orbit_partition_gate": "passed",
        "orbit_size_histogram": dict(sorted(Counter(map(len, orbits)).items())),
        "elapsed_seconds": round(time.monotonic() - started, 3),
        "max_rss_mib": round(
            resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            / (1024 * 1024 if sys.platform == "darwin" else 1024), 3),
    }
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print("F8 XY SEMILINEAR ORBIT AUDIT")
        for key, value in result.items():
            print(f"{key}: {value}")
        print("DONE f8_xy_semilinear_orbits_20260710")


if __name__ == "__main__":
    main()
