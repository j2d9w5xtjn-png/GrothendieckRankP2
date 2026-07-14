#!/usr/bin/env python3
"""Exact screen of the provisional regular-translation identities.

The coefficient ring and triangular rank-four Hopf family are imported from
``audit_tight_chain_family_independent_20260710.py``.  For every one of its
1,608 valid parameter tuples this script constructs the universal right
translation matrix on the coordinate algebra and checks:

* HF1: the regular character is an integral and has counit 4;
* HF2: the regular character is antipode-invariant;
* HF3: the regular determinant has square one;
* the conditional regular-translation polynomial (RT).

This is a finite screen over F2[u,v]/(u^2,v^2), not a universal proof.
"""

from itertools import permutations, product
from pathlib import Path
import runpy


HERE = Path(__file__).resolve().parent
ns = runpy.run_path(str(HERE / "audit_tight_chain_family_independent_20260710.py"))

ZERO = ns["ZERO"]
ONE = ns["ONE"]
radd = ns["radd"]
rmul = ns["rmul"]
rvzero = ns["rvzero"]
rvadd = ns["rvadd"]
rvscale = ns["rvscale"]
rbasis = ns["rbasis"]
family_tables = ns["family_tables"]


def aadd(x, y):
    return rvadd(x, y)


def ascale(c, x):
    return rvscale(c, x)


def coordinate_product(x, y, delta):
    """Multiplication in A=D^vee, dual to the coproduct of D."""
    out = rvzero(4)
    for i, j, k in product(range(4), repeat=3):
        out[k] ^= rmul(rmul(x[i], y[j]), delta[k][4 * i + j])
    return out


def matrix_add(x, y):
    return [[aadd(x[i][j], y[i][j]) for j in range(4)] for i in range(4)]


def matrix_mul(x, y, delta):
    out = [[rvzero(4) for _ in range(4)] for _ in range(4)]
    for i, j, k in product(range(4), repeat=3):
        out[i][j] = aadd(out[i][j], coordinate_product(x[i][k], y[k][j], delta))
    return out


def scalar_matrix(a):
    out = [[rvzero(4) for _ in range(4)] for _ in range(4)]
    for i in range(4):
        out[i][i] = a[:]
    return out


def translation_matrix(m):
    """T_{ik}=sum_j coefficient(e_k in e_i e_j) f^j."""
    out = [[rvzero(4) for _ in range(4)] for _ in range(4)]
    for i, k, j in product(range(4), repeat=3):
        out[i][k][j] ^= m[i][j][k]
    return out


def determinant(t, delta_d):
    # In characteristic two every permutation sign is +1.
    out = rvzero(4)
    for perm in permutations(range(4)):
        term = rbasis(0)
        for i in range(4):
            term = coordinate_product(term, t[i][perm[i]], delta_d)
        out = aadd(out, term)
    return out


def antipode_on_coordinate(x, antipode_d):
    # S_A(f)(e_i)=f(S_D(e_i)).
    out = rvzero(4)
    for i, k in product(range(4), repeat=2):
        out[i] ^= rmul(x[k], antipode_d[i][k])
    return out


def audit_tuple(a, c, d, s):
    m, delta_d, antipode_d = family_tables(a, c, d, s)
    t = translation_matrix(m)

    chi = rvzero(4)
    for i in range(4):
        chi = aadd(chi, t[i][i])
    determinant_t = determinant(t, delta_d)

    # HF1, including epsilon(chi)=4=0 in this characteristic-two ring.
    assert chi[0] == ZERO
    for i in range(4):
        lhs = coordinate_product(rbasis(i), chi, delta_d)
        rhs = chi if i == 0 else rvzero(4)
        assert lhs == rhs

    # HF2 and HF3.
    assert antipode_on_coordinate(chi, antipode_d) == chi
    assert coordinate_product(determinant_t, determinant_t, delta_d) == rbasis(0)

    # Determinant is group-like (a useful convention check).
    coproduct_det = rvzero(16)
    for k, i, j in product(range(4), repeat=3):
        coproduct_det[4 * i + j] ^= rmul(determinant_t[k], m[i][j][k])
    tensor_square = rvzero(16)
    for i, j in product(range(4), repeat=2):
        tensor_square[4 * i + j] = rmul(determinant_t[i], determinant_t[j])
    if not (coproduct_det == tensor_square and determinant_t[0] == ONE):
        raise AssertionError(
            f"determinant convention failure for {(a, c, d, s)}: "
            f"delta={determinant_t}, coproduct={coproduct_det}, square={tensor_square}"
        )

    # (T^2-I)(T^2-delta I)=0.
    identity = scalar_matrix(rbasis(0))
    t2 = matrix_mul(t, t, delta_d)
    left = matrix_add(t2, identity)
    right = matrix_add(t2, scalar_matrix(determinant_t))
    zero_matrix = [[rvzero(4) for _ in range(4)] for _ in range(4)]
    assert matrix_mul(left, right, delta_d) == zero_matrix
    return determinant_t


valid = 0
local_local = 0
local_local_nontrivial_determinant = 0
for a, c, d, s in product(range(16), repeat=4):
    h = radd(a, c)
    if not (
        rmul(c, h) == 0
        and rmul(c, s) == 0
        and rmul(c, d) == 0
        and rmul(s, radd(d, rmul(s, rmul(a, a)))) == 0
    ):
        continue
    determinant_t = audit_tuple(a, c, d, s)
    valid += 1
    # In this family the special dual algebra is local-local exactly when
    # a,c,d reduce to zero; s controls the remaining coalgebra form.
    if not (a & ONE) and not (c & ONE) and not (d & ONE):
        local_local += 1
        if determinant_t != rbasis(0):
            local_local_nontrivial_determinant += 1


assert valid == 1608
assert local_local == 1088
assert local_local_nontrivial_determinant == 0
print(f"HF1/HF2/HF3 and RT: PASS ({valid} valid triangular Hopf tuples)")
print(
    "local-local determinant screen: "
    f"{local_local_nontrivial_determinant} nontrivial / {local_local} tuples"
)
print("FINITE SCREEN PASS")
