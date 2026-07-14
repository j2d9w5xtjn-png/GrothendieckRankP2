#!/usr/bin/env python3
"""Exact additive Smith audit for the five-parameter base (stdlib only)."""

from itertools import product

# First quotient by the monic power relations
# a^2=2q, b^2=c^2=p^3=q^3=0.  The following 72 monomials are a free
# Z/4-spanning set before imposing the remaining relations.
basis = list(product(range(2), range(2), range(2), range(3), range(3)))
where = {m: i for i, m in enumerate(basis)}
n = len(basis)


def reduce_term(coefficient, exponent):
    coefficient %= 4
    a, b, c, p, q = exponent
    while a >= 2 and coefficient:
        a -= 2
        q += 1
        coefficient = 2 * coefficient % 4
    if not coefficient or b >= 2 or c >= 2 or p >= 3 or q >= 3:
        return None
    return coefficient, (a, b, c, p, q)


def monomial(**powers):
    position = {"a": 0, "b": 1, "c": 2, "p": 3, "q": 4}
    answer = [0] * 5
    for variable, exponent in powers.items():
        answer[position[variable]] = exponent
    return tuple(answer)


one = (0, 0, 0, 0, 0)
relations = [
    [(1, monomial(a=1, p=1)), (-2, one)],
    [(1, monomial(c=1, q=1)), (-2, one)],
    [(1, monomial(c=1, p=1))],
    [(1, monomial(b=1, q=1))],
    [(1, monomial(b=1, p=1)), (-1, monomial(a=1, q=1))],
    [(2, monomial(p=1))],
    [(2, monomial(a=1))],
    [(2, monomial(b=1))],
    [(2, monomial(c=1))],
    [(1, monomial(b=1, c=1)), (-2, monomial(q=1))],
    [(1, monomial(a=1, b=1))],
    [(1, monomial(a=1, c=1))],
]

rows = []
for relation in relations:
    for multiplier in basis:
        row = [0] * n
        for coefficient, exponent in relation:
            term = reduce_term(
                coefficient,
                tuple(exponent[i] + multiplier[i] for i in range(5)),
            )
            if term is not None:
                scalar, reduced = term
                row[where[reduced]] = (row[where[reduced]] + scalar) % 4
        if any(row):
            rows.append(row)

# Smith reduction over the principal ideal ring Z/4.  First remove unit
# pivots.  The remaining matrix is even; half of it is then row-reduced over
# F_2 to count the pivots equal to 2.
number_of_rows = len(rows)
i = j = unit_pivots = 0
while i < number_of_rows and j < n:
    pivot = None
    for r in range(i, number_of_rows):
        for column in range(j, n):
            if rows[r][column] % 2:
                pivot = r, column
                break
        if pivot is not None:
            break
    if pivot is None:
        break
    r, column = pivot
    rows[i], rows[r] = rows[r], rows[i]
    for r in range(number_of_rows):
        rows[r][j], rows[r][column] = rows[r][column], rows[r][j]
    if rows[i][j] == 3:
        rows[i] = [3 * entry % 4 for entry in rows[i]]
    for r in range(number_of_rows):
        if r != i and rows[r][j]:
            scalar = rows[r][j]
            rows[r] = [
                (rows[r][column] - scalar * rows[i][column]) % 4
                for column in range(n)
            ]
    for column in range(n):
        if column != j and rows[i][column]:
            scalar = rows[i][column]
            for r in range(number_of_rows):
                rows[r][column] = (
                    rows[r][column] - scalar * rows[r][j]
                ) % 4
    unit_pivots += 1
    i += 1
    j += 1

binary = [
    [rows[r][column] // 2 % 2 for column in range(j, n)]
    for r in range(i, number_of_rows)
]
two_pivots = column = 0
while two_pivots < len(binary) and column < n - j:
    pivot = next(
        (r for r in range(two_pivots, len(binary)) if binary[r][column]),
        None,
    )
    if pivot is None:
        column += 1
        continue
    binary[two_pivots], binary[pivot] = binary[pivot], binary[two_pivots]
    for r in range(len(binary)):
        if r != two_pivots and binary[r][column]:
            binary[r] = [x ^ y for x, y in zip(binary[r], binary[two_pivots])]
    two_pivots += 1
    column += 1

z4_factors = n - unit_pivots - two_pivots
z2_factors = two_pivots
length = 2 * z4_factors + z2_factors
assert (z4_factors, z2_factors, length) == (2, 11, 15)

print("B_add = (Z/4)^2 + (Z/2)^11")
print("length(B) = 15; |B| = 2^15")
print(
    "normal form: (Z/4){1,q} + (F_2){q^2,p,pq,pq^2,p^2,p^2q,"
    "p^2q^2,c,b,a,aq}"
)
