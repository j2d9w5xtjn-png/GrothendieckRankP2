#!/usr/bin/env python3
from __future__ import annotations

import itertools
import re
import argparse

# Z/4*1; X,Y; Z/4*Z; D; X*,Y*,D*.  Here Z*=2 and s=2Z.
MOD = (4, 2, 2, 4, 2, 2, 2, 2)
ZERO = (0,) * len(MOD)
ONE = (1,) + (0,) * (len(MOD) - 1)
VPOS = (1, 2, 3, 4)  # X,Y,Z,D
WPOS = {0: 5, 1: 6, 3: 7}  # Z* is scalar 2
ZINDEX = 2
F_SUPPORT = {
    tuple(sorted(t))
    for t in ((0, 0, 2), (0, 1, 3), (1, 3, 3), (2, 2, 2))
}


def add(x, y):
    return tuple((a + b) % m for a, b, m in zip(x, y, MOD))


def neg(x):
    return tuple((-a) % m for a, m in zip(x, MOD))


def sub(x, y):
    return add(x, neg(y))


def smul(n, x):
    return tuple((n * a) % m for a, m in zip(x, MOD))


def basis(i, c=1):
    out = [0] * len(MOD)
    out[i] = c % MOD[i]
    return tuple(out)


def f(i, j, k):
    return int(tuple(sorted((i, j, k))) in F_SUPPORT)


def mul(x, y):
    out = [0] * len(MOD)
    r, q = x[0], y[0]
    out[0] += r * q
    for pos in range(1, len(MOD)):
        out[pos] += r * y[pos] + q * x[pos]
    xv = [x[pos] & 1 for pos in VPOS]
    yv = [y[pos] & 1 for pos in VPOS]
    for k in range(4):
        coefficient = 0
        for i in range(4):
            for j in range(4):
                coefficient ^= xv[i] & yv[j] & f(i, j, k)
        if k == ZINDEX:
            out[0] += 2 * coefficient
        else:
            out[WPOS[k]] += coefficient
    pairing = 0
    for k, pos in WPOS.items():
        pairing ^= (xv[k] & (y[pos] & 1)) ^ (yv[k] & (x[pos] & 1))
    out[VPOS[ZINDEX]] += 2 * pairing
    return tuple(value % modulus for value, modulus in zip(out, MOD))


def product(items):
    out = ONE
    for x in items:
        out = mul(out, x)
    return out


def parse_polynomial(text):
    text = text.replace(" ", "")
    if text and text[0] not in "+-":
        text = "+" + text
    answer = []
    for sign, term in re.findall(r"([+-])([^+-]+)", text):
        coefficient = -1 if sign == "-" else 1
        factors = []
        for factor in term.split("*"):
            match = re.fullmatch(r"p_(\d+)(?:\^(\d+))?", factor)
            if match:
                factors.extend([int(match.group(1))] * int(match.group(2) or 1))
            else:
                coefficient *= int(factor)
        answer.append((coefficient, tuple(factors)))
    return answer


def read_export(path):
    equations, targets = [], []
    with open(path, encoding="utf-8") as stream:
        for line in stream:
            if line.startswith("E "):
                equations.append(parse_polynomial(line.rstrip().split(" ", 2)[2]))
            elif line.startswith("T "):
                targets.append(parse_polynomial(line.rstrip().split(" ", 2)[2]))
    assert (len(equations), len(targets)) == (189, 9)
    return equations, targets


def evaluate(poly, params):
    out = ZERO
    for coefficient, factors in poly:
        out = add(out, smul(coefficient, product(params[i] for i in factors)))
    return out


def parameter_values():
    p = [ZERO] * 45
    X, Y, Z, D = [basis(pos) for pos in VPOS]
    Xs, Ys, Ds = [basis(pos) for pos in range(5, 8)]
    two = basis(0, 2)
    s = basis(VPOS[ZINDEX], 2)
    values = {
        0: X, 1: Y, 8: X, 10: Z, 14: Z, 17: Xs, 18: X,
        21: add(Y, Z), 24: add(Xs, Ds), 30: D, 31: add(Y, Z),
        32: add(Xs, Ds), 38: X, 39: add(two, Ys),
        40: add(Xs, Ds), 41: s, 42: add(X, D),
        43: add(add(Y, Z), s), 44: add(Xs, Ds),
    }
    for i, value in values.items():
        p[i] = value
    return p


def decode(code):
    out = []
    for modulus in MOD:
        out.append(code % modulus)
        code //= modulus
    assert code == 0
    return tuple(out)


def additive_closure(generators):
    closure = {ZERO}
    for generator in generators:
        multiples = [ZERO]
        value = ZERO
        for _ in range(1, 4):
            value = add(value, generator)
            if value == ZERO:
                break
            multiples.append(value)
        closure = {add(x, y) for x in closure for y in multiples}
    return closure


# Direct construction of the specialized rank-four bialgebra.
def hopf_tables(p):
    def mvar(i, j, r):
        u, v = min(i, j), max(i, j)
        pair = v - 1 if u == 1 else (v + 1 if u == 2 else 5)
        return p[3 * pair + r - 1]

    def cvar(i, j, k):
        return p[18 + 9 * (i - 1) + 3 * (j - 1) + k - 1]

    e = [tuple(ONE if i == j else ZERO for i in range(4)) for j in range(4)]
    M = {}
    for i in range(4):
        for j in range(4):
            if i == 0:
                M[i, j] = e[j]
            elif j == 0:
                M[i, j] = e[i]
            else:
                row = [ZERO] * 4
                for r in range(1, 4):
                    value = mvar(i, j, r)
                    if {i, j} == {1, 2} and r == 3:
                        value = add(value, ONE)
                    row[r] = value
                M[i, j] = tuple(row)

    Delta = []
    row0 = [ZERO] * 16
    row0[0] = ONE
    Delta.append(tuple(row0))
    for i in range(1, 4):
        row = [ZERO] * 16
        row[4 * i] = ONE
        row[i] = ONE
        for j in range(1, 4):
            for k in range(1, 4):
                value = cvar(i, j, k)
                if i == 3 and (j, k) in ((1, 2), (2, 1)):
                    value = add(value, ONE)
                row[4 * j + k] = value
        Delta.append(tuple(row))
    return e, M, Delta


def direct_antipode_gate(p):
    e, M, Delta = hopf_tables(p)

    def mulA(x, y):
        out = [ZERO] * 4
        for i in range(4):
            for j in range(4):
                coefficient = mul(x[i], y[j])
                for r in range(4):
                    out[r] = add(out[r], mul(coefficient, M[i, j][r]))
        return tuple(out)

    phi = []
    for i in range(4):
        out = [ZERO] * 4
        for j in range(4):
            for k in range(4):
                coefficient = Delta[i][4 * j + k]
                for r in range(4):
                    out[r] = add(out[r], mul(coefficient, M[j, k][r]))
        phi.append(tuple(out))

    def compose(F, G):
        # F o G on coordinate vectors, with maps represented by basis images.
        images = []
        for i in range(4):
            out = [ZERO] * 4
            for j in range(4):
                for r in range(4):
                    out[r] = add(out[r], mul(G[i][j], F[j][r]))
            images.append(tuple(out))
        return tuple(images)

    p4 = compose(tuple(phi), tuple(phi))
    p8 = compose(tuple(phi), p4)
    assert p4[1][3] == basis(VPOS[ZINDEX], 2)
    assert all(p4[i][j] == ZERO for i, j in itertools.product(range(4), repeat=2)
               if not (i, j) in ((0, 0), (1, 3)))
    assert p4[0][0] == ONE
    assert p8 == (e[0], (ZERO,) * 4, (ZERO,) * 4, (ZERO,) * 4)
    print("POWER8_GATE [8]^#=unit*epsilon exactly")

    # Endomorphism is tuple of four images of basis vectors.
    ID = tuple(e)
    UNIT = (e[0], (ZERO,) * 4, (ZERO,) * 4, (ZERO,) * 4)

    def conv(F, G):
        images = []
        for i in range(4):
            out = (ZERO,) * 4
            for j in range(4):
                for k in range(4):
                    coefficient = Delta[i][4 * j + k]
                    term = mulA(F[j], G[k])
                    out = tuple(add(a0, mul(coefficient, b0)) for a0, b0 in zip(out, term))
            images.append(out)
        return tuple(images)

    def end_add(F, G):
        return tuple(tuple(add(x, y) for x, y in zip(frow, grow))
                     for frow, grow in zip(F, G))

    def end_neg(F):
        return tuple(tuple(neg(x) for x in row) for row in F)

    # Closed-fiber antipode lift S0=id.  If E=id*S0-1, then E^4=0 and
    # S=S0*(1-E+E^2-E^3) is a concrete convolution inverse.
    E = end_add(conv(ID, ID), end_neg(UNIT))
    E2 = conv(E, E)
    E3 = conv(E2, E)
    E4 = conv(E3, E)
    assert E4 == tuple((ZERO,) * 4 for _ in range(4))
    geometric = end_add(end_add(UNIT, end_neg(E)), end_add(E2, end_neg(E3)))
    S = conv(ID, geometric)
    assert conv(ID, S) == UNIT
    assert conv(S, ID) == UNIT
    print("ANTIPODE_IMAGES", S)
    print("ANTIPODE_GATE direct convolution inverse PASS (E^4=0, both sides)")


def main(export_path):
    generators = [basis(i) for i in range(len(MOD))]
    assert all(mul(x, y) == mul(y, x) for x in generators for y in generators)
    for x, y, z in itertools.product(generators, repeat=3):
        assert mul(mul(x, y), z) == mul(x, mul(y, z))
    assert all(mul(ONE, x) == x for x in generators)
    print("RING_GATE commutative/unit/associative PASS triples", len(generators) ** 3)

    elements = [decode(code) for code in range(1 << 10)]
    for x in elements:
        for y, z in itertools.product(generators, repeat=2):
            assert mul(add(x, y), z) == add(mul(x, z), mul(y, z))
    print("DISTRIBUTIVITY_GATE generator-level translations PASS (coordinate law biadditive)")

    s = basis(VPOS[ZINDEX], 2)
    max_generators = [basis(0, 2)] + generators[1:]
    assert all(product(row) == ZERO for row in itertools.product(max_generators, repeat=4))
    mpowers = [additive_closure(max_generators)]
    for _ in range(3):
        previous = mpowers[-1]
        mpowers.append(additive_closure(mul(x, y) for x in previous for y in max_generators))
    assert [len(x) for x in mpowers] == [512, 32, 2, 1]
    socle = []
    for x in elements:
        if all(mul(x, q) == ZERO for q in max_generators):
            socle.append(x)
    assert socle == [ZERO, s]
    print("BASE_GATE cardinality=1024 length=10 char=4 Hilbert=(1,4,4,1) powers=512,32,2,1")
    print("BASE_GATE additive=Z/4^2+F2^6 m4=0 socle={0,s}")

    equations, targets = read_export(export_path)
    p = parameter_values()
    bad = [(i, evaluate(poly, p)) for i, poly in enumerate(equations)
           if evaluate(poly, p) != ZERO]
    assert not bad, bad[:5]
    values = [evaluate(poly, p) for poly in targets]
    assert values == [ZERO, ZERO, s, ZERO, ZERO, ZERO, ZERO, ZERO, ZERO]
    print("HOPF_GATE all 189 exported equations vanish")
    print("POWER_GATE target2=s=2Z!=0; other eight targets zero")
    direct_antipode_gate(p)
    print("VERDICT length-10 rank-four Hopf counterexample PASS")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("export", help="integral branch-0 M2 polynomial export")
    main(parser.parse_args().export)
