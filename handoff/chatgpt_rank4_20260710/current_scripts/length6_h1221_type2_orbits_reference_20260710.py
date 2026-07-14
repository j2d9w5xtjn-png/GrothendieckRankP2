#!/usr/bin/env python3
r"""Exact finite orbit enumeration for residue-F2 rings with H=(1,2,2,1).

This is a self-contained reference computation for Section 5 of
STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md.  It uses a filtration-adapted
polycyclic basis

    1, x, y, a, b, u

of relative additive order two.  Thus 2*e_i is an F2-combination of basis
vectors in strictly deeper filtration.  The two possible associated-graded
compatible-form orbits are normalized as

    A: x^2=a, xy=b, y^2=0,  xa=u;
    B: x^2=a, xy=0, y^2=b,  xa=u,

with every omitted positive-degree product zero.  All three V*V products
may have an arbitrary u correction.  The program enumerates every triangular
additive carry and every correction, retains exactly the well-defined
associative rings, and quotients presentations by every possible ordered
tangent generating pair.  Accepted isomorphisms are checked on all 64^2
addition and multiplication pairs.

The second phase (added below) tests one-dimensional Gorenstein socle lifts.
No classification count printed by this file is inferred from a heuristic
stabilizer calculation.
"""

from __future__ import annotations

import itertools
import time
from dataclasses import dataclass


N = 6
ALL = tuple(range(1 << N))
LAYERS = (0, 1, 1, 2, 2, 3)
LIFT_N = 7
LIFT_ALL = tuple(range(1 << LIFT_N))
TOP = 1 << 6
LIFT_PAIRS = ((1, 1), (1, 2), (2, 2),
              (1, 3), (1, 4), (2, 3), (2, 4),
              (1, 5), (2, 5),
              (3, 3), (3, 4), (4, 4))


def bit_indices(mask: int):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def encode_coeffs(coeffs):
    return sum((int(c) & 1) << i for i, c in enumerate(coeffs))


@dataclass(frozen=True)
class PresentationKey:
    graded: str
    correction: int
    carries: tuple[int, ...]


class FilteredRing:
    def __init__(self, key: PresentationKey):
        self.key = key
        self.graded = key.graded
        self.correction = key.correction
        self.d = key.carries
        assert len(self.d) == N and self.d[-1] == 0
        self.zero = 0
        self.one = 1
        self.x = 1 << 1
        self.y = 1 << 2
        self.a = 1 << 3
        self.b = 1 << 4
        self.u = 1 << 5
        self._basis_mul = self._make_basis_mul()
        self._add = None
        self._mul = None

    @property
    def label(self):
        ds = ".".join(f"{x:02x}" for x in self.d[:-1])
        return f"{self.graded}_c{self.correction:01x}_d{ds}"

    def _make_basis_mul(self):
        tab = [[0] * N for _ in range(N)]
        for i in range(N):
            tab[0][i] = tab[i][0] = 1 << i
        cxx = (self.correction >> 0) & 1
        cxy = (self.correction >> 1) & 1
        cyy = (self.correction >> 2) & 1
        if self.graded == "A":
            xx, xy, yy = self.a, self.b, 0
        elif self.graded == "B":
            xx, xy, yy = self.a, 0, self.b
        else:
            raise AssertionError(self.graded)
        tab[1][1] = xx | (cxx << 5)
        tab[1][2] = tab[2][1] = xy | (cxy << 5)
        tab[2][2] = yy | (cyy << 5)
        tab[1][3] = tab[3][1] = self.u
        return tab

    def reduce(self, coeffs):
        cs = list(coeffs) + [0] * max(0, N - len(coeffs))
        for i in range(N):
            q, cs[i] = divmod(cs[i], 2)
            if q:
                for j in bit_indices(self.d[i]):
                    cs[j] += q
        return encode_coeffs(cs[:N])

    def add_raw(self, p, q):
        cs = [((p >> i) & 1) + ((q >> i) & 1) for i in range(N)]
        return self.reduce(cs)

    def neg_raw(self, p):
        return self.reduce([-((p >> i) & 1) for i in range(N)])

    def sum_raw(self, xs):
        out = 0
        for x in xs:
            out = self.add_raw(out, x)
        return out

    def mul_raw(self, p, q):
        out = 0
        for i in bit_indices(p):
            for j in bit_indices(q):
                out = self.add_raw(out, self._basis_mul[i][j])
        return out

    def add(self, p, q):
        return self._add[p][q] if self._add is not None else self.add_raw(p, q)

    def mul(self, p, q):
        return self._mul[p][q] if self._mul is not None else self.mul_raw(p, q)

    def build_tables(self):
        if self._add is None:
            self._add = [[self.add_raw(p, q) for q in ALL] for p in ALL]
            self._mul = [[self.mul_raw(p, q) for q in ALL] for p in ALL]

    def pow(self, p, n):
        out = self.one
        for _ in range(n):
            out = self.mul(out, p)
        return out

    def scalar(self, n):
        out = 0
        for _ in range(n):
            out = self.add(out, self.one)
        return out

    def characteristic(self):
        out = 0
        for n in range(1, 65):
            out = self.add(out, self.one)
            if out == 0:
                return n
        raise AssertionError

    @staticmethod
    def m_set():
        return set(range(0, 64, 2))

    @staticmethod
    def m2_set():
        return {z for z in ALL if z & 0b000111 == 0}

    @staticmethod
    def m3_set():
        return {0, 1 << 5}

    def tangent_generating_pairs(self):
        # Ordered bases in m/m^2: six GL_2(F2) choices, independently lifted
        # through the 16-element m^2.
        m = self.m_set()
        m2 = self.m2_set()
        out = []
        for p in m:
            vp = (p >> 1) & 0b11
            if not vp:
                continue
            for q in m:
                vq = (q >> 1) & 0b11
                if not vq or vq == vp:
                    continue
                out.append((p, q))
        assert len(out) == 6 * len(m2) * len(m2) == 384
        return out


def candidate_carries():
    # Explicit masks make the filtration restriction auditable.
    d0s = [sum(bits) for bits in itertools.product((0, 1 << 1),
                                                    (0, 1 << 2),
                                                    (0, 1 << 3),
                                                    (0, 1 << 4),
                                                    (0, 1 << 5))]
    d1s = [sum(bits) for bits in itertools.product((0, 1 << 3),
                                                    (0, 1 << 4),
                                                    (0, 1 << 5))]
    d2s = d1s
    d3s = (0, 1 << 5)
    d4s = d3s
    for d0, d1, d2, d3, d4 in itertools.product(d0s, d1s, d2s, d3s, d4s):
        yield (d0, d1, d2, d3, d4, 0)


GL2_BASES = tuple((p, q) for p in (1, 2, 3) for q in (1, 2, 3) if p != q)


def lin2(cols, v):
    return (cols[0] if v & 1 else 0) ^ (cols[1] if v & 2 else 0)


def coords2(cols, v):
    return next(z for z in range(4) if lin2(cols, z) == v)


def B_eval(B, v, w):
    out = 0
    if (v & 1) and (w & 1):
        out ^= B[0]
    if ((bool(v & 1) and bool(w & 2)) ^
            (bool(v & 2) and bool(w & 1))):
        out ^= B[1]
    if (v & 2) and (w & 2):
        out ^= B[2]
    return out


def L_eval(L, v, w):
    out = 0
    for i in range(2):
        for j in range(2):
            if (v >> i) & 1 and (w >> j) & 1:
                out ^= (L >> (2 * i + j)) & 1
    return out


def compatible_form_orbits():
    """Enumerate all 42 surjective B and all 16 bilinear L exactly."""
    compatible = []
    for B in itertools.product(range(4), repeat=3):
        if len({0, B[0], B[1], B[2], B[0] ^ B[1], B[0] ^ B[2],
                B[1] ^ B[2], B[0] ^ B[1] ^ B[2]}) != 4:
            continue
        for L in range(16):
            # W -> V*: its two columns must span a one-dimensional image.
            columns = tuple(sum(L_eval(L, 1 << i, 1 << j) << i
                                for i in range(2)) for j in range(2))
            if len({0, columns[0], columns[1], columns[0] ^ columns[1]}) != 2:
                continue
            # The only nontrivial associativity equations for symmetric V^3.
            if L_eval(L, 2, B[0]) != L_eval(L, 1, B[1]):
                continue
            if L_eval(L, 2, B[1]) != L_eval(L, 1, B[2]):
                continue
            compatible.append((B, L))

    def transform(pair, gv, gw):
        B, L = pair
        vx, vy = gv
        wx, wy = gw
        newB = (coords2(gw, B_eval(B, vx, vx)),
                coords2(gw, B_eval(B, vx, vy)),
                coords2(gw, B_eval(B, vy, vy)))
        newL = 0
        for i, v in enumerate((vx, vy)):
            for j, w in enumerate((wx, wy)):
                newL |= L_eval(L, v, w) << (2 * i + j)
        return newB, newL

    canonical = {}
    for pair in compatible:
        orbit = {transform(pair, gv, gw) for gv in GL2_BASES for gw in GL2_BASES}
        canonical.setdefault(min(orbit), []).append(pair)
    A = ((1, 2, 0), 1)
    B = ((1, 0, 2), 1)
    assert A in compatible and B in compatible
    assert min(transform(A, gv, gw) for gv in GL2_BASES for gw in GL2_BASES) != \
           min(transform(B, gv, gw) for gv in GL2_BASES for gw in GL2_BASES)
    assert len(canonical) == 2
    return len(compatible), sorted(len(v) for v in canonical.values())


def basis_axioms_hold(R: FilteredRing):
    # Multiplication must descend through every additive relation
    # 2e_i=d_i.  This is precisely the bilinearity/congruence gate.
    for i in range(N):
        ei = 1 << i
        for j in range(N):
            ej = 1 << j
            lhs = R.add_raw(R.mul_raw(ei, ej), R.mul_raw(ei, ej))
            rhs = R.mul_raw(R.d[i], ej)
            if lhs != rhs:
                return False
    # Once the product descends bilinearly, associativity on additive
    # generators is equivalent to associativity everywhere.
    for i, j, k in itertools.product(range(N), repeat=3):
        ei, ej, ek = 1 << i, 1 << j, 1 << k
        if R.mul_raw(R.mul_raw(ei, ej), ek) != R.mul_raw(ei, R.mul_raw(ej, ek)):
            return False
    return True


def additive_closure(R, seed):
    out = {0}
    changed = True
    while changed:
        changed = False
        for a in tuple(out):
            for b in seed:
                c = R.add(a, b)
                if c not in out:
                    out.add(c)
                    changed = True
    return out


def validate_ring(R: FilteredRing, exhaustive=False):
    R.build_tables()
    m, m2, m3 = R.m_set(), R.m2_set(), R.m3_set()
    assert len(m) == 32 and len(m2) == 8 and len(m3) == 2
    assert all(R.add(a, b) in m for a in m for b in m)
    assert all(R.add(a, b) in m2 for a in m2 for b in m2)
    assert all(R.add(a, b) in m3 for a in m3 for b in m3)
    assert all(R.mul(a, b) in m for a in m for b in ALL)
    assert {R.mul(a, b) for a in m for b in m} | {0} <= m2
    generated_m2 = additive_closure(R, [R.mul(a, b) for a in m for b in m])
    generated_m3 = additive_closure(R, [R.mul(a, b) for a in m for b in m2])
    assert generated_m2 == m2 and generated_m3 == m3
    assert all(R.mul(a, b) == 0 for a in m for b in m3)
    soc = {a for a in m if all(R.mul(a, b) == 0 for b in m)}
    assert len(soc) == 4
    units = {a for a in ALL if any(R.mul(a, b) == 1 for b in ALL)}
    assert units == set(ALL) - m
    assert additive_closure(R, [1, R.x, R.y, R.a, R.b, R.u]) == set(ALL)
    if exhaustive:
        for a in ALL:
            assert R.add(a, 0) == a and R.mul(a, 1) == a
            assert R.add(a, R.neg_raw(a)) == 0
        for a, b in itertools.product(ALL, repeat=2):
            assert R.add(a, b) == R.add(b, a)
            assert R.mul(a, b) == R.mul(b, a)
        for a, b, c in itertools.product(ALL, repeat=3):
            assert R.add(R.add(a, b), c) == R.add(a, R.add(b, c))
            assert R.mul(R.mul(a, b), c) == R.mul(a, R.mul(b, c))
            assert R.mul(a, R.add(b, c)) == R.add(R.mul(a, b), R.mul(a, c))


def enumerate_presentations():
    out = []
    total = 0
    for carries in candidate_carries():
        for graded in ("A", "B"):
            for correction in range(8):
                total += 1
                R = FilteredRing(PresentationKey(graded, correction, carries))
                if basis_axioms_hold(R):
                    validate_ring(R)
                    out.append(R)
    assert total == 8192 * 2 * 8
    return out, total


def basis_polynomials(source: FilteredRing, target: FilteredRing, X, Y):
    # Express the source's adapted additive basis as polynomials in its x,y.
    # u=x*a; the W lifts are recovered from the normalized V*V formulas.
    u = target.mul(target.mul(X, X), X)
    cxx = (source.correction >> 0) & 1
    cxy = (source.correction >> 1) & 1
    cyy = (source.correction >> 2) & 1
    xx, xy, yy = target.mul(X, X), target.mul(X, Y), target.mul(Y, Y)
    if source.graded == "A":
        a = target.add(xx, u) if cxx else xx
        b = target.add(xy, u) if cxy else xy
        # y^2 is a defining relation rather than a basis recovery.
        expected_yy = u if cyy else 0
        if yy != expected_yy:
            return None
    else:
        a = target.add(xx, u) if cxx else xx
        b = target.add(yy, u) if cyy else yy
        expected_xy = u if cxy else 0
        if xy != expected_xy:
            return None
    return (1, X, Y, a, b, u)


def evaluate_from_basis(source, target, images, z):
    out = 0
    for i in bit_indices(z):
        out = target.add(out, images[i])
    return out


def isomorphism_witness(source: FilteredRing, target: FilteredRing):
    # Return the first witness.  Every ordered tangent generating pair is
    # tested; no characteristic or presentation invariant is used to prune.
    for X, Y in target.tangent_generating_pairs():
        images_basis = basis_polynomials(source, target, X, Y)
        if images_basis is None:
            continue
        image = [evaluate_from_basis(source, target, images_basis, z) for z in ALL]
        if len(set(image)) != 64 or image[1] != 1:
            continue
        good = True
        for p, q in itertools.product(ALL, repeat=2):
            if image[source.add(p, q)] != target.add(image[p], image[q]):
                good = False
                break
            if image[source.mul(p, q)] != target.mul(image[p], image[q]):
                good = False
                break
        if good:
            return (X, Y)
    return None


def sub(R: FilteredRing, p, q):
    return R.add(p, R.neg_raw(q))


def coordinate_signature(R: FilteredRing, X, Y):
    """Full based-ring signature in coordinates functorially derived from X,Y.

    The first two independent elements among X^2,XY,Y^2 give the W lifts;
    the first nonzero V*W product gives the U lift.  This rule is preserved by
    every ring isomorphism.  Carries and all basis products then recover the
    complete addition and multiplication tables.
    """
    m3 = R.m3_set()
    candidates = (R.mul(X, X), R.mul(X, Y), R.mul(Y, Y))
    ws = []
    for w in candidates:
        if w in m3:
            continue
        if ws and sub(R, w, ws[0]) in m3:
            continue
        ws.append(w)
        if len(ws) == 2:
            break
    assert len(ws) == 2
    u = next(R.mul(v, w) for v in (X, Y) for w in ws
             if R.mul(v, w) != 0)
    assert u in m3 and u != 0
    basis = (1, X, Y, ws[0], ws[1], u)
    image = []
    for mask in ALL:
        z = 0
        for i in bit_indices(mask):
            z = R.add(z, basis[i])
        image.append(z)
    assert len(set(image)) == 64
    inverse = {z: mask for mask, z in enumerate(image)}
    carries = tuple(inverse[R.add(e, e)] for e in basis)
    products = tuple(inverse[R.mul(basis[i], basis[j])]
                     for i in range(N) for j in range(i, N))
    return carries + products, tuple(image)


def canonical_signature(R: FilteredRing):
    best = None
    best_data = None
    for X, Y in R.tangent_generating_pairs():
        sig, image = coordinate_signature(R, X, Y)
        if best is None or sig < best:
            best = sig
            best_data = (X, Y, image)
    assert best is not None
    return best, best_data


def validate_coordinate_isomorphism(A, Adata, B, Bdata):
    # Both based coordinate systems have the same complete structure code.
    Aimage, Bimage = Adata[2], Bdata[2]
    f = {Aimage[i]: Bimage[i] for i in ALL}
    assert len(f) == 64 and len(set(f.values())) == 64 and f[1] == 1
    for p, q in itertools.product(ALL, repeat=2):
        assert f[A.add(p, q)] == B.add(f[p], f[q])
        assert f[A.mul(p, q)] == B.mul(f[p], f[q])


class DSU:
    def __init__(self, n):
        self.p = list(range(n))

    def find(self, x):
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, x, y):
        x, y = self.find(x), self.find(y)
        if x != y:
            self.p[y] = x


def coarse_invariant(R: FilteredRing):
    R.build_tables()
    m = R.m_set()
    two = R.add(1, 1)
    ord2 = 99
    if two == 0:
        ord2 = 0
    elif two not in R.m2_set():
        ord2 = 1
    elif two not in R.m3_set():
        ord2 = 2
    else:
        ord2 = 3
    square_counts = tuple(sorted(
        sum(1 for z in m if R.mul(z, z) == value) for value in R.m3_set()
    ))
    annihilator_sizes = tuple(sorted(
        sum(1 for z in ALL if R.mul(a, z) == 0) for a in ALL
    ))
    element_orders = []
    for a in ALL:
        z = 0
        for n in range(1, 65):
            z = R.add(z, a)
            if z == 0:
                element_orders.append(n)
                break
    return (R.characteristic(), ord2, square_counts,
            tuple(sorted(element_orders)), annihilator_sizes)


def classify_isomorphism(rings):
    # First collapse literally equal 64-element tables.  Then compare only
    # equal coarse invariants; the final accepted relation never relies on
    # the invariant, because every witness is a fully checked table map.
    table_groups = {}
    for i, R in enumerate(rings):
        R.build_tables()
        sig = (tuple(map(tuple, R._add)), tuple(map(tuple, R._mul)))
        table_groups.setdefault(sig, []).append(i)
    representatives = [rings[ixs[0]] for ixs in table_groups.values()]
    presentation_multiplicities = [len(ixs) for ixs in table_groups.values()]
    print(f"LITERAL_TABLES {len(representatives)} from {len(rings)} valid adapted presentations")

    canonical = []
    classes = {}
    for i, R in enumerate(representatives):
        sig, data = canonical_signature(R)
        canonical.append((sig, data))
        classes.setdefault(sig, []).append(i)
    orbits = list(classes.values())
    # A complete based structure code proves nonisomorphism when canonical
    # minima differ.  For every positive identification, independently check
    # the induced bijection on all 64^2 pairs in both operations.
    positive_checks = 0
    for orbit in orbits:
        base = orbit[0]
        for j in orbit[1:]:
            validate_coordinate_isomorphism(representatives[base], canonical[base][1],
                                             representatives[j], canonical[j][1])
            positive_checks += 1
    print(f"CANONICAL_BASES {len(representatives)}*384; FULL_POSITIVE_ISO_CHECKS {positive_checks}; ISOMORPHISM_CLASSES {len(orbits)}")
    return representatives, orbits, presentation_multiplicities


def ring_summary(R: FilteredRing):
    two = R.add(1, 1)
    if two == 0:
        pos = "0"
    elif two not in R.m2_set():
        pos = "V"
    elif two not in R.m3_set():
        pos = "W"
    else:
        pos = "U"
    soc = sorted(a for a in R.m_set() if all(R.mul(a, b) == 0 for b in R.m_set()))
    return f"char={R.characteristic()} pos2={pos} two={two:02x} soc={','.join(f'{x:02x}' for x in soc)}"


class FormalLift:
    """Linearized top-layer arithmetic for all one-dimensional socle lifts."""

    def __init__(self, Q: FilteredRing):
        self.Q = Q
        self.nvars = 6 + len(LIFT_PAIRS)
        assert self.nvars == 18
        self.eps_index = {pair: 6 + i for i, pair in enumerate(LIFT_PAIRS)}

    @staticmethod
    def var(i):
        # Bit zero is the affine constant; variables begin at bit one.
        return 1 << (i + 1)

    def add_lower(self, p, q):
        cs = [((p >> i) & 1) + ((q >> i) & 1) for i in range(N)]
        top = 0
        for i in range(N):
            carry, cs[i] = divmod(cs[i], 2)
            if carry:
                for j in bit_indices(self.Q.d[i]):
                    cs[j] += carry
                if carry & 1:
                    top ^= self.var(i)
        return encode_coeffs(cs), top

    def add(self, z, w):
        p, s = z
        q, t = w
        lower, carry = self.add_lower(p, q)
        return lower, s ^ t ^ carry

    def basis_product(self, i, j):
        if i > j:
            i, j = j, i
        if i == 0:
            if j < N:
                return 1 << j, 0
            return 0, 1  # 1*top = top (affine constant)
        if j == 6:
            return 0, 0  # top is killed by the maximal ideal
        lower = self.Q._basis_mul[i][j]
        expr = self.var(self.eps_index[(i, j)]) if (i, j) in self.eps_index else 0
        return lower, expr

    def mul_lower(self, p, q):
        out = (0, 0)
        for i in bit_indices(p):
            for j in bit_indices(q):
                out = self.add(out, self.basis_product(i, j))
        return out

    def mul(self, z, w):
        p, s = z
        q, t = w
        lower, expr = self.mul_lower(p, q)
        if q & 1:
            expr ^= s
        if p & 1:
            expr ^= t
        return lower, expr

    @staticmethod
    def basis(i):
        return ((1 << i), 0) if i < N else (0, 1)

    def double_relation(self, i):
        if i < N:
            return self.Q.d[i], self.var(i)
        return 0, 0

    def equations(self):
        equations = []
        for i in range(LIFT_N):
            ei = self.basis(i)
            di = self.double_relation(i)
            for j in range(LIFT_N):
                ej = self.basis(j)
                lhs = self.add(self.mul(ei, ej), self.mul(ei, ej))
                rhs = self.mul(di, ej)
                assert lhs[0] == rhs[0]
                equations.append(lhs[1] ^ rhs[1])
        for i, j, k in itertools.product(range(LIFT_N), repeat=3):
            ei, ej, ek = self.basis(i), self.basis(j), self.basis(k)
            lhs = self.mul(self.mul(ei, ej), ek)
            rhs = self.mul(ei, self.mul(ej, ek))
            assert lhs[0] == rhs[0]
            equations.append(lhs[1] ^ rhs[1])
        return [e for e in equations if e]

    def socle_product_forms(self):
        soc = sorted(a for a in self.Q.m_set()
                     if all(self.Q.mul(a, b) == 0 for b in self.Q.m_set()))
        assert len(soc) == 4
        return soc, {a: tuple(self.mul((a, 0), self.basis(j))[1]
                              for j in range(1, N))
                     for a in soc}


def solve_affine_gf2(equations, nvars):
    """Return one solution and a nullspace basis, or None if inconsistent."""
    rows = []
    for expr in equations:
        coeff = expr >> 1
        rhs = expr & 1
        rows.append(coeff | (rhs << nvars))
    pivot_rows = {}
    for row in rows:
        coeff = row & ((1 << nvars) - 1)
        while coeff:
            p = coeff.bit_length() - 1
            if p not in pivot_rows:
                pivot_rows[p] = row
                break
            row ^= pivot_rows[p]
            coeff = row & ((1 << nvars) - 1)
        if not coeff and ((row >> nvars) & 1):
            return None
    # Reduce pivot columns from every other row, giving direct expressions.
    for p in sorted(pivot_rows):
        rowp = pivot_rows[p]
        for q in list(pivot_rows):
            if q != p and ((pivot_rows[q] >> p) & 1):
                pivot_rows[q] ^= rowp
    pivots = set(pivot_rows)
    free = [i for i in range(nvars) if i not in pivots]
    particular = 0
    for p, row in pivot_rows.items():
        if (row >> nvars) & 1:
            particular |= 1 << p
    nullspace = []
    for f in free:
        v = 1 << f
        for p, row in pivot_rows.items():
            if (row >> f) & 1:
                v |= 1 << p
        nullspace.append(v)
    # Direct audit of the returned affine parametrization.
    def satisfies(v):
        return all(((v & (e >> 1)).bit_count() & 1) == (e & 1)
                   for e in equations)
    assert satisfies(particular)
    assert all(satisfies(particular ^ v) for v in nullspace)
    return particular, nullspace, len(pivot_rows)


def eval_form(expr, assignment):
    return (expr & 1) ^ (((expr >> 1) & assignment).bit_count() & 1)


class ConcreteLift:
    def __init__(self, Q: FilteredRing, assignment: int):
        self.Q = Q
        self.assignment = assignment
        self.d = tuple(Q.d[i] | (TOP if ((assignment >> i) & 1) else 0)
                       for i in range(N)) + (0,)
        self.basis_mul = [[0] * LIFT_N for _ in range(LIFT_N)]
        for i in range(LIFT_N):
            self.basis_mul[0][i] = self.basis_mul[i][0] = 1 << i
        eps_index = {pair: 6 + k for k, pair in enumerate(LIFT_PAIRS)}
        for i in range(1, N):
            for j in range(i, N):
                base = Q._basis_mul[i][j]
                bit = ((assignment >> eps_index[(i, j)]) & 1) if (i, j) in eps_index else 0
                self.basis_mul[i][j] = self.basis_mul[j][i] = base | (bit << 6)
        self._add = self._mul = None

    def reduce(self, coeffs):
        cs = list(coeffs) + [0] * max(0, LIFT_N - len(coeffs))
        for i in range(LIFT_N):
            q, cs[i] = divmod(cs[i], 2)
            if q:
                for j in bit_indices(self.d[i]):
                    cs[j] += q
        return encode_coeffs(cs[:LIFT_N])

    def add_raw(self, p, q):
        return self.reduce([((p >> i) & 1) + ((q >> i) & 1)
                            for i in range(LIFT_N)])

    def mul_raw(self, p, q):
        out = 0
        for i in bit_indices(p):
            for j in bit_indices(q):
                out = self.add_raw(out, self.basis_mul[i][j])
        return out

    def build_tables(self):
        if self._add is None:
            self._add = [[self.add_raw(p, q) for q in LIFT_ALL] for p in LIFT_ALL]
            self._mul = [[self.mul_raw(p, q) for q in LIFT_ALL] for p in LIFT_ALL]

    def add(self, p, q):
        return self._add[p][q]

    def mul(self, p, q):
        return self._mul[p][q]


def validate_gorenstein_lift(Q, assignment, exhaustive=False):
    R = ConcreteLift(Q, assignment)
    R.build_tables()
    m = set(range(0, 128, 2))
    m2 = {z for z in LIFT_ALL if z & 0b0000111 == 0}
    m3 = {z for z in LIFT_ALL if z & 0b0011111 == 0}
    m4 = {0, TOP}

    def closure(seed):
        out = {0}
        changed = True
        while changed:
            changed = False
            for a in tuple(out):
                for b in seed:
                    c = R.add(a, b)
                    if c not in out:
                        out.add(c)
                        changed = True
        return out

    generated2 = closure([R.mul(a, b) for a in m for b in m])
    generated3 = closure([R.mul(a, b) for a in m for b in m2])
    generated4 = closure([R.mul(a, b) for a in m for b in m3])
    assert generated2 == m2 and generated3 == m3 and generated4 == m4
    assert all(R.mul(a, b) == 0 for a in m for b in m4)
    soc = {a for a in m if all(R.mul(a, b) == 0 for b in m)}
    assert soc == m4
    # Quotient by top is exactly Q, on every pair, not just on basis products.
    for a, b in itertools.product(LIFT_ALL, repeat=2):
        assert (R.add(a, b) & 63) == Q.add(a & 63, b & 63)
        assert (R.mul(a, b) & 63) == Q.mul(a & 63, b & 63)
    if exhaustive:
        for a, b, c in itertools.product(LIFT_ALL, repeat=3):
            assert R.add(R.add(a, b), c) == R.add(a, R.add(b, c))
            assert R.mul(R.mul(a, b), c) == R.mul(a, R.mul(b, c))
            assert R.mul(a, R.add(b, c)) == R.add(R.mul(a, b), R.mul(a, c))
    return R


def gorenstein_lift_data(Q: FilteredRing):
    formal = FormalLift(Q)
    equations = formal.equations()
    solved = solve_affine_gf2(equations, formal.nvars)
    assert solved is not None
    particular, nullspace, rank = solved
    soc, product_forms = formal.socle_product_forms()
    total = 1 << len(nullspace)
    good = []
    for mask in range(total):
        assignment = particular
        for i, v in enumerate(nullspace):
            if (mask >> i) & 1:
                assignment ^= v
        injective = True
        for a in soc:
            if a == 0:
                continue
            if not any(eval_form(expr, assignment) for expr in product_forms[a]):
                injective = False
                break
        if injective:
            good.append(assignment)
    if good:
        validate_gorenstein_lift(Q, good[0], exhaustive=True)
    return {"rank": rank, "dimension": len(nullspace), "extensions": total,
            "gorenstein": len(good), "witness": good[0] if good else None}


def main():
    started = time.monotonic()
    print("LENGTH6 H=(1,2,2,1) TYPE2 EXACT ORBIT ENUMERATION")
    compatible_count, compatible_orbit_sizes = compatible_form_orbits()
    print(f"COMPATIBLE_FORMS {compatible_count}; GL2xGL2_ORBITS 2 sizes={compatible_orbit_sizes} -> A,B")
    rings, total = enumerate_presentations()
    print(f"RAW_SEARCH {total}; VALID_ADAPTED_PRESENTATIONS {len(rings)} ({time.monotonic()-started:.2f}s)")
    # Full arithmetic gates on every retained presentation are redundant but
    # deliberately independent of the basis-only search gate.
    for R in rings:
        validate_ring(R)
    print(f"[64-element structural arithmetic gates] {len(rings)}/{len(rings)} PASS")
    reps, orbits, mults = classify_isomorphism(rings)
    ordered = sorted(orbits, key=lambda o: (coarse_invariant(reps[o[0]]), reps[o[0]].label))
    lift_results = []
    for n, orbit in enumerate(ordered, 1):
        R = reps[orbit[0]]
        adapted_count = sum(mults[i] for i in orbit)
        print(f"Q{n:02d} {ring_summary(R)} literal_tables={len(orbit)} adapted_presentations={adapted_count}")
        print(f"  representative {R.label}")
        lift = gorenstein_lift_data(R)
        lift_results.append(lift)
        print(f"  SOCLE_LIFTS linear_rank={lift['rank']} affine_dim={lift['dimension']} all={lift['extensions']} gorenstein={lift['gorenstein']} witness={lift['witness']}")
    liftable = sum(1 for x in lift_results if x["gorenstein"])
    print(f"GORENSTEIN_LIFTABLE {liftable}/{len(ordered)}")
    print(f"DONE quotient_classes={len(ordered)} liftable={liftable} elapsed={time.monotonic()-started:.2f}s")


if __name__ == "__main__":
    main()
