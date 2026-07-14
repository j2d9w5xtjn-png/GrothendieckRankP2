#!/usr/bin/env python3
"""Audit exact eliminations in the universal rank-four bialgebra chart.

This is a dependency-free mirror of the equation generator in
``m2/universal_local_rank4.m2``.  It does *not* compute a Groebner basis.
Instead it repeatedly uses equations of the form

    x_i + g(other variables) = 0

(up to sign) to eliminate ``x_i`` by exact polynomial substitution.  Such an
elimination is an isomorphism of the global quotient over ZZ, hence is safe
before localization at (2, all deformation variables).

The script is deliberately an audit/experiment kept separate from the main
Macaulay2 source.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from functools import reduce
from math import gcd
from typing import Dict, Iterable, List, Sequence, Tuple


Monomial = Tuple[int, ...]


@dataclass(frozen=True)
class Poly:
    terms: Tuple[Tuple[Monomial, int], ...]

    @staticmethod
    def from_dict(data: Dict[Monomial, int]) -> "Poly":
        return Poly(tuple(sorted((m, c) for m, c in data.items() if c)))

    @staticmethod
    def const(c: int) -> "Poly":
        return Poly(()) if c == 0 else Poly((((), c),))

    @staticmethod
    def var(i: int) -> "Poly":
        return Poly((((i,), 1),))

    def as_dict(self) -> Dict[Monomial, int]:
        return dict(self.terms)

    def __bool__(self) -> bool:
        return bool(self.terms)

    def __neg__(self) -> "Poly":
        return Poly(tuple((m, -c) for m, c in self.terms))

    def __add__(self, other: "Poly | int") -> "Poly":
        other = as_poly(other)
        out = self.as_dict()
        for m, c in other.terms:
            out[m] = out.get(m, 0) + c
        return Poly.from_dict(out)

    def __radd__(self, other: "Poly | int") -> "Poly":
        return self + other

    def __sub__(self, other: "Poly | int") -> "Poly":
        return self + (-as_poly(other))

    def __rsub__(self, other: "Poly | int") -> "Poly":
        return as_poly(other) - self

    def __mul__(self, other: "Poly | int") -> "Poly":
        other = as_poly(other)
        if not self or not other:
            return ZERO
        out: Dict[Monomial, int] = {}
        for m, c in self.terms:
            for n, d in other.terms:
                mn = tuple(sorted(m + n))
                out[mn] = out.get(mn, 0) + c * d
        return Poly.from_dict(out)

    def __rmul__(self, other: "Poly | int") -> "Poly":
        return self * other

    def degree(self) -> int:
        return max((len(m) for m, _ in self.terms), default=-1)

    def variables(self) -> set[int]:
        return {i for m, _ in self.terms for i in m}

    def constant(self) -> int:
        return dict(self.terms).get((), 0)

    def coefficient_of_bare_var(self, i: int) -> int:
        return dict(self.terms).get((i,), 0)

    def has_other_occurrence(self, i: int) -> bool:
        return any(i in m and m != (i,) for m, _ in self.terms)

    def split_linear_in(self, i: int) -> Tuple["Poly", "Poly"] | None:
        """Return (coefficient, remainder) if the degree in x_i is at most one."""
        coeff: Dict[Monomial, int] = {}
        rest: Dict[Monomial, int] = {}
        for m, c in self.terms:
            power = m.count(i)
            if power > 1:
                return None
            if power == 1:
                residual = tuple(j for j in m if j != i)
                coeff[residual] = coeff.get(residual, 0) + c
            else:
                rest[m] = rest.get(m, 0) + c
        return Poly.from_dict(coeff), Poly.from_dict(rest)

    def substitute(self, i: int, value: "Poly") -> "Poly":
        out = ZERO
        powers = [ONE]
        max_power = max((m.count(i) for m, _ in self.terms), default=0)
        for _ in range(max_power):
            powers.append(powers[-1] * value)
        for m, c in self.terms:
            power = m.count(i)
            residual = tuple(j for j in m if j != i)
            out = out + Poly(((residual, c),)) * powers[power]
        return out

    def primitive_signed(self) -> "Poly":
        """Canonicalize by integer content and the first coefficient's sign."""
        if not self:
            return self
        content = reduce(gcd, (abs(c) for _, c in self.terms))
        data = [(m, c // content) for m, c in self.terms]
        if data[0][1] < 0:
            data = [(m, -c) for m, c in data]
        return Poly(tuple(data))

    def local_signed(self) -> "Poly":
        """Canonicalize by a unit in ZZ_(2): sign and odd integer content."""
        if not self:
            return self
        content = reduce(gcd, (abs(c) for _, c in self.terms))
        odd_content = content
        while odd_content and odd_content % 2 == 0:
            odd_content //= 2
        data = [(m, c // odd_content) for m, c in self.terms]
        if data[0][1] < 0:
            data = [(m, -c) for m, c in data]
        return Poly(tuple(data))


def as_poly(value: Poly | int) -> Poly:
    return value if isinstance(value, Poly) else Poly.const(value)


ZERO = Poly.const(0)
ONE = Poly.const(1)
X = [Poly.var(i) for i in range(45)]


def unique_nonzero(polys: Iterable[Poly], canonical_sign: bool = False) -> List[Poly]:
    seen = set()
    out = []
    for f in polys:
        if not f:
            continue
        key = f.local_signed() if canonical_sign else f
        if key not in seen:
            seen.add(key)
            out.append(f)
    return out


def pair_position(a: int, b: int) -> int:
    u, v = sorted((a, b))
    if u == 1:
        return v - 1
    if u == 2:
        return v + 1
    return 5


def mvar(i: int, j: int, r: int) -> Poly:
    return X[3 * pair_position(i, j) + r - 1]


def cvar(i: int, j: int, k: int) -> Poly:
    return X[18 + 9 * (i - 1) + 3 * (j - 1) + k - 1]


def ebas(i: int) -> List[Poly]:
    return [ONE if r == i else ZERO for r in range(4)]


def idx2(a: int, b: int) -> int:
    return 4 * a + b


def idx3(a: int, b: int, c: int) -> int:
    return 16 * a + 4 * b + c


def build(branch: int):
    is_t4 = branch >= 2
    t4_code = branch - 2 if is_t4 else 0
    c1bit = t4_code // 2 if is_t4 else 0
    c4bit = t4_code % 2 if is_t4 else 0
    fiber_mul = {(1, 1, 2), (1, 2, 3)} if is_t4 else {(1, 2, 3)}

    def pin_cop(i: int, j: int, k: int) -> int:
        if not is_t4:
            if (i, j, k) in {(3, 1, 2), (3, 2, 1)}:
                return 1
            if branch == 1 and (i, j, k) == (2, 1, 1):
                return 1
            return 0
        if i == 1:
            if (j, k) in {(1, 2), (2, 1), (2, 3), (3, 2)}:
                return c1bit
            if (j, k) == (2, 2):
                return c4bit
            return 0
        if i == 2:
            return 0
        if (j, k) in {(1, 2), (2, 1)}:
            return 1
        if (j, k) in {(2, 3), (3, 2)}:
            return c1bit
        return 0

    def mc(i: int, j: int, r: int) -> Poly:
        return int((min(i, j), max(i, j), r) in fiber_mul) + mvar(i, j, r)

    def cc(i: int, j: int, k: int) -> Poly:
        return pin_cop(i, j, k) + cvar(i, j, k)

    stab = {}
    for a in range(4):
        for b in range(4):
            if a == 0:
                stab[a, b] = ebas(b)
            elif b == 0:
                stab[a, b] = ebas(a)
            else:
                stab[a, b] = [ZERO, mc(a, b, 1), mc(a, b, 2), mc(a, b, 3)]

    delta = []
    for i in range(4):
        if i == 0:
            delta.append([ONE] + [ZERO] * 15)
            continue
        v = [ZERO] * 16
        v[idx2(i, 0)] = ONE
        v[idx2(0, i)] = ONE
        for j in range(1, 4):
            for k in range(1, 4):
                v[idx2(j, k)] = cc(i, j, k)
        delta.append(v)

    def mul_a(u: Sequence[Poly], v: Sequence[Poly]) -> List[Poly]:
        out = [ZERO] * 4
        for i in range(4):
            for j in range(4):
                for r in range(4):
                    out[r] = out[r] + u[i] * v[j] * stab[i, j][r]
        return out

    def d_vec(v: Sequence[Poly]) -> List[Poly]:
        out = [ZERO] * 16
        for r in range(4):
            for t in range(16):
                out[t] = out[t] + v[r] * delta[r][t]
        return out

    def mul_t2(u: Sequence[Poly], v: Sequence[Poly]) -> List[Poly]:
        out = [ZERO] * 16
        for a in range(4):
            for b in range(4):
                for aa in range(4):
                    for bb in range(4):
                        uv = u[idx2(a, b)] * v[idx2(aa, bb)]
                        for r in range(4):
                            for s in range(4):
                                out[idx2(r, s)] = (
                                    out[idx2(r, s)]
                                    + uv * stab[a, aa][r] * stab[b, bb][s]
                                )
        return out

    assoc_raw = []
    for i in range(1, 4):
        for j in range(1, 4):
            for k in range(1, 4):
                left = mul_a(stab[i, j], ebas(k))
                right = mul_a(ebas(i), stab[j, k])
                assoc_raw.extend(left[r] - right[r] for r in range(1, 4))

    compat_raw = []
    for i in range(1, 4):
        for j in range(i, 4):
            left = d_vec(stab[i, j])
            right = mul_t2(delta[i], delta[j])
            compat_raw.extend(
                left[idx2(r, s)] - right[idx2(r, s)]
                for r in range(1, 4)
                for s in range(1, 4)
            )

    coassoc_raw = []
    for i in range(1, 4):
        left = [ZERO] * 64
        right = [ZERO] * 64
        for r in range(4):
            for s in range(4):
                u = delta[i][idx2(r, s)]
                for a in range(4):
                    for b in range(4):
                        left[idx3(a, b, s)] = (
                            left[idx3(a, b, s)] + u * delta[r][idx2(a, b)]
                        )
                for b in range(4):
                    for c in range(4):
                        right[idx3(r, b, c)] = (
                            right[idx3(r, b, c)] + u * delta[s][idx2(b, c)]
                        )
        coassoc_raw.extend(
            left[idx3(a, b, c)] - right[idx3(a, b, c)]
            for a in range(1, 4)
            for b in range(1, 4)
            for c in range(1, 4)
        )

    phi = [ebas(0)]
    for i in range(1, 4):
        out = [ZERO] * 4
        for j in range(4):
            for k in range(4):
                for r in range(4):
                    out[r] = out[r] + delta[i][idx2(j, k)] * stab[j, k][r]
        phi.append(out)

    p4 = []
    for i in range(1, 4):
        out = [ZERO] * 4
        for r in range(1, 4):
            for s in range(1, 4):
                out[s] = out[s] + phi[i][r] * phi[r][s]
        p4.append(out)

    assoc = unique_nonzero(assoc_raw)
    compat = unique_nonzero(compat_raw)
    coassoc = unique_nonzero(coassoc_raw)
    eqs = unique_nonzero(assoc + compat + coassoc)
    targets = [p4[i][r] for i in range(3) for r in range(1, 4)]
    return (assoc, compat, coassoc), eqs, targets


def direct_unit_candidates(eqs: Sequence[Poly], active: set[int]):
    candidates = []
    occurrence = {i: 0 for i in active}
    for f in eqs:
        for i in f.variables() & active:
            occurrence[i] += 1
    for row, f in enumerate(eqs):
        for i in f.variables() & active:
            c = f.coefficient_of_bare_var(i)
            if abs(c) == 1 and not f.has_other_occurrence(i):
                g = f - c * X[i]
                score = (len(g.terms) * max(1, occurrence[i] - 1), len(g.terms), g.degree())
                candidates.append((score, row, i, c, g))
    return sorted(candidates, key=lambda z: z[0])


def local_unit_candidates(eqs: Sequence[Poly], active: set[int]):
    candidates = []
    occurrence = {i: 0 for i in active}
    for f in eqs:
        for i in f.variables() & active:
            occurrence[i] += 1
    for row, f in enumerate(eqs):
        for i in f.variables() & active:
            split = f.split_linear_in(i)
            if split is None:
                continue
            coefficient, remainder = split
            if coefficient.constant() % 2:
                score = (
                    len(coefficient.terms) * len(remainder.terms)
                    * max(1, occurrence[i] - 1),
                    len(coefficient.terms),
                    len(remainder.terms),
                )
                candidates.append((score, row, i, coefficient, remainder))
    return sorted(candidates, key=lambda z: z[0])


def eliminate(eqs: List[Poly], targets: List[Poly], limit: int):
    active = set(range(45))
    history = []
    for step in range(limit):
        candidates = direct_unit_candidates(eqs, active)
        if not candidates:
            break
        score, row, i, c, g = candidates[0]
        value = -c * g  # c is +1 or -1, so x_i = -g/c = -c*g.
        old_terms = sum(len(f.terms) for f in eqs)
        new_eqs = []
        for j, f in enumerate(eqs):
            if j == row:
                continue
            new_eqs.append(f.substitute(i, value))
        eqs = unique_nonzero(new_eqs, canonical_sign=True)
        targets = [f.substitute(i, value) for f in targets]
        active.remove(i)
        new_terms = sum(len(f.terms) for f in eqs)
        history.append(
            {
                "step": step + 1,
                "variable": i,
                "def_terms": len(g.terms),
                "def_degree": g.degree(),
                "equations": len(eqs),
                "terms_before": old_terms,
                "terms_after": new_terms,
                "max_degree": max((f.degree() for f in eqs), default=-1),
            }
        )
    return eqs, targets, active, history


def substitute_fraction_clear(f: Poly, i: int, numerator: Poly, denominator: Poly) -> Poly:
    """Numerator of f(...,x_i=numerator/denominator,...) with a unit denominator."""
    max_power = max((m.count(i) for m, _ in f.terms), default=0)
    num_powers = [ONE]
    den_powers = [ONE]
    for _ in range(max_power):
        num_powers.append(num_powers[-1] * numerator)
        den_powers.append(den_powers[-1] * denominator)
    out = ZERO
    for m, c in f.terms:
        power = m.count(i)
        residual = tuple(j for j in m if j != i)
        term = Poly(((residual, c),))
        out = out + term * num_powers[power] * den_powers[max_power - power]
    return out.local_signed()


def eliminate_local(eqs: List[Poly], targets: List[Poly], limit: int):
    """Eliminate variables whose coefficient is a unit at (2,x_0,...,x_44)."""
    active = set(range(45))
    history = []
    for step in range(limit):
        candidates = local_unit_candidates(eqs, active)
        if not candidates:
            break
        score, row, i, coefficient, remainder = candidates[0]
        numerator = -remainder
        denominator = coefficient
        assert denominator.constant() % 2
        old_terms = sum(len(f.terms) for f in eqs)
        new_eqs = []
        for j, f in enumerate(eqs):
            if j == row:
                continue
            new_eqs.append(
                substitute_fraction_clear(f, i, numerator, denominator)
            )
        eqs = unique_nonzero(new_eqs, canonical_sign=True)
        targets = [
            substitute_fraction_clear(f, i, numerator, denominator)
            for f in targets
        ]
        active.remove(i)
        new_terms = sum(len(f.terms) for f in eqs)
        history.append(
            {
                "step": step + 1,
                "variable": i,
                "coefficient_terms": len(coefficient.terms),
                "coefficient_degree": coefficient.degree(),
                "remainder_terms": len(remainder.terms),
                "remainder_degree": remainder.degree(),
                "equations": len(eqs),
                "terms_before": old_terms,
                "terms_after": new_terms,
                "max_degree": max((f.degree() for f in eqs), default=-1),
            }
        )
    return eqs, targets, active, history


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--branch", type=int, choices=range(6), default=0)
    parser.add_argument("--limit", type=int, default=45)
    parser.add_argument("--local-eliminate", action="store_true")
    args = parser.parse_args()

    categories, eqs, targets = build(args.branch)
    print(
        "branch", args.branch,
        "category_unique", tuple(len(v) for v in categories),
        "equations", len(eqs),
        "equation_terms", sum(len(f.terms) for f in eqs),
        "max_degree", max(f.degree() for f in eqs),
        "target_terms", sum(len(f.terms) for f in targets),
        "target_max_degree", max(f.degree() for f in targets),
    )
    local_candidates = local_unit_candidates(eqs, set(range(45)))
    print(
        "INITIAL_LOCAL_UNIT_CANDIDATES",
        len(local_candidates),
        "distinct_variables",
        len({item[2] for item in local_candidates}),
    )
    for score, row, i, coefficient, remainder in local_candidates[:12]:
        print(
            "LOCAL_CANDIDATE",
            f"row={row}",
            f"x{i}",
            f"coefficient_terms={len(coefficient.terms)}",
            f"coefficient_degree={coefficient.degree()}",
            f"remainder_terms={len(remainder.terms)}",
            f"remainder_degree={remainder.degree()}",
            f"score={score}",
        )
    if args.local_eliminate:
        reduced_eqs, reduced_targets, active, history = eliminate_local(
            eqs, targets, args.limit
        )
    else:
        reduced_eqs, reduced_targets, active, history = eliminate(
            eqs, targets, args.limit
        )
    for item in history:
        print(
            "LOCAL_ELIM" if args.local_eliminate else "ELIM",
            item["step"],
            f"x{item['variable']}",
            f"def_terms={item.get('def_terms', item.get('remainder_terms'))}",
            f"def_degree={item.get('def_degree', item.get('remainder_degree'))}",
            f"unit_terms={item.get('coefficient_terms', 1)}",
            f"unit_degree={item.get('coefficient_degree', 0)}",
            f"eqs={item['equations']}",
            f"terms={item['terms_before']}->{item['terms_after']}",
            f"max_degree={item['max_degree']}",
        )
    print(
        "RESULT",
        f"eliminated={45-len(active)}",
        f"active={len(active)}",
        f"equations={len(reduced_eqs)}",
        f"equation_terms={sum(len(f.terms) for f in reduced_eqs)}",
        f"max_degree={max((f.degree() for f in reduced_eqs), default=-1)}",
        f"target_terms={sum(len(f.terms) for f in reduced_targets)}",
        f"target_max_degree={max((f.degree() for f in reduced_targets), default=-1)}",
        "active_variables=" + ",".join(f"x{i}" for i in sorted(active)),
    )


if __name__ == "__main__":
    main()
