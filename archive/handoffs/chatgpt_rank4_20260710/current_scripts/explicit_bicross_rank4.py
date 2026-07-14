#!/usr/bin/env python3
"""Symbolic equations for a two-sided Oort--Tate cross-coproduct ansatz.

Run with ``python3 scripts/explicit_bicross_rank4.py``.  The coordinate algebra is

    A = R[x,y]/(x^2-a*x, y^2-c*y),

and the proposed coproduct is

    Dx = x1+x2-b*x1*x2+p*y1*x2,
    Dy = y1+y2-d*y1*y2+q*x1*y2.

Here a*b=c*d=2 in the undeformed Oort--Tate factors.  The script reduces the
relation-preservation and coassociativity defects in the free R-bases of
A^tensor 2 and A^tensor 3.  It also computes the pointwise square and fourth
power maps.  This is a deliberately small explicit family, not the general
rank-four search.
"""

NAMES = ("a", "b", "c", "d", "p", "q", "r", "s", "u", "v")


class P:
    """Tiny multivariate polynomial class over Z (keeps this script dependency-free)."""

    def __init__(self, terms=None):
        if isinstance(terms, P):
            self.terms = dict(terms.terms)
        elif isinstance(terms, int):
            self.terms = {} if terms == 0 else {(0,) * len(NAMES): terms}
        elif terms is None:
            self.terms = {}
        else:
            self.terms = {m: int(v) for m, v in terms.items() if v}

    @staticmethod
    def variable(index):
        exponent = [0] * len(NAMES)
        exponent[index] = 1
        return P({tuple(exponent): 1})

    def _coerce(self, other):
        return other if isinstance(other, P) else P(other)

    def __bool__(self):
        return bool(self.terms)

    def __eq__(self, other):
        return self.terms == self._coerce(other).terms

    def __add__(self, other):
        other = self._coerce(other)
        out = dict(self.terms)
        for monomial, coeff in other.terms.items():
            out[monomial] = out.get(monomial, 0) + coeff
            if out[monomial] == 0:
                del out[monomial]
        return P(out)

    __radd__ = __add__

    def __neg__(self):
        return P({m: -v for m, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other) - self

    def __mul__(self, other):
        if not isinstance(other, (P, int)):
            return NotImplemented
        other = self._coerce(other)
        out = {}
        for m1, v1 in self.terms.items():
            for m2, v2 in other.terms.items():
                monomial = tuple(i + j for i, j in zip(m1, m2))
                out[monomial] = out.get(monomial, 0) + v1 * v2
        return P(out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        ans = P(1)
        base = self
        while exponent:
            if exponent & 1:
                ans *= base
            base *= base
            exponent //= 2
        return ans

    def __str__(self):
        if not self.terms:
            return "0"
        pieces = []
        # Highest total degree first, then lexicographically.
        for monomial, coeff in sorted(
            self.terms.items(), key=lambda item: (sum(item[0]), item[0]), reverse=True
        ):
            factors = []
            for name, exponent in zip(NAMES, monomial):
                if exponent == 1:
                    factors.append(name)
                elif exponent:
                    factors.append(f"{name}^{exponent}")
            monomial_text = "*".join(factors)
            magnitude = abs(coeff)
            if monomial_text:
                term = monomial_text if magnitude == 1 else f"{magnitude}*{monomial_text}"
            else:
                term = str(magnitude)
            if not pieces:
                pieces.append(("-" if coeff < 0 else "") + term)
            else:
                pieces.append((" - " if coeff < 0 else " + ") + term)
        return "".join(pieces)


a, b, c, d, p, q, r, s, u, v = (P.variable(i) for i in range(len(NAMES)))


class E:
    """Element of the tensor power, in basis {1,x,y,xy} in each slot."""

    def __init__(self, n, terms=None):
        self.n = n
        self.terms = {m: P(v) for m, v in (terms or {}).items() if P(v)}

    @staticmethod
    def scalar(n, value):
        return E(n, {(0,) * n: P(value)})

    @staticmethod
    def generator(n, slot, mask):
        monomial = [0] * n
        monomial[slot] = mask
        return E(n, {tuple(monomial): P(1)})

    def _coerce(self, other):
        return other if isinstance(other, E) else E.scalar(self.n, other)

    def __add__(self, other):
        other = self._coerce(other)
        out = dict(self.terms)
        for monomial, coeff in other.terms.items():
            out[monomial] = out.get(monomial, P()) + coeff
            if out[monomial] == 0:
                del out[monomial]
        return E(self.n, out)

    __radd__ = __add__

    def __neg__(self):
        return E(self.n, {m: -v for m, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other) - self

    def __mul__(self, other):
        other = self._coerce(other)
        out = {}
        for m1, v1 in self.terms.items():
            for m2, v2 in other.terms.items():
                scalar = v1 * v2
                monomial = []
                for s1, s2 in zip(m1, m2):
                    if (s1 & 1) and (s2 & 1):
                        scalar *= a
                    if (s1 & 2) and (s2 & 2):
                        scalar *= c
                    monomial.append(s1 | s2)
                monomial = tuple(monomial)
                out[monomial] = out.get(monomial, P()) + scalar
        return E(self.n, out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        ans = E.scalar(self.n, 1)
        base = self
        while exponent:
            if exponent & 1:
                ans *= base
            base *= base
            exponent //= 2
        return ans

    def map_generators(self, images):
        """Apply an algebra map specified by images[(slot, 'x'/'y')]."""
        target_n = next(iter(images.values())).n
        ans = E(target_n)
        for monomial, coeff in self.terms.items():
            term = E.scalar(target_n, coeff)
            for slot, mask in enumerate(monomial):
                if mask & 1:
                    term *= images[(slot, "x")]
                if mask & 2:
                    term *= images[(slot, "y")]
            ans += term
        return ans


def gens(n):
    ans = []
    for slot in range(n):
        ans += [E.generator(n, slot, 1), E.generator(n, slot, 2)]
    return ans


def coproduct_pair(x1, y1, x2, y2):
    dx = x1 + x2 - b * x1 * x2 + p * y1 * x2
    dy = y1 + y2 - d * y1 * y2 + q * x1 * y2
    return dx, dy


def coproduct_general(x1, y1, x2, y2):
    """All cross-terms bilinear in x,y, retaining the two OT diagonal terms."""
    dx = (
        x1
        + x2
        - b * x1 * x2
        + p * y1 * x2
        + r * x1 * y2
        + u * y1 * y2
    )
    dy = (
        y1
        + y2
        - d * y1 * y2
        + q * x1 * y2
        + s * y1 * x2
        + v * x1 * x2
    )
    return dx, dy


def defects():
    x1, y1, x2, y2 = gens(2)
    dx, dy = coproduct_pair(x1, y1, x2, y2)
    relation_x = dx**2 - a * dx
    relation_y = dy**2 - c * dy

    x1, y1, x2, y2, x3, y3 = gens(3)
    dx12, dy12 = coproduct_pair(x1, y1, x2, y2)
    dx23, dy23 = coproduct_pair(x2, y2, x3, y3)
    left_x, left_y = coproduct_pair(dx12, dy12, x3, y3)
    right_x, right_y = coproduct_pair(x1, y1, dx23, dy23)
    coassoc_x = left_x - right_x
    coassoc_y = left_y - right_y

    # Multiplication m: A tensor A -> A.
    x, y = gens(1)
    multiplication = {
        (0, "x"): x,
        (0, "y"): y,
        (1, "x"): x,
        (1, "y"): y,
    }
    phi_x = dx.map_generators(multiplication)
    phi_y = dy.map_generators(multiplication)
    phi = {(0, "x"): phi_x, (0, "y"): phi_y}
    phi4_x = phi_x.map_generators(phi)
    phi4_y = phi_y.map_generators(phi)
    return relation_x, relation_y, coassoc_x, coassoc_y, phi_x, phi_y, phi4_x, phi4_y


def general_defects():
    x1, y1, x2, y2 = gens(2)
    dx, dy = coproduct_general(x1, y1, x2, y2)
    relation_x = dx**2 - a * dx
    relation_y = dy**2 - c * dy

    x1, y1, x2, y2, x3, y3 = gens(3)
    dx12, dy12 = coproduct_general(x1, y1, x2, y2)
    dx23, dy23 = coproduct_general(x2, y2, x3, y3)
    left_x, left_y = coproduct_general(dx12, dy12, x3, y3)
    right_x, right_y = coproduct_general(x1, y1, dx23, dy23)
    coassoc_x = left_x - right_x
    coassoc_y = left_y - right_y

    x, y = gens(1)
    multiplication = {
        (0, "x"): x,
        (0, "y"): y,
        (1, "x"): x,
        (1, "y"): y,
    }
    phi_x = dx.map_generators(multiplication)
    phi_y = dy.map_generators(multiplication)
    phi = {(0, "x"): phi_x, (0, "y"): phi_y}
    phi4_x = phi_x.map_generators(phi)
    phi4_y = phi_y.map_generators(phi)
    return relation_x, relation_y, coassoc_x, coassoc_y, phi_x, phi_y, phi4_x, phi4_y


def basis_name(monomial):
    slots = []
    for slot, mask in enumerate(monomial, 1):
        name = "1"
        if mask == 1:
            name = f"x{slot}"
        elif mask == 2:
            name = f"y{slot}"
        elif mask == 3:
            name = f"x{slot}y{slot}"
        slots.append(name)
    return " * ".join(slots)


def show(label, element):
    print(f"\n{label}")
    if not element.terms:
        print("  0")
    else:
        for monomial, coeff in sorted(element.terms.items()):
            print(f"  {basis_name(monomial):24s}: {coeff}")


def main():
    rx, ry, cx, cy, phi_x, phi_y, phi4_x, phi4_y = defects()
    show("relation defect for x", rx)
    show("relation defect for y", ry)
    show("coassociativity defect for x", cx)
    show("coassociativity defect for y", cy)
    show("pointwise square phi(x)", phi_x)
    show("pointwise square phi(y)", phi_y)
    show("pointwise fourth power phi^2(x)", phi4_x)
    show("pointwise fourth power phi^2(y)", phi4_y)

    print("\n" + "=" * 78)
    print("GENERAL BILINEAR CROSS ANSATZ")
    print("=" * 78)
    rx, ry, cx, cy, phi_x, phi_y, phi4_x, phi4_y = general_defects()
    show("general relation defect for x", rx)
    show("general relation defect for y", ry)
    show("general coassociativity defect for x", cx)
    show("general coassociativity defect for y", cy)
    show("general pointwise square phi(x)", phi_x)
    show("general pointwise square phi(y)", phi_y)
    show("general pointwise fourth power phi^2(x)", phi4_x)
    show("general pointwise fourth power phi^2(y)", phi4_y)


if __name__ == "__main__":
    main()
