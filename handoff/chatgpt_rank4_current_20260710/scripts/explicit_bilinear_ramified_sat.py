#!/usr/bin/env python3
"""Exact SAT search in an explicit bilinear Oort--Tate rank-four family.

Base: R_N = Z[pi]/(pi^2-2, pi^N), residue field F_2.  The algebra is

    A = R_N[x,y]/(x^2-pi*x, y^2+2*y),

the tensor product of the alpha-type Oort--Tate factor (a=b=pi) and mu_2.
Starting from their product coproduct, all six off-diagonal bilinear cross
terms are allowed:

 Dx = x1+x2-pi*x1*x2 + p*y1*x2+r*x1*y2+u*y1*y2,
 Dy = y1+y2+y1*y2     + q*x1*y2+s*y1*x2+v*x1*x2.

All p,q,r,s,u,v lie in (pi), so the special fiber is alpha_2 x mu_2.
The script imposes preservation of both algebra relations and full
coassociativity, and asks directly whether [4]^# is nontrivial.  A SAT answer
would only be a counterexample inside this explicit family; UNSAT excludes the
family over the exact indicated R_N.
"""

from __future__ import annotations

import argparse

from z3 import And, BitVec, BitVecVal, Extract, Or, Solver, ZeroExt, sat


class RamifiedQuadratic:
    """R_N = Z[pi]/(pi^2-2,pi^N), as A+B*pi with exact bit widths."""

    def __init__(self, N):
        assert N >= 2
        self.N = N
        self.wa = (N + 1) // 2
        self.wb = N // 2
        self.name = f"Z[pi]/(pi^2-2,pi^{N})"
        self._fresh = 0

    def zero(self):
        return BitVecVal(0, self.wa), BitVecVal(0, self.wb)

    def integer(self, value):
        return BitVecVal(value, self.wa), BitVecVal(0, self.wb)

    def one(self):
        return self.integer(1)

    def pi(self):
        return BitVecVal(0, self.wa), BitVecVal(1, self.wb)

    def ot_a(self):
        return self.pi()

    def ot_b(self):
        return self.pi()

    def var(self, tag):
        self._fresh += 1
        name = f"{tag}_{self._fresh}"
        return BitVec(name + "_a", self.wa), BitVec(name + "_b", self.wb)

    def add(self, x, y):
        return x[0] + y[0], x[1] + y[1]

    def neg(self, x):
        return -x[0], -x[1]

    def sub(self, x, y):
        return x[0] - y[0], x[1] - y[1]

    def mul(self, x, y):
        xa, xb = x
        ya, yb = y
        xb_wide = ZeroExt(self.wa - self.wb, xb)
        yb_wide = ZeroExt(self.wa - self.wb, yb)
        constant = xa * ya + 2 * xb_wide * yb_wide
        xa_low = xa if self.wa == self.wb else Extract(self.wb - 1, 0, xa)
        ya_low = ya if self.wa == self.wb else Extract(self.wb - 1, 0, ya)
        pi_coeff = xa_low * yb + xb * ya_low
        return constant, pi_coeff

    def eq0(self, x):
        return And(x[0] == 0, x[1] == 0)

    def neq0(self, x):
        return Or(x[0] != 0, x[1] != 0)

    def in_maximal_ideal(self, x):
        return (x[0] & 1) == 0

    # Compatibility aliases for scripts/order4sat.py's ring interface.
    lowzero = in_maximal_ideal

    def deform(self, tag):
        return self.mul(self.pi(), self.var(tag))


class RamifiedEisenstein:
    """R_{e,N}=Z[pi]/(pi^e-2,pi^N), with an OT split e=r+(e-r)."""

    def __init__(self, N, e, alpha_r=1):
        assert e >= 2 and N >= e and 1 <= alpha_r < e
        self.N = N
        self.e = e
        self.alpha_r = alpha_r
        self.widths = [((N - 1 - i) // e + 1) for i in range(e)]
        self.name = f"Z[pi]/(pi^{e}-2,pi^{N}), alpha split ({alpha_r},{e-alpha_r})"
        self._fresh = 0

    @staticmethod
    def _resize(value, width):
        old = value.size()
        if old == width:
            return value
        if old < width:
            return ZeroExt(width - old, value)
        return Extract(width - 1, 0, value)

    def zero(self):
        return tuple(BitVecVal(0, width) for width in self.widths)

    def integer(self, value):
        return (BitVecVal(value, self.widths[0]),) + tuple(
            BitVecVal(0, width) for width in self.widths[1:]
        )

    def one(self):
        return self.integer(1)

    def pi(self):
        out = list(self.zero())
        out[1] = BitVecVal(1, self.widths[1])
        return tuple(out)

    def var(self, tag):
        self._fresh += 1
        name = f"{tag}_{self._fresh}"
        return tuple(BitVec(name + f"_{i}", width) for i, width in enumerate(self.widths))

    def add(self, x, y):
        return tuple(a + b for a, b in zip(x, y))

    def neg(self, x):
        return tuple(-a for a in x)

    def sub(self, x, y):
        return tuple(a - b for a, b in zip(x, y))

    def mul(self, x, y):
        out = list(self.zero())
        for i, xi in enumerate(x):
            for j, yj in enumerate(y):
                exponent = i + j
                index = exponent % self.e
                carry = exponent // self.e
                width = self.widths[index]
                term = self._resize(xi, width) * self._resize(yj, width) * (2**carry)
                out[index] = out[index] + term
        return tuple(out)

    def power(self, value, exponent):
        ans = self.one()
        while exponent:
            if exponent & 1:
                ans = self.mul(ans, value)
            value = self.mul(value, value)
            exponent //= 2
        return ans

    def ot_a(self):
        return self.power(self.pi(), self.alpha_r)

    def ot_b(self):
        return self.power(self.pi(), self.e - self.alpha_r)

    def eq0(self, x):
        return And(*[part == 0 for part in x])

    def neq0(self, x):
        return Or(*[part != 0 for part in x])

    def in_maximal_ideal(self, x):
        return (x[0] & 1) == 0

    lowzero = in_maximal_ideal

    def deform(self, tag):
        return self.mul(self.pi(), self.var(tag))


class E:
    """Element of A^tensor n in the basis {1,x,y,xy} in every slot."""

    def __init__(self, R, n, terms=None):
        self.R = R
        self.n = n
        self.terms = dict(terms or {})

    @staticmethod
    def scalar(R, n, value):
        coeff = value if isinstance(value, tuple) else R.integer(value)
        return E(R, n, {(0,) * n: coeff})

    @staticmethod
    def generator(R, n, slot, mask):
        monomial = [0] * n
        monomial[slot] = mask
        return E(R, n, {tuple(monomial): R.integer(1)})

    def _coerce(self, other):
        return other if isinstance(other, E) else E.scalar(self.R, self.n, other)

    def __add__(self, other):
        other = self._coerce(other)
        out = dict(self.terms)
        for monomial, coeff in other.terms.items():
            out[monomial] = self.R.add(out.get(monomial, self.R.zero()), coeff)
        return E(self.R, self.n, out)

    __radd__ = __add__

    def __neg__(self):
        return E(self.R, self.n, {m: self.R.neg(v) for m, v in self.terms.items()})

    def __sub__(self, other):
        return self + (-self._coerce(other))

    def __rsub__(self, other):
        return self._coerce(other) - self

    def __mul__(self, other):
        other = self._coerce(other)
        out = {}
        a = self.R.ot_a()
        c = self.R.integer(-2)
        for m1, v1 in self.terms.items():
            for m2, v2 in other.terms.items():
                coeff = self.R.mul(v1, v2)
                monomial = []
                for s1, s2 in zip(m1, m2):
                    if (s1 & 1) and (s2 & 1):
                        coeff = self.R.mul(coeff, a)
                    if (s1 & 2) and (s2 & 2):
                        coeff = self.R.mul(coeff, c)
                    monomial.append(s1 | s2)
                monomial = tuple(monomial)
                out[monomial] = self.R.add(out.get(monomial, self.R.zero()), coeff)
        return E(self.R, self.n, out)

    __rmul__ = __mul__

    def __pow__(self, exponent):
        ans = E.scalar(self.R, self.n, 1)
        base = self
        while exponent:
            if exponent & 1:
                ans *= base
            base *= base
            exponent //= 2
        return ans

    def map_generators(self, images):
        target = next(iter(images.values()))
        ans = E(target.R, target.n)
        for monomial, coeff in self.terms.items():
            term = E.scalar(target.R, target.n, coeff)
            for slot, mask in enumerate(monomial):
                if mask & 1:
                    term *= images[(slot, "x")]
                if mask & 2:
                    term *= images[(slot, "y")]
            ans += term
        return ans


def gens(R, n):
    ans = []
    for slot in range(n):
        ans += [E.generator(R, n, slot, 1), E.generator(R, n, slot, 2)]
    return ans


def coproduct(x1, y1, x2, y2, coeff):
    R = x1.R
    p, q, r, s, u, v = (coeff[name] for name in ("p", "q", "r", "s", "u", "v"))
    dx = x1 + x2 - R.ot_b() * x1 * x2 + p * y1 * x2 + r * x1 * y2 + u * y1 * y2
    dy = y1 + y2 + y1 * y2 + q * x1 * y2 + s * y1 * x2 + v * x1 * x2
    return dx, dy


def coproduct_full(x1, y1, x2, y2, coeff):
    """The product OT coproduct plus every possible I tensor I correction."""
    R = x1.R
    left = (x1, y1, x1 * y1)
    right = (x2, y2, x2 * y2)
    dx = x1 + x2 - R.ot_b() * x1 * x2
    dy = y1 + y2 + y1 * y2
    for i in range(3):
        for j in range(3):
            dx += coeff[f"x{i+1}{j+1}"] * left[i] * right[j]
            dy += coeff[f"y{i+1}{j+1}"] * left[i] * right[j]
    return dx, dy


def equations(R, coeff):
    x1, y1, x2, y2 = gens(R, 2)
    dx, dy = coproduct(x1, y1, x2, y2, coeff)
    relation_x = dx**2 - R.ot_a() * dx
    relation_y = dy**2 + R.integer(2) * dy

    x1, y1, x2, y2, x3, y3 = gens(R, 3)
    dx12, dy12 = coproduct(x1, y1, x2, y2, coeff)
    dx23, dy23 = coproduct(x2, y2, x3, y3, coeff)
    left_x, left_y = coproduct(dx12, dy12, x3, y3, coeff)
    right_x, right_y = coproduct(x1, y1, dx23, dy23, coeff)
    coassoc_x = left_x - right_x
    coassoc_y = left_y - right_y

    x, y = gens(R, 1)
    multiplication = {
        (0, "x"): x,
        (0, "y"): y,
        (1, "x"): x,
        (1, "y"): y,
    }
    phi_x = dx.map_generators(multiplication)
    phi_y = dy.map_generators(multiplication)
    phi = {(0, "x"): phi_x, (0, "y"): phi_y}
    fourth_x = phi_x.map_generators(phi)
    fourth_y = phi_y.map_generators(phi)
    axioms = [relation_x, relation_y, coassoc_x, coassoc_y]
    return axioms, (phi_x, phi_y), (fourth_x, fourth_y)


def equations_full(R, coeff):
    x1, y1, x2, y2 = gens(R, 2)
    dx, dy = coproduct_full(x1, y1, x2, y2, coeff)
    relation_x = dx**2 - R.ot_a() * dx
    relation_y = dy**2 + R.integer(2) * dy

    x1, y1, x2, y2, x3, y3 = gens(R, 3)
    dx12, dy12 = coproduct_full(x1, y1, x2, y2, coeff)
    dx23, dy23 = coproduct_full(x2, y2, x3, y3, coeff)
    left_x, left_y = coproduct_full(dx12, dy12, x3, y3, coeff)
    right_x, right_y = coproduct_full(x1, y1, dx23, dy23, coeff)
    coassoc_x = left_x - right_x
    coassoc_y = left_y - right_y

    x, y = gens(R, 1)
    multiplication = {
        (0, "x"): x,
        (0, "y"): y,
        (1, "x"): x,
        (1, "y"): y,
    }
    phi_x = dx.map_generators(multiplication)
    phi_y = dy.map_generators(multiplication)
    phi = {(0, "x"): phi_x, (0, "y"): phi_y}
    fourth_x = phi_x.map_generators(phi)
    fourth_y = phi_y.map_generators(phi)
    axioms = [relation_x, relation_y, coassoc_x, coassoc_y]
    return axioms, (phi_x, phi_y), (fourth_x, fourth_y)


def all_zero_constraints(R, elements):
    return [R.eq0(value) for element in elements for value in element.terms.values()]


def any_nonzero(R, elements):
    return Or(*[R.neq0(value) for element in elements for value in element.terms.values()])


def concrete(R, model, value):
    return tuple(int(model.eval(part, model_completion=True).as_long()) for part in value)


def run(N, timeout_ms, full=False, e=2, alpha_r=1):
    R = RamifiedQuadratic(N) if e == 2 else RamifiedEisenstein(N, e, alpha_r)
    if full:
        names = [f"{which}{i}{j}" for which in ("x", "y") for i in range(1, 4) for j in range(1, 4)]
        coeff = {name: R.var(name) for name in names}
        axioms, square, fourth = equations_full(R, coeff)
    else:
        coeff = {name: R.var(name) for name in ("p", "q", "r", "s", "u", "v")}
        axioms, square, fourth = equations(R, coeff)
    solver = Solver()
    solver.set(timeout=timeout_ms)
    solver.add(*[R.in_maximal_ideal(value) for value in coeff.values()])
    solver.add(*all_zero_constraints(R, axioms))

    gate = solver.check()
    solver.push()
    solver.add(any_nonzero(R, square))
    square_result = solver.check()
    solver.pop()
    noncomm_result = None
    if full:
        noncomm = Or(
            *[
                R.neq0(R.sub(coeff[f"{which}{i}{j}"], coeff[f"{which}{j}{i}"]))
                for which in ("x", "y")
                for i in range(1, 4)
                for j in range(i + 1, 4)
            ]
        )
        solver.push()
        solver.add(noncomm)
        noncomm_result = solver.check()
        solver.pop()
    solver.push()
    solver.add(any_nonzero(R, fourth))
    result = solver.check()
    family = "full-18" if full else "bilinear-6"
    extra = f"; noncocommutative={noncomm_result}" if full else ""
    print(
        f"{R.name} ({family}): axiom gate={gate}; [2]!=e={square_result}{extra}; [4]!=e={result}",
        flush=True,
    )
    if result == sat:
        model = solver.model()
        print("  cross coefficients:", {name: concrete(R, model, value) for name, value in coeff.items()})
        print(
            "  nonzero [4] coefficients:",
            [
                (which, monomial, concrete(R, model, value))
                for which, element in zip(("x", "y"), fourth)
                for monomial, value in element.terms.items()
                if concrete(R, model, value) != (0, 0)
            ],
        )
    solver.pop()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--min-n", type=int, default=5)
    parser.add_argument("--max-n", type=int, default=10)
    parser.add_argument("--timeout-ms", type=int, default=300000)
    parser.add_argument("--full", action="store_true", help="allow all 18 I tensor I corrections")
    parser.add_argument("--e", type=int, default=2, help="ramification index in pi^e=2")
    parser.add_argument("--alpha-r", type=int, default=1, help="OT parameter a=pi^r")
    args = parser.parse_args()
    for N in range(args.min_n, args.max_n + 1):
        run(N, args.timeout_ms, full=args.full, e=args.e, alpha_r=args.alpha_r)


if __name__ == "__main__":
    main()
