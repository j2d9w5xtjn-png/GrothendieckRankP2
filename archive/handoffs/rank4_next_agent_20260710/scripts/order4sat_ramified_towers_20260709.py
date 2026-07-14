#!/usr/bin/env python3
r"""
Exact rank-four counterexample search over ramified truncated DVRs.

The base rings are

    R(e,N) = Z_2[pi] / (pi^e - 2, pi^N),       2 <= e < N.

They have 2^N elements, residue field F_2, maximal ideal (pi), and length N.
An element has the unique form

    sum_{r=0}^{e-1} a_r pi^r,
    a_r in Z / 2^{ceil((N-r)/e)}.

Thus the coefficient bit widths vary with r.  This representation incorporates
all carries caused by pi^e=2 exactly; there is no approximation or layer
truncation in the Hopf equations.

For each requested ring and each of the two possible local rank-four algebra
shapes, the script asks whether there is a commutative rank-four bialgebra with
killed-by-2 special fiber and [4]^# nonzero.  If this bialgebra query is SAT it
then imposes the antipode identities, so only that second SAT verdict would be
a finite-flat group-scheme counterexample.  Bialgebra UNSAT is already enough
to exclude a counterexample over that exact ring and fiber shape.

Before solving, exhaustive concrete gates check the ring cardinality,
commutative ring axioms, the presentation relations, and the complete
pi-adic filtration.  R(2,3) and R(2,4) are additionally cross-checked against
the independently written legacy Rram and Rram4 implementations.

Examples:

  ~/.venvs/z3env/bin/python scripts/order4sat_ramified_towers_20260709.py \
      --rings 3,4 3,5 2,6 --timeout 7200

The output is intended to be redirected to a new log file.  Existing scripts
and logs are not modified.
"""

from __future__ import annotations

import argparse
import itertools
import time

from z3 import (
    And,
    BitVec,
    BitVecVal,
    Extract,
    Or,
    Solver,
    ZeroExt,
    is_true,
    sat,
    set_param,
    simplify,
    unsat,
)

from order4sat import Rram, build, fresh
from order4sat_beyond import Rram4


def resize_unsigned(x, width):
    """Reduce/extend a bitvector to ``width`` low bits."""
    old = x.size()
    if old == width:
        return x
    if old < width:
        return ZeroExt(width - old, x)
    return Extract(width - 1, 0, x)


class EisensteinTrunc:
    """The exact finite ring R(e,N)=Z_2[pi]/(pi^e-2,pi^N)."""

    def __init__(self, e, N):
        if not (2 <= e < N):
            raise ValueError("need 2 <= e < N for a mixed-characteristic ring")
        self.e = e
        self.N = N
        self.widths = tuple((N - 1 - r) // e + 1 for r in range(e))
        self.name = f"Z_2[pi]/(pi^{e}-2,pi^{N})"

    def zero(self):
        return tuple(BitVecVal(0, w) for w in self.widths)

    def one(self):
        return tuple(BitVecVal(1 if r == 0 else 0, w)
                     for r, w in enumerate(self.widths))

    def var(self, tag):
        name = fresh(tag)
        return tuple(BitVec(f"{name}_{r}", w)
                     for r, w in enumerate(self.widths))

    def add(self, a, b):
        return tuple(x + y for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple(x - y for x, y in zip(a, b))

    def mul(self, a, b):
        out = [BitVecVal(0, w) for w in self.widths]
        for r in range(self.e):
            for s in range(self.e):
                q, t = divmod(r + s, self.e)
                w = self.widths[t]
                ar = resize_unsigned(a[r], w)
                bs = resize_unsigned(b[s], w)
                out[t] = out[t] + BitVecVal(1 << q, w) * ar * bs
        return tuple(out)

    def eq0(self, a):
        return And(*[x == 0 for x in a])

    def neq0(self, a):
        return Or(*[x != 0 for x in a])

    def lowzero(self, a):
        # Reduction modulo (pi) is the low bit of a_0.
        return Extract(0, 0, a[0]) == 0

    def deform(self, tag):
        # Generic element of (pi): a_0 is arbitrary even; every other
        # coefficient is arbitrary.  This parametrization is surjective.
        v = self.var(tag)
        return (BitVecVal(2, self.widths[0]) * v[0],) + v[1:]

    def pi(self):
        return tuple(BitVecVal(1 if r == 1 else 0, w)
                     for r, w in enumerate(self.widths))

    def two(self):
        return tuple(BitVecVal(2 if r == 0 else 0, w)
                     for r, w in enumerate(self.widths))

    def concrete(self, coeffs):
        return tuple(BitVecVal(a, w) for a, w in zip(coeffs, self.widths))

    def elements(self):
        for coeffs in itertools.product(*[range(1 << w) for w in self.widths]):
            yield self.concrete(coeffs)


def value(x):
    if isinstance(x, tuple):
        return tuple(value(y) for y in x)
    return simplify(x).as_long()


def cpow(R, x, n):
    out = R.one()
    for _ in range(n):
        out = R.mul(out, x)
    return out


def exhaustive_ring_gates(R):
    """Concrete, exhaustive validation independent of the Hopf solver."""
    started = time.monotonic()
    els = list(R.elements())
    vals = {value(x) for x in els}
    assert len(els) == len(vals) == 1 << R.N
    zero, one, pi = R.zero(), R.one(), R.pi()

    # Presentation and exact nilpotence order.
    assert value(cpow(R, pi, R.e)) == value(R.two())
    assert value(cpow(R, pi, R.N)) == value(zero)
    assert value(cpow(R, pi, R.N - 1)) != value(zero)

    # Full binary operation tables, closure, identities, commutativity and
    # distributivity.  Associativity is checked exhaustively below.
    addtab = {}
    multab = {}
    for x in els:
        xv = value(x)
        assert value(R.add(x, zero)) == xv
        assert value(R.mul(x, one)) == xv
        assert value(R.mul(x, zero)) == value(zero)
        for y in els:
            yv = value(y)
            av = value(R.add(x, y))
            mv = value(R.mul(x, y))
            assert av in vals and mv in vals
            assert av == value(R.add(y, x))
            assert mv == value(R.mul(y, x))
            addtab[(xv, yv)] = av
            multab[(xv, yv)] = mv

    for x in els:
        xv = value(x)
        for y in els:
            yv = value(y)
            xy = multab[(xv, yv)]
            for z in els:
                zv = value(z)
                # (xy)z=x(yz), using canonical concrete representatives.
                left = value(R.mul(R.concrete(xy), z))
                yz = multab[(yv, zv)]
                right = value(R.mul(x, R.concrete(yz)))
                assert left == right
                # x(y+z)=xy+xz.
                yzadd = addtab[(yv, zv)]
                lhs = value(R.mul(x, R.concrete(yzadd)))
                rhs = addtab[(xy, multab[(xv, zv)])]
                assert lhs == rhs

    # m=(pi), and every ideal (pi^k) has the correct cardinality 2^(N-k).
    low_m = {value(x) for x in els if is_true(simplify(R.lowzero(x)))}
    piR = {value(R.mul(pi, x)) for x in els}
    assert low_m == piR and len(piR) == 1 << (R.N - 1)
    for k in range(R.N + 1):
        pik = cpow(R, pi, k)
        ideal = {value(R.mul(pik, x)) for x in els}
        assert len(ideal) == 1 << (R.N - k)

    elapsed = time.monotonic() - started
    print(f"  [ring gates] |R|={len(els)}, widths={R.widths}, "
          f"|(pi^k)|={[1 << (R.N-k) for k in range(1,R.N+1)]} "
          f"-> PASS ({elapsed:.2f}s)", flush=True)


def crosscheck_legacy(e, N):
    """Compare the new e=2 rings against both legacy implementations."""
    if (e, N) not in {(2, 3), (2, 4)}:
        return
    new = EisensteinTrunc(e, N)
    old = Rram() if N == 3 else Rram4()
    els = list(new.elements())
    for x in els:
        for y in els:
            nx, ny = value(x), value(y)
            ox = tuple(BitVecVal(a, w) for a, w in zip(nx, new.widths))
            oy = tuple(BitVecVal(a, w) for a, w in zip(ny, new.widths))
            assert value(new.add(x, y)) == value(old.add(ox, oy))
            assert value(new.mul(x, y)) == value(old.mul(ox, oy))
    print(f"  [legacy cross-check] R(2,{N}) agrees on every pair -> PASS",
          flush=True)


FIBERS = [
    ("F_2[x,y]/(x^2,y^2)", {(1, 2, 3): 1}),
    ("F_2[t]/(t^4)", {(1, 1, 2): 1, (1, 2, 3): 1}),
]


def model_nonzero_decls(model):
    ans = []
    for d in model.decls():
        v = model[d]
        if hasattr(v, "as_long") and v.as_long() != 0:
            ans.append((str(d), v.as_long()))
    return sorted(ans)


def solve_ring_fiber(R, fiber_name, fiber, timeout_seconds):
    print(f"  --- fiber {fiber_name}; killed-by-2 special fiber ---", flush=True)
    build_started = time.monotonic()
    base, anti, p4nz, _ = build(R, fiber, with_antipode=True)
    print(f"    built {len(base)} base constraints and {len(anti)} antipode "
          f"constraints in {time.monotonic()-build_started:.2f}s", flush=True)

    solver = Solver()
    solver.set("timeout", int(timeout_seconds * 1000))
    solver.add(*base)
    t0 = time.monotonic()
    sanity = solver.check()
    print(f"    [H0 full bialgebra sanity] -> {sanity} "
          f"({time.monotonic()-t0:.2f}s)", flush=True)
    if sanity != sat:
        print("    INVALID SEARCH ROW: the non-vacuity gate did not return SAT",
              flush=True)
        return "invalid"

    solver.push()
    solver.add(p4nz)
    t0 = time.monotonic()
    bialg = solver.check()
    print(f"    [H1 full bialgebra + [4]^# != 0] -> {bialg} "
          f"({time.monotonic()-t0:.2f}s)", flush=True)
    if bialg == sat:
        print(f"      H1 nonzero assignments: "
              f"{model_nonzero_decls(solver.model())}", flush=True)
    solver.pop()

    if bialg == unsat:
        print("    VERDICT: EXCLUDED over this exact ring/fiber "
              "(bialgebra-level UNSAT)", flush=True)
        return "unsat"
    if bialg != sat:
        print("    VERDICT: OPEN (solver returned unknown)", flush=True)
        return "unknown"

    hopf = Solver()
    hopf.set("timeout", int(timeout_seconds * 1000))
    hopf.add(*base, p4nz, *anti)
    t0 = time.monotonic()
    hres = hopf.check()
    print(f"    [H2 + full antipode identities] -> {hres} "
          f"({time.monotonic()-t0:.2f}s)", flush=True)
    if hres == sat:
        print(f"      H2 nonzero assignments: "
              f"{model_nonzero_decls(hopf.model())}", flush=True)
        print("    VERDICT: CANDIDATE COUNTEREXAMPLE -- requires independent "
              "model reconstruction", flush=True)
        return "sat"
    if hres == unsat:
        print("    VERDICT: no Hopf counterexample, although a bialgebra "
              "witness exists", flush=True)
        return "hopf-unsat"
    print("    VERDICT: OPEN at the antipode stage", flush=True)
    return "hopf-unknown"


def parse_ring(text):
    try:
        e, N = (int(x) for x in text.split(","))
    except Exception as exc:
        raise argparse.ArgumentTypeError("ring must be written e,N") from exc
    if not (2 <= e < N):
        raise argparse.ArgumentTypeError("ring must satisfy 2 <= e < N")
    return e, N


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--rings", nargs="+", type=parse_ring,
        default=[(2, 3), (2, 4), (3, 4), (3, 5), (2, 6)],
        help="pairs e,N, for example --rings 3,4 3,5 2,6")
    parser.add_argument("--timeout", type=int, default=7200,
                        help="per solver query timeout in seconds")
    parser.add_argument("--skip-ring-gates", action="store_true",
                        help="skip expensive exhaustive concrete ring checks")
    args = parser.parse_args()

    set_param("parallel.enable", True)
    print("EXACT RAMIFIED RANK-4 SEARCH", flush=True)
    print("All equations: associativity + Delta multiplicativity + "
          "coassociativity + killed-by-2 fiber; H2 also adds antipode.",
          flush=True)
    print(f"Per-query timeout: {args.timeout}s", flush=True)
    summary = []
    for e, N in args.rings:
        R = EisensteinTrunc(e, N)
        print(f"===== base {R.name}; length={N}, ramification index={e} =====",
              flush=True)
        if not args.skip_ring_gates:
            exhaustive_ring_gates(R)
            crosscheck_legacy(e, N)
        for fiber_name, fiber in FIBERS:
            verdict = solve_ring_fiber(R, fiber_name, fiber, args.timeout)
            summary.append((e, N, fiber_name, verdict))

    print("===== SUMMARY =====", flush=True)
    for e, N, fiber_name, verdict in summary:
        print(f"R({e},{N}) | {fiber_name} | {verdict}", flush=True)
    print("DONE order4sat_ramified_towers_20260709", flush=True)


if __name__ == "__main__":
    main()
