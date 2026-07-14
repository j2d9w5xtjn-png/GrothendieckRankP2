#!/usr/bin/env python3
r"""Exact S' sweep on the four length-six rank-one quotients F0,Fa,Fr,F2.

The rings are the four explicit (1,4,1) quotients in Section 8 of
STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md.  Every 64-element ring is
checked exhaustively for the full ring tables, presentation, locality,
maximal-ideal filtration, generator ideal, type-four socle, and deformation
range before a Hopf query is built.

There are four maximal-ideal generators, so enumerating R^4 to discover the
division syzygy would inspect 64^4 tuples.  Instead, this script derives the
quotient exactly as follows.  It exhaustively computes Soc(R), gates
Soc(R)*m=0, partitions all 64 elements into the four additive cosets of the
socle, and enumerates only the 4^4=256 coefficient-coset tuples.  Exactly
eight lie in Syz(g_1,...,g_4)/Soc(R)^4.  The coset partition and annihilation
gate prove that these eight representatives, together with arbitrary
Soc(R)^4 shifts, are the complete 524288-element syzygy module.

Under fiber2 every entry of phi=[2]^# lies in m, so socle shifts affect
neither division nor kernel membership.  Each split FAIL_i is therefore the
exact quantifier-free unroll over 8^3=512 residual division choices.  All six
F2-rational xy pins and all four t4 normal forms are included.  H0-vacuous,
SAT failure, UNSAT, and unknown rows are classified separately.  Any SAT
failure is independently validated from the concrete model against every
asserted equation, the division identity, and all 512 residual choices.
"""

from __future__ import annotations

import argparse
import itertools
import sys
import time

from z3 import (
    And, BitVec, BitVecVal, Extract, Not, Or, Solver, ZeroExt, is_true, sat,
    set_param, simplify, unknown, unsat,
)

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat import fresh
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_embdim2_len6_20260709 import PinCoproductResidue
from order4sat_ramified_towers_20260709 import value
from ringcheck import Tab, add_closure, check_axioms, check_locality, ev
from sprime_ramified_length4_six_20260709 import (
    in_kernel, module_div_eqs, sp_nonprincipal_holds,
)
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT, XY_MULT, t4_pins,
)
from s2check import build_blocks, phi_of_coords


def cast(x, width):
    old = x.size()
    if old == width: return x
    if old < width: return ZeroExt(width - old, x)
    return Extract(width - 1, 0, x)


class RankOneTableRing:
    """Finite commutative ring on a direct sum of cyclic 2-power groups."""

    def __init__(self, key, name, widths, products, generator_coords,
                 socle_values, presentation):
        self.key, self.name = key, name
        self.widths = tuple(widths)
        self.products = {(0, i): {i: 1} for i in range(len(widths))}
        for pair, image in products.items():
            self.products[tuple(sorted(pair))] = dict(image)
        self.generator_coords = tuple(generator_coords)
        self.socle_values = set(socle_values)
        self.presentation = presentation

    def zero(self): return tuple(BitVecVal(0, w) for w in self.widths)
    def one(self):
        out = list(self.zero()); out[0] = BitVecVal(1, self.widths[0]); return tuple(out)
    def var(self, tag):
        nm = fresh(tag)
        return tuple(BitVec(f"{nm}_{i}", w) for i, w in enumerate(self.widths))
    def concrete(self, *coords):
        assert len(coords) == len(self.widths)
        return tuple(BitVecVal(a, w) for a, w in zip(coords, self.widths))
    def add(self, a, b): return tuple(x + y for x, y in zip(a, b))
    def sub(self, a, b): return tuple(x - y for x, y in zip(a, b))
    def mul(self, a, b):
        out = [BitVecVal(0, w) for w in self.widths]
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                for k, coeff in self.products.get(tuple(sorted((i, j))), {}).items():
                    w = self.widths[k]
                    out[k] = out[k] + cast(ai, w) * cast(bj, w) * BitVecVal(coeff, w)
        return tuple(out)
    def eq0(self, a): return And(*[x == 0 for x in a])
    def neq0(self, a): return Or(*[x != 0 for x in a])
    def lowzero(self, a): return (a[0] & 1) == 0
    def deform(self, tag):
        v = self.var(tag); return (2 * v[0],) + v[1:]
    def elements(self):
        return [self.concrete(*c) for c in itertools.product(
            *[range(1 << w) for w in self.widths])]
    def generators(self): return [self.concrete(*c) for c in self.generator_coords]
    def expected_socle(self): return set(self.socle_values)


def all_rings():
    # Coordinate bases are listed in each name comment below.
    f0_soc = {(0, 0, a, b, c, d) for a, b, c, d in itertools.product((0, 1), repeat=4)}
    F0 = RankOneTableRing(
        "F0", "F0=F2[x,u,v,w]/(x^3,xu,xv,xw,(u,v,w)^2)",
        (1, 1, 1, 1, 1, 1), {(1, 1): {2: 1}},
        ((0,1,0,0,0,0), (0,0,0,1,0,0),
         (0,0,0,0,1,0), (0,0,0,0,0,1)),
        f0_soc, "F0")  # basis 1,x,x2,u,v,w

    fa_soc = {(4*a, u, v, w) for a, u, v, w in itertools.product((0, 1), repeat=4)}
    Fa = RankOneTableRing(
        "Fa", "Fa=Z/8[u,v,w]/(2u,2v,2w,(u,v,w)^2)",
        (3, 1, 1, 1), {},
        ((2,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1)),
        fa_soc, "Fa")  # basis 1,u,v,w

    fr_soc = {(2*a, 0, b, c, d) for a, b, c, d in itertools.product((0, 1), repeat=4)}
    Fr = RankOneTableRing(
        "Fr", "Fr=Z/4[x,u,v]/(2x,2u,2v,x^3,xu,xv,(u,v)^2)",
        (2, 1, 1, 1, 1), {(1, 1): {2: 1}},
        ((2,0,0,0,0), (0,1,0,0,0), (0,0,0,1,0), (0,0,0,0,1)),
        fr_soc, "Fr")  # basis 1,x,x2,u,v

    f2_soc = {(2*a, 0, u, v, w) for a, u, v, w in itertools.product((0, 1), repeat=4)}
    F2 = RankOneTableRing(
        "F2", "F2=Z/4[x,u,v,w]/(x^2-2,x^3,xu,xv,xw,(u,v,w)^2)",
        (2, 1, 1, 1, 1), {(1, 1): {0: 2}},
        ((0,1,0,0,0), (0,0,1,0,0), (0,0,0,1,0), (0,0,0,0,1)),
        f2_soc, "F2")  # basis 1,x,u,v,w
    return {R.key: R for R in (F0, Fa, Fr, F2)}


def v(x): return value(x)


def cpow(R, x, n):
    out = R.one()
    for _ in range(n): out = R.mul(out, x)
    return out


def validate_presentation(R):
    z, one = R.zero(), R.one(); two = R.add(one, one)
    gens = R.generators()
    if R.key == "F0":
        x, u, vv, w = gens
        assert v(two) == v(z) and v(cpow(R, x, 2)) != v(z) and v(cpow(R, x, 3)) == v(z)
        assert all(v(R.mul(a, b)) == v(z) for a, b in itertools.combinations_with_replacement((u,vv,w), 2))
        assert all(v(R.mul(x, a)) == v(z) for a in (u,vv,w))
    elif R.key == "Fa":
        two_g, u, vv, w = gens
        assert v(two_g) == v(two) and v(cpow(R, two, 2)) != v(z) and v(cpow(R, two, 3)) == v(z)
        assert all(v(R.mul(two, a)) == v(z) for a in (u,vv,w))
        assert all(v(R.mul(a, b)) == v(z) for a, b in itertools.combinations_with_replacement((u,vv,w), 2))
    elif R.key == "Fr":
        two_g, x, u, vv = gens
        assert v(two_g) == v(two) and v(R.mul(x, x)) != v(z) and v(cpow(R, x, 3)) == v(z)
        assert all(v(R.mul(two, a)) == v(z) for a in (x,u,vv))
        assert all(v(R.mul(x, a)) == v(z) for a in (u,vv))
        assert all(v(R.mul(a, b)) == v(z) for a, b in itertools.combinations_with_replacement((u,vv), 2))
    elif R.key == "F2":
        x, u, vv, w = gens
        assert v(R.mul(x, x)) == v(two) and v(cpow(R, x, 3)) == v(z)
        assert all(v(R.mul(x, a)) == v(z) for a in (u,vv,w))
        assert all(v(R.mul(a, b)) == v(z) for a, b in itertools.combinations_with_replacement((u,vv,w), 2))
    else:
        raise ValueError(R.key)


def validate_ring(R):
    started = time.monotonic(); els = R.elements(); vals = [ev(x) for x in els]
    assert len(els) == len(set(vals)) == 64
    T = Tab(R, els)
    check_axioms(T, vals, triple_cap=64)
    nm, residue, powers = check_locality(T, expect_residue_deg=1)
    assert (nm, residue, powers) == (32, 2, [32, 2, 1])

    maximal = {x for x in vals if T.lowzero(x)}
    raw = {T.mul(ev(g), a) for g in R.generators() for a in vals}
    generated = add_closure(T, raw)
    assert generated == maximal

    soc = {ev(a) for a in els if all(v(R.mul(a, g)) == v(R.zero())
                                      for g in R.generators())}
    assert soc == R.expected_socle() and len(soc) == 16
    assert all(T.mul(s, a) == T.zero for s in soc for a in maximal)
    validate_presentation(R)
    print(f"  [ring/presentation/locality/type gate] {R.key}: |R|=64, "
          f"|m^k|=32,2,1, |Soc|=16, type=4 -> PASS "
          f"({time.monotonic()-started:.2f}s)", flush=True)
    return [T.by_val[x] for x in sorted(soc)]


def tuple_add(R, a, b): return tuple(R.add(x, y) for x, y in zip(a, b))
def tuple_key(a): return tuple(v(x) for x in a)


def residual_syzygy_cosets(R, gens, soc):
    """Derive Syz(gens)/Soc^4 by enumerating only (R/Soc)^4."""
    els, z = R.elements(), R.zero(); soc_by_key = {v(x): x for x in soc}
    covered = set(); quotient_reps = []
    for a in els:
        if v(a) in covered: continue
        coset = {v(R.add(a, s)) for s in soc}
        assert len(coset) == 16 and not (coset & covered)
        quotient_reps.append(a); covered |= coset
    assert covered == {v(a) for a in els} and len(quotient_reps) == 4

    # Soc*m=0 makes the generator map constant on every coefficient coset.
    assert all(v(R.mul(s, g)) == v(z) for s in soc for g in gens)
    residual = []
    for coeffs in itertools.product(quotient_reps, repeat=4):
        total = z
        for a, g in zip(coeffs, gens): total = R.add(total, R.mul(a, g))
        if v(total) == v(z): residual.append(coeffs)
    assert len(residual) == 8 and len({tuple_key(x) for x in residual}) == 8

    # Independently gate the quotient group: it is elementary of order 8 and
    # the selected residual tuples are closed modulo Soc^4.
    residual_keys = {tuple_key(x) for x in residual}
    for a in residual:
        assert all(v(x) in soc_by_key for x in tuple_add(R, a, a))
    for a, b in itertools.product(residual, repeat=2):
        c = tuple_add(R, a, b)
        assert any(all(v(R.sub(x, y)) in soc_by_key for x, y in zip(c, r))
                   for r in residual)

    full_size = len(residual) * (len(soc) ** 4)
    # The generator map R^4 -> m is surjective by the preceding generator
    # ideal gate, so the group-homomorphism kernel has this same cardinality.
    assert full_size == (len(els) ** 4) // 32 == 524288
    print("  [exact full-syzygy/coset gate] |R/Soc|=4; tested 4^4=256 "
          "coefficient cosets; |Syz/Soc^4|=8 (C2^3); "
          "|Syz|=524288 -> PASS", flush=True)
    print("    residual representatives: "
          + repr([[v(x) for x in row] for row in residual]), flush=True)
    return residual


def fail_i_unrolled(R, phi, gens, residual, tag, i):
    q = len(gens)
    vecs = [[R.var(f"{tag}_{i}_{j}_{r}") for r in range(3)] for j in range(q)]
    division = And(*module_div_eqs(R, phi[i], vecs, gens))
    misses = []
    for coordinate_shifts in itertools.product(residual, repeat=3):
        shifted = [list(row) for row in vecs]
        for r, shift in enumerate(coordinate_shifts):
            for j in range(q): shifted[j][r] = R.add(shifted[j][r], shift[j])
        misses.append(Not(And(*[in_kernel(R, phi, row) for row in shifted])))
    assert len(misses) == 512
    return And(division, *misses), vecs


def concrete_term(model, x):
    if isinstance(x, tuple): return tuple(concrete_term(model, y) for y in x)
    y = model.eval(x, model_completion=True)
    return BitVecVal(y.as_long(), x.size())


def model_value(model, x): return v(concrete_term(model, x))


def concrete_kernel(R, phi, vec):
    return all(v(x) == v(R.zero()) for x in phi_of_coords(R, phi, vec))


def validate_sat_seed(R, model, asserted, phi, gens, residual, vecs, i, c, mtab):
    assert all(is_true(model.eval(a, model_completion=True)) for a in asserted)
    cphi = [[concrete_term(model, x) for x in row] for row in phi]
    cvecs = [[concrete_term(model, x) for x in row] for row in vecs]
    for r in range(3):
        total = R.zero()
        for g, row in zip(gens, cvecs): total = R.add(total, R.mul(g, row[r]))
        assert v(total) == v(cphi[i][r + 1])
    checked = 0
    for coordinate_shifts in itertools.product(residual, repeat=3):
        shifted = [list(row) for row in cvecs]
        for r, shift in enumerate(coordinate_shifts):
            for j in range(4): shifted[j][r] = R.add(shifted[j][r], shift[j])
        assert not all(concrete_kernel(R, cphi, row) for row in shifted)
        checked += 1
    assert checked == 512
    print("      [independent SAT seed validation] asserted equations, division, "
          "and all 512 residual choices -> PASS", flush=True)
    mult_seed = {str(k): model_value(model, x) for k, x in sorted(mtab.items())
                 if model_value(model, x) != v(R.zero())}
    cop_seed = {str(k): model_value(model, x) for k, x in sorted(c.items())
                if model_value(model, x) != v(R.zero())}
    div_seed = [[model_value(model, x) for x in row] for row in vecs]
    print(f"      SAT_SEED multiplication_nonzero={mult_seed}", flush=True)
    print(f"      SAT_SEED coproduct_nonzero={cop_seed}", flush=True)
    print(f"      SAT_SEED FAIL_{i}_division={div_seed}", flush=True)


def solve(label, constraints, timeout, on_sat=None):
    solver = Solver(); solver.set("timeout", timeout * 1000); solver.add(*constraints)
    started = time.monotonic(); ans = solver.check(); elapsed = time.monotonic() - started
    reason = f" reason={solver.reason_unknown()}" if ans == unknown else ""
    print(f"    [{label}] -> {ans} ({elapsed:.2f}s){reason}", flush=True)
    if ans == sat and on_sat is not None: on_sat(solver.model(), constraints)
    return ans


def run_row(base, gens, residual, fib, pins, label, timeout, only_i):
    print(f"  --- {label} ---", flush=True)
    R = PinCoproductResidue(base, pins)
    A, M, C, F, phi, c, mtab = build_blocks(R, fib); core = A + M + C + F
    h0 = solve("H0 axioms+fiber2 sanity", core, timeout)
    result = {"H0": str(h0), "S1": "not-run", "S2": {}, "class": "unknown"}
    if h0 == unsat:
        result["class"] = "H0-vacuous"
        print("    [H0-VACUOUS: no bialgebra lift in this stratum]", flush=True)
        return result
    if h0 == unknown:
        print("    [ROW UNKNOWN: H0 did not terminate]", flush=True)
        return result

    holds = sp_nonprincipal_holds(R, phi, gens, "r1H")
    s1 = solve("S1 axioms+fiber2+S'-HOLDS", core + [holds], timeout)
    result["S1"] = str(s1)
    if s1 != sat: print("    [S1 sanity did not return SAT; FAIL_i still run]", flush=True)

    row_class = "UNSAT" if set(only_i) == {1,2,3} else "partial-UNSAT"
    for i in only_i:
        failure, vecs = fail_i_unrolled(base, phi, gens, residual, "r1F", i)
        asserted = core + [failure]
        def on_sat(model, constraints, i=i, vecs=vecs):
            validate_sat_seed(base, model, constraints, phi, gens, residual,
                              vecs, i, c, mtab)
        ans = solve(f"S2.{i} axioms+fiber2+S'-FAIL_i", asserted, timeout, on_sat)
        result["S2"][str(i)] = str(ans)
        if ans == sat: row_class = "SAT S'-failure"
        elif ans == unknown and row_class != "SAT S'-failure": row_class = "unknown"
    result["class"] = row_class
    print(f"    [ROW CLASS] {row_class}", flush=True)
    return result


def main():
    rings = all_rings()
    ap = argparse.ArgumentParser()
    ap.add_argument("--rings", nargs="+", choices=tuple(rings) + ("all",), default=("all",))
    ap.add_argument("--fibers", choices=("xy", "t4", "all"), default="all")
    ap.add_argument("--xy-models", nargs="+", choices=tuple(XY_MODELS), default=tuple(XY_MODELS))
    ap.add_argument("--t4-forms", nargs="+", choices=("00","01","10","11"),
                    default=("00","01","10","11"))
    ap.add_argument("--only-i", nargs="+", type=int, choices=(1,2,3), default=(1,2,3))
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--validate-only", action="store_true")
    args = ap.parse_args(); set_param("parallel.enable", True)
    selected = list(rings) if "all" in args.rings else args.rings
    print("EXACT S' SWEEP -- FOUR LENGTH-SIX RANK-ONE QUOTIENTS", flush=True)
    print("Results are S' verdicts, not direct [4] verdicts.", flush=True)
    summaries = []
    for key in selected:
        base = rings[key]
        print(f"===== LENGTH6 RANK-ONE {key}: {base.name} =====", flush=True)
        soc = validate_ring(base); gens = base.generators()
        residual = residual_syzygy_cosets(base, gens, soc)
        if args.validate_only: continue
        rows = []
        if args.fibers in ("xy", "all"):
            for name in args.xy_models:
                rows.append((f"xy/{name}", run_row(
                    base, gens, residual, XY_MULT, XY_MODELS[name], f"xy/{name}",
                    args.timeout, tuple(args.only_i))))
        if args.fibers in ("t4", "all"):
            for form in args.t4_forms:
                c1, c4 = int(form[0]), int(form[1]); label = f"t4/c1={c1},c4={c4}"
                rows.append((label, run_row(
                    base, gens, residual, T4_MULT, t4_pins(c1,c4), label,
                    args.timeout, tuple(args.only_i))))
        print("SUMMARY", flush=True)
        for label, row in rows:
            s2 = ",".join(f"{i}:{x}" for i, x in sorted(row["S2"].items())) or "not-run"
            print(f"  {label}: class={row['class']}; H0={row['H0']}; "
                  f"S1={row['S1']}; S2={s2}", flush=True)
        print(f"DONE {key}", flush=True); summaries.extend((key,label,row) for label,row in rows)

    print("===== LENGTH6 RANK-ONE TERMINAL SUMMARY =====", flush=True)
    counts = {"H0-vacuous":0, "SAT S'-failure":0, "UNSAT":0,
              "partial-UNSAT":0, "unknown":0}
    for key, label, row in summaries:
        counts[row["class"]] = counts.get(row["class"], 0) + 1
    print("COUNTS " + ", ".join(f"{k}={x}" for k,x in counts.items()), flush=True)
    print("DONE sprime_length6_rankone_four_stratified_20260710", flush=True)


if __name__ == "__main__": main()
