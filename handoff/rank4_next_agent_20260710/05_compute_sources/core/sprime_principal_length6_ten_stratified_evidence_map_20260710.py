#!/usr/bin/env python3
r"""Exact S' sweep on the ten principal residue-F2 length-six rings.

The base list is the completed carry/uniformizer classification in
principal_length6_chain_classification_evidence_map_20260710.py.  Each
canonical ring is encoded symbolically in its binary t-adic digits, and the
symbolic operations are exhaustively compared on all 64^2 pairs with the
independently gated concrete carry tables before any Hopf query is run.

For m=(t), ann(t)=m^5 has two elements.  Hence each split S'-failure query
is the exact eight-choice unroll over ann(t)^3, with no quantifier.
"""

from __future__ import annotations

import argparse
import itertools
import resource
import shlex
import sys
import time

from z3 import (
    And, BitVec, BitVecVal, Extract, Or, Solver, ZeroExt, is_true, sat,
    set_param, simplify, unknown, unsat,
)

sys.path.insert(0, __file__.rsplit("/", 1)[0])

from order4sat import fresh
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_embdim2_len6_20260709 import PinCoproductResidue
from order4sat_ramified_towers_20260709 import value
from principal_length6_chain_classification_evidence_map_20260710 import (
    CarryRing, presentations,
)
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT, XY_MULT, t4_pins,
)
from s2check import build_blocks, phi_of_coords


# Exact integer range audit over add/sub/mul, all 64^2 input pairs, and all ten
# carry laws gives intermediate coefficients in [-5, 10].  Six signed bits
# ([-32, 31]) therefore leave ample headroom while keeping every term compact.
WIDTH = 6
CANONICAL = (
    "e1_0000",
    "e2_000", "e2_001", "e2_100", "e2_110",
    "e3_00",
    "e4_0", "e4_1",
    "e5_-",
    "eqchar",
)


class SymbolicCarryRing:
    def __init__(self, concrete: CarryRing):
        self.C = concrete
        self.e, self.tail, self.support = concrete.e, concrete.tail, concrete.support
        self.label = concrete.label
        self.name = "principal-length6[" + concrete.label + "]"

    def zero(self):
        return tuple(BitVecVal(0, 1) for _ in range(6))

    def one(self):
        return (BitVecVal(1, 1),) + tuple(BitVecVal(0, 1) for _ in range(5))

    def pi(self):
        return (BitVecVal(0, 1), BitVecVal(1, 1)) + tuple(
            BitVecVal(0, 1) for _ in range(4)
        )

    def var(self, tag):
        name = fresh(tag)
        return tuple(BitVec(f"{name}_{i}", 1) for i in range(6))

    def concrete_int(self, a):
        return tuple(BitVecVal((a >> i) & 1, 1) for i in range(6))

    def elements(self):
        return [self.concrete_int(a) for a in range(64)]

    @staticmethod
    def wide(x):
        return ZeroExt(WIDTH - 1, x)

    def reduce(self, coeffs):
        cs = list(coeffs) + [BitVecVal(0, WIDTH)] * (6 - len(coeffs))
        out = []
        for i in range(6):
            out.append(Extract(0, 0, cs[i]))
            quotient = cs[i] >> 1  # arithmetic shift also handles subtraction
            if self.e is not None:
                for d in self.support:
                    if i + d < 6:
                        cs[i + d] = cs[i + d] + quotient
        return tuple(out)

    def add(self, a, b):
        return self.reduce([self.wide(x) + self.wide(y) for x, y in zip(a, b)])

    def sub(self, a, b):
        return self.reduce([self.wide(x) - self.wide(y) for x, y in zip(a, b)])

    def mul(self, a, b):
        cs = [BitVecVal(0, WIDTH) for _ in range(6)]
        for i in range(6):
            for j in range(6 - i):
                # The factors are one-bit digits, so their product is their AND.
                cs[i + j] = cs[i + j] + self.wide(a[i] & b[j])
        return self.reduce(cs)

    def eq0(self, a):
        return And(*[x == 0 for x in a])

    def neq0(self, a):
        return Or(*[x != 0 for x in a])

    def lowzero(self, a):
        return a[0] == 0

    def deform(self, tag):
        x = self.var(tag)
        return (BitVecVal(0, 1),) + x[1:]


def val(x):
    return value(x)


def symbolic_gate(C):
    C.build_tables()
    R = SymbolicCarryRing(C)
    els = R.elements()
    assert len({val(x) for x in els}) == 64
    for a in range(64):
        za = els[a]
        assert is_true(simplify(R.lowzero(za))) == (not bool(a & 1))
        for b in range(64):
            zb = els[b]
            assert val(R.add(za, zb)) == tuple((C.add(a, b) >> i) & 1 for i in range(6))
            assert val(R.sub(za, zb)) == tuple((C.sub(a, b) >> i) & 1 for i in range(6))
            assert val(R.mul(za, zb)) == tuple((C.mul(a, b) >> i) & 1 for i in range(6))
    pi = R.pi()
    ann = [a for a in els if val(R.mul(pi, a)) == val(R.zero())]
    assert {val(a) for a in ann} == {val(R.zero()), val(R.concrete_int(1 << 5))}
    print(f"  [symbolic-vs-concrete 64^2 gate] {C.label}: add/sub/mul exact; "
          "ann(t)={0,t^5} -> PASS", flush=True)
    return R, pi, ann


def in_kernel(R, phi, vec):
    return And(*[R.eq0(x) for x in phi_of_coords(R, phi, vec)])


def holds_formula(R, phi, pi, tag):
    rows = []
    for i in range(1, 4):
        k = [R.var(f"{tag}_h_{i}_{r}") for r in range(3)]
        division = And(*[
            R.eq0(R.sub(R.mul(pi, k[r]), phi[i][r + 1])) for r in range(3)
        ])
        rows.append(And(division, in_kernel(R, phi, k)))
    return And(*rows)


def fail_i_formula(R, phi, pi, ann, tag, i):
    k = [R.var(f"{tag}_f_{i}_{r}") for r in range(3)]
    division = And(*[
        R.eq0(R.sub(R.mul(pi, k[r]), phi[i][r + 1])) for r in range(3)
    ])
    misses = []
    for shift in itertools.product(ann, repeat=3):
        shifted = [R.add(a, b) for a, b in zip(k, shift)]
        misses.append(Or(*[R.neq0(x) for x in phi_of_coords(R, phi, shifted)]))
    assert len(misses) == 8
    return And(division, *misses), k


def concrete_term(model, x):
    if isinstance(x, tuple):
        return tuple(concrete_term(model, y) for y in x)
    y = model.eval(x, model_completion=True)
    return BitVecVal(y.as_long(), x.size())


def validate_sat(R, model, constraints, phi, pi, ann, k, i):
    assert all(is_true(model.eval(a, model_completion=True)) for a in constraints)
    cphi = [[concrete_term(model, x) for x in row] for row in phi]
    ck = [concrete_term(model, x) for x in k]
    for r in range(3):
        assert val(R.mul(pi, ck[r])) == val(cphi[i][r + 1])
    for shift in itertools.product(ann, repeat=3):
        shifted = [R.add(a, b) for a, b in zip(ck, shift)]
        assert any(val(x) != val(R.zero())
                   for x in phi_of_coords(R, cphi, shifted))
    print("      [independent SAT validation] equations, division, all 8 shifts -> PASS",
          flush=True)


def solve(label, constraints, timeout, on_sat=None):
    s = Solver()
    s.set("timeout", timeout * 1000)
    s.add(*constraints)
    started = time.monotonic()
    ans = s.check()
    reason = f" reason={s.reason_unknown()}" if ans == unknown else ""
    print(f"    [{label}] -> {ans} ({time.monotonic()-started:.2f}s){reason}", flush=True)
    if ans == sat and on_sat is not None:
        on_sat(s.model(), constraints)
    return ans


def run_row(base, pi, ann, fib, pins, label, timeout, only_i):
    print(f"  --- {label} ---", flush=True)
    R = PinCoproductResidue(base, pins)
    A, M, C, F, phi, _, _ = build_blocks(R, fib)
    core = A + M + C + F
    h0 = solve("H0 axioms+fiber2", core, timeout)
    row = {"H0": str(h0), "S1": "not-run", "S2": {}, "class": "unknown"}
    if h0 == unsat:
        row["class"] = "H0-vacuous"
        print("    [H0-VACUOUS]", flush=True)
        return row
    if h0 == unknown:
        return row
    holds = holds_formula(base, phi, pi, "p6")
    s1 = solve("S1 axioms+fiber2+S'-HOLDS", core + [holds], timeout)
    row["S1"] = str(s1)
    cls = "UNSAT" if set(only_i) == {1, 2, 3} else "partial-UNSAT"
    for i in only_i:
        failure, k = fail_i_formula(base, phi, pi, ann, "p6", i)
        constraints = core + [failure]
        ans = solve(f"S2.{i} exact S'-FAIL_i", constraints, timeout,
                    lambda model, asserted, i=i, k=k: validate_sat(
                        base, model, asserted, phi, pi, ann, k, i))
        row["S2"][str(i)] = str(ans)
        if ans == sat:
            cls = "SAT S'-failure"
        elif ans == unknown and cls != "SAT S'-failure":
            cls = "unknown"
    row["class"] = cls
    print(f"    [ROW CLASS] {cls}", flush=True)
    return row


def main():
    process_started = time.monotonic()
    concrete = {R.label: R for R in presentations()}
    ap = argparse.ArgumentParser()
    ap.add_argument("--rings", nargs="+", choices=CANONICAL + ("all",), default=("all",))
    ap.add_argument("--fibers", choices=("xy", "t4", "all"), default="all")
    ap.add_argument("--xy-models", nargs="+", choices=tuple(XY_MODELS), default=tuple(XY_MODELS))
    ap.add_argument("--t4-forms", nargs="+", choices=("00", "01", "10", "11"),
                    default=("00", "01", "10", "11"))
    ap.add_argument("--only-i", nargs="+", type=int, choices=(1, 2, 3), default=(1, 2, 3))
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument(
        "--memory-mb", type=int, default=0,
        help="Z3 hard memory ceiling in MiB (0 leaves Z3's default unlimited)",
    )
    ap.add_argument("--validate-only", action="store_true")
    args = ap.parse_args()
    if args.timeout <= 0:
        ap.error("--timeout must be positive")
    if args.memory_mb < 0:
        ap.error("--memory-mb must be nonnegative")
    # Avoid Z3's parallel portfolio (which duplicates solver state and can use
    # substantially more memory); both relevant engines are explicitly serial.
    set_param("parallel.enable", False)
    set_param("smt.threads", 1)
    set_param("sat.threads", 1)
    if args.memory_mb:
        set_param("memory_max_size", args.memory_mb)
    selected = CANONICAL if "all" in args.rings else tuple(args.rings)
    all_rows = []
    print("EXACT S' SWEEP -- TEN PRINCIPAL LENGTH-SIX CHAIN RINGS", flush=True)
    print("COMMAND " + shlex.join([sys.executable] + sys.argv), flush=True)
    memory_label = f"{args.memory_mb}MiB" if args.memory_mb else "unlimited"
    print(f"Sequential/single-threaded; Z3 memory ceiling={memory_label}.", flush=True)
    for label in selected:
        C = concrete[label]
        print(f"===== {label} =====", flush=True)
        base, pi, ann = symbolic_gate(C)
        if args.validate_only:
            continue
        rows = []
        if args.fibers in ("xy", "all"):
            for name in args.xy_models:
                pins = XY_MODELS[name]
                row_label = "xy/" + name
                rows.append((row_label, run_row(
                    base, pi, ann, XY_MULT, pins, row_label, args.timeout,
                    tuple(args.only_i))))
        if args.fibers in ("t4", "all"):
            for form in args.t4_forms:
                c1, c4 = int(form[0]), int(form[1])
                row_label = f"t4/c1={c1},c4={c4}"
                rows.append((row_label, run_row(
                    base, pi, ann, T4_MULT, t4_pins(c1, c4), row_label,
                    args.timeout, tuple(args.only_i))))
        print("SUMMARY", flush=True)
        for row_label, row in rows:
            s2 = ",".join(f"{i}:{x}" for i, x in sorted(row["S2"].items())) or "not-run"
            print(f"  {row_label}: class={row['class']}; H0={row['H0']}; "
                  f"S1={row['S1']}; S2={s2}", flush=True)
        print(f"DONE {label}", flush=True)
        all_rows.extend((label, row_label, row) for row_label, row in rows)
    print("===== TERMINAL SUMMARY =====", flush=True)
    counts = {"H0-vacuous": 0, "SAT S'-failure": 0, "UNSAT": 0,
              "partial-UNSAT": 0, "unknown": 0}
    for _, _, row in all_rows:
        counts[row["class"]] = counts.get(row["class"], 0) + 1
    print("COUNTS " + ", ".join(f"{k}={v}" for k, v in counts.items()), flush=True)
    maxrss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    maxrss_mib = maxrss / (1024 * 1024) if sys.platform == "darwin" else maxrss / 1024
    print(f"PROCESS_RESOURCE elapsed_seconds={time.monotonic()-process_started:.2f} "
          f"maxrss_mib={maxrss_mib:.2f} platform={sys.platform}", flush=True)
    print("DONE sprime_principal_length6_ten_stratified_evidence_map_20260710", flush=True)


if __name__ == "__main__":
    main()
