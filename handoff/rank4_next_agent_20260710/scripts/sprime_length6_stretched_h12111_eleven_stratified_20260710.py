#!/usr/bin/env python3
r"""Exact S' runner for the eleven-coordinate stretched H=(1,2,1,1,1) list.

Section 4 of ``STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md`` gives an
upper list for the type-two length-six quotients of a hypothetical
length-seven Gorenstein base with Hilbert function (1,2,1,1,1,1).  It has
seven split fiber products

    P x_F2 F2[y]/y^2,

one for each principal length-five ring P, and four hidden-carry forms

    Q_ab = Z[x]/(x^5, 2x-a*x^3-b*x^4, 4-a*x^4),  a,b in F2.

These are coordinate representatives, not a claim that the four Q_ab are
pairwise nonisomorphic or all Gorenstein-liftable.  The P_00/P_01 duplicate
in the eight-coordinate principal list is removed only after an exhaustive
64^2-pair table isomorphism check (x maps to x+2 and y maps to y).

Before any solver query, every 64-element table is exhaustively checked for
the ring laws, the displayed presentation, locality, Hilbert filtration

    |m^k| = 32, 8, 4, 2, 1,

type-two socle, and generation of m by the active chain generator x and the
hidden socle generator y.  The syzygy quotient is computed by literal
additive cosets: no F2-vector-space structure is assumed.  In every valid
row |Syz(x,y)|=128 and |Syz/Soc(Q)^2|=8, so a split FAIL_i condition is the
exact quantifier-free unroll over 8^3=512 residual division choices.

The Hopf/S' encoding and independently checked SAT-seed validator are shared
with the audited H=(1,2,2,1) runner.  Rings and rows are processed serially,
Z3 portfolios are disabled, one SMT/SAT thread is selected, and both a
per-stage timeout and an optional Z3 memory ceiling are exposed on the CLI.
The default selects one ring; use ``--rings all`` only intentionally.
"""

from __future__ import annotations

import argparse
from collections import Counter
import itertools
import resource
import shlex
import sys
import time

from z3 import set_param

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from sprime_length5_pointed_quadratic_sweep_20260710 import AdditiveTableRing
from sprime_length6_h1221_type2_nineteen_stratified_20260710 import (
    run_row,
    val,
)
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT,
    XY_MULT,
    t4_pins,
)
from ringcheck import Tab, add_closure, check_axioms, check_locality, ev


RING_KEYS = (
    "s_f2",
    "s_z32",
    "s_e2_00",
    "s_e2_10",
    "s_e2_11",
    "s_e3",
    "s_e4",
    "q00",
    "q01",
    "q10",
    "q11",
)


def decorate(R, key, name, generator_coords, kind, ab=None):
    R.key = key
    R.name = name
    R.kind = kind
    R.ab = ab
    R.generator_coords = tuple(tuple(c) for c in generator_coords)
    return R


def split_e2(c, d, key):
    """B(P_cd), P_cd=Z/8[x]/(4x,x^2-2-2cx-4d)."""
    R = AdditiveTableRing(
        f"B(P_{c}{d})",
        (3, 2, 1),
        {(1, 1): {0: 2 + 4 * d, 1: 2 * c}},
    )
    return decorate(
        R,
        key,
        f"P_{c}{d} x_F2 F2[y]/y^2",
        ((0, 1, 0), (0, 0, 1)),
        f"split_e2_{c}{d}",
    )


def build_rings():
    rings = {}

    # F2[x]/x^5, with one annihilated hidden tangent y.
    R = AdditiveTableRing(
        "B(F2[x]/x^5)",
        (1, 1, 1, 1, 1, 1),
        {
            (1, 1): {2: 1},
            (1, 2): {3: 1},
            (1, 3): {4: 1},
            (2, 2): {4: 1},
        },
    )
    rings["s_f2"] = decorate(
        R,
        "s_f2",
        "F2[x,y]/(x^5,xy,y^2)",
        ((0, 1, 0, 0, 0, 0), (0, 0, 0, 0, 0, 1)),
        "split_f2",
    )

    # Z/32, where the active uniformizer is x=2.
    R = AdditiveTableRing("B(Z/32)", (5, 1), {})
    rings["s_z32"] = decorate(
        R,
        "s_z32",
        "Z/32[y]/(2y,y^2)",
        ((2, 0), (0, 1)),
        "split_z32",
    )

    # P_00 and P_01 are isomorphic.  Keep P_00, P_10, and P_11.
    rings["s_e2_00"] = split_e2(0, 0, "s_e2_00")
    rings["s_e2_10"] = split_e2(1, 0, "s_e2_10")
    rings["s_e2_11"] = split_e2(1, 1, "s_e2_11")

    # P_3=Z/4[x]/(x^3-2,x^5), basis 1,x,x^2 with widths 2,2,1.
    R = AdditiveTableRing(
        "B(P_3)",
        (2, 2, 1, 1),
        {(1, 1): {2: 1}, (1, 2): {0: 2}, (2, 2): {1: 2}},
    )
    rings["s_e3"] = decorate(
        R,
        "s_e3",
        "Z/4[x,y]/(x^3-2,x^5,xy,y^2)",
        ((0, 1, 0, 0), (0, 0, 0, 1)),
        "split_e3",
    )

    # P_4=Z/4[x]/(x^4-2,x^5), basis 1,x,x^2,x^3.
    R = AdditiveTableRing(
        "B(P_4)",
        (2, 1, 1, 1, 1),
        {
            (1, 1): {2: 1},
            (1, 2): {3: 1},
            (1, 3): {0: 2},
            (2, 2): {0: 2},
        },
    )
    rings["s_e4"] = decorate(
        R,
        "s_e4",
        "Z/4[x,y]/(x^4-2,x^5,xy,y^2)",
        ((0, 1, 0, 0, 0), (0, 0, 0, 0, 1)),
        "split_e4",
    )

    # Q_00: additive basis 1 (mod 4), x,x^2,x^3,x^4 (mod 2), y=2.
    R = AdditiveTableRing(
        "Q_00",
        (2, 1, 1, 1, 1),
        {
            (1, 1): {2: 1},
            (1, 2): {3: 1},
            (1, 3): {4: 1},
            (2, 2): {4: 1},
        },
    )
    rings["q00"] = decorate(
        R,
        "q00",
        "Q_00=Z[x]/(x^5,2x,4)",
        ((0, 1, 0, 0, 0), (2, 0, 0, 0, 0)),
        "hidden_carry",
        (0, 0),
    )

    # Q_01: x^4=2x, so use basis 1 (mod 4), x (mod 4), x^2,x^3.
    R = AdditiveTableRing(
        "Q_01",
        (2, 2, 1, 1),
        {
            (1, 1): {2: 1},
            (1, 2): {3: 1},
            (1, 3): {1: 2},
            (2, 2): {1: 2},
        },
    )
    rings["q01"] = decorate(
        R,
        "q01",
        "Q_01=Z[x]/(x^5,2x-x^4,4)",
        ((0, 1, 0, 0), (2, 0, 0, 1)),
        "hidden_carry",
        (0, 1),
    )

    # For a=1 put s=x^2-2.  Then widths are (3,2,1), x^2=2+s,
    # x*s=4b, and y=2-x^2-b*x^3 is s (b=0) or 4+2x+s (b=1).
    for b in (0, 1):
        products = {(1, 1): {0: 2, 2: 1}}
        if b:
            products[(1, 2)] = {0: 4}
        R = AdditiveTableRing(f"Q_1{b}", (3, 2, 1), products)
        ycoords = (0, 0, 1) if not b else (4, 2, 1)
        key = f"q1{b}"
        rings[key] = decorate(
            R,
            key,
            f"Q_1{b}=Z[x]/(x^5,2x-x^3-{b}x^4,4-x^4)",
            ((0, 1, 0), ycoords),
            "hidden_carry",
            (1, b),
        )

    assert tuple(rings) == RING_KEYS
    return rings


def cpow(R, x, n):
    answer = R.one()
    for _ in range(n):
        answer = R.mul(answer, x)
    return answer


def smul(R, n, x):
    answer = R.zero()
    for _ in range(n):
        answer = R.add(answer, x)
    return answer


def generators(R):
    return [R.concrete(*coords) for coords in R.generator_coords]


def validate_presentation(R, gens):
    x, y = gens
    zero, one = R.zero(), R.one()
    two, four = smul(R, 2, one), smul(R, 4, one)
    powers = {n: cpow(R, x, n) for n in range(1, 6)}
    assert all(val(powers[n]) != val(zero) for n in range(1, 5))
    assert val(powers[5]) == val(zero)
    assert val(R.mul(x, y)) == val(zero)
    assert val(R.mul(y, y)) == val(zero)

    if R.kind == "split_f2":
        assert val(two) == val(zero)
    elif R.kind == "split_z32":
        assert val(x) == val(two)
    elif R.kind.startswith("split_e2_"):
        c, d = (int(q) for q in R.kind[-2:])
        rhs = R.add(two, R.add(smul(R, 2 * c, x), smul(R, 4 * d, one)))
        assert val(R.mul(x, x)) == val(rhs)
        assert val(smul(R, 4, x)) == val(zero)
    elif R.kind == "split_e3":
        assert val(powers[3]) == val(two)
    elif R.kind == "split_e4":
        assert val(powers[4]) == val(two)
    elif R.kind == "hidden_carry":
        a, b = R.ab
        rhs_2x = R.add(smul(R, a, powers[3]), smul(R, b, powers[4]))
        assert val(R.mul(two, x)) == val(rhs_2x)
        assert val(four) == val(smul(R, a, powers[4]))
        displayed_y = R.sub(two, R.add(smul(R, a, powers[2]),
                                      smul(R, b, powers[3])))
        assert val(y) == val(displayed_y)
    else:
        raise AssertionError(f"unknown presentation kind {R.kind}")


def validate_ring(R):
    started = time.monotonic()
    els = R.elements()
    values = [ev(a) for a in els]
    assert len(els) == len(set(values)) == 64
    table = Tab(R, els)
    check_axioms(table, values, triple_cap=64)
    maximal_size, residue_size, powers = check_locality(table, expect_residue_deg=1)
    assert (maximal_size, residue_size, powers) == (32, 2, [32, 8, 4, 2, 1])

    gens = generators(R)
    maximal = {a for a in values if table.lowzero(a)}
    generated = {table.mul(ev(g), a) for g in gens for a in values}
    assert add_closure(table, generated) == maximal
    soc = [a for a in els
           if all(val(R.mul(a, g)) == val(R.zero()) for g in gens)]
    assert len(soc) == 4
    assert all(table.mul(ev(s), a) == table.zero for s in soc for a in maximal)

    validate_presentation(R, gens)
    x, y = gens
    x4 = cpow(R, x, 4)
    expected_socle = {
        val(R.zero()), val(x4), val(y), val(R.add(x4, y)),
    }
    assert len(expected_socle) == 4 == len({val(a) for a in soc})
    assert {val(a) for a in soc} == expected_socle
    print(
        f"  [ring/presentation/locality/Hilbert/type gate] {R.key}: |R|=64, "
        f"additive_widths={R.widths}, |m^k|=32,8,4,2,1, "
        f"Soc=<x^4,y> of order 4 -> PASS ({time.monotonic()-started:.2f}s)",
        flush=True,
    )
    return gens, soc


def validate_split_duplicate():
    """Check B(P_01) -> B(P_00), x |-> x+2, y |-> y, on all tables."""
    source = split_e2(0, 1, "s_e2_01_coordinate")
    target = split_e2(0, 0, "s_e2_00_coordinate")

    def image(element):
        a, b, y = val(element)
        return target.concrete((a + 2 * b) % 8, b, y)

    source_elements = source.elements()
    images = {val(image(a)) for a in source_elements}
    assert len(images) == 64
    for a, b in itertools.product(source_elements, repeat=2):
        assert val(image(source.add(a, b))) == val(target.add(image(a), image(b)))
        assert val(image(source.mul(a, b))) == val(target.mul(image(a), image(b)))
    assert val(image(source.one())) == val(target.one())
    print("[split-coordinate isomorphism gate] B(P_01) ~= B(P_00) via "
          "x -> x+2, y -> y; bijection and all 64^2 add/mul pairs -> PASS",
          flush=True)


def tuple_add(R, a, b):
    return tuple(R.add(x, y) for x, y in zip(a, b))


def exact_residual_syzygies(R, gens, soc):
    """Enumerate Syz(x,y)/Soc(R)^2 using concrete additive cosets."""
    assert len(gens) == 2 and len(soc) == 4
    els, zero = R.elements(), R.zero()
    covered, quotient_reps = set(), []
    for a in els:
        if val(a) in covered:
            continue
        coset = {val(R.add(a, s)) for s in soc}
        assert len(coset) == 4 and not (coset & covered)
        quotient_reps.append(a)
        covered |= coset
    assert len(quotient_reps) == 16
    assert covered == {val(a) for a in els}
    assert all(val(R.mul(s, g)) == val(zero) for s in soc for g in gens)

    residual = []
    for coefficients in itertools.product(quotient_reps, repeat=2):
        total = zero
        for coefficient, generator in zip(coefficients, gens):
            total = R.add(total, R.mul(coefficient, generator))
        if val(total) == val(zero):
            residual.append(coefficients)
    assert len(residual) == 8
    assert len({tuple(val(a) for a in row) for row in residual}) == 8

    soc_values = {val(a) for a in soc}

    def same_class(a, b):
        return all(val(R.sub(x, y)) in soc_values for x, y in zip(a, b))

    # Closure is tested modulo the actual four-element socle, not bitwise.
    for a, b in itertools.product(residual, repeat=2):
        total = tuple_add(R, a, b)
        matches = [row for row in residual if same_class(total, row)]
        assert len(matches) == 1

    orders = []
    for row in residual:
        total = (zero, zero)
        for order in range(1, 9):
            total = tuple_add(R, total, row)
            if all(val(a) in soc_values for a in total):
                orders.append(order)
                break
        else:
            raise AssertionError("residual syzygy class has order > 8")
    distribution = dict(sorted(Counter(orders).items()))
    labels = {
        ((1, 1), (2, 7)): "C2^3",
        ((1, 1), (2, 3), (4, 4)): "C4xC2",
        ((1, 1), (2, 1), (4, 2), (8, 4)): "C8",
    }
    quotient_group = labels.get(tuple(distribution.items()))
    assert quotient_group is not None, distribution
    full_size = len(residual) * len(soc) ** len(gens)
    assert full_size == 128 == len(els) ** 2 // 32
    print(
        "  [exact full-syzygy/coset gate] |R/Soc|=16; tested 16^2=256 "
        f"coefficient cosets; |Syz/Soc^2|=8 ({quotient_group}, "
        f"order_counts={distribution}); |Syz|=128 -> PASS",
        flush=True,
    )
    print("    residual representatives: "
          + repr([[val(x) for x in row] for row in residual]), flush=True)
    return residual


def main():
    process_started = time.monotonic()
    rings = build_rings()
    parser = argparse.ArgumentParser()
    parser.add_argument("--rings", nargs="+", choices=RING_KEYS + ("all",),
                        default=("s_f2",))
    parser.add_argument("--fibers", choices=("xy", "t4", "all"), default="all")
    parser.add_argument("--xy-models", nargs="+", choices=tuple(XY_MODELS),
                        default=tuple(XY_MODELS))
    parser.add_argument("--t4-forms", nargs="+", choices=("00", "01", "10", "11"),
                        default=("00", "01", "10", "11"))
    parser.add_argument("--only-i", nargs="+", type=int, choices=(1, 2, 3),
                        default=(1, 2, 3))
    parser.add_argument("--timeout", type=int, default=600,
                        help="seconds for each H0, S1, or S2 solver stage")
    parser.add_argument(
        "--memory-mb", type=int, default=0,
        help="Z3 hard memory ceiling in MiB (0 leaves Z3's default unlimited)",
    )
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    if args.memory_mb < 0:
        parser.error("--memory-mb must be nonnegative")

    set_param("parallel.enable", False)
    set_param("smt.threads", 1)
    set_param("sat.threads", 1)
    if args.memory_mb:
        set_param("memory_max_size", args.memory_mb)

    selected = list(RING_KEYS) if "all" in args.rings else args.rings
    print("EXACT S' RUNNER -- ELEVEN-COORDINATE LENGTH6 STRETCHED "
          "H=(1,2,1,1,1) TYPE-TWO UPPER LIST", flush=True)
    print("COMMAND " + shlex.join([sys.executable] + sys.argv), flush=True)
    memory_label = f"{args.memory_mb}MiB" if args.memory_mb else "unlimited"
    print("Sequential/single-threaded; per-stage timeout="
          f"{args.timeout}s; Z3 memory ceiling={memory_label}; results are S' "
          "verdicts, not direct [4] verdicts.", flush=True)
    validate_split_duplicate()

    all_rows = []
    for key in selected:
        R = rings[key]
        print(f"===== STRETCHED H12111 COORDINATE {key}: {R.name} =====", flush=True)
        gens, soc = validate_ring(R)
        residual = exact_residual_syzygies(R, gens, soc)
        if args.validate_only:
            continue

        rows = []
        if args.fibers in ("xy", "all"):
            for name in args.xy_models:
                label = f"xy/{name}"
                rows.append((label, run_row(R, gens, residual, XY_MULT,
                                            XY_MODELS[name], label, args.timeout,
                                            tuple(args.only_i))))
        if args.fibers in ("t4", "all"):
            for form in args.t4_forms:
                c1, c4 = int(form[0]), int(form[1])
                label = f"t4/c1={c1},c4={c4}"
                rows.append((label, run_row(R, gens, residual, T4_MULT,
                                            t4_pins(c1, c4), label, args.timeout,
                                            tuple(args.only_i))))
        print("SUMMARY", flush=True)
        for label, row in rows:
            s2 = ",".join(f"{i}:{answer}" for i, answer in sorted(row["S2"].items())) \
                or "not-run"
            print(f"  {label}: class={row['class']}; H0={row['H0']}; "
                  f"S1={row['S1']}; S2={s2}", flush=True)
        print(f"DONE {key}", flush=True)
        all_rows.extend((key, label, row) for label, row in rows)

    print("===== STRETCHED H12111 TERMINAL SUMMARY =====", flush=True)
    counts = {"H0-vacuous": 0, "SAT S'-failure": 0, "UNSAT": 0,
              "partial-UNSAT": 0, "unknown": 0}
    for _, _, row in all_rows:
        counts[row["class"]] = counts.get(row["class"], 0) + 1
    print("COUNTS " + ", ".join(f"{key}={count}" for key, count in counts.items()),
          flush=True)
    maxrss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    maxrss_mib = maxrss / (1024 * 1024) if sys.platform == "darwin" else maxrss / 1024
    print(f"PROCESS_RESOURCE elapsed_seconds={time.monotonic()-process_started:.2f} "
          f"maxrss_mib={maxrss_mib:.2f} platform={sys.platform}", flush=True)
    print("DONE sprime_length6_stretched_h12111_eleven_stratified_20260710",
          flush=True)


if __name__ == "__main__":
    main()
