#!/usr/bin/env python3
r"""Exact S' sweep on the 19 relevant H=(1,2,2,1), type-two quotients.

The companion reference computation

    length6_h1221_type2_orbits_reference_20260710.py

classifies 27 residue-F2 local rings Q of length six with Hilbert function
(1,2,2,1) and Cohen--Macaulay type two.  Exactly 19 are quotients by the
socle of a length-seven Gorenstein ring.  Those 19, and only those 19, are
the targets here.  Universal S' on all of them excludes the remaining
length-seven base stratum H_R=(1,2,2,1,1).

Each Q is first converted, with a fully checked 64^2 table isomorphism, from
the reference computation's polycyclic binary basis to an invariant-factor
additive basis suitable for symbolic bit-vector arithmetic.  The displayed
Gorenstein lift witness is checked directly.  Exhaustive gates then verify
the ring laws, locality, filtration, type-two socle, and generation of the
maximal ideal by x,y.

For q=2 generators, |Syz(x,y)|=64^2/32=128 and |Soc(Q)^2|=4^2=16.
Consequently Syz/Soc(Q)^2 has exactly eight residual classes.  The complete
FAIL_i condition therefore has only 8^3=512 division representatives.  It
is expanded exactly and quantifier-free.  Socle shifts may be discarded
because fiber2 puts every coefficient of phi=[2]^# in the maximal ideal,
which annihilates Soc(Q).

The runner is deliberately memory-conscious: rings and Hopf rows are
processed serially, Z3 parallel mode is not enabled, and the default is the
single pilot quotient q01.  Use ``--rings all`` only for an intentional
sequential sweep.
"""

from __future__ import annotations

import argparse
import itertools
import math
import resource
import shlex
import sys
import time

from z3 import And, BitVecVal, Not, Solver, is_true, sat, set_param, unknown, unsat

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from length6_h1221_type2_orbits_reference_20260710 import (
    FilteredRing,
    FormalLift,
    PresentationKey,
    eval_form,
    validate_gorenstein_lift,
    validate_ring as validate_filtered_ring,
)
from order4sat_f8ram_alpha2mu2_pinned_20260709 import MODELS as XY_MODELS
from order4sat_ramified_embdim2_len6_20260709 import PinCoproductResidue
from order4sat_ramified_towers_20260709 import value
from ringcheck import Tab, add_closure, check_axioms, check_locality, ev
from sprime_length5_pointed_quadratic_sweep_20260710 import AdditiveTableRing
from sprime_ramified_length4_six_20260709 import (
    in_kernel,
    module_div_eqs,
    sp_nonprincipal_holds,
)
from sprime_ramified_principal_depth5_stratified_20260709 import (
    T4_MULT,
    XY_MULT,
    t4_pins,
)
from s2check import build_blocks, phi_of_coords


# Q number, graded form, correction mask, five displayed carries, and the
# positive Gorenstein-lift witness from the independently audited orbit run.
# The sixth carry (for u) is zero in every adapted presentation.
QUOTIENT_DATA = {
    "q01": ("B", 0x0, (0x00, 0x00, 0x00, 0x00, 0x00), 0xB000),
    "q03": ("A", 0x4, (0x00, 0x00, 0x00, 0x00, 0x00), 0xB000),
    "q05": ("B", 0x0, (0x10, 0x00, 0x00, 0x00, 0x00), 0xB004),
    "q06": ("B", 0x4, (0x10, 0x00, 0x00, 0x00, 0x00), 0xB406),
    "q07": ("B", 0x0, (0x08, 0x20, 0x00, 0x00, 0x00), 0xB008),
    "q08": ("B", 0x0, (0x18, 0x20, 0x00, 0x00, 0x00), 0xB00C),
    "q09": ("B", 0x1, (0x08, 0x20, 0x00, 0x00, 0x00), 0xB008),
    "q10": ("B", 0x1, (0x18, 0x20, 0x00, 0x00, 0x00), 0xB00C),
    "q15": ("A", 0x4, (0x10, 0x00, 0x00, 0x00, 0x00), 0xB004),
    "q16": ("A", 0x4, (0x08, 0x20, 0x00, 0x00, 0x00), 0xB008),
    "q17": ("A", 0x4, (0x18, 0x20, 0x00, 0x00, 0x00), 0xBE08),
    "q18": ("B", 0x0, (0x20, 0x00, 0x00, 0x00, 0x00), 0xB002),
    "q20": ("A", 0x4, (0x20, 0x00, 0x00, 0x00, 0x00), 0xB002),
    "q21": ("B", 0x0, (0x04, 0x00, 0x10, 0x00, 0x00), 0xB010),
    "q22": ("B", 0x2, (0x04, 0x20, 0x10, 0x00, 0x00), 0xB818),
    "q23": ("A", 0x4, (0x04, 0x10, 0x20, 0x00, 0x00), 0xB010),
    "q24": ("B", 0x0, (0x02, 0x08, 0x00, 0x20, 0x00), 0xB020),
    "q25": ("B", 0x0, (0x06, 0x08, 0x10, 0x20, 0x00), 0xB030),
    "q27": ("A", 0x4, (0x02, 0x08, 0x10, 0x20, 0x00), 0xB020),
}


def val(x):
    return value(x)


def scalar_multiple(Q, n, a):
    out = Q.zero
    for _ in range(n):
        out = Q.add(out, a)
    return out


def additive_order(Q, a):
    out = Q.zero
    for n in range(1, 65):
        out = Q.add(out, a)
        if out == Q.zero:
            return n
    raise AssertionError("element order exceeds 64")


def invariant_widths(Q):
    """Recover the 2-primary invariant factors from exact killed counts."""
    logs = [0]
    for k in range(1, 7):
        killed = sum(scalar_multiple(Q, 1 << k, a) == Q.zero for a in range(64))
        assert killed > 0 and killed & (killed - 1) == 0
        logs.append(killed.bit_length() - 1)
    at_least = [logs[k] - logs[k - 1] for k in range(1, 7)]
    widths = []
    for j in range(at_least[0]):
        widths.append(max(k for k in range(1, 7) if at_least[k - 1] > j))
    widths.sort(reverse=True)
    assert sum(widths) == 6
    assert (1 << widths[0]) == Q.characteristic()
    return tuple(widths)


def cyclic_subgroups(Q, width):
    order = 1 << width
    groups = {}
    for a in range(64):
        if additive_order(Q, a) != order:
            continue
        elems = []
        z = Q.zero
        for _ in range(order):
            elems.append(z)
            z = Q.add(z, a)
        assert z == Q.zero and len(set(elems)) == order
        key = frozenset(elems)
        groups.setdefault(key, a)
        groups[key] = min(groups[key], a)
    return tuple((a, group) for group, a in sorted(groups.items(), key=lambda x: min(x[0])))


def invariant_basis_with_unit(Q):
    """Find a direct-sum additive basis, forcing the first vector to be 1."""
    widths = invariant_widths(Q)
    unit_width = int(math.log2(Q.characteristic()))
    remaining = list(widths)
    remaining.remove(unit_width)

    unit_group = frozenset(scalar_multiple(Q, n, Q.one)
                           for n in range(1 << unit_width))
    candidates = {w: cyclic_subgroups(Q, w) for w in set(remaining)}
    dead = set()

    def search(i, subgroup, basis):
        if i == len(remaining):
            return basis if len(subgroup) == 64 else None
        state = (i, subgroup)
        if state in dead:
            return None
        w = remaining[i]
        for generator, cyclic in candidates[w]:
            if subgroup.intersection(cyclic) != {Q.zero}:
                continue
            enlarged = frozenset(Q.add(a, b) for a in subgroup for b in cyclic)
            if len(enlarged) != len(subgroup) * len(cyclic):
                continue
            answer = search(i + 1, enlarged, basis + (generator,))
            if answer is not None:
                return answer
        dead.add(state)
        return None

    basis = search(0, unit_group, (Q.one,))
    assert basis is not None
    assert tuple(additive_order(Q, a).bit_length() - 1 for a in basis) == widths
    return widths, basis


def coordinate_maps(Q, widths, basis):
    forward = {}
    for coords in itertools.product(*[range(1 << w) for w in widths]):
        out = Q.zero
        for coefficient, generator in zip(coords, basis):
            out = Q.add(out, scalar_multiple(Q, coefficient, generator))
        assert coords not in forward
        forward[coords] = out
    assert len(forward) == 64 and len(set(forward.values())) == 64
    inverse = {a: coords for coords, a in forward.items()}
    assert set(inverse) == set(range(64))
    return forward, inverse


def build_ring(key):
    graded, correction, carries5, witness = QUOTIENT_DATA[key]
    Q = FilteredRing(PresentationKey(graded, correction, carries5 + (0,)))
    assert Q.label == f"{graded}_c{correction:x}_d" + ".".join(f"{x:02x}" for x in carries5)
    validate_filtered_ring(Q)
    widths, basis = invariant_basis_with_unit(Q)
    _, inverse = coordinate_maps(Q, widths, basis)

    products = {}
    for i in range(1, len(basis)):
        for j in range(i, len(basis)):
            coords = inverse[Q.mul(basis[i], basis[j])]
            products[(i, j)] = {k: c for k, c in enumerate(coords) if c}
    R = AdditiveTableRing(f"{key.upper()} {Q.label}", widths, products)
    R.key, R.filtered, R.basis, R.inverse = key, Q, basis, inverse
    gens = [R.concrete(*inverse[Q.x]), R.concrete(*inverse[Q.y])]

    # Complete conversion audit: both operations on all 64^2 pairs.
    for a, b in itertools.product(range(64), repeat=2):
        ra, rb = R.concrete(*inverse[a]), R.concrete(*inverse[b])
        assert val(R.add(ra, rb)) == inverse[Q.add(a, b)]
        assert val(R.mul(ra, rb)) == inverse[Q.mul(a, b)]

    # Check that the hard-coded positive lift witness actually solves every
    # affine arithmetic equation and makes the quotient-socle pairing
    # injective.  Then validate the resulting 128-element Gorenstein ring.
    formal = FormalLift(Q)
    assert all(eval_form(equation, witness) == 0 for equation in formal.equations())
    socq, forms = formal.socle_product_forms()
    assert all(any(eval_form(expr, witness) for expr in forms[a])
               for a in socq if a != 0)
    validate_gorenstein_lift(Q, witness, exhaustive=False)
    R.lift_witness = witness
    return R, gens


def validate_ring(R, gens):
    started = time.monotonic()
    els = R.elements()
    values = [ev(a) for a in els]
    assert len(els) == len(set(values)) == 64
    T = Tab(R, els)
    check_axioms(T, values, triple_cap=64)
    nm, residue, powers = check_locality(T, expect_residue_deg=1)
    assert (nm, residue, powers) == (32, 2, [32, 8, 2, 1])
    maximal = {a for a in values if T.lowzero(a)}
    raw = {T.mul(ev(g), a) for g in gens for a in values}
    assert add_closure(T, raw) == maximal
    soc = [a for a in els if all(val(R.mul(a, g)) == val(R.zero()) for g in gens)]
    assert len(soc) == 4
    assert all(T.mul(ev(s), a) == T.zero for s in soc for a in maximal)
    print(f"  [ring/direct-sum/lift/locality/type gate] {R.key}: |R|=64, "
          f"additive_widths={R.widths}, |m^k|=32,8,2,1, |Soc|=4, "
          f"G-lift=0x{R.lift_witness:05x} -> PASS "
          f"({time.monotonic()-started:.2f}s)", flush=True)
    return soc


def exact_residual_syzygies(R, gens, soc):
    """Return every class of Syz(x,y)/Soc(R)^2, without linearity assumptions."""
    assert len(gens) == 2 and len(soc) == 4
    els, zero = R.elements(), R.zero()
    covered, qreps = set(), []
    for a in els:
        if val(a) in covered:
            continue
        coset = {val(R.add(a, s)) for s in soc}
        assert len(coset) == 4 and not (coset & covered)
        qreps.append(a)
        covered |= coset
    assert len(qreps) == 16 and covered == {val(a) for a in els}
    assert all(val(R.mul(s, g)) == val(zero) for s in soc for g in gens)

    residual = []
    for coeffs in itertools.product(qreps, repeat=2):
        total = zero
        for coefficient, generator in zip(coeffs, gens):
            total = R.add(total, R.mul(coefficient, generator))
        if val(total) == val(zero):
            residual.append(coeffs)
    assert len(residual) == 8
    assert len({tuple(val(a) for a in row) for row in residual}) == 8
    soc_values = {val(a) for a in soc}
    quotient_orders = []
    for row in residual:
        total = tuple(R.zero() for _ in range(2))
        for order in range(1, 9):
            total = tuple(R.add(a, b) for a, b in zip(total, row))
            if all(val(a) in soc_values for a in total):
                quotient_orders.append(order)
                break
        else:
            raise AssertionError("residual class has order greater than eight")
    non_elementary = R.key in {"q24", "q25", "q27"}
    assert (4 in quotient_orders) == non_elementary
    quotient_group = "C4xC2" if non_elementary else "C2^3"
    full = len(residual) * len(soc) ** len(gens)
    assert full == 128 == len(els) ** 2 // 32
    print("  [exact full-syzygy/coset gate] |R/Soc|=16; tested 16^2=256 "
          f"coefficient cosets; |Syz/Soc^2|=8 ({quotient_group}); "
          "|Syz|=128 -> PASS", flush=True)
    print("    residual representatives: "
          + repr([[val(x) for x in row] for row in residual]), flush=True)
    return residual


def fail_i_unrolled(R, phi, gens, residual, tag, i):
    assert len(gens) == 2 and len(residual) == 8
    vecs = [[R.var(f"{tag}_{i}_{j}_{r}") for r in range(3)] for j in range(2)]
    division = And(*module_div_eqs(R, phi[i], vecs, gens))
    cache = [{}, {}]

    def cached_kernel(j, shifts):
        key = tuple(val(x) for x in shifts)
        if key not in cache[j]:
            shifted = [R.add(vecs[j][r], shifts[r]) for r in range(3)]
            cache[j][key] = in_kernel(R, phi, shifted)
        return cache[j][key]

    misses = []
    for coordinate_shifts in itertools.product(residual, repeat=3):
        per_generator = [
            [coordinate_shifts[r][j] for r in range(3)] for j in range(2)
        ]
        misses.append(Not(And(*(cached_kernel(j, per_generator[j])
                                for j in range(2)))))
    assert len(misses) == 512
    print("      [exact unroll cache] 512 combined representatives; distinct "
          f"coefficient shifts={len(cache[0])},{len(cache[1])}", flush=True)
    return And(division, *misses), vecs


def concrete_term(model, x):
    if isinstance(x, tuple):
        return tuple(concrete_term(model, y) for y in x)
    y = model.eval(x, model_completion=True)
    return BitVecVal(y.as_long(), x.size())


def concrete_kernel(R, phi, vec):
    return all(val(x) == val(R.zero()) for x in phi_of_coords(R, phi, vec))


def validate_sat(R, model, asserted, phi, gens, residual, vecs, i, c, mtab):
    assert all(is_true(model.eval(a, model_completion=True)) for a in asserted)
    cphi = [[concrete_term(model, x) for x in row] for row in phi]
    cvecs = [[concrete_term(model, x) for x in row] for row in vecs]
    for r in range(3):
        total = R.zero()
        for generator, row in zip(gens, cvecs):
            total = R.add(total, R.mul(generator, row[r]))
        assert val(total) == val(cphi[i][r + 1])
    checked = 0
    for shifts in itertools.product(residual, repeat=3):
        shifted = [list(row) for row in cvecs]
        for r, shift in enumerate(shifts):
            for j in range(2):
                shifted[j][r] = R.add(shifted[j][r], shift[j])
        assert not all(concrete_kernel(R, cphi, row) for row in shifted)
        checked += 1
    assert checked == 512
    nonzero_m = {str(k): val(concrete_term(model, x))
                 for k, x in sorted(mtab.items())
                 if val(concrete_term(model, x)) != val(R.zero())}
    nonzero_c = {str(k): val(concrete_term(model, x))
                 for k, x in sorted(c.items())
                 if val(concrete_term(model, x)) != val(R.zero())}
    divisions = [[val(concrete_term(model, x)) for x in row] for row in vecs]
    print("      [independent SAT seed validation] equations, division, all "
          "512 residual choices -> PASS", flush=True)
    print(f"      SAT_SEED multiplication_nonzero={nonzero_m}", flush=True)
    print(f"      SAT_SEED coproduct_nonzero={nonzero_c}", flush=True)
    print(f"      SAT_SEED FAIL_{i}_division={divisions}", flush=True)


def solve(label, constraints, timeout):
    solver = Solver()
    solver.set("timeout", timeout * 1000)
    solver.add(*constraints)
    started = time.monotonic()
    answer = solver.check()
    elapsed = time.monotonic() - started
    reason = f" reason={solver.reason_unknown()}" if answer == unknown else ""
    print(f"    [{label}] -> {answer} ({elapsed:.2f}s){reason}", flush=True)
    return answer, solver.model() if answer == sat else None


def run_row(base, gens, residual, fiber, pins, label, timeout, only_i):
    print(f"  --- {label} ---", flush=True)
    R = PinCoproductResidue(base, pins)
    A, M, C, F, phi, c, mtab = build_blocks(R, fiber)
    core = A + M + C + F
    h0, _ = solve("H0 axioms+fiber2 sanity", core, timeout)
    out = {"H0": str(h0), "S1": "not-run", "S2": {}, "class": "unknown"}
    if h0 == unsat:
        out["class"] = "H0-vacuous"
        print("    [H0-VACUOUS: no bialgebra lift]", flush=True)
        return out
    if h0 == unknown:
        return out

    holds = sp_nonprincipal_holds(R, phi, gens, "h1221H")
    s1, _ = solve("S1 axioms+fiber2+S'-HOLDS", core + [holds], timeout)
    out["S1"] = str(s1)
    if s1 != sat:
        print("    [S1 sanity did not return SAT; FAIL_i still run]", flush=True)

    row_class = "UNSAT" if set(only_i) == {1, 2, 3} else "partial-UNSAT"
    for i in only_i:
        failure, vecs = fail_i_unrolled(base, phi, gens, residual, "h1221F", i)
        asserted = core + [failure]
        answer, model = solve(f"S2.{i} axioms+fiber2+S'-FAIL_i", asserted, timeout)
        out["S2"][str(i)] = str(answer)
        if answer == sat:
            validate_sat(base, model, asserted, phi, gens, residual,
                         vecs, i, c, mtab)
            row_class = "SAT S'-failure"
        elif answer == unknown and row_class != "SAT S'-failure":
            row_class = "unknown"
    out["class"] = row_class
    print(f"    [ROW CLASS] {row_class}", flush=True)
    return out


def main():
    process_started = time.monotonic()
    parser = argparse.ArgumentParser()
    parser.add_argument("--rings", nargs="+", choices=tuple(QUOTIENT_DATA) + ("all",),
                        default=("q01",))
    parser.add_argument("--fibers", choices=("xy", "t4", "all"), default="all")
    parser.add_argument("--xy-models", nargs="+", choices=tuple(XY_MODELS),
                        default=tuple(XY_MODELS))
    parser.add_argument("--t4-forms", nargs="+", choices=("00", "01", "10", "11"),
                        default=("00", "01", "10", "11"))
    parser.add_argument("--only-i", nargs="+", type=int, choices=(1, 2, 3),
                        default=(1, 2, 3))
    parser.add_argument("--timeout", type=int, default=600)
    parser.add_argument(
        "--memory-mb", type=int, default=0,
        help="Z3 hard memory ceiling in MiB (0 leaves Z3's default unlimited)",
    )
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    if args.memory_mb < 0:
        parser.error("--memory-mb must be nonnegative")

    # Keep each process to one CPU and avoid Z3's parallel portfolios, which
    # duplicate solver state and can increase peak memory substantially.
    set_param("parallel.enable", False)
    set_param("smt.threads", 1)
    set_param("sat.threads", 1)
    if args.memory_mb:
        set_param("memory_max_size", args.memory_mb)

    selected = list(QUOTIENT_DATA) if "all" in args.rings else args.rings
    all_rows = []
    print("EXACT S' SWEEP -- 19 GORENSTEIN-LIFTABLE LENGTH6 H=(1,2,2,1) "
          "TYPE-TWO QUOTIENTS", flush=True)
    print("COMMAND " + shlex.join([sys.executable] + sys.argv), flush=True)
    memory_label = f"{args.memory_mb}MiB" if args.memory_mb else "unlimited"
    print("Sequential/single-threaded; results are S' verdicts, not direct [4] verdicts; "
          f"Z3 memory ceiling={memory_label}.", flush=True)
    for key in selected:
        print(f"===== H1221 TYPE2 QUOTIENT {key} =====", flush=True)
        R, gens = build_ring(key)
        soc = validate_ring(R, gens)
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
            s2 = ",".join(f"{i}:{x}" for i, x in sorted(row["S2"].items())) or "not-run"
            print(f"  {label}: class={row['class']}; H0={row['H0']}; "
                  f"S1={row['S1']}; S2={s2}", flush=True)
        print(f"DONE {key}", flush=True)
        all_rows.extend((key, label, row) for label, row in rows)

    print("===== H1221 TYPE2 TERMINAL SUMMARY =====", flush=True)
    counts = {"H0-vacuous": 0, "SAT S'-failure": 0, "UNSAT": 0,
              "partial-UNSAT": 0, "unknown": 0}
    for _, _, row in all_rows:
        counts[row["class"]] = counts.get(row["class"], 0) + 1
    print("COUNTS " + ", ".join(f"{key}={count}" for key, count in counts.items()),
          flush=True)
    maxrss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    # Darwin reports bytes; Linux (including RCC) reports KiB.
    maxrss_mib = maxrss / (1024 * 1024) if sys.platform == "darwin" else maxrss / 1024
    print(f"PROCESS_RESOURCE elapsed_seconds={time.monotonic()-process_started:.2f} "
          f"maxrss_mib={maxrss_mib:.2f} platform={sys.platform}", flush=True)
    print("DONE sprime_length6_h1221_type2_nineteen_stratified_20260710", flush=True)


if __name__ == "__main__":
    main()
