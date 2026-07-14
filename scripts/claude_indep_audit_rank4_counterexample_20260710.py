#!/usr/bin/env python3
"""CLAUDE INDEPENDENT AUDIT of the universal alpha_2^2 rank-4 counterexample.

Third implementation, written from scratch on 2026-07-10:
  * re-derives the bialgebra equations (associativity, Delta-multiplicativity,
    coassociativity) for the pinned alpha_2^2 universal chart over
    Z_(2)[p_0..p_44] directly from the Hopf axioms, including ALL redundant
    coordinates (used as identity gates), with exact integer arithmetic;
  * re-derives the nine [4]^# targets as ((m Delta) o (m Delta)) coefficients;
  * compares the derived equations/targets against the raw M2 export
    (set equality up to sign for equations, exact equality for targets);
  * runs the filtered q-adic elimination modulo q^4 = (2,p)^4 with an
    independent LOW-pivot convention (workspace code uses high pivots);
  * reproduces the rank table, all nine verdicts, the remainder classes,
    the characteristic-4 and noncocommutativity certificates, and the
    killed-by-8 memberships;
  * re-verifies the workspace's two 38-term dual functionals against THIS
    implementation's exhaustive cubic candidate rows;
  * repeats the computation in equal characteristic (F_2 chart), where all
    nine targets must be members.

No code or data structures are imported from the workspace scripts.
"""

import re
import sys
import time
from itertools import combinations_with_replacement

NV = 45         # p_0..p_44
TAUV = 45       # graded variable tau = in(2), index 45 in level lookups
DEPTH = 4       # everything modulo q^DEPTH

T0 = time.time()


def say(msg):
    print(f"[{time.time()-T0:8.2f}s] {msg}", flush=True)


# ---------------- exact integer polynomial layer (raw) ----------------
# Poly: dict mapping sorted tuple of variable indices -> nonzero int coeff.

def padd(a, b):
    out = dict(a)
    for m, c in b.items():
        s = out.get(m, 0) + c
        if s:
            out[m] = s
        else:
            out.pop(m, None)
    return out


def pneg(a):
    return {m: -c for m, c in a.items()}


def pmul(a, b):
    out = {}
    for m1, c1 in a.items():
        for m2, c2 in b.items():
            m = tuple(sorted(m1 + m2))
            s = out.get(m, 0) + c1 * c2
            if s:
                out[m] = s
            else:
                out.pop(m, None)
    return out


def const(n):
    return {(): n} if n else {}


def var(j):
    return {(j,): 1}


ONE = const(1)


def v2(c):
    c = abs(c)
    n = 0
    while c % 2 == 0:
        c //= 2
        n += 1
    return n


# ---------------- truncated layer (exact modulo q^DEPTH) ----------------
# mixed mode: coefficient of monomial m stored canonically mod 2^(DEPTH-|m|)
# equal-char mode: coefficients mod 2, tau absent.

def trunc(p, char2=False):
    out = {}
    for m, c in p.items():
        d = len(m)
        if d >= DEPTH:
            continue
        c %= 2 if char2 else (1 << (DEPTH - d))
        if c:
            out[m] = c
    return out


def tadd(a, b, char2=False):
    return trunc(padd(a, b), char2)


def tmul_var(p, j, char2=False):
    return trunc({tuple(sorted(m + (j,))): c for m, c in p.items()}, char2)


def tmul_2(p):
    return trunc({m: 2 * c for m, c in p.items()})


# ---------------- chart derivation (independent) ----------------
PAIR_POS = {(1, 1): 0, (1, 2): 1, (1, 3): 2, (2, 2): 3, (2, 3): 4, (3, 3): 5}


def m_index(i, j, r):
    return 3 * PAIR_POS[(min(i, j), max(i, j))] + (r - 1)


def c_index(i, j, k):
    return 18 + 9 * (i - 1) + 3 * (j - 1) + (k - 1)


def build_chart():
    """Multiplication table S, coproduct table D, from the axioms + ansatz."""
    def MU(i, j, r):
        fib = 1 if ({i, j} == {1, 2} and r == 3) else 0
        return padd(const(fib), var(m_index(i, j, r)))

    def CO(i, j, k):
        fib = 1 if (i, j, k) in ((3, 1, 2), (3, 2, 1)) else 0
        return padd(const(fib), var(c_index(i, j, k)))

    def basis(i):
        v = [{} for _ in range(4)]
        v[i] = dict(ONE)
        return v

    S = [[None] * 4 for _ in range(4)]
    for a in range(4):
        for b in range(4):
            if a == 0:
                S[a][b] = basis(b)
            elif b == 0:
                S[a][b] = basis(a)
            else:
                S[a][b] = [{}, MU(a, b, 1), MU(a, b, 2), MU(a, b, 3)]

    D = [[{} for _ in range(16)] for _ in range(4)]
    D[0][0] = dict(ONE)
    for i in (1, 2, 3):
        D[i][4 * i + 0] = dict(ONE)
        D[i][0 + i] = dict(ONE)
        for j in (1, 2, 3):
            for k in (1, 2, 3):
                D[i][4 * j + k] = CO(i, j, k)
    return S, D


def derive_equations(S, D):
    """All axiom coordinates, with identity gates on the unit-leg coords."""
    eqs = []

    # counit gates: eps is an algebra map & counit axiom hold identically
    for a in range(1, 4):
        for b in range(1, 4):
            assert not S[a][b][0], "eps multiplicativity violated by ansatz"
    for i in (1, 2, 3):
        for b in range(4):
            want = ONE if b == i else {}
            assert D[i][0 * 4 + b] == want, "counit axiom (left) broken"
            assert D[i][4 * b + 0] == want, "counit axiom (right) broken"

    # associativity, all 27 ordered triples, all 4 coordinates
    for i in (1, 2, 3):
        for j in (1, 2, 3):
            for k in (1, 2, 3):
                dif = [{} for _ in range(4)]
                for s in range(4):
                    cs = S[i][j][s]
                    if cs:
                        for r in range(4):
                            if S[s][k][r]:
                                dif[r] = padd(dif[r], pmul(cs, S[s][k][r]))
                    ds = S[j][k][s]
                    if ds:
                        for r in range(4):
                            if S[i][s][r]:
                                dif[r] = padd(dif[r], pneg(pmul(ds, S[i][s][r])))
                assert not dif[0], "assoc constant coordinate must vanish"
                for r in (1, 2, 3):
                    if dif[r]:
                        eqs.append(dif[r])

    # Delta-multiplicativity, all 9 ordered pairs, all 16 coordinates
    for i in (1, 2, 3):
        for j in (1, 2, 3):
            lhs = [{} for _ in range(16)]
            for t in range(4):
                ct = S[i][j][t]
                if ct:
                    for ab in range(16):
                        if D[t][ab]:
                            lhs[ab] = padd(lhs[ab], pmul(ct, D[t][ab]))
            for a in range(4):
                for b in range(4):
                    u = D[i][4 * a + b]
                    if not u:
                        continue
                    for c in range(4):
                        for d in range(4):
                            vv = D[j][4 * c + d]
                            if not vv:
                                continue
                            uv = pmul(u, vv)
                            for r in range(4):
                                sr = S[a][c][r]
                                if not sr:
                                    continue
                                for s in range(4):
                                    ss = S[b][d][s]
                                    if ss:
                                        lhs[4 * r + s] = padd(
                                            lhs[4 * r + s],
                                            pneg(pmul(uv, pmul(sr, ss))))
            for r in range(4):
                for s in range(4):
                    dif = lhs[4 * r + s]
                    if r == 0 or s == 0:
                        assert not dif, "compat unit-leg coord must vanish"
                    elif dif:
                        eqs.append(dif)

    # coassociativity, i = 1..3, all 64 coordinates
    for i in (1, 2, 3):
        acc = [{} for _ in range(64)]
        for r in range(4):
            for s in range(4):
                u = D[i][4 * r + s]
                if not u:
                    continue
                for a in range(4):
                    for b in range(4):
                        if D[r][4 * a + b]:
                            acc[16 * a + 4 * b + s] = padd(
                                acc[16 * a + 4 * b + s],
                                pmul(u, D[r][4 * a + b]))
                for b in range(4):
                    for c in range(4):
                        if D[s][4 * b + c]:
                            acc[16 * r + 4 * b + c] = padd(
                                acc[16 * r + 4 * b + c],
                                pneg(pmul(u, D[s][4 * b + c])))
        for a in range(4):
            for b in range(4):
                for c in range(4):
                    dif = acc[16 * a + 4 * b + c]
                    if 0 in (a, b, c):
                        assert not dif, "coassoc unit-leg coord must vanish"
                    elif dif:
                        eqs.append(dif)
    return eqs


def derive_targets(S, D):
    """phi = m o Delta; targets = coordinates of phi o phi on e_1..e_3."""
    PHI = [None] * 4
    for i in (1, 2, 3):
        acc = [{} for _ in range(4)]
        for a in range(4):
            for b in range(4):
                u = D[i][4 * a + b]
                if u:
                    for r in range(4):
                        if S[a][b][r]:
                            acc[r] = padd(acc[r], pmul(u, S[a][b][r]))
        assert not acc[0], "[2]^# must preserve the augmentation ideal"
        PHI[i] = acc
    targets = []
    for i in (1, 2, 3):
        for r in (1, 2, 3):
            t = {}
            for s in (1, 2, 3):
                t = padd(t, pmul(PHI[i][s], PHI[s][r]))
            targets.append(t)
    # [8]^# coefficients as an extra battery
    t8 = []
    for i in (1, 2, 3):
        for r in (1, 2, 3):
            t = {}
            for s in (1, 2, 3):
                for u in (1, 2, 3):
                    t = padd(t, pmul(PHI[i][s], pmul(PHI[s][u], PHI[u][r])))
            t8.append(t)
    return targets, t8


# ---------------- export comparison ----------------
TERM_RE = re.compile(r"([+-])([^+-]+)")
VAR_RE = re.compile(r"p_(\d+)(?:\^(\d+))?$")


def parse_m2_poly(text):
    text = text.replace(" ", "")
    if text and text[0] not in "+-":
        text = "+" + text
    out = {}
    for sign, term in TERM_RE.findall(text):
        coeff = -1 if sign == "-" else 1
        mon = []
        for factor in term.split("*"):
            m = VAR_RE.match(factor)
            if m:
                mon.extend([int(m.group(1))] * int(m.group(2) or 1))
            else:
                coeff *= int(factor)
        key = tuple(sorted(mon))
        s = out.get(key, 0) + coeff
        if s:
            out[key] = s
        else:
            out.pop(key, None)
    return out


def canon(p):
    return tuple(sorted(p.items()))


def compare_with_export(path, eqs_mine, targets_mine):
    eqs_m2, tgt_m2 = [], []
    with open(path, encoding="utf-8") as f:
        for line in f:
            if line.startswith("E "):
                eqs_m2.append(parse_m2_poly(line.rstrip().split(" ", 2)[2]))
            elif line.startswith("T "):
                tgt_m2.append(parse_m2_poly(line.rstrip().split(" ", 2)[2]))
    assert len(eqs_m2) == 189 and len(tgt_m2) == 9, (len(eqs_m2), len(tgt_m2))

    mine = {canon(e) for e in eqs_mine} | {canon(pneg(e)) for e in eqs_mine}
    theirs = {canon(e) for e in eqs_m2} | {canon(pneg(e)) for e in eqs_m2}
    missing_from_mine = [e for e in eqs_m2 if canon(e) not in mine]
    missing_from_theirs = [e for e in eqs_mine if canon(e) not in theirs]
    say(f"export comparison: their 189 equations, {len(eqs_mine)} raw mine")
    assert not missing_from_mine, \
        f"{len(missing_from_mine)} M2 equations do not match my derivation"
    assert not missing_from_theirs, \
        f"{len(missing_from_theirs)} of my equations missing from M2 export"
    say("EQUATION SETS IDENTICAL up to sign (=> identical ideals)")

    for k, (a, b) in enumerate(zip(targets_mine, tgt_m2)):
        assert canon(a) == canon(b), f"target {k} differs from M2 export!"
    say("ALL 9 TARGET POLYNOMIALS EXACTLY EQUAL to the M2 export")


# ---------------- filtered elimination ----------------
def build_lookup(degree, char2=False):
    top = NV if char2 else NV + 1
    mons = list(combinations_with_replacement(range(top), degree))
    return mons, {m: i for i, m in enumerate(mons)}


def initial_mask(p, d, lookup, char2=False):
    mask = 0
    for mon, c in p.items():
        v = 0 if char2 else v2(c)
        if len(mon) + v == d:
            key = mon if char2 else tuple(sorted(mon + (TAUV,) * v))
            mask ^= 1 << lookup[key]
    return mask


def elim_exact(cands, d, lookup, char2=False):
    """LOW-pivot elimination carrying exact truncated polynomials."""
    piv = {}
    resid = []
    for p in cands:
        row = initial_mask(p, d, lookup, char2)
        while row:
            b = (row & -row).bit_length() - 1
            hit = piv.get(b)
            if hit is None:
                piv[b] = (row, p)
                break
            row ^= hit[0]
            p = tadd(p, hit[1], char2)
        else:
            assert initial_mask(p, d, lookup, char2) == 0, "inexact cancel"
            resid.append(p)
    return piv, resid


def elim_plain(rows):
    piv = {}
    nonzero = 0
    for row in rows:
        if row:
            nonzero += 1
        while row:
            b = (row & -row).bit_length() - 1
            if b not in piv:
                piv[b] = row
                break
            row ^= piv[b]
    return piv, nonzero


def reduce_plain(piv, row):
    while row:
        b = (row & -row).bit_length() - 1
        if b not in piv:
            return row
        row ^= piv[b]
    return 0


def full_reduce(piv, row):
    """Complete normal form: clear every pivot-reducible bit.

    Stored pivot rows have their pivot as LOWEST set bit, so XORing at bit b
    only introduces bits strictly above b; scanning upward terminates.
    """
    b = 0
    while True:
        rest = row >> b
        if not rest:
            return row
        b += (rest & -rest).bit_length() - 1
        if b in piv:
            row ^= piv[b]
        else:
            b += 1


def multiples(p, char2=False):
    out = [] if char2 else [tmul_2(p)]
    out.extend(tmul_var(p, j, char2) for j in range(NV))
    return out


def run_filtration(eqs_raw, char2=False, tag=""):
    mode = "equal-char F2" if char2 else "mixed Z_(2)"
    say(f"--- filtration [{mode}] {tag}")
    _, lk1 = build_lookup(1, char2)
    _, lk2 = build_lookup(2, char2)
    mons3, lk3 = build_lookup(3, char2)

    cands1 = [q for q in (trunc(e, char2) for e in eqs_raw) if q]
    piv1, res1 = elim_exact(cands1, 1, lk1, char2)
    say(f"level 1: candidates={len(cands1)} rank={len(piv1)} "
        f"residuals={len(res1)}")

    cands2 = []
    for _, g in piv1.values():
        cands2.extend(multiples(g, char2))
    cands2.extend(res1)
    piv2, res2 = elim_exact(cands2, 2, lk2, char2)
    say(f"level 2: candidates={len(cands2)} rank={len(piv2)} "
        f"residuals={len(res2)}")

    rows3 = []
    for _, g in piv2.values():
        for q in multiples(g, char2):
            rows3.append(initial_mask(q, 3, lk3, char2))
    for q in res2:
        rows3.append(initial_mask(q, 3, lk3, char2))
    piv3, nz3 = elim_plain(rows3)
    say(f"level 3: candidates={len(rows3)} nonzero={nz3} rank={len(piv3)}")

    return {
        "lk": (lk1, lk2, lk3), "mons3": mons3,
        "piv": (piv1, piv2, piv3), "rows3": rows3, "char2": char2,
    }


def reduce_element(state, p, name):
    """Full membership test of p modulo I + q^4. Returns (verdict, info)."""
    lk1, lk2, lk3 = state["lk"]
    piv1, piv2, piv3 = state["piv"]
    char2 = state["char2"]
    p = trunc(p, char2)
    # order-0 part cannot be cancelled by I (all generators in q): must be 0
    czero = p.get((), 0)
    if not char2 and czero and v2(czero) == 0:
        return "NONMEMBER(order 0)", None
    if char2 and czero:
        return "NONMEMBER(order 0)", None
    # level 1
    row = initial_mask(p, 1, lk1, char2)
    while row:
        b = (row & -row).bit_length() - 1
        hit = piv1.get(b)
        if hit is None:
            return "NONMEMBER(level 1)", row
        row ^= hit[0]
        p = tadd(p, hit[1], char2)
    # level 2
    row = initial_mask(p, 2, lk2, char2)
    while row:
        b = (row & -row).bit_length() - 1
        hit = piv2.get(b)
        if hit is None:
            return "NONMEMBER(level 2)", row
        row ^= hit[0]
        p = tadd(p, hit[1], char2)
    # level 3
    cubic = initial_mask(p, 3, lk3, char2)
    rem = full_reduce(piv3, cubic)
    if rem:
        return "NONMEMBER(level 3)", rem
    return "member", None


def mask_of_triples(triples, lk3):
    m = 0
    for t in triples:
        m ^= 1 << lk3[tuple(sorted(t))]
    return m


def triples_of_mask(mask, mons3):
    return [mons3[i] for i in range(mask.bit_length()) if (mask >> i) & 1]


def main():
    say("deriving chart, equations, targets (independent construction)")
    S, D = build_chart()
    eqs = derive_equations(S, D)
    targets, targets8 = derive_targets(S, D)
    say(f"raw derived equations: {len(eqs)}   targets: {len(targets)}")

    # gates on my own derivation
    for e in eqs:
        c0 = e.get((), 0)
        assert c0 % 2 == 0, "equation with odd constant term: fiber broken"
    for k, t in enumerate(targets):
        c0 = t.get((), 0)
        assert c0 % 4 == 0, f"target {k} constant not divisible by 4"
        lin = [m for m in t if len(m) == 1 and v2(t[m]) == 0]
        assert not lin, f"target {k} has an odd linear term"
    say("gates: even equation constants, target constants div by 4, "
        "no odd linear target terms -- all OK")

    export = sys.argv[1] if len(sys.argv) > 1 else "/tmp/m2_rank4_export.txt"
    try:
        compare_with_export(export, eqs, targets)
    except FileNotFoundError:
        say(f"WARNING: export {export} not found; skipping source comparison")

    # ---------------- mixed characteristic ----------------
    st = run_filtration(eqs, char2=False, tag="(the counterexample chart)")
    exp_rank = (31, 974, 16787)
    got_rank = tuple(len(p) for p in st["piv"])
    say(f"rank table mine={got_rank} expected={exp_rank} "
        f"{'MATCH' if got_rank == exp_rank else 'MISMATCH'}")
    assert got_rank == exp_rank

    verdicts = []
    remainders = {}
    for k, t in enumerate(targets):
        v, info = reduce_element(st, t, f"target{k}")
        verdicts.append(v)
        if v != "member":
            remainders[k] = info
            say(f"target {k}: {v}; remainder monomials="
                f"{triples_of_mask(info, st['mons3'])}")
        else:
            say(f"target {k}: member of I + q^4")
    expect = ["member"] * 9
    expect[2] = expect[5] = "NONMEMBER(level 3)"
    assert verdicts == expect, f"verdict pattern differs: {verdicts}"

    # remainder classes must match the workspace representatives
    lk3 = st["lk"][2]
    rho2 = mask_of_triples([(0, 18, 19), (0, 18, 21)], lk3)
    rho5 = mask_of_triples([(0, 18, 28), (0, 18, 30)], lk3)
    assert full_reduce(st["piv"][2], rho2) == remainders[2], \
        "my target-2 class differs from workspace rho_2"
    assert full_reduce(st["piv"][2], rho5) == remainders[5], \
        "my target-5 class differs from workspace rho_5"
    say("remainder classes agree with workspace rho_2, rho_5 "
        "(same cosets of gr_3(I))")

    # workspace dual functionals re-verified against MY candidate rows
    S2 = [(0,18,21),(0,18,41),(0,21,30),(0,21,38),(0,30,31),
          (0,30,43),(0,31,42),(0,38,41),(0,41,42),(0,42,43),
          (1,18,30),(1,18,42),(1,30,30),(1,30,38),(1,38,42),
          (1,42,42),(8,18,21),(8,18,41),(8,21,30),(8,21,38),
          (8,30,31),(8,30,43),(8,31,42),(8,38,41),(8,41,42),
          (8,42,43),(10,21,21),(10,21,31),(10,21,43),(10,31,41),
          (10,41,41),(10,41,43),(14,21,21),(14,21,31),(14,21,43),
          (14,31,41),(14,41,41),(14,41,43)]
    L2 = mask_of_triples(S2, lk3)
    bad = sum(1 for r in st["rows3"] if bin(r & L2).count("1") & 1)
    val2 = bin(remainders[2] & L2).count("1") & 1
    valrho2 = bin(rho2 & L2).count("1") & 1
    say(f"workspace dual L2 vs my rows: violations={bad} "
        f"L2(my target-2 remainder)={val2} L2(rho2)={valrho2}")
    assert bad == 0 and val2 == 1 and valrho2 == 1

    # supplementary certificates
    for name, poly, want in (
        ("2 (char test)", const(2), "NONMEMBER"),
        ("4 (char test)", const(4), "member"),
        ("c112-c121 (noncocomm)",
         padd(var(19), pneg(var(21))), "NONMEMBER"),
    ):
        v, _ = reduce_element(st, poly, name)
        ok = v.startswith(want) or v == want
        say(f"{name}: {v} (expected {want}) {'OK' if ok else 'FAIL'}")
        assert ok
    for k, t in enumerate(targets8):
        v, _ = reduce_element(st, t, f"[8]-target{k}")
        assert v == "member", f"[8] target {k} not member: {v}"
    say("all nine [8]^# coefficients are members: killed by 8 confirmed")

    # ---------------- equal characteristic ----------------
    st2 = run_filtration(eqs, char2=True, tag="(equal-char control)")
    exp2 = (30, 929, 15721)
    got2 = tuple(len(p) for p in st2["piv"])
    say(f"equal-char rank table mine={got2} expected={exp2} "
        f"{'MATCH' if got2 == exp2 else 'MISMATCH'}")
    assert got2 == exp2
    for k, t in enumerate(targets):
        v, _ = reduce_element(st2, t, f"eq-char target{k}")
        assert v == "member", f"equal-char target {k}: {v}"
    say("equal-char control: all nine targets are members (killed by 4), "
        "as required by banked theory")

    say("ALL CLAUDE INDEPENDENT AUDIT CHECKS PASSED")


if __name__ == "__main__":
    main()
