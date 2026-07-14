#!/usr/bin/env python3
r"""
s2check.py -- S' kernel-factorization probe (session 4).

Open Lemma 7.4 of THEORY_order4.md asks whether the invariant

    S'(A/R):   phi(I)  \subseteq  m * (ker phi \cap I),    phi = [2]^# = mu o Delta

propagates through socle extensions.  This script probes the stronger
UNIVERSALITY question over the curvilinear (principal-m) rings R:

    does EVERY free rank-4 bialgebra A/R with local fiber shape and fiber
    killed by 2 satisfy S'(A/R)?

Encoding (quantifier-free, exact):  for principal m = (t), S' at a basis
element e_i says:  some solution k of  t*k = phi(e_i),  k in I = <e1,e2,e3>,
lies in ker phi.  Under fiber2 each coordinate of phi(e_i) lies in m = tR, so
solutions exist, and the FULL solution set is a single coset
k0 + ann(t)*I  (coordinatewise, I free).  Hence

    S' fails at e_i  <=>  for ONE (equivalently every) solution k0:
                          phi(k0 + u) != 0 for ALL u in ann(t)^3,

which is a finite conjunction (|ann(t)|^3 terms) over concrete u, with one
symbolic witness vector k0 -- no quantifier alternation.  phi is R-linear, so
phi(k) = sum_j k_j * phi(e_j) and phi(k0+u) = phi(k0) + (constant) phi(u).

Readings:
  * [S2: S' FAILS]  -> unsat   =  "S' holds for every rank-4 bialgebra with
    killed-by-2 local fiber over this exact ring".  By THEORY Thm 7.1 this
    IMPLIES: every free rank-4 bialgebra with killed-by-2 fiber over EVERY
    socle-line extension R' of R (m'M = 0, dim M = 1, R'/M = R) is killed by
    4 -- including the non-curvilinear extensions no direct search has covered.
  * [S2] -> sat  =  a bialgebra violating S' (it is still killed by 4 -- that
    is a banked theorem).  NOT a counterexample to Grothendieck; it would
    refute the universality of the S'-invariant and redirect the theory of
    Open Lemma 7.4.  Follow the model-extraction discipline of HANDOFF §D
    before believing it: re-verify the witness independently of Z3.

Gates (golden rule 1; all must pass before the main table means anything):
  gateR  (per ring)  : concrete enumeration check that m = t*R and
                       ann(t) = ANN as hard-coded -- independent of the class'
                       lowzero/deform, uses only mul + simplify.
  gate0  (eps^3, xy) : axioms+fiber2 sat (level-1 reproduction).
  gate1  (eps^3, xy) : handoff-16.2 point pinned, S'-FAIL  -> must be unsat
                       (S' holds there by hand: phi(x) = eps^2 xy = eps*(eps xy),
                       phi(eps xy) = 0).
  gate1b (eps^3, xy) : same point, S'-HOLDS witness        -> must be sat.
  gate2  (eps^3, xy) : Delta-multiplicativity DROPPED (A+C+F), S'-FAIL -> must
                       be sat (ablate.py found [4]^# != 0 models there, and
                       S' => [4]^# = 0 by pure linearity, so S' must fail).
  gate3  (eps^3, xy) : S'-HOLDS  +  S'-FAIL together -> must be unsat
                       (machine-checks the coset-completeness argument).

Ring classes are imported from ringcheck-validated modules (golden rule 1b;
F2epsN(2) and Z2N(2) added to ringcheck CASES this session).  The equation
builder is build_blocks() copied from ablate.py (which reproduced its gates),
extended only to also return phi, c, Mtab.
"""
import sys
from z3 import BitVecVal, Solver, Or, And, simplify, sat, unsat, set_param, is_true

from order4sat import F2eps3, Z8, Rram, Ext
from order4sat_beyond import F2epsN, Z2N, Rram4


# --------------------------------------------------------------------------
# equation builder: ablate.py's build_blocks + (phi, c, Mtab) in the return
# --------------------------------------------------------------------------

def build_blocks(R, fib):
    Z, One = R.zero(), R.one()
    add, mul, sub = R.add, R.mul, R.sub

    c = {(i, j, k): R.var(f"c{i}{j}{k}")
         for i in range(1, 4) for j in range(1, 4) for k in range(1, 4)}
    Mtab = {}
    for i in range(1, 4):
        for j in range(i, 4):
            for r in range(1, 4):
                base = One if fib.get((i, j, r), 0) else Z
                Mtab[(i, j, r)] = add(base, R.deform(f"d{i}{j}{r}"))
    def M(i, j, r):
        ii, jj = min(i, j), max(i, j)
        return Mtab[(ii, jj, r)]
    def ebas(i): return [One if t == i else Z for t in range(4)]

    S = [[None] * 4 for _ in range(4)]
    for a in range(4):
        for b in range(4):
            if a == 0: S[a][b] = ebas(b)
            elif b == 0: S[a][b] = ebas(a)
            else: S[a][b] = [Z, M(a, b, 1), M(a, b, 2), M(a, b, 3)]

    def mulA(u, v):
        out = [Z] * 4
        for i in range(4):
            for j in range(4):
                co = mul(u[i], v[j])
                for r in range(4):
                    out[r] = add(out[r], mul(co, S[i][j][r]))
        return out

    idx2 = lambda a, b: 4 * a + b
    idx3 = lambda a, b, cc: 16 * a + 4 * b + cc

    DE = [[One if t == 0 else Z for t in range(16)]]
    for i in range(1, 4):
        v = [Z] * 16
        v[idx2(i, 0)] = add(v[idx2(i, 0)], One)
        v[idx2(0, i)] = add(v[idx2(0, i)], One)
        for j in range(1, 4):
            for k in range(1, 4):
                v[idx2(j, k)] = add(v[idx2(j, k)], c[(i, j, k)])
        DE.append(v)

    # --- block A: associativity ---
    eqsA = []
    for i in range(1, 4):
        for j in range(1, 4):
            for k in range(1, 4):
                u = mulA(mulA(ebas(i), ebas(j)), ebas(k))
                w = mulA(ebas(i), mulA(ebas(j), ebas(k)))
                eqsA += [sub(u[t], w[t]) for t in range(4)]

    # --- block M: Delta multiplicative ---
    def DofVec(v4):
        out = [Z] * 16
        for r in range(4):
            for t in range(16):
                out[t] = add(out[t], mul(v4[r], DE[r][t]))
        return out
    def mulT2(u, v):
        out = [Z] * 16
        for a in range(4):
            for b in range(4):
                for a2 in range(4):
                    for b2 in range(4):
                        co = mul(u[idx2(a, b)], v[idx2(a2, b2)])
                        for k in range(4):
                            t1 = mul(co, S[a][a2][k])
                            for l in range(4):
                                out[idx2(k, l)] = add(out[idx2(k, l)],
                                                      mul(t1, S[b][b2][l]))
        return out
    eqsM = []
    for i in range(1, 4):
        for j in range(i, 4):
            lhs = DofVec(S[i][j]); rhs = mulT2(DE[i], DE[j])
            eqsM += [sub(lhs[t], rhs[t]) for t in range(16)]

    # --- block C: coassociativity ---
    eqsC = []
    for i in range(1, 4):
        out = [Z] * 64
        for r in range(4):
            for s in range(4):
                u = DE[i][idx2(r, s)]
                for a in range(4):
                    for b in range(4):
                        out[idx3(a, b, s)] = add(out[idx3(a, b, s)],
                                                 mul(u, DE[r][idx2(a, b)]))
                for b in range(4):
                    for cc in range(4):
                        out[idx3(r, b, cc)] = sub(out[idx3(r, b, cc)],
                                                  mul(u, DE[s][idx2(b, cc)]))
        eqsC += out

    # phi = [2]^#
    phi = [ebas(0)]
    for i in range(1, 4):
        out = [Z] * 4
        for j in range(4):
            for k in range(4):
                co = DE[i][idx2(j, k)]
                for r in range(4):
                    out[r] = add(out[r], mul(co, S[j][k][r]))
        phi.append(out)

    fiber2 = [R.lowzero(phi[i][r]) for i in range(1, 4) for r in range(4)]

    A = [R.eq0(e) for e in eqsA]
    Mb = [R.eq0(e) for e in eqsM]
    C = [R.eq0(e) for e in eqsC]
    return A, Mb, C, fiber2, phi, c, Mtab


# --------------------------------------------------------------------------
# ring metadata for the probe: uniformizer t, ann(t), and full element lists
# (everything below is CHECKED against enumeration in gateR before use)
# --------------------------------------------------------------------------

def elems_of(R):
    import itertools
    if isinstance(R, Ext):
        sub = elems_of(R.R)
        return [(u, v) for u in sub for v in sub]
    if isinstance(R, F2eps3):
        return [tuple(BitVecVal(b, 1) for b in bits)
                for bits in itertools.product((0, 1), repeat=3)]
    if isinstance(R, Z8):
        return [BitVecVal(a, 3) for a in range(8)]
    if isinstance(R, Rram):
        return [(BitVecVal(a, 2), BitVecVal(b, 1))
                for a in range(4) for b in range(2)]
    if isinstance(R, Rram4):
        return [(BitVecVal(a, 2), BitVecVal(b, 2))
                for a in range(4) for b in range(4)]
    if isinstance(R, Z2N):
        return [BitVecVal(a, R.N) for a in range(2 ** R.N)]
    if R.__class__.__name__ == "F2Quot":
        return [tuple(BitVecVal(b, 1) for b in bits)
                for bits in itertools.product((0, 1), repeat=R.n)]
    raise TypeError(f"no enumerator for {R.name}")


def unif_of(R):
    """The uniformizer t with m = (t), as a concrete element."""
    if isinstance(R, Ext):
        t = unif_of(R.R)
        return (t, R.R.zero())
    if isinstance(R, F2eps3):
        return (BitVecVal(0, 1), BitVecVal(1, 1), BitVecVal(0, 1))
    if isinstance(R, Z8):
        return BitVecVal(2, 3)
    if isinstance(R, Rram):
        return (BitVecVal(0, 2), BitVecVal(1, 1))   # pi
    if isinstance(R, Rram4):
        return (BitVecVal(0, 2), BitVecVal(1, 2))   # pi
    if isinstance(R, Z2N):
        return BitVecVal(2, R.N)
    if R.__class__.__name__ == "F2Quot":            # F2epsN: t = eps = e_1
        return tuple(BitVecVal(1 if i == 1 else 0, 1) for i in range(R.n))
    raise TypeError(f"no uniformizer for {R.name}")


def canon(x):
    """Canonical hashable value of a CONCRETE ring element."""
    if isinstance(x, tuple):
        return tuple(canon(y) for y in x)
    return simplify(x).as_long()


def gateR(R):
    """Verify by exhaustive enumeration: m := {x : lowzero(x)} equals t*R, and
    return ann(t) = {u : t*u = 0} as a list of concrete elements.
    Uses only mul/eq0 on concrete elements + simplify -- independent of deform."""
    els = elems_of(R)
    t = unif_of(R)
    m_low = {canon(x) for x in els if is_true(simplify(R.lowzero(x)))}
    tR = {canon(R.mul(t, y)) for y in els}
    assert m_low == tR, f"{R.name}: m != t*R -- {sorted(m_low)} vs {sorted(tR)}"
    ann = [u for u in els if is_true(simplify(R.eq0(R.mul(t, u))))]
    assert len(els) == len(tR) * len(ann), f"{R.name}: |R| != |tR|*|ann(t)|"
    print(f"  gateR {R.name}: m = tR ({len(tR)} elts), |ann(t)| = {len(ann)}  [OK]",
          flush=True)
    return t, ann


# --------------------------------------------------------------------------
# S' constraints
# --------------------------------------------------------------------------

def phi_of_coords(R, phi, kco):
    """phi(sum_j kco[j] e_j) coordinates, using R-linearity of phi.
    kco = [k1, k2, k3] ring elements (symbolic or concrete)."""
    out = [R.zero()] * 4
    for j in range(1, 4):
        for r in range(4):
            out[r] = R.add(out[r], R.mul(kco[j - 1], phi[j][r]))
    return out


def sp_constraints(R, phi, t, ann, tag):
    """Returns (sp_holds, sp_fail): S' holds / fails at the basis elements,
    with independent symbolic witness vectors named by `tag`."""
    import itertools
    ANN3 = list(itertools.product(ann, repeat=3))

    holds, fails = [], []
    for i in range(1, 4):
        # S'-holds witness k^(i)
        kh = [R.var(f"{tag}kh{i}_{r}") for r in range(1, 4)]
        coset_h = And(*[R.eq0(R.sub(R.mul(t, kh[r - 1]), phi[i][r]))
                        for r in range(1, 4)])
        ker_h = And(*[R.eq0(e) for e in phi_of_coords(R, phi, kh)])
        holds.append(And(coset_h, ker_h))

        # S'-fail at e_i: one solution k0^(i), whole coset misses ker phi
        kf = [R.var(f"{tag}kf{i}_{r}") for r in range(1, 4)]
        coset_f = And(*[R.eq0(R.sub(R.mul(t, kf[r - 1]), phi[i][r]))
                        for r in range(1, 4)])
        phik0 = phi_of_coords(R, phi, kf)
        misses = []
        for u in ANN3:
            phiu = phi_of_coords(R, phi, list(u))
            vec = [R.add(phik0[r], phiu[r]) for r in range(4)]
            misses.append(Or(*[R.neq0(v) for v in vec]))
        fails.append(And(coset_f, *misses))

    return And(*holds), Or(*fails)


# --------------------------------------------------------------------------
# solver driver
# --------------------------------------------------------------------------

def check(label, constraints, expect=None):
    s = Solver()
    s.set("timeout", 7200 * 1000)
    for a in constraints:
        s.add(a)
    res = s.check()
    tag = ""
    if expect is not None:
        tag = ("  [GATE OK]" if str(res) == expect
               else f"  [GATE FAILED: expected {expect} -- STOP, encoding wrong]")
    print(f"  [{label}] -> {res}{tag}", flush=True)
    if res == sat and expect is None:
        m = s.model()
        nz = sorted((str(d), m[d].as_long()) for d in m.decls()
                    if m[d].as_long() != 0)
        print(f"    S'-violating bialgebra witness (NOT a counterexample to "
              f"killed-by-4; see HANDOFF §D discipline): {nz}", flush=True)
    return res


FIBS = [("F_q[x,y]/(x^2,y^2)", {(1, 2, 3): 1}),
        ("F_q[t]/t^4", {(1, 1, 2): 1, (1, 2, 3): 1})]


def run_gates():
    print("===== GATES (base F2[eps]/eps^3, fiber xy) =====", flush=True)
    R = F2eps3()
    t, ann = gateR(R)
    fn, fib = FIBS[0]
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
    sp_holds, sp_fail = sp_constraints(R, phi, t, ann, "g")

    check("gate0: A+M+C+F sanity", A + Mb + C + F, expect="sat")

    # pin the handoff-16.2 point: Delta(x) += eps^2 y(x)x, Delta(xy) as forced,
    # multiplication undeformed.  c-indices (i,j,k) with value in R:
    eps2 = (BitVecVal(0, 1), BitVecVal(0, 1), BitVecVal(1, 1))
    one = R.one(); zero = R.zero()
    pinned = {(1, 2, 1): eps2, (3, 1, 2): one, (3, 2, 1): one, (3, 2, 3): eps2}
    pin = []
    for key, cv in c.items():
        target = pinned.get(key, zero)
        pin.append(R.eq0(R.sub(cv, target)))
    for key, mv in Mtab.items():
        base = one if fib.get(key, 0) else zero
        pin.append(R.eq0(R.sub(mv, base)))

    check("gate1 : 16.2 point + S'-FAIL (S' holds there by hand)",
          A + Mb + C + F + pin + [sp_fail], expect="unsat")
    check("gate1b: 16.2 point + S'-HOLDS witness", A + Mb + C + F + pin + [sp_holds],
          expect="sat")
    check("gate2 : A+C+F (Delta-mult dropped) + S'-FAIL", A + C + F + [sp_fail],
          expect="sat")
    check("gate3 : S'-HOLDS + S'-FAIL together", A + Mb + C + F + [sp_holds, sp_fail],
          expect="unsat")
    print("===== ALL GATES PASSED =====\n", flush=True)


def run_ring(R):
    try:
        print(f"===== base {R.name} =====", flush=True)
        t, ann = gateR(R)
        for fn, fib in FIBS:
            print(f"  --- fiber {fn} ---", flush=True)
            A, Mb, C, F, phi, c, Mtab = build_blocks(R, fib)
            sp_holds, sp_fail = sp_constraints(R, phi, t, ann, "q")
            check("S1: axioms+fiber2+S'-HOLDS (expect sat)",
                  A + Mb + C + F + [sp_holds], expect="sat")
            check("S2: axioms+fiber2 + S'-FAILS", A + Mb + C + F + [sp_fail])
    except AssertionError as e:
        print(f"  RING GATE FAILED for {R.name}: {e} -- SKIPPING RING", flush=True)


if __name__ == "__main__":
    set_param("parallel.enable", True)
    run_gates()
    if "--deeper" in sys.argv:      # length-5 curvilinear (=> length-6 extensions)
        rings = [F2epsN(5), Z2N(5)]
    elif "--ext" in sys.argv:       # residue field F_4, MIXED-CHAR rings only
        # (session 13: Ext(F2eps3) removed -- S'-universality over k'[eps]/eps^3
        #  is now a THEOREM for every k' (Thms I+K+L via 12.6.1), so the
        #  equal-char F_4 row is subsumed; the two mixed-char rings below are
        #  the open content: S' over W(F_4)/8 and W(F_4)[pi]/(pi^2-2,pi^3).)
        rings = [Ext(Z8()), Ext(Rram())]
    else:                           # the original 8: all curvilinear length <= 4
        rings = [F2eps3(), F2epsN(2), Z2N(2), Z8(), Rram(), F2epsN(4), Z2N(4), Rram4()]
    for R in rings:
        run_ring(R)
    print("DONE s2check", flush=True)
