#!/usr/bin/env python3
"""
ringcheck.py -- VALIDATION GATE for every base-ring class used by the Z3 search.

Motivation (golden rule 1 of HANDOFF_NEXT.md, applied to the *ring* layer):
the SAT results are only as good as the arithmetic of the base-ring classes.
A wrong multiplication table or a wrong `deform`/`lowzero` silently turns an
UNSAT into a meaningless statement.  Nothing in the existing scripts ever
checked these.  This script does, by two independent means:

  (1) AXIOMS, checked on concrete elements (exhaustive for small rings,
      randomised for big ones):
        commutativity, associativity, distributivity, 0/1 units,
        additive inverses.
  (2) REFERENCE CROSS-CHECK against a completely independent implementation
      (plain Python integer / polynomial arithmetic, reducing modulo the
      defining ideal by hand) for every ring where such a model is available.

  (3) SEMANTICS of the two hooks the search relies on:
        * m := { x : lowzero(x) } is an ideal, is nilpotent, and has the right
          codimension  (=> R is local with the intended residue field);
        * `deform(tag)` ranges over exactly m  (the search uses it to write the
          most general m-deformation of the fiber structure constants);
        * eq0 / neq0 are complementary.

Run:  <z3venv>/bin/python scripts/ringcheck.py
Exit code 0 and a final "ALL RING CHECKS PASSED" line = every class is sound.
"""
import itertools
import random
import sys

from z3 import BitVecVal, simplify, is_true, Solver, sat, unsat, Not, And

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from order4sat import F2eps3, Z8, Rram, Ext
from order4sat_beyond import F2Quot, F2epsN, FatPoint3, FatPoint2, BiDual, Z2N, Rram4
from order4sat_f8 import Ext3

random.seed(20260708)

# --------------------------------------------------------------------------
# concrete-element plumbing:  turn a z3 expression tree of constants into ints
# --------------------------------------------------------------------------

def ev(x):
    """Evaluate a (nested tuple of) z3 bitvector constant expression(s)."""
    if isinstance(x, tuple):
        return tuple(ev(v) for v in x)
    return simplify(x).as_long()


def istrue(b):
    return is_true(simplify(b))


class Tab:
    """Value-level view of a ring class.

    Every element is identified with its concrete value `ev(e)`; products and
    sums are computed through z3 at most once per argument pair and then cached,
    so the cubic axiom sweeps run as pure integer arithmetic.  `els` must be the
    complete element list, so that products can always be resolved back to a
    representative expression.
    """

    def __init__(self, R, els):
        self.R = R
        self.by_val = {ev(e): e for e in els}
        self.vals = list(self.by_val)
        self.zero, self.one = ev(R.zero()), ev(R.one())
        self._mul, self._add, self._sub = {}, {}, {}

    def _bin(self, cache, op, u, v):
        k = (u, v)
        if k not in cache:
            cache[k] = ev(op(self.by_val[u], self.by_val[v]))
        return cache[k]

    def mul(self, u, v): return self._bin(self._mul, self.R.mul, u, v)
    def add(self, u, v): return self._bin(self._add, self.R.add, u, v)
    def sub(self, u, v): return self._bin(self._sub, self.R.sub, u, v)

    def lowzero(self, u): return istrue(self.R.lowzero(self.by_val[u]))
    def eq0(self, u):     return istrue(self.R.eq0(self.by_val[u]))
    def neq0(self, u):    return istrue(self.R.neq0(self.by_val[u]))


# --------------------------------------------------------------------------
# element enumerators.  Each returns a list of ring elements in the class's
# own representation, built out of BitVecVal so that ev() can read them back.
# --------------------------------------------------------------------------

def enum_F2Quot(R):
    return [tuple(BitVecVal(b, 1) for b in bits)
            for bits in itertools.product((0, 1), repeat=R.n)]

def enum_Z2N(R):
    return [BitVecVal(a, R.N) for a in range(2 ** R.N)]

def enum_F2eps3(R):
    return [tuple(BitVecVal(b, 1) for b in bits)
            for bits in itertools.product((0, 1), repeat=3)]

def enum_Z8(R):
    return [BitVecVal(a, 3) for a in range(8)]

def enum_Rram(R):        # a in Z/4, b in Z/2
    return [(BitVecVal(a, 2), BitVecVal(b, 1))
            for a in range(4) for b in range(2)]

def enum_Rram4(R):       # a, b in Z/4
    return [(BitVecVal(a, 2), BitVecVal(b, 2))
            for a in range(4) for b in range(4)]

def enum_Ext(R):
    sub = enum_of(R.R)
    return [(u, v) for u in sub for v in sub]

def enum_Ext3(R):
    sub = enum_of(R.R)
    return [(u, v, z) for u in sub for v in sub for z in sub]


def enum_of(R):
    if isinstance(R, Ext3):   return enum_Ext3(R)
    if isinstance(R, Ext):    return enum_Ext(R)
    if isinstance(R, F2Quot): return enum_F2Quot(R)
    if isinstance(R, Z2N):    return enum_Z2N(R)
    if isinstance(R, F2eps3): return enum_F2eps3(R)
    if isinstance(R, Z8):     return enum_Z8(R)
    if isinstance(R, Rram4):  return enum_Rram4(R)
    if isinstance(R, Rram):   return enum_Rram(R)
    raise TypeError(f"no enumerator for {R}")


# --------------------------------------------------------------------------
# (1) ring axioms
# --------------------------------------------------------------------------

def sample(els, cap):
    return els if len(els) <= cap else random.sample(els, cap)


def check_axioms(T, probe, triple_cap=26):
    name = T.R.name
    Z, One = T.zero, T.one

    # additive group + units
    for a in probe:
        assert T.add(a, Z) == a,   f"{name}: a+0 != a"
        assert T.mul(a, One) == a, f"{name}: a*1 != a"
        assert T.mul(a, Z) == Z,   f"{name}: a*0 != 0"
        assert T.sub(a, a) == Z,   f"{name}: a-a != 0"

    # commutativity + add/sub coherence
    for a, b in itertools.product(probe, probe):
        assert T.mul(a, b) == T.mul(b, a),   f"{name}: mul not commutative"
        assert T.add(a, b) == T.add(b, a),   f"{name}: add not commutative"
        assert T.add(T.sub(a, b), b) == a,   f"{name}: (a-b)+b != a"

    # associativity + distributivity: cubic, so cap the triple sweep
    tri = sample(probe, triple_cap)
    for a, b, c in itertools.product(tri, tri, tri):
        assert T.mul(T.mul(a, b), c) == T.mul(a, T.mul(b, c)), \
            f"{name}: mul NOT ASSOCIATIVE at {a},{b},{c}"
        assert T.add(T.add(a, b), c) == T.add(a, T.add(b, c)), \
            f"{name}: add not associative"
        assert T.mul(a, T.add(b, c)) == T.add(T.mul(a, b), T.mul(a, c)), \
            f"{name}: NOT DISTRIBUTIVE at {a},{b},{c}"
    return len(probe), len(tri)


# --------------------------------------------------------------------------
# (3) locality semantics: m = {lowzero}, ideal, nilpotent, codim, deform image
# --------------------------------------------------------------------------

def add_closure(T, seed):
    """Additive span of `seed` (a set of element-values), inside the ring."""
    cur = set(seed) | {T.zero}
    frontier = list(cur)
    while frontier:
        nxt = []
        for u in frontier:
            for v in list(cur):
                w = T.add(u, v)
                if w not in cur:
                    cur.add(w)
                    nxt.append(w)
        frontier = nxt
    return cur


def check_locality(T, expect_residue_deg=None):
    """Exhaustive: T must hold ALL elements (codim/nilpotency need that)."""
    R, name = T.R, T.R.name
    els = T.vals
    m = [a for a in els if T.lowzero(a)]
    ks = set(m)

    # eq0/neq0 complementary, and eq0 really means "= 0"
    for a in els:
        z, nz = T.eq0(a), T.neq0(a)
        assert z != nz, f"{name}: eq0/neq0 not complementary at {a}"
        assert z == (a == T.zero), f"{name}: eq0 wrong at {a}"

    # m is an additive subgroup and an ideal
    for a in m:
        for b in m:
            assert T.add(a, b) in ks, f"{name}: m not closed under +"
    for a in m:
        for r in els:
            assert T.mul(r, a) in ks, f"{name}: m NOT AN IDEAL"

    # Every element OUTSIDE m is a unit.  This is what actually makes m the
    # unique maximal ideal (=> R local, R/m a field).  Without it, "codim of m"
    # says nothing about a residue *field*.
    for a in els:
        if a in ks:
            continue
        assert any(T.mul(a, b) == T.one for b in els), \
            f"{name}: {a} lies outside m but is NOT A UNIT => m not maximal"

    # m nilpotent.  m^{k+1} = additive span of { x*y : x in m, y in m^k }.
    cur, powers = set(ks), [len(ks)]
    for _ in range(32):
        if cur == {T.zero}:
            break
        prods = {T.mul(a, v) for a in m for v in cur}
        nxt = add_closure(T, prods)
        assert nxt != cur, f"{name}: m NOT NILPOTENT (m^k stabilised at {len(cur)})"
        cur = nxt
        powers.append(len(cur))
    else:
        raise AssertionError(f"{name}: m not nilpotent within 32 steps")

    # codim of m  => residue field size (needs the FULL element list)
    assert len(els) % len(ks) == 0, f"{name}: |R| not divisible by |m|"
    q = len(els) // len(ks)
    if expect_residue_deg is not None:
        assert q == 2 ** expect_residue_deg, \
            f"{name}: residue field has {q} elements, expected {2**expect_residue_deg}"

    # `deform(tag)` must range over exactly m: (a) never escapes m,
    # (b) attains every element of m.  Both decided symbolically by Z3.
    d = R.deform("chk")
    s = Solver(); s.add(Not(R.lowzero(d)))
    assert s.check() == unsat, f"{name}: deform() can leave m"
    for a in m:
        s = Solver(); s.add(R.eq0(R.sub(d, T.by_val[a])))
        assert s.check() == sat, f"{name}: deform() cannot attain {a} in m"

    return len(ks), q, powers


# --------------------------------------------------------------------------
# (2) independent reference implementations
# --------------------------------------------------------------------------

def ref_check_Z2N(R, els):
    """Z/2^N against plain python ints.  (order4sat.Z8 has no .N; it is Z/8.)"""
    M = 2 ** getattr(R, "N", 3)
    for a, b in itertools.product(els, els):
        x, y = ev(a), ev(b)
        assert ev(R.mul(a, b)) == (x * y) % M
        assert ev(R.add(a, b)) == (x + y) % M
        assert ev(R.sub(a, b)) == (x - y) % M
    return f"vs python ints mod {M}"


def _poly_mul_pi(x, y, mod_a, mod_b):
    """(a+b*pi)(c+d*pi) in Z[pi]/(pi^2-2), coefficients reduced afterwards."""
    a, b = x
    c, d = y
    return ((a * c + 2 * b * d) % mod_a, (a * d + b * c) % mod_b)


def ref_check_Rram(R, els):
    """Z[pi]/(pi^2-2, pi^3): pi^3 = 2*pi = 0 and pi^4 = 4 = 0 => a in Z/4, b in Z/2.

    Independent model: integer pairs, multiply as polynomials in pi, substitute
    pi^2 -> 2, then reduce a mod 4 and b mod 2.
    """
    for a, b in itertools.product(els, els):
        x, y = ev(a), ev(b)
        assert ev(R.mul(a, b)) == _poly_mul_pi(x, y, 4, 2), \
            f"Rram mul mismatch at {x},{y}: got {ev(R.mul(a,b))}, want {_poly_mul_pi(x,y,4,2)}"
    return "vs Z[pi]/(pi^2-2,pi^3) polynomial model (a mod 4, b mod 2)"


def ref_check_Rram4(R, els):
    """Z[pi]/(pi^2-2, pi^4): pi^4 = 4 = 0, so a, b in Z/4."""
    for a, b in itertools.product(els, els):
        x, y = ev(a), ev(b)
        assert ev(R.mul(a, b)) == _poly_mul_pi(x, y, 4, 4), \
            f"Rram4 mul mismatch at {x},{y}: got {ev(R.mul(a,b))}, want {_poly_mul_pi(x,y,4,4)}"
    return "vs Z[pi]/(pi^2-2,pi^4) polynomial model (a, b mod 4)"


def ref_check_F2epsN(R, N, els):
    """F_2[eps]/eps^N against truncated polynomial multiplication over F_2."""
    for a, b in itertools.product(els, els):
        x, y = ev(a), ev(b)
        want = [0] * N
        for i in range(N):
            for j in range(N - i):
                want[i + j] ^= x[i] & y[j]
        assert ev(R.mul(a, b)) == tuple(want), f"F2eps{N} mul mismatch at {x},{y}"
    return f"vs truncated F_2[eps]/eps^{N} polynomial model"


def ref_check_bidual(R, els):
    """F_2[x,y]/(x^2,y^2): basis 1,x,y,xy. Monomial exponent model."""
    basis = [(0, 0), (1, 0), (0, 1), (1, 1)]     # (deg_x, deg_y)
    idx = {e: i for i, e in enumerate(basis)}
    for a, b in itertools.product(els, els):
        x, y = ev(a), ev(b)
        want = [0] * 4
        for i, ei in enumerate(basis):
            for j, ej in enumerate(basis):
                if not (x[i] & y[j]):
                    continue
                e = (ei[0] + ej[0], ei[1] + ej[1])
                if e[0] < 2 and e[1] < 2:        # x^2 = y^2 = 0
                    want[idx[e]] ^= 1
        assert ev(R.mul(a, b)) == tuple(want), f"BiDual mul mismatch at {x},{y}"
    return "vs F_2[x,y]/(x^2,y^2) monomial model"


def ref_check_fatpoint3(R, els):
    """F_2[x,y]/(x,y)^3: basis 1,x,y,x^2,xy,y^2; kill total degree >= 3."""
    basis = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]
    idx = {e: i for i, e in enumerate(basis)}
    for a, b in itertools.product(els, els):
        x, y = ev(a), ev(b)
        want = [0] * 6
        for i, ei in enumerate(basis):
            for j, ej in enumerate(basis):
                if not (x[i] & y[j]):
                    continue
                e = (ei[0] + ej[0], ei[1] + ej[1])
                if e[0] + e[1] <= 2:
                    want[idx[e]] ^= 1
        assert ev(R.mul(a, b)) == tuple(want), f"FatPoint3 mul mismatch at {x},{y}"
    return "vs F_2[x,y]/(x,y)^3 monomial model"


def ref_check_fatpoint2(R, els):
    """F_2[u,v]/(u,v)^2: basis 1,u,v; kill total degree >= 2 (session 13)."""
    basis = [(0, 0), (1, 0), (0, 1)]
    idx = {e: i for i, e in enumerate(basis)}
    for a, b in itertools.product(els, els):
        x, y = ev(a), ev(b)
        want = [0] * 3
        for i, ei in enumerate(basis):
            for j, ej in enumerate(basis):
                if not (x[i] & y[j]):
                    continue
                e = (ei[0] + ej[0], ei[1] + ej[1])
                if e[0] + e[1] <= 1:
                    want[idx[e]] ^= 1
        assert ev(R.mul(a, b)) == tuple(want), f"FatPoint2 mul mismatch at {x},{y}"
    return "vs F_2[u,v]/(u,v)^2 monomial model"


def _minpoly_of_w(R, deg):
    """Compute w^deg in the basis 1, w, ..., w^{deg-1}.  Returns the coefficient
    tuple (a_0, ..., a_{deg-1}) with  w^deg = sum a_i w^i,  i.e. the minimal
    polynomial of w is  X^deg - a_{deg-1} X^{deg-1} - ... - a_1 X - a_0."""
    B = R.R
    w = tuple(B.one() if i == 1 else B.zero() for i in range(deg))
    p = R.one()
    for _ in range(deg):
        p = R.mul(p, w)
    return p          # = w^deg, as a deg-tuple of base elements


def _residue_bits(B, coeffs):
    """Reduce base-ring coefficients mod m_B: returns 0 if in m_B, else 1.
    (Residue field of B has characteristic 2 in every ring we use.)"""
    return tuple(0 if istrue(B.lowzero(c)) else 1 for c in coeffs)


def ref_check_ext(R, els, _unused=None):
    """R[w]/(f) with deg f = 2.  Two things are verified:

    (a) the implemented product agrees with polynomial multiplication reduced by
        the relation that `w` actually satisfies in this class; and
    (b) that relation reduces mod m_B to an IRREDUCIBLE quadratic over F_2,
        which -- together with locality and freeness of rank 2 -- certifies that
        R is *the* unramified quadratic extension (residue field F_4).
    """
    B = R.R
    a0, a1 = _minpoly_of_w(R, 2)          # w^2 = a0 + a1 w
    for a, b in itertools.product(sample(els, 40), sample(els, 40)):
        (u1, v1), (u2, v2) = a, b
        # (u1+v1 w)(u2+v2 w) = u1u2 + (u1v2+u2v1) w + v1v2 w^2,  w^2 = a0 + a1 w
        vv = B.mul(v1, v2)
        lo = B.add(B.mul(u1, u2), B.mul(vv, a0))
        hi = B.add(B.add(B.mul(u1, v2), B.mul(u2, v1)), B.mul(vv, a1))
        assert ev(R.mul(a, b)) == (ev(lo), ev(hi)), f"{R.name}: mul mismatch"
    # X^2 - a1 X - a0  mod m_B  must be X^2 + X + 1 (the only irreducible one)
    bits = _residue_bits(B, (a0, a1))
    assert bits == (1, 1), \
        f"{R.name}: w^2 = {bits} mod m -- min poly not X^2+X+1 mod m, not unramified F_4"
    return "min poly of w = X^2+X+1 mod m (irreducible) + product formula"


def ref_check_ext3(R, els, _unused=None):
    """R[w]/(f), deg f = 3.  Same two checks; the irreducible cubics over F_2 are
    X^3+X+1 and X^3+X^2+1, and either certifies residue field F_8.

    NOTE: `Ext3` reduces using w^3 = w + 1 (it uses `add` throughout, no sign).
    Over a char-2 base that IS w^3 + w + 1 = 0.  Over Z/8 it is w^3 - w - 1 = 0,
    a *different* monic lift -- but its reduction mod 2 is the same irreducible
    cubic, so the ring is still the unramified cubic extension W(F_8)/8, which is
    unique up to isomorphism.  This check is what pins that down.
    """
    B = R.R
    a0, a1, a2 = _minpoly_of_w(R, 3)      # w^3 = a0 + a1 w + a2 w^2
    for a, b in itertools.product(sample(els, 30), sample(els, 30)):
        (u1, v1, z1), (u2, v2, z2) = a, b
        # multiply as polynomials, then reduce w^3 and w^4 = w*w^3
        c = [B.mul(u1, u2),
             B.add(B.mul(u1, v2), B.mul(v1, u2)),
             B.add(B.add(B.mul(u1, z2), B.mul(v1, v2)), B.mul(z1, u2)),
             B.add(B.mul(v1, z2), B.mul(z1, v2)),
             B.mul(z1, z2)]
        # w^3 = a0 + a1 w + a2 w^2
        out = [c[0], c[1], c[2]]
        for k, ak in ((0, a0), (1, a1), (2, a2)):
            out[k] = B.add(out[k], B.mul(c[3], ak))
        # w^4 = w * w^3 = a0 w + a1 w^2 + a2 w^3 = a2 a0 + (a0 + a2 a1) w + (a1 + a2 a2) w^2
        q0 = B.mul(a2, a0)
        q1 = B.add(a0, B.mul(a2, a1))
        q2 = B.add(a1, B.mul(a2, a2))
        for k, qk in ((0, q0), (1, q1), (2, q2)):
            out[k] = B.add(out[k], B.mul(c[4], qk))
        assert ev(R.mul(a, b)) == tuple(ev(o) for o in out), f"{R.name}: mul mismatch"
    bits = _residue_bits(B, (a0, a1, a2))
    # X^3 - a2 X^2 - a1 X - a0 mod 2 = X^3 + a2 X^2 + a1 X + a0
    irred = {(1, 1, 0), (1, 0, 1)}        # X^3+X+1  and  X^3+X^2+1
    assert bits in irred, \
        f"{R.name}: w^3 = {bits} mod m -- min poly reducible mod m, NOT residue field F_8"
    poly = "X^3+X+1" if bits == (1, 1, 0) else "X^3+X^2+1"
    return f"min poly of w = {poly} mod m (irreducible) + product formula"


# --------------------------------------------------------------------------
# driver
# --------------------------------------------------------------------------

CASES = [
    # (ring, residue-field degree, reference checker or None)
    (F2eps3(),      1, lambda R, e: ref_check_F2epsN(R, 3, e)),
    (Z8(),          1, ref_check_Z2N),
    (Rram(),        1, ref_check_Rram),
    (F2epsN(4),     1, lambda R, e: ref_check_F2epsN(R, 4, e)),
    (F2epsN(5),     1, lambda R, e: ref_check_F2epsN(R, 5, e)),
    (F2epsN(6),     1, lambda R, e: ref_check_F2epsN(R, 6, e)),
    (BiDual,        1, ref_check_bidual),
    (FatPoint3,     1, ref_check_fatpoint3),
    (FatPoint2,     1, ref_check_fatpoint2),   # session 13 (Theorem N gates)
    (Z2N(4),        1, ref_check_Z2N),
    (Z2N(5),        1, ref_check_Z2N),
    (Rram4(),       1, ref_check_Rram4),
    # length-2 bases for the S' probe (s2check.py, session 4)
    (F2epsN(2),     1, lambda R, e: ref_check_F2epsN(R, 2, e)),
    (Z2N(2),        1, ref_check_Z2N),
    (Ext(F2eps3()), 2, ref_check_ext),
    (Ext(Z8()),     2, ref_check_ext),
    (Ext(Rram()),   2, ref_check_ext),
    (Ext(F2epsN(4)),2, ref_check_ext),
    # F4[eps]/eps^2 -- base ring of firstorder_gates.py (session 8)
    (Ext(F2epsN(2)),2, ref_check_ext),
    (Ext(Z2N(4)),   2, ref_check_ext),
    (Ext(FatPoint3),2, ref_check_ext),
    # residue field F_8 -- the rings behind order4sat_f8.py / order4sat_f8ram.py
    (Ext3(Z8()),    3, ref_check_ext3),
    (Ext3(F2eps3()),3, ref_check_ext3),
    (Ext3(Rram()),  3, ref_check_ext3),
]

AXIOM_CAP = 80     # above this, sample elements for the axiom/reference sweeps
LOCAL_CAP = 512    # above this, locality (codim + nilpotency) is not exhaustive


def main():
    failures, skipped = [], []
    for R, degf, ref in CASES:
        els = enum_of(R)
        big = len(els) > AXIOM_CAP
        probe_e = sample(els, 40) if big else els
        try:
            T = Tab(R, els)
            check_axioms(T, [ev(e) for e in probe_e], triple_cap=14 if big else 26)
            if len(els) <= LOCAL_CAP:
                nm, q, powers = check_locality(T, expect_residue_deg=degf)
                loc = f"m: {nm:4d} elts, residue field F_{q}, |m^k| {powers}"
            else:
                skipped.append(f"{R.name}: locality (|R| = {len(els)} > {LOCAL_CAP})")
                loc = f"m: (locality skipped, |R| = {len(els)})"
            note = ref(R, probe_e) if ref else "no reference model"
            tag = "OK  " if len(els) <= LOCAL_CAP else "OK* "
            print(f"{tag}{R.name:34s} |{len(els):5d} elts | {loc} | {note}"
                  + ("  [axioms sampled]" if big else ""), flush=True)
        except AssertionError as e:
            failures.append(str(e))
            print(f"FAIL {R.name:33s} | {e}", flush=True)
        except Exception as e:  # noqa: BLE001
            failures.append(f"{R.name}: {type(e).__name__}: {e}")
            print(f"ERR  {R.name:33s} | {type(e).__name__}: {e}", flush=True)

    print()
    for s in skipped:
        print(f"NOTE partial coverage -- {s}")
    if failures:
        print(f"\n*** {len(failures)} RING CHECK(S) FAILED ***")
        for f in failures:
            print("  -", f)
        sys.exit(1)
    print("\nALL RING CHECKS PASSED")


if __name__ == "__main__":
    main()
