#!/usr/bin/env python3
r"""s3gates.py -- session-9 machine gates for the s = 3 layer identity,
t^4 fiber (THEORY 12.6.4-to-be).

The hand proof being gated (all elements of I_H = <t,t^2,t^3>, char 2,
R = k'[eps]/eps^3, fiber2, mu = mu0+eps mu1+eps^2 mu2, w = w0+eps w1+eps^2 w2,
Psi1 = mu0 w1 + mu1 w0, Psi2 = mu0 w2 + mu1 w1 + mu2 w0):

  notation:  w0 t = c1 t*t^2 + c1^2 t^2*t^3 + c4 t^2@t^2   (* = symmetrized)
             beta = w1 t,  Y = w1 t^2,  Theta = w1 t^3   (3x3 digit matrices)
             mu1(t,t) = p t + p2 t^2 + p3 t^3,  q = mu1(t,t^2)_t
             u = mu1(t^2,t^2) = a t + b t^2 + (a c1) t^3  (a c4 = 0)
             v = mu2(t^2,t^2),  Psi1 t = B t^2 + C t^3
             lam := p c1 + p3 + a c1^2

  (1) [G3]  Y = lam * w0(t^3)  +  p c4 * t^2@t^2
            (from the eps-digit of Delta(t.t) = (Delta t)^2:
             Y = w0(mu1(t,t)) + S(t), S(t) = c1^2 (u@t^2 + t^2@u))
  (2) [G6]  c4 v_t = a beta_22 + p b c4
            (from the eps^2-digit of Delta(t^2.t^2) = (Delta t^2)^2:
             w0(v) = w1(u) + Y^2 and Y^2 = 0 in H@H)
  (3) [G4]  beta_13 = beta_31  ( = c1 lam + c1^2 Theta_11 )
            (coefficients of t@t@t^2 and t^2@t@t in order-1 coassociativity
             (w0@1)w1t + (w1@1)w0t = (1@w0)w1t + (1@w1)w0t)
  (4) [G5]  Theta_22 = q c4    (eps-digit of Delta(t.t^2) = Delta t Delta t^2)
  (5) [G7]  Psi2(t^2) = p Psi1(t),  Psi2(t^3) = q Psi1(t)
            (eps^2-digit of phi(ab) = phi(a)phi(b))
  (6) [G8]  (Psi2 t)_t = p B + q C   (assembly of (1)-(4) +
             Hochschild values mu1(t,t^3)_t = a, mu1(t^2,t^3)_t = 0,
             mu1(t^3,t^3) = a t^3 [G10])
  (7) [G9]  Psi1 Psi2 + Psi2 Psi1 = 0   (the s = 3 identity; endpoint)

Every G* query asserts the axioms plus the NEGATION of one lemma and must
come back unsat over BOTH F2[eps]/eps^3 and F4[eps]/eps^3 (the latter
catches semilinearity slips).  A sat on a G* = the hand proof is wrong there;
the model is the counterexample -- stop and debug (golden rule 1).
N* queries are non-vacuity/discovery probes (expected sat, or open).
Equation builder = s2check.build_blocks (gate-validated, unchanged).
"""
import sys
from z3 import Solver, Or, And, BitVecVal, sat, unsat, set_param

sys.path.insert(0, ".")
from order4sat import F2eps3, Ext
from s2check import build_blocks

T4 = {(1, 1, 2): 1, (1, 2, 3): 1}
FAILED = [0]


# ---------- residue-field arithmetic on eps-digits ----------

class KF2:
    name = "F2"
    def zero(self): return BitVecVal(0, 1)
    def one(self):  return BitVecVal(1, 1)
    def add(self, a, b): return a ^ b
    def mul(self, a, b): return a & b
    def eq0(self, a):  return a == 0
    def neq0(self, a): return a != 0


class KF4:
    """F4 = F2[w]/(w^2+w+1), element = (u, v) pair of bits, matching Ext."""
    name = "F4"
    def zero(self): return (BitVecVal(0, 1), BitVecVal(0, 1))
    def one(self):  return (BitVecVal(1, 1), BitVecVal(0, 1))
    def add(self, a, b): return (a[0] ^ b[0], a[1] ^ b[1])
    def mul(self, a, b):
        u1, v1 = a; u2, v2 = b
        return ((u1 & u2) ^ (v1 & v2), (u1 & v2) ^ (u2 & v1) ^ (v1 & v2))
    def eq0(self, a):  return And(a[0] == 0, a[1] == 0)
    def neq0(self, a): return Or(a[0] != 0, a[1] != 0)


def digit(R, x, l):
    """eps^l-digit of a ring element as a residue-field element."""
    if isinstance(R, Ext):
        return (x[0][l], x[1][l])
    return x[l]


# ---------- driver ----------

def run(R, K):
    print(f"===== s3gates over {R.name} =====", flush=True)
    A, Mb, C, F, phi, c, Mtab = build_blocks(R, T4)
    base = A + Mb + C + F
    base_noC = A + Mb + F

    d = lambda x, l: digit(R, x, l)
    M = lambda i, j, r: Mtab[(min(i, j), max(i, j), r)]
    kadd, kmul = K.add, K.mul

    def ksum(*xs):
        out = xs[0]
        for x in xs[1:]:
            out = kadd(out, x)
        return out

    # named digit quantities
    c1 = d(c[(1, 1, 2)], 0)
    c4 = d(c[(1, 2, 2)], 0)
    beta = {(j, k): d(c[(1, j, k)], 1) for j in range(1, 4) for k in range(1, 4)}
    Yd = {(j, k): d(c[(2, j, k)], 1) for j in range(1, 4) for k in range(1, 4)}
    Th = {(j, k): d(c[(3, j, k)], 1) for j in range(1, 4) for k in range(1, 4)}
    p = d(M(1, 1, 1), 1); p3 = d(M(1, 1, 3), 1)
    q = d(M(1, 2, 1), 1)
    a = d(M(2, 2, 1), 1); b_ = d(M(2, 2, 2), 1); u3 = d(M(2, 2, 3), 1)
    vt = d(M(2, 2, 1), 2)
    P1 = {(i, r): d(phi[i][r], 1) for i in range(1, 4) for r in range(4)}
    P2 = {(i, r): d(phi[i][r], 2) for i in range(1, 4) for r in range(4)}
    lam = ksum(kmul(p, c1), p3, kmul(a, kmul(c1, c1)))
    Bc = P1[(1, 2)]; Cc = P1[(1, 3)]

    def gate(label, zero_claims, axioms=None, expect="unsat"):
        s = Solver()
        s.set("timeout", 7200 * 1000)
        for e in (base if axioms is None else axioms):
            s.add(e)
        s.add(Or(*[K.neq0(x) for x in zero_claims]))
        r = s.check()
        ok = (str(r) == expect)
        if not ok:
            FAILED[0] += 1
        tag = "GATE OK" if ok else f"GATE FAILED (expect {expect}) -- STOP"
        print(f"  [{label}] -> {r}  [{tag}]", flush=True)

    def probe(label, constraint, expect=None, axioms=None):
        s = Solver()
        s.set("timeout", 7200 * 1000)
        for e in (base if axioms is None else axioms):
            s.add(e)
        s.add(constraint)
        r = s.check()
        note = f" (expect {expect})" if expect else " (discovery)"
        if expect and str(r) != expect:
            FAILED[0] += 1
            note += "  [GATE FAILED -- STOP]"
        print(f"  [{label}] -> {r}{note}", flush=True)

    # sanity
    probe("G0 : axioms sat", And(True), expect="sat")

    # layer-1 recap (banked, Thm 12.3.2 / 12.1.1)
    gate("G1a: Psi1(t) in I^2, Psi1(I^2) = 0, counit rows",
         [P1[(1, 1)], P1[(1, 0)], P2[(1, 0)]]
         + [P1[(i, r)] for i in (2, 3) for r in range(4)]
         + [P2[(i, 0)] for i in (2, 3)])
    gate("G1b: a c4 = 0", [kmul(a, c4)])
    gate("G1c: u_3 = a c1", [kadd(u3, kmul(a, c1))])

    # w0 normal form (12.3.1, from order-0 axioms)
    g2 = [d(c[(1, 1, 1)], 0),                                  # fiber2: no t@t
          kadd(d(c[(1, 1, 2)], 0), d(c[(1, 2, 1)], 0)),        # cocommutative
          d(c[(1, 1, 3)], 0), d(c[(1, 3, 1)], 0),              # c2 = 0
          d(c[(1, 3, 3)], 0),                                  # c5 = 0
          kadd(d(c[(1, 2, 3)], 0), kmul(c1, c1)),              # c3 = c1^2
          kadd(d(c[(1, 3, 2)], 0), kmul(c1, c1))]
    g2 += [d(c[(2, j, k)], 0) for j in range(1, 4) for k in range(1, 4)]  # w0t2=0
    w0t3 = {(1, 2): K.one(), (2, 1): K.one(), (2, 3): c1, (3, 2): c1}
    g2 += [kadd(d(c[(3, j, k)], 0), w0t3.get((j, k), K.zero()))
           for j in range(1, 4) for k in range(1, 4)]
    gate("G2 : w0 normal form (c2=c5=0, c3=c1^2, w0t2=0, w0t3 pinned)", g2)

    # (1) Y-shape
    g3 = [kadd(Yd[(1, 2)], lam), kadd(Yd[(2, 1)], lam),
          kadd(Yd[(2, 3)], kmul(c1, lam)), kadd(Yd[(3, 2)], kmul(c1, lam)),
          kadd(Yd[(2, 2)], kmul(p, c4)),
          Yd[(1, 1)], Yd[(1, 3)], Yd[(3, 1)], Yd[(3, 3)]]
    gate("G3 : Y = lam*w0t3 + p c4 t2@t2", g3)

    # (3) beta symmetry (needs coassoc)
    gate("G4a: beta_13 = beta_31", [kadd(beta[(1, 3)], beta[(3, 1)])])
    sharp = ksum(kmul(c1, lam), kmul(kmul(c1, c1), Th[(1, 1)]))
    gate("G4b: beta_13 = c1 lam + c1^2 Theta_11", [kadd(beta[(1, 3)], sharp)])
    gate("G4c: beta_31 = c1 lam + c1^2 Theta_11", [kadd(beta[(3, 1)], sharp)])

    # (4) Theta_22
    gate("G5 : Theta_22 = q c4", [kadd(Th[(2, 2)], kmul(q, c4))])

    # (2) layer-2 diagonal identity, t2@t2 coefficient
    gate("G6 : c4 v_t = a beta_22 + p b c4",
         [ksum(kmul(c4, vt), kmul(a, beta[(2, 2)]), kmul(kmul(p, b_), c4))])

    # (5) Psi2 on I^2
    gate("G7 : Psi2(t^2) = p Psi1(t), Psi2(t^3) = q Psi1(t)",
         [P2[(2, 1)], kadd(P2[(2, 2)], kmul(p, Bc)), kadd(P2[(2, 3)], kmul(p, Cc)),
          P2[(3, 1)], kadd(P2[(3, 2)], kmul(q, Bc)), kadd(P2[(3, 3)], kmul(q, Cc))])

    # (6) main assembly
    gate("G8 : (Psi2 t)_t = p B + q C",
         [ksum(P2[(1, 1)], kmul(p, Bc), kmul(q, Cc))])

    # (7) endpoint: s = 3 identity as digit matrices
    g9 = []
    for i in range(1, 4):
        for ss in range(1, 4):
            terms = []
            for r in range(1, 4):
                terms.append(kmul(P2[(i, r)], P1[(r, ss)]))
                terms.append(kmul(P1[(i, r)], P2[(r, ss)]))
            g9.append(ksum(*terms))
    gate("G9 : s=3 identity Psi1 Psi2 + Psi2 Psi1 = 0", g9)

    # Hochschild values used in (6)
    gate("G10: mu1(t,t^3)_t = a; mu1(t^2,t^3)_t = 0; mu1(t^3,t^3) = a t^3",
         [kadd(d(M(1, 3, 1), 1), a), d(M(2, 3, 1), 1),
          d(M(3, 3, 1), 1), d(M(3, 3, 2), 1), kadd(d(M(3, 3, 3), 1), a)])

    # discovery: is the s=3 identity coassociativity-free (minassoc-style)?
    # sat = coassoc is load-bearing at layer 2; unsat = minassoc pattern persists
    probe("G9nc: s=3 violated, coassociativity DROPPED",
          Or(*[K.neq0(x) for x in g9]), axioms=base_noC)

    # non-vacuity / discovery probes
    probe("N1 : (Psi2 t)_t != 0 realizable (Q1 reproduction)",
          K.neq0(P2[(1, 1)]), expect="sat")
    probe("N2 : a != 0 realizable", K.neq0(a), expect="sat")
    probe("N3 : a * beta_13 != 0 realizable (cancellation is real)",
          K.neq0(kmul(a, beta[(1, 3)])))
    probe("N4 : p c4 != 0 realizable (Y's diagonal term real)",
          K.neq0(kmul(p, c4)))
    probe("N5 : a * beta_13 * B != 0 realizable (dangerous product real)",
          K.neq0(kmul(kmul(a, beta[(1, 3)]), Bc)))


if __name__ == "__main__":
    set_param("parallel.enable", True)
    run(F2eps3(), KF2())
    if "--f2only" not in sys.argv:
        run(Ext(F2eps3()), KF4())
    verdict = "ALL S3 GATES PASSED" if FAILED[0] == 0 else \
        f"{FAILED[0]} GATE(S) FAILED -- the hand proof is wrong somewhere"
    print(f"===== {verdict} =====", flush=True)
    print("DONE s3gates", flush=True)
