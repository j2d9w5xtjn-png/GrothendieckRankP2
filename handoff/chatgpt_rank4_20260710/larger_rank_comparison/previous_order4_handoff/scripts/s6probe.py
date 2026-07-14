#!/usr/bin/env python3
"""s6probe.py (session 13) -- exact-F2 probe of the s = 6 layer identity and
the 15.8.3 SUSPENSION question, t^4 fiber over F2[eps]/eps^6.

Encoding lineage: fifth-push bundle probe (s5_t4_partial_probe.py, verified
session 13) = project build_blocks + (c1,c4)-pinned Delta_0 (F2: c1 = c1^2,
Frobenius-invisible) + banked lower identities as constraints.  Here the
banked set is D2-D5 (D5 status at F2: all nine components unsat -- bundle
logs + s5gates battery B incl. the (1,3) gap, session 13).

Rows:
  A. D6 components, product rows first, cotangent row (1,1),(1,2),(1,3)
     LAST (hardest).  All `unsat` => the s = 6 identity has no F2
     counterexample; with 12.6.1 this is the exact-F2 content of S' over
     F2[eps]/eps^6 (first probe at this depth; s2check --deeper stopped at
     eps^5).
  B. SUSPENSION discovery rows (THEORY 15.8.3(b)): with D2-D5 enforced, are
     the index-shifted sums Sigma_s = sum_{m+n=s} Psi_{m+1} Psi_{n+1}
     forcibly zero?  s = 2 (Psi2 Psi2) and s = 3 (Psi2 Psi3 + Psi3 Psi2).
     NO expectation -- `unsat` = evidence FOR the suspension-closure route
     to the uniform lemma; `sat` = that route needs correction terms.
     (Note: D4 = 0 makes Psi2^2 = Psi1Psi3 + Psi3Psi1, so the s = 2 row
     also reads: can Psi1 Psi3 + Psi3 Psi1 be nonzero ALONE at eps^6.)
"""
import sys
from z3 import Solver, BitVec, BitVecVal, set_param

from order4sat_beyond import F2epsN
from s2check import build_blocks
from s3gates import KF2, digit

T4 = {(1, 1, 2): 1, (1, 2, 3): 1}
K = KF2()
NN = 6


def ksum(xs):
    out = K.zero()
    for x in xs:
        out = K.add(out, x)
    return out


def dmat(P, s, shift=0):
    out = {}
    for i in range(1, 4):
        for ss in range(1, 4):
            terms = []
            for n in range(1, s):
                m = s - n
                if (n + shift) in P and (m + shift) in P:
                    for r in range(1, 4):
                        terms.append(K.mul(P[n + shift][(i, r)],
                                           P[m + shift][(r, ss)]))
            out[(i, ss)] = ksum(terms)
    return out


R = F2epsN(NN)
A, Mb, C, F, phi, c, Mtab = build_blocks(R, T4)
base = A + Mb + C + F
c1 = BitVec('pin_c1_s6', 1)
c4 = BitVec('pin_c4_s6', 1)


def pin0(i, j, k):
    if i == 1:
        if (j, k) in [(1, 2), (2, 1), (2, 3), (3, 2)]:
            return c1        # F2: c1^2 = c1
        if (j, k) == (2, 2):
            return c4
        return BitVecVal(0, 1)
    if i == 2:
        return BitVecVal(0, 1)
    if (j, k) in [(1, 2), (2, 1)]:
        return BitVecVal(1, 1)
    if (j, k) in [(2, 3), (3, 2)]:
        return c1
    return BitVecVal(0, 1)


for i in range(1, 4):
    for j in range(1, 4):
        for k in range(1, 4):
            base.append(digit(R, c[(i, j, k)], 0) == pin0(i, j, k))

P = {n: {(i, r): digit(R, phi[i][r], n)
         for i in range(1, 4) for r in range(1, 4)} for n in range(1, NN)}
known = []
for s in (2, 3, 4, 5):
    known += list(dmat(P, s).values())

set_param("parallel.enable", True)
print(f"s6probe over F2[eps]/eps^{NN}, t^4 pinned, banked D2-D5"
      f" ({len(known)} constraints)", flush=True)

D6 = dmat(P, 6)
order = [(2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3),
         (1, 1), (1, 2), (1, 3)]
for key in order:
    s = Solver()
    for e in base:
        s.add(e)
    for x in known:
        s.add(K.eq0(x))
    s.add(K.neq0(D6[key]))
    kind = "cotangent" if key[0] == 1 else "Lemma 1.1 row"
    print(f"  [D6{key} negation ({kind})] -> {s.check()}  (expect unsat)",
          flush=True)

for s_idx in (2, 3):
    Sh = dmat(P, s_idx, shift=1)
    s = Solver()
    for e in base:
        s.add(e)
    for x in known:
        s.add(K.eq0(x))
    from z3 import Or
    s.add(Or(*[K.neq0(v) for v in Sh.values()]))
    print(f"  [SUSPENSION s={s_idx}: shifted sum != 0 (discovery)] "
          f"-> {s.check()}  (no expectation)", flush=True)

print("DONE s6probe", flush=True)
