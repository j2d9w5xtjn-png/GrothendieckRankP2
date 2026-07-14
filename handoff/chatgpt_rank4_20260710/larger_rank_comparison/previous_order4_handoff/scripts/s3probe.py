#!/usr/bin/env python3
"""s3probe.py -- discovery probes for the s = 3 layer-symbol identity
(THEORY section 12.6.3), t^4 fiber first, xy fiber second.

Over R = F2[eps]/eps^3 (all rank-4 bialgebras, fiber2, either fiber):
  [Q1 t4] is the e1-coefficient of phi(e1) identically zero?
          (phi(e1)[e1] = eps^2 * (Psi_2 t)_t since (Psi_1 t)_t = 0 by
          Theorem 12.3.2.)  UNSAT => Psi_2(I) subset I^2: the t^4
          first-order mechanism persists at layer 2 verbatim.
  [Q2 t4] are phi(e2), phi(e3) in eps^2*I^2?  (layer-2 analogue of
          psi(I^2) = 0 cannot hold exactly -- Psi_2(I^2) = Psi_1(mu_1(I,I))
          -- so probe the weaker landing spot instead.)
  [Q3 xy] is the I/I^2-block of the eps^2-digit of phi nilpotent-compatible:
          probe whether phi(e_i) has zero x,y-components mod eps^2 for
          i = 1,2 AFTER imposing w0 = 0 on x,y (alpha_2 x alpha_2 pin) --
          i.e. does case (1) stay "psi_2(I) in I^2" at layer 2?
Read the results as evidence about WHICH layer-2 statement to try to prove
by hand; a sat here is NOT a counterexample to anything banked.
"""
from z3 import Solver, Or, sat, unsat, set_param
from order4sat import F2eps3
from order4sat_beyond import F2epsN
from s2check import build_blocks

FIBS = [("xy", {(1, 2, 3): 1}), ("t4", {(1, 1, 2): 1, (1, 2, 3): 1})]


def check(base, extra, label, expect=None):
    s = Solver()
    s.set("timeout", 7200 * 1000)
    for a in base:
        s.add(a)
    for a in extra:
        s.add(a)
    r = s.check()
    note = f" (expect {expect})" if expect else ""
    print(f"  [{label}] -> {r}{note}", flush=True)
    return r


def pin_digit0(c, pins):
    out = []
    for i in range(1, 4):
        for j in range(1, 4):
            for k in range(1, 4):
                v = 1 if (i, j, k) in pins else 0
                out.append(c[(i, j, k)][0] == v)
    return out


if __name__ == "__main__":
    set_param("parallel.enable", True)
    R = F2eps3()
    print(f"===== s3probe over {R.name} =====", flush=True)

    # t4 fiber
    A, Mb, C, fiber2, phi, c, Mtab = build_blocks(R, FIBS[1][1])
    base = A + Mb + C + fiber2
    check(base, [], "t4 sanity", "sat")
    check(base, [R.neq0(phi[1][1])], "Q1 t4: phi(e1) has e1-component")
    # Q2: e1-components of phi(e2), phi(e3)
    check(base, [Or(R.neq0(phi[2][1]), R.neq0(phi[3][1]))],
          "Q2 t4: phi(I^2) has e1-component")

    # xy fiber, alpha2 x alpha2 pin at layer 0
    A, Mb, C, fiber2, phi, c, Mtab = build_blocks(R, FIBS[0][1])
    base = A + Mb + C + fiber2
    check(base, [], "xy sanity", "sat")
    pins = pin_digit0(c, {(3, 1, 2), (3, 2, 1)})
    check(base, pins, "xy a2a2-pin sanity", "sat")
    check(base, pins + [Or(R.neq0(phi[1][1]), R.neq0(phi[1][2]),
                           R.neq0(phi[2][1]), R.neq0(phi[2][2]))],
          "Q3 xy(a2a2): phi(e1),phi(e2) stick out of I^2")
    print("DONE s3probe", flush=True)
