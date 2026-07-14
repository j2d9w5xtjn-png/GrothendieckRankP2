#!/usr/bin/env python3
"""rank16_c44_full_sweep.py — the full 64-case honest-solver sweep of ChatGPT's
rank-16 F2[a,b]/(a^4,b^4) carry family (its NEW_RANK16_HANDOFF Step A, which it
could not finish for lack of z3).

For every (ca,cb) in 0..7 x 0..7 it builds the FULL first-order bialgebra
deformation over F2[e]/e^2 and asks, under all axioms, whether the leading
rank-16 obstruction Psi_1^4 != 0 (and Psi_1^3 != 0) is realizable.

If every case is `unsat`, the whole carry family has TD_4 = Psi_1^4 = 0 at first
order -> NO rank-16 leading-layer counterexample seed anywhere in the family;
ChatGPT's `single_power_nonzero[4]=true` cotangent-scanner signals are refuted
as linear-relaxation artifacts (idempotent = etale, not realizable).

Run:  ~/.venvs/z3env/bin/python rank16_c44_full_sweep.py
"""
import time, sys
sys.argv = ['x']                       # keep imported argparse in the module quiet
from z3 import BitVecVal, sat, unsat
import rank16_c44_seed_z3 as M

T0 = time.time()
print('=== rank16 c44 full 64-case honest-solver sweep (Psi_1^3, Psi_1^4) ===', flush=True)
seeds = []
for ca in range(8):
    for cb in range(8):
        S, nonzero_cond = M.build(NE=2, ca=ca, cb=cb)
        row = {}
        for K in (3, 4):
            cond = nonzero_cond(K)
            if cond is True:
                row[K] = 'sat*'                 # trivially nonzero (identically)
            elif cond is False:
                row[K] = 'unsat'
            else:
                S.push(); S.add(cond); r = S.check(); S.pop()
                row[K] = str(r)
        flag = ' <<< SEED' if row[4] in ('sat', 'sat*') else ''
        if flag: seeds.append((ca, cb))
        print(f'  c44_ca{ca}_cb{cb}:  Psi1^3={row[3]:>5}  Psi1^4={row[4]:>5}'
              f'{flag}   ({time.time()-T0:.0f}s)', flush=True)
print(f'=== DONE sweep: {len(seeds)} genuine Psi_1^4 seeds out of 64 '
      f'({seeds if seeds else "NONE"}) ===', flush=True)
print('DONE rank16_c44_full_sweep', flush=True)
