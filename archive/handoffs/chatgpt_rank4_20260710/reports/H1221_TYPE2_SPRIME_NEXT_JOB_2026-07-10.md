# Next exact job: the 19 liftable \((1,2,2,1)\) quotients

## Mathematical scope

The exact orbit computation in
[`LENGTH6_H1221_TYPE2_ORBITS_REFERENCE_2026-07-10.md`](LENGTH6_H1221_TYPE2_ORBITS_REFERENCE_2026-07-10.md)
classifies 27 residue-\(\mathbf F_2\), length-six local rings of Hilbert
function \((1,2,2,1)\) and type two.  Exactly 19 are quotients by the socle
of a length-seven Gorenstein ring.  They are

\[
 Q_{01},Q_{03},Q_{05},\ldots,Q_{10},Q_{15},Q_{16},Q_{17},Q_{18},
 Q_{20},\ldots,Q_{25},Q_{27}.
\]

The next exact finite computation is universal \(S'\) on these 19 rings,
using every one of the six rational \(xy\) fibers and all four \(t^4\)
normal forms.  This is 190 ring/fiber rows and 570 split failure queries.
If every row is H0-vacuous or all three failure queries are UNSAT, Theorem
7.1 excludes the length-seven base stratum

\[
 H_R=(1,2,2,1,1).
\]

A SAT \(S'\)-failure would be a seed for a direct Hopf-lift search, not by
itself a counterexample to Grothendieck's conjecture.

## Exact reduction and implementation

The runner is
[`scripts/sprime_length6_h1221_type2_nineteen_stratified_20260710.py`](scripts/sprime_length6_h1221_type2_nineteen_stratified_20260710.py).
Each quotient has two maximal-ideal generators, socle order four, and

\[
 |\operatorname{Syz}(x,y)|=128,
 \qquad
 |\operatorname{Syz}(x,y)/\operatorname{Soc}(Q)^2|=8.
\]

Thus each exact `FAIL_i` expands only \(8^3=512\) concrete division
classes.  The runner enumerates the eight cosets directly: the quotient is
\(C_4\times C_2\), rather than an \(\mathbf F_2\)-vector space, for
\(Q_{24},Q_{25},Q_{27}\).  No residual-linearity assumption is made.

Before a Hopf query, the runner checks the complete \(64^2\) table conversion,
the displayed positive Gorenstein-lift witness, ring laws, locality,
filtration, type-two socle, generator ideal, and the full syzygy count.  Z3
parallel portfolios are disabled.  Rings should be run one at a time; the
optional `--memory-mb` argument sets a Z3 memory ceiling.

## Banked validation and pilot

All 19 structural/syzygy gates passed.  The banked log is
[`scripts/sprime_length6_h1221_type2_nineteen_validate_20260710.log`](scripts/sprime_length6_h1221_type2_nineteen_validate_20260710.log),
with SHA-256

```text
e8ac4bdccbd3ba8302b01e7ae5d01c37422c8f736622b58a6ae8dbff6d241eef
```

The first memory canary used \(Q_{01}\), the difficult `xy/mu2a2` fiber,
and `FAIL_1`.  It returned H0 SAT, S1 SAT, and S2.1 UNSAT.  Peak process RSS
was 889.80 MiB.  This is only a partial row verdict.  Its log is
[`scripts/sprime_length6_h1221_q01_xy_mu2a2_i1_canary_20260710.log`](scripts/sprime_length6_h1221_q01_xy_mu2a2_i1_canary_20260710.log),
with SHA-256

```text
1d927b78dea0cb3b48b6bcf627680bbfcd00364f0720b458b30c23057c42f8fb
```

The exact canary command was

```bash
/Users/akhilmathew/.venvs/z3env/bin/python -u \
  scripts/sprime_length6_h1221_type2_nineteen_stratified_20260710.py \
  --rings q01 --fibers xy --xy-models mu2a2 --only-i 1 --timeout 300
```

No wider solver sweep has been launched.  After resource review, the next
local step should complete `--only-i 1 2 3` for this one row, still in a
single process.  An RCC array should likewise assign one ring/fiber row to
each one-CPU Slurm task and record every job ID and resource result.
