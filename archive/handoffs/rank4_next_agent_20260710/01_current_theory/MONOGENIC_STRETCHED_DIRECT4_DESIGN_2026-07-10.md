# Direct `[4]` experiment for the two stretched `t4_11` timeouts

**Date:** 2026-07-10  
**Status at design freeze:** source, gate-only validation, and Slurm design
complete. A later bounded local run closed all six direct queries UNSAT; see
MONOGENIC_STRETCHED_DIRECT4_RESULT_2026-07-10.md for immutable evidence.

## Purpose

The old computations ask whether the stronger sufficient condition `S'`
holds on the two length-six quotient rings

\[
 Q_s=\mathbf F_2[x,y]/(x^5,xy,y^2),\qquad
 Q_q=\mathbf Z[x]/(x^5,2x,4).
\]

For the `t4(c1=1,c4=1)/i1` row, the 3600-second and 7200-second encodings
both timed out.  A failure of `S'` would still be only a lifting seed.  The
new job instead enumerates the Gorenstein socle lifts of these two rings and
asks the actual question `[4]^# != eta epsilon` on each lift.

## Complete socle-lift list

Let `z` generate the one-dimensional socle kernel.  In the stretched
Hilbert profile, `z=m^5` and the active chain gives `x^5=z`.

For `Q_s`, every lift has

\[
 2=\gamma z,\qquad xy=\alpha z,\qquad y^2=\beta z.
\]

The multiplication pairing from
`Soc(Q_s)=<x^4,y>` to the top socle, against the cotangent basis `<x,y>`, is

\[
 \begin{pmatrix}1&0\\ \alpha&\beta\end{pmatrix}.
\]

Gorensteinness forces `beta=1`.  Thus `gamma,alpha in F2` give four
coordinate presentations.  The change `y -> y+alpha*x^4` removes `alpha`,
so these are two isomorphism classes, distinguished by characteristic two
versus four.  Both alpha values are deliberately retained as an encoding
cross-check.

For `Q_q`, every lift has

\[
 x^5=z,\qquad 2x=\alpha z,\qquad 4=\gamma z.
\]

The analogous pairing is

\[
 \begin{pmatrix}1&0\\ \alpha&\gamma\end{pmatrix},
\]

so Gorensteinness forces `gamma=1`.  The change `x -> x+2` toggles `alpha`,
leaving one isomorphism class.  Again both coordinates are run.  This gives
the six array tasks

```text
sf2_g0_a0  sf2_g0_a1  sf2_g1_a0  sf2_g1_a1  q00_a0  q00_a1
```

The driver independently gates each 128-element table, its Hilbert powers,
socle, and its quotient onto the advertised 64-element ring.

## Monogenic normalization and exact query

Every algebra lift of the `t^4` fiber is monogenic.  After choosing a lift
`T`, use the basis `1,T,T^2,T^3` and write

\[
 A=R[T]/(T^4-aT-bT^2-dT^3),\qquad a,b,d\in\mathfrak m_R.
\]

Write

\[
 \Delta(T)=T\otimes1+1\otimes T+
   \sum_{1\le i,j\le3}c_{ij}T^i\otimes T^j,
\]

with the residues of the nine `c_ij` pinned to the `t4_11` normal form.
The solver imposes:

1. stability of the monic quartic relation under `Delta`;
2. coassociativity on `T`;
3. the redundant safety check that `q(T)` is in the maximal ideal, where
   `q=mu Delta`.

Multiplicativity of `Delta` is built into this construction.  If
`q(T)=mu Delta(T)`, the main disequality is

\[
 q(q(T))\ne0.
\]

Since `T` generates `A`, this is exactly `[4]^# != eta epsilon`, not `S'`.
A SAT answer is therefore an actual counterexample candidate, subject to the
independent model and Hopf verification.  An UNSAT answer excludes that base
ring and fiber.  Timeout, OOM, malformed output, or nonzero exit is
inconclusive.

## Files and validation

- `scripts/monogenic_stretched_direct4_20260710.py`
- `slurm/run_monogenic_stretched_direct4_array.sbatch`

Frozen SHA-256 values after the gate-only audit are

```text
ac70fdf145989723133d4c4efecb740353b0d8530bc9ee060089271de7a3caac  scripts/monogenic_stretched_direct4_20260710.py
b59ec9fbd6ce00167d15725262023f241df8e18e30b347ab7f7ef234a05c8e8c  slurm/run_monogenic_stretched_direct4_array.sbatch
```

Before creating a solver the driver checks all `128^3` associativity and
distributivity triples, all units, the maximal-ideal power sizes
`64,16,8,4,2,1`, the one-dimensional socle, and all `128^2` addition and
multiplication pairs in the quotient map.  If Z3 returns SAT, a separate
integer arithmetic implementation recomputes relation stability,
coassociativity, the killed-by-two fiber condition, and nonvanishing of
`q(q(T))`.  The JSON certificate can later be checked with

```bash
python scripts/monogenic_stretched_direct4_20260710.py \
  --verify-certificate results/monogenic_direct4/CERTIFICATE.json
```

This verifier does not by itself classify the resulting group scheme up to
isomorphism.  Before announcing a counterexample, also construct or verify
the antipode independently and recheck the model in a second algebra system.
For a finite free bialgebra over an Artin-local base whose special fiber is
Hopf, existence of the antipode follows by lifting the convolution inverse,
but an explicit check is still appropriate for a headline claim.

Before each base-ring gate, a standalone F2 bit-mask implementation also
checks that the fixed `t4_11` coproduct preserves `T^4=0`, is coassociative,
and has `q(T)=0`.  A transcription error therefore aborts before solver
creation instead of masquerading as an H0-vacuous row.

All six `--validate-only` invocations completed successfully.  Each checked
the advertised `128^3` ring triples and `128^2` quotient pairs, with measured
elapsed times from 0.49 to 1.00 seconds.  The three redundant `alpha=1`
presentations also passed explicit bijection and all-`128^2` operation checks
against their `alpha=0` companions.  Python compilation and `bash -n` passed.
A no-solver construction check built the normalized formula with 84 core
constraints, nine coproduct parameters, and four coordinates each for
`q(T)` and `q(q(T))`.

## Canonical bounded local result

After this design was frozen, all six presentations were run locally in
fresh processes with Z3 4.16.0, one thread, a 1024 MiB ceiling, and
300-second stage timeouts. Every H0 core was SAT and every actual
\(q(q(T))\ne0\) query was UNSAT. The crash-safe run ID and directory are

    local1g_20260710
    results/monogenic_direct4/local1g_20260710

The run completed in 88.714 seconds; per-process elapsed times were
11.78--16.48 seconds and peak RSS was 497.91 MiB. The standard-library
strict auditor exited zero with

    AUDIT PASS six_of_six_H0_SAT_and_direct4_UNSAT errors=0 unknown=0 SAT=0

The six log hashes, exact source manifest, commands, versions, and resource
records are in RUN_COMPLETE.json and RUN_MANIFEST.json. Full interpretation
is in MONOGENIC_STRETCHED_DIRECT4_RESULT_2026-07-10.md.

Thus the direct search covers and excludes the entire coproduct-lift branch
over each of the six base presentations. It is not merely a verdict on the
old auxiliary coordinate-i1 condition.

## Optional bounded Slurm reproduction

No Slurm job was needed for the canonical run, and there is no job ID to
report. To reproduce independently on RCC from a staged project root with
Z3 4.16.0:

```bash
sbatch slurm/run_monogenic_stretched_direct4_array.sbatch
```

The default contract is:

- array `0-5%2`;
- one CPU per task;
- 8 GiB Slurm memory and a 6144-MiB Z3 ceiling;
- 600 seconds for the expected-easy core SAT gate;
- 10,800 seconds for the direct counterexample query;
- four hours wall time;
- unique stdout, stderr, and SAT-certificate paths by array job/task ID.

If a reproduction unexpectedly times out with low measured memory, rerun
only that task with the QF_BV-specific engine:

```bash
sbatch --array=TASK --export=ALL,ENGINE=qfbv \
  slurm/run_monogenic_stretched_direct4_array.sbatch
```

Do not treat the alternative engine as independent mathematical evidence;
it is a different decision procedure for the same formula.  Use `sacct` to
record state, elapsed time, requested memory, `MaxRSS`, CPUs, and exit code
for every task before interpreting any solver line.

## Scope

The six audited UNSAT verdicts close the two formerly timed-out stretched
quotient/fiber branches at length seven under the standard
minimal-Gorenstein reduction. They do not finish the principal length-seven
frontier, residue-field extensions, arbitrary-depth mixed characteristic,
or the full rank-four conjecture.
