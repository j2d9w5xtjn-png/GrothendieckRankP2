# Midway arrays for the remaining rank-four length-seven frontier

These arrays are Python/Z3 computations; they do not use Macaulay2 or the
Macaulay2 Apptainer image.

## Purpose

- `slurm/run_stretched_array.sbatch` tests the eleven-coordinate upper list
  for quotient Hilbert function `(1,2,1,1,1)`.
- `slurm/run_principal_array.sbatch` tests the ten classified principal
  length-six quotients.

Each array task is one fresh `(ring, rational fiber, FAIL_i)` process.  This
returns the Z3 context to the OS after every coordinate and gives unambiguous
per-case logs.

## Setup and submission

From the project root on a Midway login node:

```bash
mkdir -p logs results notes
bash slurm/setup_z3_env.sh
sbatch slurm/run_stretched_array.sbatch
sbatch slurm/run_principal_array.sbatch
```

The scripts intentionally omit a partition and use the account default.
They start at four concurrent tasks, one CPU and 8 GiB per task.  Each task
has a 6144 MiB Z3 ceiling, a 3600-second per-stage timeout, and a 4.5-hour
Slurm wall time.

Record every returned job ID.  Monitor and harvest with:

```bash
squeue -u "$USER"
sacct -j JOBID --format=JobID,State,Elapsed,MaxRSS,ReqMem,AllocCPUS,ExitCode
```

## Evidence rule

A task is complete only if Slurm reports `COMPLETED`/`0:0` and its log has
the exact driver terminal marker plus `TASK_DONE`.  H0 UNSAT makes the fiber
row vacuous.  For a nonvacuous row, all three `i` tasks must be UNSAT to
close the row.  A validated S2 SAT is an `S'`-failure candidate, not yet a
direct `[4]` counterexample.  Timeout, OOM, `unknown`, missing output, or a
nonzero exit is inconclusive.

Retry only inconclusive task IDs.  A timeout retry may use a 7200-second
solver timeout and an 8-hour Slurm limit.  A memory retry may use 16 GiB with
a Z3 ceiling around 14336 MiB.  Do not resubmit successful tasks.

## Staged bundle

The self-contained source bundle is
`midway/rank4_frontier_arrays_20260710.tar.gz`, with SHA-256

```text
6fbff24fa2382222ed88f8b6e4eefda722c0461cb297ca10d904735b6d9ad929
```

The two array scripts were syntax-checked and locally exercised on one
H0-vacuous mapped task each.  Both printed the expected `CASE_SPEC`, exact
structural gates, driver terminal marker, `PROCESS_RESOURCE`, and
`TASK_DONE`, and both exited zero.
