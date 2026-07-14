# Handoff: Grothendieck's conjecture for finite locally free group schemes

Snapshot date: 2026-07-10.

## The question

Grothendieck's conjecture predicts that a finite locally free group scheme of
rank `n` is killed by `n`.  The immediate target here is rank four: either
prove that every rank-four finite locally free group scheme is killed by four,
or construct a genuine counterexample, potentially over a very ramified and
complicated base.

Please make an independent, skeptical pass.  In particular:

1. audit every structural reduction and identify any hidden hypothesis;
2. look for a conceptual proof that replaces finite searches;
3. look actively for a rank-four counterexample outside the searched strata;
4. exploit the exact finite computations without treating them as a proof of
   cases they do not cover; and
5. propose concrete, bounded computations for the remaining frontier.

## Current strongest conclusion

No rank-four counterexample has been found.  Conditional only on the audited
standard reductions and the recorded exact finite-ring/Z3 UNSAT certificates,
every rank-four finite locally free group scheme over an Artin local base with
residue field `F_2` and base length at most six is killed by four.

For a minimal counterexample, the base may be taken Artin local Gorenstein.
If `M` is its one-dimensional socle, the induced bialgebra over `R/M` must
fail the stronger invariant

```text
S'(A/R): phi(I) is contained in m (ker(phi) intersect I),
```

where `phi=[2]^#=mu Delta`.  Universal `S'` on the socle quotient therefore
excludes every one-socle lift as a counterexample.

## Residue-F_2 length-seven frontier

The possible Hilbert functions of a minimal length-seven Gorenstein base and
the Hilbert functions of its length-six socle quotient are:

| base | quotient | status at this snapshot |
|---|---|---|
| `(1,1,1,1,1,1,1)` | `(1,1,1,1,1,1)` | 10 quotient classes classified; exact `S'` sweep incomplete |
| `(1,2,1,1,1,1)` | `(1,2,1,1,1)` | at most 11 immediate representatives; exact sweep running |
| `(1,2,2,1,1)` | `(1,2,2,1)` | 27 classes, 19 Gorenstein-liftable; final exact batch running |
| `(1,3,1,1,1)` | `(1,3,1,1)` | closed |
| `(1,3,2,1)` | `(1,3,2)` | closed |
| `(1,4,1,1)` | `(1,4,1)` | closed |
| `(1,5,1)` | `(1,5)` | closed |

At the end of the audited second `(1,2,2,1)` batch, 158 of 190
ring/fiber rows were closed, with no SAT `S'`-failure, timeout, OOM, or
unknown.  A final six-ring batch was active when this archive was made and
is not claimed complete here.  The stretched `(1,2,1,1,1)` sweep was also
active.  The principal sweep had prior incomplete attempts and was not
counted as closed.

The full conjecture remains open in this project.  Important unclosed regions
include larger residue fields, longer bases, and any gap in the reductions
from arbitrary bases/group schemes to the finite local connected branch.

## High-value directions

### Mathematical

- Re-audit the minimal-base Gorenstein argument and the socle-extension
  theorem for `S'`, especially all freeness/intersection assertions.
- Seek a classification-free proof of universal `S'` in rank four.
- Analyze whether a noncommutative rank-four Hopf algebra can evade every
  rank-two normal filtration.  Rank-two-by-rank-two extensions and the
  tested matched Oort--Tate ansatz are structurally killed by four.
- Move beyond `F_2`.  The rational special-fiber orbit list changes over
  nonprime or imperfect residue fields; do not silently replace rational
  classes by geometric classes.
- Investigate whether the type lemma and inverse-system/Teter constraints
  force all higher-length quotient strata into a finite inductive pattern.
- If looking for a counterexample, target simultaneous nontrivial
  multiplication and coproduct deformations over a high-embedding-dimension
  Gorenstein base, with no finite-flat rank-two normal subgroup.

### Computational

- Complete and independently audit the three remaining residue-`F_2`,
  length-seven quotient sweeps: principal, stretched, and `(1,2,2,1)`.
- Treat SAT `S'` failure only as a seed for a direct Hopf lift, not as a
  counterexample by itself.
- Treat timeout, OOM, `unknown`, missing output, and nonzero exit as
  inconclusive, never as mathematical evidence.
- Keep each solver coordinate in a fresh process with an explicit timeout
  and memory ceiling.  Recheck ring arithmetic, locality, filtration,
  Gorenstein liftability, rational fiber pinning, and the full division
  syzygy before trusting a solver result.

## Reading order

1. `reports/RANK4_SERIOUS_RAMIFIED_COUNTEREXAMPLE_PASS_2026-07-09.md`
2. `reports/STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md`
3. `reports/STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md`
4. `reports/AUDIT_REPORT_GROTHENDIECK_FINITE_FLAT_GROUP_SCHEMES_2026-07-09.md`
5. the classification and batch reports in `reports/`
6. current exact drivers in `current_scripts/`
7. representative terminal evidence in `evidence/`
8. `prior_order4_handoff/` for the earlier algebraic and bidual work
9. `larger_rank_comparison/` for possible construction ideas in ranks 8/16

## Reproducibility notes

The principal current computations use Python 3 and Z3 4.16.0.  Macaulay2
was used for certificate construction/verification; the low-memory sources
and certificate outputs are included.  Hundreds of repetitive case logs are
omitted from this curated archive.  Their audited counts and aggregate
SHA-256 values appear in the result reports; representative complete logs
are included.  `SHA256SUMS` hashes every archived file other than itself.

This archive deliberately contains no container image, virtual environment,
Python bytecode, credentials, or transient process state.
