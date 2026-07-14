# Current handoff: rank four and Grothendieck's conjecture

Snapshot: 2026-07-10.  This file supersedes all older handoff/status files.

## Task for the receiving model

Grothendieck's conjecture predicts that every finite locally free group
scheme of rank `n` is killed by `n`.  Make a serious independent attempt in
rank four: either prove the conjecture or find a genuine counterexample,
potentially over a highly ramified and complicated base.

Please be skeptical.  Audit the proof reductions, look actively for hidden
hypotheses and counterexamples outside the searched strata, and seek a
conceptual argument that could replace the finite computations.  A useful
response should distinguish theorem, exact finite computation, heuristic
evidence, and open speculation.

## Honest current conclusion

No counterexample and no proof of the full conjecture has been found.

The strongest bounded conclusion in this archive is: subject to the audited
standard reductions and the recorded exact finite-ring/Z3 UNSAT verdicts,
every rank-four finite locally free group scheme over an Artin local base
with residue field `F_2` and base length at most six is killed by four.

For a length-minimal counterexample the base may be taken Artin local
Gorenstein.  If `M=Soc(R)` is its one-dimensional socle, then the induced
bialgebra over `R/M` must fail

```text
S'(A/R): phi(I) is contained in m (ker(phi) intersect I),
phi = [2]^# = mu Delta.
```

Universal `S'` on the quotient therefore excludes all its one-socle lifts.
An `S'` failure is only a seed for a direct Hopf-lift search; it is not itself
a counterexample.

## First open residue-F_2 layer

For a minimal base of length seven, the quotient by its socle has length six.
The seven possible base/quotient Hilbert profiles and snapshot status are:

| base | quotient | status |
|---|---|---|
| `(1,1,1,1,1,1,1)` | `(1,1,1,1,1,1)` | 10 quotient classes classified; exact principal sweep incomplete |
| `(1,2,1,1,1,1)` | `(1,2,1,1,1)` | at most 11 immediate representatives; exact sweep active |
| `(1,2,2,1,1)` | `(1,2,2,1)` | closed: 27 classes, exactly 19 Gorenstein-liftable, 190/190 rows |
| `(1,3,1,1,1)` | `(1,3,1,1)` | closed |
| `(1,3,2,1)` | `(1,3,2)` | closed |
| `(1,4,1,1)` | `(1,4,1)` | closed |
| `(1,5,1)` | `(1,5)` | closed |

The strict archive audit closes all 190 H=(1,2,2,1) ring/fiber rows: 160 by
three exact failure-coordinate UNSAT verdicts and 30 as H0-vacuous.  All 19
Gorenstein-liftable quotient classes are complete, with no SAT `S'` failure,
unknown, timeout, OOM, malformed terminal log, audit contradiction, or retry
task.  This supersedes the older 98/190, 158/190, and 180/190 snapshots in
the dated reports and eliminates the length-seven base profile
`(1,2,2,1,1)` under the stated reduction.  The stretched eleven-ring sweep
was still active.  A single principal canary
`e3_00/t4_10/FAIL_1` was active with one CPU, a 6144 MiB Z3 ceiling, and a
3600-second timeout.  These live logs are deliberately omitted.

## Most valuable mathematical directions

1. Re-audit the minimal-Gorenstein argument and the socle-extension theorem,
   especially freeness and ideal-intersection assertions.
2. Seek a classification-free proof of universal `S'` for rank-four Hopf
   algebras with killed-by-two connected special fiber.
3. Analyze the noncommutative branch with no rank-two finite-flat normal
   filtration.  Rank-two-by-rank-two extensions and the tested matched
   Oort--Tate constructions are structurally killed by four.
4. Move beyond `F_2`: rational fiber orbits over larger, nonprime, or
   imperfect residue fields must not be replaced silently by geometric
   orbits.
5. Investigate whether the type lemma, inverse systems, and Teter/Gorenstein
   liftability force an inductive pattern at arbitrary base length.
6. For counterexamples, target simultaneous nontrivial multiplication and
   coproduct deformations over a high-embedding-dimension Gorenstein base,
   with no rank-two normal subgroup.

## Computational discipline

- Each exact coordinate should run in a fresh, single-threaded process with
  a bounded timeout and memory ceiling.
- Recheck arithmetic, locality, filtration, rational special-fiber pinning,
  liftability, and the full division syzygy before trusting solver output.
- SAT `S'` failure requires a direct Hopf-lift search.
- Timeout, OOM, solver `unknown`, missing output, and nonzero exit are
  inconclusive and are never negative mathematical results.
- The existing monolithic `s2check.py --ext` computation over a ramified
  `W(F_4)` extension previously consumed very large resources without a
  verdict; do not rerun it unchanged.  Split it by ring/fiber/coordinate.

## Reading order

1. `AUDIT_REPORT_GROTHENDIECK_FINITE_FLAT_GROUP_SCHEMES_2026-07-09.md`
2. `RANK4_SERIOUS_RAMIFIED_COUNTEREXAMPLE_PASS_2026-07-09.md`
3. `STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md`
4. `STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md`
5. `H1221_FULL_RESULT_2026-07-10.md`
6. `H1221_BATCH1_RESULT_2026-07-10.md`
7. `H1221_BATCH2_RESULT_2026-07-10.md`
8. the remaining classification and result reports at archive root
9. `scripts/` for source and terminal evidence

Read the audit report before relying on `THEORY_order4.md` or
`REPORT_order4.md`; those older documents contain claims subsequently
corrected or narrowed.

## Archive contents

- Current reports and structural reductions at archive root.
- All top-level repository `scripts/*.py` and `scripts/*.m2` sources, so the
  import graph is intact.
- Low-memory M2 certificate sources and outputs.
- Ring-classification and validation transcripts.
- Complete raw H1221 evidence for all 19 audited classes, together with the
  strict terminal audit.
- Completed summaries for the lower-length and closed length-seven strata.
- Slurm array scripts as reproducibility templates, although the ChatGPT app
  may use a different compute environment.
- `FILE_NOTES.tsv` and `SHA256SUMS` for provenance and integrity.

The archive contains no container image, virtual environment, credentials,
Python bytecode, or transient process state.
