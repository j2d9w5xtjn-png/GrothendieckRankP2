# Direct [4] result on the two stretched \(t^4_{11}\) timeout branches

**Date:** 2026-07-10  
**Outcome:** successful exact finite computation; all six direct
counterexample queries are UNSAT.

## 1. Conclusion

The two rows left inconclusive by both the 3600-second and 7200-second
strong-\(S'\) searches were

    s_f2 / t4_11 / i1
    q00  / t4_11 / i1.

Rather than repeat \(S'\), the new computation enumerates every
length-seven Gorenstein socle lift of those quotient rings, uses the
monogenic normalization of every \(t^4\) algebra lift, and asks the actual
question

\[
 [4]^\#(T)\ne0.
\]

All six coordinate presentations have a nonempty Hopf core, and all six
direct disequalities are UNSAT. Thus no non-killed-by-four rank-four group
scheme occurs over any of these socle lifts with the pinned \(t^4_{11}\)
fiber.

Subject to the minimal-Gorenstein-base and socle-extension reduction used in
STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md and
STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md, this closes the two formerly
unknown stretched branches for the rank-four conjecture. It does not prove
the stronger condition \(S'\) on the quotient rows.

Together with the earlier 83 \(S'\)-UNSAT rows and 25 H0-vacuous rows, the
entire residue-\(\mathbf F_2\), stretched
\(H_Q=(1,2,1,1,1)\) quotient frontier is now closed for actual killedness
by four. This is a bounded computational result, not an arbitrary-depth
proof of the rank-four conjecture.

## 2. Six-case universe

The complete Gorenstein socle-lift list has four presentations above

\[
 \mathbf F_2[x,y]/(x^5,xy,y^2)
\]

and two above

\[
 \mathbf Z[x]/(x^5,2x,4).
\]

The exact presentations and the nondegenerate socle-pairing proof are in
MONOGENIC_STRETCHED_DIRECT4_DESIGN_2026-07-10.md and
RANK4_CONORMAL_DIRECT4_ATTACK_2026-07-10.md. Three presentations are
deliberate coordinate duplicates; exhaustive table isomorphisms were checked
as an encoding control.

For each base \(R\), the solver writes

\[
 A=R[T]/(T^4-aT-bT^2-dT^3),\qquad a,b,d\in\mathfrak m_R,
\]

and parameterizes the nine coefficients of

\[
 \Delta T=T\otimes1+1\otimes T+
 \sum_{1\le i,j\le3}c_{ij}T^i\otimes T^j.
\]

It pins the special fiber to \(t^4_{11}\), imposes relation stability and
coassociativity, forms \(q(T)=\mu\Delta(T)\), and asks
\(q(q(T))\ne0\). Counitality is built into the form of \(\Delta T\);
multiplicativity follows from relation stability. A finite free bialgebra
over the Artin-local base with Hopf special fiber has an antipode by lifting
convolution invertibility.

Since \(T\) generates \(A\), \(q(q(T))=0\) is equivalent to
\([4]^\#=e\) on all of \(A\).

## 3. Audited results

The canonical local run is

    results/monogenic_direct4/local1g_20260710

It used Python 3.14 and Z3 4.16.0, one solver thread, a 1024 MiB Z3 ceiling,
300-second H0 and direct-query timeouts, and one fresh process per case.

| case | H0 core | direct \([4](T)\ne0\) | classification | total | peak RSS |
|---|---|---|---|---:|---:|
| sf2_g0_a0 | SAT | UNSAT | direct-[4]-UNSAT | 14.63 s | 462.83 MiB |
| sf2_g0_a1 | SAT | UNSAT | direct-[4]-UNSAT | 16.48 s | 461.67 MiB |
| sf2_g1_a0 | SAT | UNSAT | direct-[4]-UNSAT | 15.56 s | 479.55 MiB |
| sf2_g1_a1 | SAT | UNSAT | direct-[4]-UNSAT | 15.75 s | 497.50 MiB |
| q00_a0 | SAT | UNSAT | direct-[4]-UNSAT | 11.78 s | 493.61 MiB |
| q00_a1 | SAT | UNSAT | direct-[4]-UNSAT | 13.65 s | 497.91 MiB |

The crash-safe runner completed all six in 88.714 seconds. The strict
standard-library auditor exited zero and reported

    AUDIT PASS six_of_six_H0_SAT_and_direct4_UNSAT errors=0 unknown=0 SAT=0

Every process also passed:

- the independent \(\mathbf F_2\) bit-mask check of the \(t^4_{11}\)
  relation, coassociativity, and killed-by-two condition;
- all \(128^3\) base-ring associativity and distributivity triples;
- locality, units, maximal-ideal sizes \(64,16,8,4,2,1\), and one-dimensional
  socle checks;
- all \(128^2\) operations in the quotient map;
- the applicable all-\(128^2\) duplicate-presentation isomorphism check;
- the exact system-size gate: 84 core constraints and 12 ring-valued
  parameters.

There were no partial logs, failed processes, solver unknowns, SAT
candidates, or audit errors.

## 4. Adversarial controls

The disequality \(q(q(T))\ne0\) was detached from the Hopf equations on one
representative of each of the three base-ring isomorphism classes. All three
detached formulas were SAT. Thus the encoded defect is not identically zero
by construction.

The same three representatives were also run through the QF_BV-specific
solver. Each again had H0 SAT and direct disequality UNSAT. This is a
different decision procedure for the same formula, not independent
mathematical evidence.

## 5. Frozen source and evidence hashes

    ac70fdf145989723133d4c4efecb740353b0d8530bc9ee060089271de7a3caac
      scripts/monogenic_stretched_direct4_20260710.py

    804e1ef6ce47860c4707148e0b5507d303e7f89097d588e15b5b99ff5ddf2f33
      scripts/run_monogenic_stretched_direct4_local_20260710.py

    29806e4d415cc5dfb1b886bc872eb3765c28e1be1509666ea8e69680f9562357
      scripts/audit_monogenic_stretched_direct4_local_20260710.py

    6a2e338b7826a9a338a5df90590a377e0fa14c7b995e84fe809e60b36886b55d
      results/monogenic_direct4/local1g_20260710/RUN_MANIFEST.json

    6a5c3897db3cddae4c00c35ada0d909a30eb80e548eb870b206be70305dfe8e7
      results/monogenic_direct4/local1g_20260710/RUN_COMPLETE.json

The six individual log hashes are recorded inside RUN_COMPLETE.json and are
recomputed by the strict auditor.

## 6. Scope and next target

This computation closes the two stretched timeout branches at length seven
for actual \([4]\), under the stated structural reduction. It does not close:

- the partial principal length-seven local--local sweep;
- larger residue fields;
- arbitrary base length;
- the uniform local--local conormal obstruction
  \((1+\delta)(J/J^2)\).

The last item is the remaining hand-theoretic wall described in
REGULAR_TRANSLATION_RANK4_EXPONENT8_2026-07-10.md and
RANK4_CONORMAL_DIRECT4_ATTACK_2026-07-10.md.
