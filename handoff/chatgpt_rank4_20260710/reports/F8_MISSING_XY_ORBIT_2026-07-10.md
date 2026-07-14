# The missing rank-four `xy` orbit over \(\mathbf F_8\)

Date: 2026-07-10

## Outcome

An exact orbit audit found one \(\mathbf F_8\)-rational killed-by-two
rank-four tangent fiber that was absent from the six older
\(\mathbf F_2\)-defined pins.  A full-deformation query over the very
ramified base used by the order-four search proves that this missing fiber
does **not** produce a \([4]\)-defect.  Thus it is not a counterexample to
Grothendieck's conjecture within this deformation family.

This is an exact UNSAT result.  It is not inferred from a timeout, a memory
failure, or a missing model.

## Exact fiber classification

The script `scripts/f8_xy_semilinear_orbits_20260710.py` exhausts all
\(8^4=4096\) Frobenius-semilinear \(2\times2\) matrices over \(\mathbf F_8\)
and all 3528 twisted changes of basis in \(GL_2(\mathbf F_8)\).  It finds six
orbits, of sizes

\[
  1,\ 504,\ 63,\ 1764,\ 588,\ 1176.
\]

The older pins cover five of the six.  In particular, the two old labels
`mu2mu2` and `mu2mu2_irreducible` become equivalent after extension to
\(\mathbf F_8\).  The unique missing orbit has size 1176 and representative

\[
 A=\begin{pmatrix}0&1\\1&w\end{pmatrix},
\]

encoded as `(0,1,1,2)`.  The classifier independently checks the associated
finite coproduct, coassociativity, cocommutativity, counit, and \([2]=0\)
identities.

## Full-deformation computation

The runner `scripts/order4sat_f8ram_xy_missing_orbit_20260710.py` pins only
this residue coproduct and leaves all higher multiplication and coproduct
digits free over the ramified mixed-characteristic coefficient ring.  It
uses one Z3 thread and a hard `memory_max_size` ceiling.

The 4 GiB canary established nonvacuity:

- 408 base constraints;
- H0 bialgebra plus fiber constraints: SAT;
- peak RSS about 2.44 GiB.

The subsequent MAIN run used a 12 GiB ceiling and a six-hour per-query
timeout, although it completed immediately after construction:

- construction: 15.00 seconds, 615.0 MiB RSS;
- H0: SAT in 2.06 seconds;
- MAIN bialgebra plus \([4]^\#\ne e\): UNSAT in 2.11 seconds;
- peak RSS: 2455.1 MiB;
- wall time: 21.11 seconds.

The antipode equations were deliberately deferred: any finite flat group
scheme counterexample would first give a bialgebra point satisfying MAIN,
and MAIN is already inconsistent.  Deferring the antipode therefore lowers
memory without weakening this negative conclusion.

## Scope and caveat

The result closes the unique missing \(\mathbf F_8\) orbit for this `xy`
deformation problem.  It does not by itself prove Grothendieck's conjecture
over arbitrary bases, nor does it rule out fibers that require a different
rank-four algebra type or a still more complicated base.  Its significance
is that a genuine residue-field coverage gap was found, proved nonvacuous,
and then eliminated exactly.

## Reproducibility

The recorded SHA-256 values are in
`scripts/f8_missing_xy_orbit_evidence_20260710.sha256`.  The decisive log is
`scripts/order4sat_f8ram_xy_missing_orbit_main_12g_20260710.log`.

