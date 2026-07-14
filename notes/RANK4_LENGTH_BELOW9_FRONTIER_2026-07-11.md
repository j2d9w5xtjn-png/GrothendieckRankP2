# Rank four below base length nine: audited frontier

**Date:** 11 July 2026  
**Verdict:** no rank-four counterexample of base length below nine is
currently certified, but global nonexistence below nine is **not proved**.
Length nine is the smallest fully verified example, not a proved global
minimum.

## 1. What the length-nine example proves

The audited example has

\[
R_9=(\mathbf Z/4)[x,y]/(x^3,y^3,xy^2-2)
\]

and

\[
A=R_9[U,V]/(U^2-xyU-x^2V,\;V^2-y^2V).
\]

With

\[
\lambda=(1+yU)(1+xV),\qquad
\Delta(U)=U\otimes1+\lambda\otimes U,\qquad
\Delta(V)=V\otimes\lambda+1\otimes V,
\]

one has

\[
[4]^\#(U)=2xUV\ne0,\qquad [8]=e.
\]

The base is Gorenstein of Hilbert function \((1,2,3,2,1)\), and
\(2x=x^2y^2\) spans its socle. Consequently every proper quotient of this
particular base kills the displayed defect; in particular the length-eight
quotient \(R_9/(2x)\) is killed by four.

This proves quotient-minimality, not global minimality. The bridge coefficient
equations also force \(x^3=y^3=0\) and \(xy^2=-2\), so the same conclusion
holds throughout that exact group-like bridge family.

The apparent larger-residue-field loophole in the cardinality argument can be
closed. If the bridge maps to a local Artin ring \(S\) with perfect residue
field \(k\) and \(2x\) survives, then \(S\) contains the coefficient ring
\(W_2(k)\). The induced map

\[
R_9\otimes_{\mathbf Z/4}W_2(k)\longrightarrow S
\]

is injective: its source is local Gorenstein of \(k\)-length nine with socle
\(k(2x)\), so any nonzero kernel would kill \(2x\). Thus every base in this
bridge family has ordinary Artin length at least nine, over any finite residue
field.

## 2. What was known below nine

For residue field \(\mathbf F_2\), the existing structural classifications and
exact solver corpus exclude lengths at most six, conditional on the recorded
solver encodings and the socle-extension reduction.

At length seven there are seven Gorenstein Hilbert profiles. Six nonprincipal
profiles are closed for actual killedness by four. The principal profile
\((1,1,1,1,1,1,1)\) is not globally closed: its ten length-six quotient ring
classes are classified, but the inherited local-local sweep contains unknown
and incomplete rows.

At length eight there was no global ring classification or exhaustive Hopf
search in the workspace. Exact \(\mathbf F_2\) computations also do not
automatically exclude solutions over larger residue fields. Hence the older
files do not justify the assertion that nine is globally minimal.

## 3. Structural reduction of the length-eight problem

A shortest counterexample base can be quotiented maximally while retaining a
nonzero fourth-power coefficient. The resulting base is Artin local
Gorenstein and that coefficient spans its socle.

The complete numerical list of length-eight Gorenstein Hilbert functions is:

| socle degree | Hilbert functions |
|---:|---|
| 2 | \((1,6,1)\) |
| 3 | \((1,5,1,1),(1,4,2,1),(1,3,3,1)\) |
| 4 | \((1,4,1,1,1),(1,3,2,1,1),(1,2,2,2,1)\) |
| 5 | \((1,3,1,1,1,1),(1,2,2,1,1,1)\) |
| 6 | \((1,2,1,1,1,1,1)\) |
| 7 | \((1,1,1,1,1,1,1,1)\) |

The tangent-square lemma puts the fourth-power defect in \(\mathfrak m^3\),
so socle degree two is impossible. At socle degree three, the recorded mixed
\(\alpha_2^2\) cubic MinRank calculation forces the middle catalecticant rank
to be at least four; Gorenstein duality then forces length at least ten. The
other audited geometric local-local charts have zero cubic target. Thus,
conditional on that Boolean MinRank UNSAT verdict, the four profiles of socle
degree at most three are excluded over \(\mathbf F_2\).

The initial residue-\(\mathbf F_2\) length-eight frontier was therefore the
seven profiles of socle degree at least four. The needed filtered calculation
has now been completed on the mixed \(\alpha_2^2\) chart. Formal implicit
elimination leaves 15 tangent parameters, and the filtered universal quotient
through degree four has graded dimensions

\[
 (15,107,509,1871).
\]

For a socle functional \(\lambda=(\lambda_3,\lambda_4)\), the relevant
degree-two dimension is the rank of the filtered block

\[
 \begin{pmatrix}M_{22}&M_{21}\\0&M_{31}\end{pmatrix}
 \quad\text{minus}\quad \operatorname{rank}(M_{31}),
\]

where \(M_{21}\) includes the quartic Bockstein tail created while cancelling
the cubic relations. The exact Boolean search split \(M_{31}\) into its five
possible \(\mathbf F_2\)-rank strata. All strata were `UNSAT`, including the
symmetry-broken rank-two stratum in 96.30 seconds. Conditional on those solver
verdicts, every target-retaining socle-degree-four quotient in this chart has
\(h_2\ge3\), which is incompatible with base length eight.

This is genuinely filtered: the homogeneous \(M_{22}\)-only problem has a
rank-two `SAT` point, but its filtered completion is inconsistent. The ledger
is `results/rank4_filtered_quartic_a2a2_audit_20260711.json`. Thus all
socle-degree-at-most-four cases of the mixed \(\alpha_2^2\) chart are excluded
over residue \(\mathbf F_2\). Other local-local fibres at socle degree four,
all charts at higher socle degree, and larger residue fields remain open.

## 4. New exact length-eight computations

The three mixed-characteristic complete intersections

\[
R_k=\mathbf Z[x,y]/(x^2,y^4,xy^k-2),\qquad k=1,2,3,
\]

all have length eight, Hilbert function \((1,2,2,2,1)\), and residue field
\(\mathbf F_2\). They are the most direct \((2,4)\)-grid replacements for the
\((3,3)\)-grid length-nine base.

The exact integral universal \(\alpha_2^2\) chart has 45 ring-valued
parameters, 189 bialgebra equations, and nine fourth-power coordinates. A
specialized Boolean implementation used seven bits for each maximal-ideal
element, preserved the characteristic-four addition carries, and retained all
ordinary parameter terms through degree four; terms of degree at least five
vanish on these bases.

For each \(R_k\):

- all \(128^2\) sums and products were checked against a separate concrete
  coordinate implementation;
- random evaluations of all 189 equations and nine targets were compared with
  the independent polynomial evaluator;
- the nonvanishing query was run separately for each of the nine target
  coordinates;
- every one of the 27 queries returned `UNSAT` within the 120-second,
  2048-MiB bound;
- there were no timeouts, unknowns, or memory failures.

Thus the outcome is successful and mathematically negative for the full
universal \(\alpha_2^2\) chart over these three exact rings. It is not merely
a fixed-algebra or bridge-ansatz result. The audit ledger is
`results/rank4_length8_ci_bool_audit_20260711.json`.

Scope is essential: these three rings cover the double-line quadratic
associated-graded type with particularly simple quartic relations. By
themselves they do not address split or irreducible quadratic types, other
filtered rings with the same Hilbert function, the other local-local Hopf
fibres, or the other surviving Hilbert profiles.

Two additional characteristic-four complete intersections were then tested:

\[
 R_{\mathrm{sp}}=\mathbf Z[x,y]/(xy,x^4+y^4,x^4-2)
\]

and

\[
 R_{\mathrm{irr}}=\mathbf Z[x,y]/(x^2+xy+y^2,x^4,x^3y-2).
\]

Both have cardinality \(2^8\), Hilbert function \((1,2,2,2,1)\), and socle
\(\mathbf F_2(2)\). Full 256-element table gates and independent monomial
reducers passed. On \(R_{\mathrm{sp}}\), all nine universal
\(\alpha_2^2\) target queries were `UNSAT`. On \(R_{\mathrm{irr}}\), seven
were `UNSAT`, but targets 2 and 5 timed out both in broad nonzero form and in
the narrower exact-socle form; this ring is therefore inconclusive. See
`results/rank4_length8_other_ci_bool_audit_20260711.json`.

These are one split and one irreducible lift, not classifications of their
filtered quadratic types. In particular, they do not close other quartic
forms, filtered corrections, or cases in which 2 has smaller filtration
order.

The broader shared-group-like, opposite-skew-primitive ansatz was also tested
on the three \(R_k\) bases. It has a nonempty core for \(R_2,R_3\) but no nonzero
fourth-power coordinate; the \(R_1\) core is empty. A different exact Hopf
correction exists on \(R_2\), but its doubling word is already the unit word.

## 5. New length-seven checks

On the principal base \(\mathbf F_2[t]/t^7\), all four normalized monogenic
\(t^4_{c_1c_4}\) charts were tested directly. Independent bit-mask gates
checked relation stability, coassociativity, and killedness by two on every
special fibre. All \(128^3\) base-ring associativity/distributivity triples
also passed. Each exact Hopf core was `SAT`, while each direct query
\([4]^\#(T)\ne0\) was `UNSAT`. The four builds took 12.93--13.40 seconds and
the four terminal disequalities took 0.015--0.075 seconds.

This closes the complete monogenic \(t^4\) branch over this one
equal-characteristic principal base. It does not close the other principal
mixed-characteristic rings or the nonmonogenic \(\alpha_2^2\) and \(W_2[F]\)
fibres. The combined ledger is
`results/principal_length7_f2_t7_all_t4_pins_audit_20260711.json`; the older
single-row ledger remains as an independent \(t^4_{11}\) run.

A separate exact Boolean encoding of the full 45-parameter chart on the same
base also began the nonmonogenic local-local rows. On the \(\alpha_2^2\) chart,
targets 0 and 1 were `UNSAT`, while target 2 reached the 120-second timeout and
is inconclusive. On the \(W_2[F]\) chart, target 0 was `UNSAT`; the remaining
targets were not run. The 189 equations and nine targets have ordinary
parameter degree at most four, so this encoding is exact on
\(\mathbf F_2[t]/t^7\); only the solver coverage is partial. The ledger is
`results/principal_length7_f2_t7_universal_partial_20260711.json`.

An independent Boolean implementation next tested target 2 of the universal
\(\alpha_2^2\) chart on the six pure principal rings

\[
 R_e=\mathbf Z[t]/(t^7,2-t^e),\qquad 1\le e\le6.
\]

All 128-element arithmetic tables and the full 189-equation polynomial source
were cross-gated against a separate integral carry reducer. The \(e=1\) query
was `UNSAT`; the five queries \(e=2,\ldots,6\) each reached the 120-second
timeout and are inconclusive. Even the narrower exact-socle query for
\(e=2\) timed out, so the other targets and nonzero carry tails were left
unrun. This is recorded in
`results/PRINCIPAL_LENGTH7_MIXED_TAILZERO_BOOL_INDEPENDENT_20260711.md`.

## 6. Reproduction

Representative commands on the local Mac are:

```bash
python3 scripts/search_rank4_length8_ci_bool_20260711.py \
  --k 2 --target 2 --condition nonzero \
  --timeout 120 --memory-mb 2048 --audit-trials 2

python3 scripts/probe_principal_length7_t4_11_direct_20260711.py \
  --timeout 120 --gate-timeout 60 --memory-mb 2048 --engine smt

python3 scripts/prototype_rank4_filtered_quartic_20260711.py \
  --target 2 --search-filtered --q-rank-case 2 --timeout-ms 240000
```

The earlier mixed-width length-eight searches timed out at 60 seconds. Those
runs are classified as inconclusive and are not used as negative evidence;
the later Boolean queries completed with exact `UNSAT` verdicts and supersede
them.

## 7. Conclusion

The correct answer is presently:

\[
\boxed{\text{No counterexample of length below nine is known here, but none is
globally ruled out.}}
\]

Length nine remains the smallest certified construction. Proving it minimal
still requires extending the filtered calculation to the other local-local
fibres and to the higher-socle-degree length-eight profiles, completing the
principal length-seven frontier, and controlling residue-field extensions.
Conversely, a single `SAT` model in any remaining exact chart would have to be
independently verified as a Hopf algebra before being announced as a shorter
example.
