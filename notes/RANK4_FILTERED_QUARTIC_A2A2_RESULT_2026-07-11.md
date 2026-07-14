# Filtered quartic obstruction on the universal mixed `alpha_2^2` chart

**Date:** 11 July 2026  
**Outcome:** successful, computer-assisted negative result on this chart.  
**Global scope warning:** this does not settle all rank-four group schemes of
base length below nine.

## Result

Let

\[
 P=\mathbf Z_{(2)}[p_0,\ldots,p_{44}],\qquad
 \mathfrak q=(2,p_0,\ldots,p_{44}),
\]

and let `I` be the 189-equation bialgebra ideal on the universal mixed
`alpha_2^2` chart.  Work in the exact filtered jet

\[
 C=P/(I+\mathfrak q^5).
\]

Conditional on the recorded Z3 UNSAT verdicts, every socle-degree-four
filtered Gorenstein quotient of `C` which retains a fourth-power coordinate
has

\[
 \boxed{h_2\ge 3.}
\]

Thus this chart has no target-retaining quotient with any of the three
length-eight socle-degree-four Hilbert functions

\[
 (1,4,1,1,1),\qquad (1,3,2,1,1),\qquad (1,2,2,2,1).
\]

The exact ledger is
[`results/rank4_filtered_quartic_a2a2_audit_20260711.json`](../results/rank4_filtered_quartic_a2a2_audit_20260711.json),
and the executable prototype is
[`scripts/prototype_rank4_filtered_quartic_20260711.py`](../scripts/prototype_rank4_filtered_quartic_20260711.py).

## Exact elimination and filtered ranks

The parameter part of the linearized 189 equations has rank 30.  Formal
implicit iteration eliminates those 30 actual parameters through
`q`-order four, leaving 15 actual parameters and the `2`-adic symbol.  Every
selected implicit equation has residual order at least five after
substitution.

The resulting 16-symbol filtered standard-basis calculation gives

| degree | ambient dimension | initial-ideal rank | quotient dimension |
|---:|---:|---:|---:|
| 1 | 16 | 1 | 15 |
| 2 | 136 | 29 | 107 |
| 3 | 816 | 307 | 509 |
| 4 | 3876 | 2005 | 1871 |

The first three quotient dimensions reproduce the independently audited
mixed cubic dimensions `(15,107,509)`.  This is an internal check that the
new formal elimination has preserved the earlier exact calculation.

At every level, integer polynomials are added before an initial form is
taken.  Multiplication by the sixteenth symbol means multiplication by the
integer `2`.  Hence a cancellation of two odd coefficients produces the
next filtered carry instead of disappearing as it would after premature
reduction modulo two.

## Why homogeneous `gr_4` is insufficient

Write a filtered dual through the top two relevant layers as

\[
 \lambda=(\lambda_3,\lambda_4).
\]

After canonical cancellation through degree three, define

\[
\begin{aligned}
 M_{22}(a,b)&=\lambda_4(ab),\\
 M_{31}(c,x)&=\lambda_4(cx),\\
 M_{21}(a,x)&=
 \lambda_3\bigl((ax)_3\bigr)
 +\lambda_4\bigl((ax)_4^{\mathrm{carry}}\bigr).
\end{aligned}
\]

Here `a,b` lie in the degree-two quotient, `c` in degree three, and `x` in
degree one.  The last summand is the filtered/Bockstein term created when
degree-three pivot relations are cancelled by exact integral lifts.  It is
not determined by the homogeneous quartic multiplication table.

For the degree-two layer of the filtered apolar quotient one obtains

\[
 h_2=
 \operatorname{rank}
 \begin{pmatrix}M_{22}&M_{21}\\0&M_{31}\end{pmatrix}
 -\operatorname{rank}(M_{31}).
\]

Indeed, a degree-two initial class can be killed by a degree-three
correction precisely when its `M22` row vanishes and its `M21` row lies in
the row space of `M31`.  Equivalently, the kernel is the kernel of

\[
 A_2\longrightarrow A_2^*\oplus\operatorname{coker}(M_{31}),
 \qquad a\longmapsto(M_{22}(a,-),[M_{21}(a,-)]).
\]

This also gives the necessary condition for any actual filtered Gorenstein
quotient: its top socle functional and the next filtered lift produce such a
pair.  In particular, `h2 <= 2` forces `rank(M22) <= 2`; the homogeneous
quartic apolar algebra then has `rank(M31) <= 2` by Macaulay growth.

There are exact homogeneous quartics satisfying the target-2 socle
conditions with

\[
\operatorname{rank}M_{22}=\operatorname{rank}M_{31}=2.
\]

One solver witness has 743 nonzero quartic coordinates and hash
`f1886b3e...eff7`.  For that fixed quartic, however, the 1,392 filtered
linear equations in the 509 cubic-dual coordinates have rank 489 and are
inconsistent.  Thus homogeneous `gr_4` not only fails logically; it gives a
literal false positive on this chart.

## Exact rank-two encoding

Over `F2`, the full condition `h2 <= 2` is equivalent to the existence of
two-column/two-row factorizations

\[
 M_{22}=U V_{22},\qquad
 M_{31}=QZ,\qquad
 M_{21}=U V_{21}+WZ,
\]

with `rowspace(W)` contained in `rowspace(Q)`.  The containment guarantees
that `WZ` is an actual degree-three correction coming from `M31`; omitting
it creates spurious SAT models.

The possible row spaces of a two-column matrix `Q` over `F2` are exhaustive:

- rank zero;
- one of the three lines `10`, `01`, `11`;
- rank two.

The first four strata are UNSAT in at most 1.68 seconds.  In the rank-two
stratum, `Q` and `Z` both have rank two.  The residual `GL_2(F2)` symmetry is
fixed without loss by requiring the first nonzero row of `Q` to be `10` and
the first row outside that line to be `01`.  This final stratum is UNSAT in
96.30 seconds.  The five canonical SMT hashes are recorded in the JSON
ledger.

Two earlier exact but ungauged encodings reached their 120-second timeout.
They remain classified as inconclusive and are not used as negative
evidence; their hashes are retained in the ledger.

## All nine targets

The swap `e1 <-> e2` is an automorphism of the branch-0 pinned fiber and of
the universal chart.  It has target orbits

\[
 \{0,4\},\quad\{1,3\},\quad\{2,5\},\quad\{6,7\},\quad\{8\}.
\]

- Targets 2 and 5 have two-term cubic classes and two-term quartic carry
  classes.  Multiplication by the 15 tangent directions gives six
  independent top-socle constraints.  The full filtered five-stratum query
  above is UNSAT for target 2, hence also for target 5 by the exact swap.
- Targets 0, 1, and 8 have zero cubic class.  Their quartic classes have
  support 2, 2, and 4.  Therefore a retaining functional must already detect
  that homogeneous quartic.  The necessary `rank(M22) <= 2` queries are
  separately UNSAT in 0.25, 0.25, and 0.26 seconds.  Symmetry transfers the
  first two results to targets 4 and 3.
- Targets 6 and 7 are zero through order four.

This exhausts all nine fourth-power coordinates on the mixed
`alpha_2^2` jet.

## Reproduction and qualification

Representative local commands are

```bash
python3 scripts/prototype_rank4_filtered_quartic_20260711.py \
  --target 2 --emit-products

python3 scripts/prototype_rank4_filtered_quartic_20260711.py \
  --target 2 --search-filtered --q-rank-case 2 --timeout-ms 120000

python3 scripts/prototype_rank4_filtered_quartic_20260711.py \
  --target 0 --search-homogeneous --timeout-ms 60000
```

The source rebuilds the universal equations rather than reading a frozen
quartic export.  Its degree-one through degree-three ranks agree with the
independent cubic auditors, but the quartic ranks and solver encodings have
not yet been independently reimplemented.  The UNSAT conclusions are
therefore computer-assisted and conditional on the solver verdicts and this
new source.  They prove the desired obstruction on the universal mixed
`alpha_2^2` chart only; branches `W2[F]` and `t4`, greater Loewy depth, and
the other surviving length-eight profiles remain outside this computation.

The decisive rank-two payload was also rerun from the final source.  A first
repeat reached the 120-second bound and is correctly inconclusive.  Repeating
the identical payload with a 240-second bound returned `UNSAT` in 96.35
seconds, with the same SMT SHA-256 recorded above.  Both reruns are retained
in the JSON ledger.
