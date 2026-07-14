# Length-eight split and irreducible quadratic CI audit

**Date:** 11 July 2026  
**Environment:** local Mac, one Z3 thread, 120 seconds and 2048 MiB per query  
**Ledger:** `results/rank4_length8_other_ci_bool_audit_20260711.json`

## Explicit rings

Two especially clean mixed-characteristic complete intersections fill the two
quadratic tangent-cone types missing from the earlier three double-line rings:

\[
R_{\mathrm{sp}}=
\mathbf Z[x,y]/(xy,\ x^4+y^4,\ x^4-2)
\]

and

\[
R_{\mathrm{irr}}=
\mathbf Z[x,y]/(x^2+xy+y^2,\ x^4,\ x^3y-2).
\]

For the split ring, first set
\(B_{\mathrm{sp}}=\mathbf Z[x,y]/(xy,x^4+y^4)\).  The two displayed
homogeneous equations form a regular sequence, and \(B_{\mathrm{sp}}\) is
free of rank eight over \(\mathbf Z\).  Multiplication by the positive-degree
nilpotent \(x^4\) is nilpotent, so multiplication by \(2-x^4\) has determinant
\(2^8\) and is injective.  Thus adjoining the third equation is again a
regular element and the quotient has cardinality \(2^8=256\).

Similarly,
\(B_{\mathrm{irr}}=\mathbf Z[x,y]/(x^2+xy+y^2,x^4)\) is free of rank eight
over \(\mathbf Z\), with basis
\(1,x,y,x^2,xy,x^3,x^2y,x^3y\).  Multiplication by \(x^3y\) is nilpotent,
so \(2-x^3y\) is injective with determinant \(2^8\).  This proves that both
rings really are zero-dimensional complete intersections, independently of
the finite-table calculation.

In both cases the additive group is \(\mathbf Z/4\oplus(\mathbf Z/2)^6\),
the maximal ideal has 128 elements, and \(2\ne0\), \(4=0\).  Exact table
calculation gives

\[
(|\mathfrak m|,|\mathfrak m^2|,|\mathfrak m^3|,
  |\mathfrak m^4|,|\mathfrak m^5|)=(128,32,8,2,1),
\]

so the Hilbert function is \((1,2,2,2,1)\).  The socle is exactly
\(\mathbf F_2\cdot2\).  The kernel of
\(\operatorname{Sym}^2(\mathfrak m/\mathfrak m^2)\to
\mathfrak m^2/\mathfrak m^3\), in coordinates \((x^2,xy,y^2)\), is generated
by \((0,1,0)\) for \(R_{\mathrm{sp}}\) and by \((1,1,1)\) for
\(R_{\mathrm{irr}}\).  The latter form has no projective zero over
\(\mathbf F_2\), hence is irreducible.

## Exact gates

The concrete table script constructs all \(256^2\) sums and products for each
ring.  Every product was compared with a second evaluator that reduces
monomials directly from the presentation.  It also checks the residue map,
units, ring relations, maximal-ideal powers, socle, and quadratic kernel.

The Boolean solver script then exhaustively compares all \(128^2\) sums and
products in the maximal ideal with those concrete tables.  Before the focused
queries, two deterministic random assignments were evaluated in all 189
integral bialgebra equations and all nine fourth-power coordinates by both
the Boolean and coordinate evaluators.  All 396 comparisons per ring passed.
The universal chart is retained through parameter degree four, which is exact
because every parameter lies in \(\mathfrak m\) and \(\mathfrak m^5=0\).

## Solver outcome

For \(R_{\mathrm{sp}}\), targets 2 and 5 returned `UNSAT` in 45.097 and
62.488 seconds.  The other seven targets returned `UNSAT` in 0.344--2.617
seconds.  Therefore the outcome is **successful and mathematically negative**
for the full universal \(\alpha_2^2\) chart over this exact split ring.

For \(R_{\mathrm{irr}}\), targets 0, 1, 3, 4, 6, 7, and 8 returned `UNSAT`
in 5.851--15.423 seconds.  The broad nonzero queries for targets 2 and 5 each
reached the 120-second timeout.  Their narrower exact-socle variants also
timed out at 120 seconds.  The irreducible-ring outcome is therefore
**inconclusive overall**.  None of these four timeouts is mathematical
negative evidence.

No SAT model occurred.  Had one occurred, the script would have re-evaluated
all equations and targets with two concrete evaluators and exited with a
distinct campaign-stop status only after that verification.

## Exact scope and remaining gaps

This computation covers exactly two characteristic-four, residue-\(\mathbf
F_2\) complete intersections in which \(2\) is the quartic socle, and only
the universal \(\alpha_2^2\) special-fibre chart.  It does not classify all
filtered rings having split or irreducible quadratic tangent cone.  In
particular it leaves open lifts with \(2\) in degree two or three, other
quartic forms and filtered corrections, other local-local rank-four fibres,
larger residue fields, and the other length-eight Gorenstein Hilbert profiles.
It also leaves targets 2 and 5 unresolved on the one irreducible ring above.

Thus this pass supplies a complete negative result for one natural split
ring and a seven-of-nine partial negative result for one natural irreducible
ring.  It does not prove global nonexistence in length eight.
