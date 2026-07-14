# Structural shape of a minimal order-four counterexample

This note isolates consequences of the reductions in `THEORY_order4.md` and
`REPORT_order4.md`.  It distinguishes ordinary killed-by-four results from
the stronger invariant \(S'\).  It also records a small-ring classification
over residue field \(\mathbf F_2\).  The purpose is to identify the smallest
base rings on which a genuine counterexample could still occur, not to claim
that one occurs.

## 1. Reductions that every counterexample must satisfy

Suppose that a finite locally free group scheme of rank four is not killed by
four.  The standard reductions and the order-four analysis allow one to take
the base to be an Artin local ring \((R,\mathfrak m,k)\), with finite residue
field of characteristic two.  In the remaining branch:

1. the special fiber is connected and killed by two;
2. after a finite residue-field extension its coordinate algebra is one of
   \(k[t]/(t^4)\) or \(k[x,y]/(x^2,y^2)\);
3. the total group scheme is noncommutative (otherwise Deligne applies);
4. \(\mathfrak m^2\ne0\) (square-zero maximal ideals are covered by Schoof).

The non-killed-by-two connected fibers and the fibers with a nontrivial
etale quotient are disposed of by the connected-etale sequence, the order-two
case, rigidity, and Schoof--Torti, as explained in the report.

Now choose a counterexample whose base has minimal length.  For every socle
line \(M\subset\operatorname{Soc}(R)\), its reduction modulo \(M\) is killed by
four.  Hence the nonzero obstruction

\[
 d=[4]^\#-\eta\epsilon
\]

takes values in \(MA\).  If the socle contained two distinct lines, the
values of \(d\) would lie in their zero intersection.  Therefore

\[
 \dim_k\operatorname{Soc}(R)=1.
\]

Thus a length-minimal base is Artin Gorenstein.  Its socle line is contained
in \(\mathfrak m^2\), by Proposition 4.2/4.3 of `THEORY_order4.md`.  Moreover,
if \(\bar A=A/MA\), then \(S'(\bar A/R/M)\) must fail: Theorem 7.1 would
otherwise kill every lift.  Consequently an actual counterexample occurs one
socle layer above a failure of \(S'\), not merely above a ring on which
killedness is known.

## 2. General length and residue-field bounds

Length one and two are excluded over every finite residue field.  A
Gorenstein local ring of length three is necessarily curvilinear unless it
has square-zero maximal ideal.  The equal-characteristic case is covered for
all finite residue fields.  The exact mixed-characteristic calculations cover
both ramification types for \(k=\mathbf F_2,\mathbf F_4\), and the unramified
case for \(k=\mathbf F_8\).

Thus a counterexample of length three is still logically possible only in an
untested mixed-characteristic residue-field regime: the ramified
\(\mathbf F_8\) ring, or the relevant unramified/ramified rings over larger
finite fields.  This matters when minimizing *length*.  When minimizing the
cardinality of the finite base, the \(\mathbf F_2\) rings below come first.

## 3. Gorenstein rings of length four over \(\mathbf F_2\)

Their Hilbert function is either \((1,1,1,1)\) or \((1,2,1)\).

### 3.1 The curvilinear case

Besides the equal-characteristic and unramified rings, there are two
ramification indices and a unit-twist at ramification index two.  A complete
list is represented by

\[
 \mathbf F_2[\pi]/\pi^4,\quad \mathbf Z/16,\quad
 \mathbf Z/4[\pi]/(\pi^2-2),\quad
 \mathbf Z/4[\pi]/(\pi^2-2\pi-2),\quad
 \mathbf Z/4[\pi]/(\pi^3-2,\pi^4).
\]

The fourth ring corresponds to \(2=\pi^2+\pi^3\).  It cannot be removed by a
change of uniformizer: replacing \(\pi\) by any other generator of the
maximal ideal does not change the coefficient of \(\pi^3\) in this length.
This ring and the \(e=3\) ring were omitted from the earlier phrase “all
curvilinear rings of length at most four.”

The first three are covered by existing theorem/exact \(S'\) results.  New
exact full-bialgebra searches give killed-by-four for the last two, for both
local algebra shapes.  Subsequent exact queries prove \(S'\) itself for both
of the last two rings, so every one of their socle-line lifts is also killed.
These new runs should be cited only with their consolidated terminal log.

### 3.2 Hilbert function \((1,2,1)\)

Put \(V=\mathfrak m/\mathfrak m^2\) and
\(S=\mathfrak m^2\).  Multiplication is a nonzero symmetric bilinear form

\[
 B:\operatorname{Sym}^2(V)\longrightarrow S.
\]

The ring is Gorenstein exactly when \(B\) is nondegenerate.

* If \(2=0\), killedness follows from the equal-characteristic
  \(\mathfrak m^3=0\) theorem.  There are alternating and nonalternating
  nondegenerate forms; the latter is an \(S'\) gap but not a killedness gap
  at this length.
* If \(0\ne2\in\mathfrak m^2\), then \(\mathfrak m^2=(2)\).  Quotienting by
  this socle gives an equal-characteristic square-zero base, which satisfies
  \(S'\) by Theorem N.  Theorem 7.1 therefore kills the original ring.  This
  eliminates both nondegenerate forms at theorem level.
* If \(2\notin\mathfrak m^2\), pointed bilinear-form classification gives
  exactly three Gorenstein rings:

\[
 R_0=\mathbf Z/4[y]/(y^2),\qquad
 R_1=\mathbf Z/4[y]/(y^2-2y),\qquad
 R_u=\mathbf Z/8[y]/(2y,y^2-4).
\]

  Each has unique socle (respectively \((2y),(2y),(4)\)), and each socle
  quotient is \(B_0=\mathbf Z/4[y]/(2y,y^2)\), a mixed-characteristic
  square-zero ring for which universal \(S'\) is not known.  New exact
  full-bialgebra searches nevertheless give killed-by-four for all three
  rings and both fiber algebra shapes; again, cite the consolidated log.

It follows from this classification plus the exact runs that no
\(\mathbf F_2\)-residue counterexample has length at most four.  Section 6
below improves this to length five, so the smallest possible cardinality of a
finite local base is now at least \(2^6=64\).  This cardinality statement does
not exclude the still-open length-three rings with larger residue field.

## 4. A useful associativity lemma at length five

A Gorenstein local ring of length five has one of the Hilbert functions

\[
 (1,1,1,1,1),\qquad (1,2,1,1),\qquad (1,3,1).
\]

In the middle case, let \(t\) span \(\mathfrak m^3\), let \(s\) span
\(\mathfrak m^2/\mathfrak m^3\), and put
\(V=\mathfrak m/\mathfrak m^2\).  Write

\[
 uv=B(u,v)s\pmod {\mathfrak m^3},\qquad us=L(u)t.
\]

Here \(L\ne0\), since \(\mathfrak m^3\ne0\).  Associativity makes
\(B(u,v)L(w)\) symmetric in \(u,v,w\).  Choose \(a\) with \(L(a)=1\).
Then

\[
 B(u,v)=L(u)B(v,a)=L(u)L(v)B(a,a).
\]

Since \(B\ne0\), after scaling \(s\) this says

\[
 B=L\otimes L.
\]

Thus the multiplication form in the length-four socle quotient has rank one.
This has two useful consequences.

1. None of the rank-two \(S'\) gaps at length four (the nonalternating
   equal-characteristic form, the alternating/nonalternating ramified forms,
   or \(R_0,R_1,R_u\)) can be the socle quotient of a length-five
   Gorenstein ring with Hilbert function \((1,2,1,1)\).
2. If \(2\) itself is the socle at length five, every possible quotient is
   already an \(S'\)-known equal-characteristic ring: a principal
   \(\mathbf F_2[\pi]/\pi^4\), a square-zero ring, or the rank-one RingT
   algebra.  Hence every length-five Gorenstein ring with \((2)=\operatorname{Soc}(R)\)
   is killed by four at theorem level.

The genuinely ramified search must therefore keep \(2\) alive below the top
socle layer.

## 5. The smallest genuinely untested ramified nonprincipal base

A natural length-five, embedding-dimension-two example is

\[
 R_5=\mathbf Z/4[\pi,y]/
 (\pi^2-2,\ 2y,\ \pi y-2\pi,\ y^2-2\pi).
\]

Its additive group is \(\mathbf Z/4\{1\}\oplus
\mathbf Z/4\{\pi\}\oplus\mathbf F_2\{y\}\), so it has 32 elements, and

\[
 \mathfrak m=(\pi,y),\quad
 \mathfrak m^2=(2,2\pi),\quad
 \mathfrak m^3=(2\pi)=\operatorname{Soc}(R_5),\quad
 \mathfrak m^4=0.
\]

Its socle quotient is the mixed-characteristic rank-one ring

\[
 B_1=\mathbf Z/4[x,y]/(2x,2y,x^2-2,xy,y^2),
\]

for which \(S'\) was not previously proved.  A new exact full-bialgebra
search on this particular lift is UNSAT for a nonzero \([4]^\#\), for both
fiber algebra shapes.  The subsequent \(S'\) computation on \(B_1\), recorded
in Section 6, now excludes every socle-line lift of \(B_1\), not only this
representative.

## 6. Six length-four \(S'\) queries close every length-five
\(\mathbf F_2\) base

Rather than enumerate every 32-element Gorenstein lift, it is enough to prove
exact \(S'\) over the following six length-four rings:

\[
\begin{aligned}
 C_{34}&=\mathbf Z/4[\pi]/(\pi^3-2,\pi^4),\\
 C_{2\mathrm{tw}}&=\mathbf Z/4[\pi]/(\pi^2-2\pi-2),\\
 B_{00}&=\mathbf Z/4[x,y]/(2x,2y,(x,y)^2),\\
 B_1&=\mathbf Z/4[x,y]/(2x,2y,x^2-2,xy,y^2),\\
 C_4&=\mathbf Z/4[y]/(2y,y^3),\\
 C_8&=\mathbf Z/8[y]/(2y,y^2).
\end{aligned}
\]

The failure queries for **all six rings** have now returned UNSAT for both
local fiber algebra shapes, with SAT non-vacuity gates.  For the two principal
rings this uses the validated finite \(\operatorname{ann}(\pi)\)-coset
encoding.  For the four nonprincipal rings, division coefficients were first
quotiented by \(\operatorname{Soc}(R)=\operatorname{Ann}(\mathfrak m)\): the
fiber-killed-by-two constraints put every coefficient of \(\phi\) in
\(\mathfrak m\), so socle shifts change neither the division equation nor
kernel membership.  Exhaustive gates compare the resulting parametrization
with the full syzygy set.  The residual division space is trivial for
\(B_{00}\) and one-dimensional over \(\mathbf F_2\) for each of
\(B_1,C_4,C_8\), leaving only eight cases across the three augmentation-ideal
coordinates.  Every split failure row is UNSAT.

Indeed:

* a principal length-five ring has a principal length-four socle quotient;
  the other three principal quotient types already satisfy \(S'\);
* a \((1,3,1)\) ring with shallow mixed characteristic has quotient
  \(B_{00}\), while the equal-characteristic and \(2=\)socle cases are
  already covered;
* a \((1,2,1,1)\) ring has rank-one quotient by the associativity lemma.  If
  \(2\in\mathfrak m^2\setminus\mathfrak m^3\) the quotient is \(B_1\); if
  \(2\in\mathfrak m\setminus\mathfrak m^2\), the two pointed rank-one forms
  are \(C_4,C_8\); the remaining characteristic positions are already
  covered.

Consequently every Artin local \(\mathbf F_2\)-algebra of length at most five
is killed by four in the remaining local-fiber branch.  This is substantially
more powerful than six isolated killedness searches, because Theorem 7.1
handles every socle lift.  Together with the standard reductions for the
other special fibers, there is no rank-four counterexample over a
residue-\(\mathbf F_2\) base of length at most five.

## 7. Necessary profile at the smallest possible cardinality

Combining the preceding results, any counterexample on a finite base has
cardinality at least \(64\).  At cardinality \(64\), the residue-field and
length bounds leave only a residue-\(\mathbf F_2\), length-six base: the
corresponding length-three \(\mathbf F_4\) and length-two larger-residue-field
regimes are already covered.  A length-minimal such base must be Gorenstein,
and each of its length-five socle quotients must fail \(S'\).  Killedness of
all length-five bases is not enough to exclude this: the socle-extension
theorem specifically requires \(S'\) on the quotient.

The group scheme must still have connected killed-by-two special fiber, one
of the two local coordinate-algebra shapes, while the total Hopf algebra is
noncocommutative.  Minimizing *length* rather than cardinality continues to
leave the ramified length-three rings over larger residue fields open.

## 8. Recommended counterexample/proof search order

1. Classify the possible length-five socle quotients of a length-six
   Gorenstein base and query \(S'\) on those quotients, not merely
   \([4]^\#\ne0\) on selected lifts.
2. The six length-four computations in Section 6 already kill every
   length-five \(\mathbf F_2\) base.  Direct full-bialgebra runs on particular
   length-five lifts are now independent cross-checks rather than open cases.
3. For larger residue fields, finish the ramified length-three
   \(\mathbf F_8\) row before deeper searches: it is still the smallest
   unresolved base by length.
4. Keep both multiplication and comultiplication variable and test the two
   local rank-four algebra shapes.  A fixed-algebra or coproduct-only SAT
   signal is not a counterexample.
5. Treat the mixed-characteristic \(\alpha_2\times\mu_2\) deformation as the
   most credible special-fiber locus, but do not omit the other killed-by-two
   Hopf structures in a proof-grade exhaustive run.

The structural conclusion is not that a counterexample exists at length six.
It is that the first possible residue-\(\mathbf F_2\) layer has moved from
length five to length six, and any such example must lie over a length-five
failure of the stronger invariant \(S'\).
