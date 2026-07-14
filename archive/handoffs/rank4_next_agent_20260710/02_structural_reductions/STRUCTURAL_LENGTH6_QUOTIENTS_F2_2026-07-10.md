# Length-six Gorenstein bases over \(\mathbf F_2\): length-five socle quotients

This note classifies a finite list of length-five rings whose universal
\(S'\) identities suffice to exclude every residue-\(\mathbf F_2\),
length-six minimal counterexample in the rank-four problem.  The list is an
upper list of quotient profiles: any further Gorenstein-liftability
restriction can only shorten it.

## 1. Two general lemmas

Let \((R,\mathfrak m,k)\) be Artin local Gorenstein of length six, with
\(k=\mathbf F_2\), and let \(T=\operatorname{Soc}(R)\).  Put \(Q=R/T\) and
\(e=\dim_k\mathfrak m/\mathfrak m^2\).

First,

\[
 \dim_k\operatorname{Soc}(Q)=e.
\]

Indeed,

\[
 \operatorname{Soc}(Q)=(T:\mathfrak m)/T
   =\operatorname{Ann}_R(\mathfrak m^2)/T.
\]

Gorenstein duality gives
\(\ell(\operatorname{Ann}_R(\mathfrak m^2))=
\ell(R/\mathfrak m^2)=1+e\), while \(\ell(T)=1\).

Second, positivity of the nonzero Hilbert layers, the one-dimensional final
layer, and the total length give exactly five possible Hilbert functions.
Here one also uses that the associated graded ring is generated in degree
one: if the embedding dimension is one, every nonzero graded layer has
dimension one.  This excludes positive numerical compositions such as
\((1,1,2,1,1)\), which do not occur as local-ring Hilbert functions.  The
five possibilities are:

\[
 (1,1,1,1,1,1),\quad (1,2,1,1,1),\quad (1,2,2,1),
 \quad (1,3,1,1),\quad (1,4,1).
\]

Their quotients and types are:

| \(H_R\) | \(H_Q\) | \(\dim\operatorname{Soc}(Q)\) |
|---|---|---:|
| \((1,1,1,1,1,1)\) | \((1,1,1,1,1)\) | 1 |
| \((1,2,1,1,1)\) | \((1,2,1,1)\) | 2 |
| \((1,2,2,1)\) | \((1,2,2)\) | 2 |
| \((1,3,1,1)\) | \((1,3,1)\) | 3 |
| \((1,4,1)\) | \((1,4)\) | 4 |

In particular, a nonprincipal socle quotient is never Gorenstein.  The
already-checked length-five Gorenstein rings \(R_5\) and \(R_{xy}\) have type
one, so neither can be the socle quotient of a length-six minimal
Gorenstein base.  Their \(S'\) results are valid but do not remove a profile
from the list below.

Write \(j=\operatorname{ord}_{\mathfrak m}(2)\), with \(j=\infty\) if
\(2=0\).  If \(j\) is the socle degree then \(2\) dies in \(Q\); if it is
smaller, its initial form survives in the same graded degree.

## 2. Principal quotient: seven ring classes, all already closed

For \(H_R=(1,1,1,1,1,1)\), \(Q\) is a principal length-five ring.  There
are seven residue-\(\mathbf F_2\) isomorphism classes, represented by eight
coordinate presentations in the completed solver sweep:

1. \(\mathbf F_2[t]/t^5\);
2. \(\mathbf Z/32\);
3. three \(e=2\) ring classes, represented by
   \[
   P_{c,d}=\mathbf Z/8[t]/
     (4t,\ t^2-2-2ct-4d),\qquad(c,d)\in\mathbf F_2^2;
   \]
4. \(P_3=\mathbf Z/4[t]/(t^3-2,t^5)\);
5. \(P_4=\mathbf Z/4[t]/(t^4-2,t^5)\).

Here \(P_{0,0}\cong P_{0,1}\): in \(P_{0,0}\), the uniformizer
\(q=t+2\) satisfies \(q^2=6\), giving the \((0,1)\) presentation; the same
change gives the inverse identification.  Exhaustive enumeration of
uniformizers separates the other two presentations.  Thus these correspond
to \(j=\infty,1,2,3,4\), with three isomorphism classes at \(j=2\).
Universal \(S'\) is closed on all seven classes (all eight coordinate
presentations were queried), including all six rational \(xy\) Hopf fibers
and all four \(t^4\) normal forms.  Hence the principal length-six stratum is
eliminated.

## 3. Stretched quotient \((1,2,1,1)\): seven rings

Here \(e=2\) and \(Q\) has type two.  Choose a hidden socle element
\(y\notin\mathfrak m_Q^2\) and an active generator \(x\).  To see the
normalization, put \(V=\mathfrak m_Q/\mathfrak m_Q^2\), let

\[
 B:\operatorname{Sym}^2V\longrightarrow
   \mathfrak m_Q^2/\mathfrak m_Q^3,
 \qquad
 L:V\longrightarrow
   \operatorname{Hom}(\mathfrak m_Q^2/\mathfrak m_Q^3,
                      \mathfrak m_Q^3)
\]

be the two graded multiplication maps.  Associativity says

\[
 B(a,b)L(c)=B(b,c)L(a).
\]

Since \(L\ne0\), this forces \(B\) to be a nonzero scalar multiple of
\(L\otimes L\).  Thus there is one active tangent direction and one radical
direction.  A shift of the radical lift by a multiple of \(x^2\) kills its
product with \(x\); type two then forces its square to vanish, since otherwise
there would be no second socle direction.  Consequently the constraints
normalize to

\[
 x^2\ne0,\quad x^3\ne0,\quad x^4=0,\qquad y\mathfrak m_Q=0.
\]

Five rings are split fiber products

\[
 B(P)=P\times_{\mathbf F_2}\mathbf F_2[y]/y^2
     =P[y]/(y^2,\mathfrak m_Py),
\]

one for each principal length-four ring

\[
 \mathbf F_2[x]/x^4,\quad \mathbf Z/16,\quad
 \mathbf Z/4[x]/(x^2-2),\quad
 \mathbf Z/4[x]/(x^2-2x-2),\quad
 \mathbf Z/4[x]/(x^3-2,x^4).
\]

The remaining two occur when the tangent class of \(2\) is the hidden
socle direction.  Write

\[
 2=y+a x^2+b x^3.
\]

Changing \(y\) by \(b x^3\) removes \(b\), but changing it by \(x^2\) would
destroy the condition that \(y\) is socle.  Thus \(a\in\mathbf F_2\) is a
real filtered invariant, giving

\[
 Q_0=\mathbf Z/4[x]/(x^4,2x),\qquad
 Q_1=\mathbf Z/4[x]/(x^4,2x-x^3).
\]

They are nonisomorphic: \(2\in\operatorname{Soc}(Q_0)\), whereas
\(2\notin\operatorname{Soc}(Q_1)\).  Both occur.  For example,

\[
 \mathbf Z/8[x]/(2x,x^4-4)
\]

is a Gorenstein lift of \(Q_0\), while

\[
 \mathbf Z/4[x]/(x^5,2x-x^3)
\]

is a Gorenstein lift of \(Q_1\); in each case the killed socle is generated
by \(x^4\).

Thus this stratum contributes seven new \(S'\) base rings.  The exact sweep
on all seven is now complete.  Every ring passed exhaustive arithmetic,
locality, filtration, socle, generator, and full-syzygy gates.  Across the
70 ring/fiber rows, 15 were H0-vacuous and 55 were nonvacuous with H0 and S1
SAT; all 165 coordinate failure queries were UNSAT, with no timeout or
unknown.  The residual syzygy quotient was enumerated by cosets, including
the cyclic order-four quotient for the \(B(\mathbf Z/16)\) row.

See
[`SPRIME_STRETCHED_LENGTH5_STRATIFIED_2026-07-10.md`](SPRIME_STRETCHED_LENGTH5_STRATIFIED_2026-07-10.md).

## 4. Quotient \((1,2,2)\): fourteen pointed quadratic types

Put \(V=\mathfrak m_Q/\mathfrak m_Q^2\), \(\dim V=2\), and
\(W=\mathfrak m_Q^2\), \(\dim W=2\).  Since \(\mathfrak m_Q^3=0\), the
ring multiplication is exactly a surjection

\[
 \operatorname{Sym}^2V\longrightarrow W.
\]

Its kernel is a line generated by a nonzero binary quadratic \(q\).  Let
\(\mathfrak n=(x,y)\) and put

\[
 r=x^2+xy+y^2.
\]

Every candidate ring has one of the following explicit presentations.

### 4.1 Equal characteristic: three rings

\[
 C(q;0)=\mathbf F_2[x,y]/(q,\mathfrak n^3),qquad
 q\in\{x^2,xy,r\}.
\]

### 4.2 The tangent class of \(2\) is nonzero: five rings

\[
 C(q;p)=\mathbf Z[x,y]/(2-p,q,\mathfrak n^3),
\]

for

\[
 (q,p)=(x^2,x),(x^2,y),(xy,x),(xy,x+y),(r,x).
\]

### 4.3 The initial form of \(2\) lies in degree two: six rings

\[
 C(q;w)=\mathbf Z[x,y]/(2-w,q,\mathfrak n^3),
\]

for

\[
\begin{aligned}
 q=x^2:&\quad w=y^2,\ xy,\ xy+y^2;\\
 q=xy:&\quad w=x^2,\ x^2+y^2;\\
 q=r:&\quad w=x^2.
\end{aligned}
\]

These are local finite rings at the displayed nilpotent maximal ideal; the
relations involving \(2\) automatically give the required additive carries.
There is no omitted higher carry: if the tangent class of \(2\) is
\(p\in V\), initially write \(2=\widetilde p+w\) with \(w\in W\), then
replace the chosen lift \(\widetilde p\) by \(\widetilde p+w\).  Since
\(\mathfrak m_Q^3=0\), this does not change the multiplication kernel
\(q\).  If \(2\) has order two in the filtration, its nonzero class
\(w\in W\) is itself the complete point datum.  Thus the pairs \((q,p)\)
and \((q,w)\) below exhaust the filtered possibilities.

The orbit count is elementary and auditable.  The group
\(\mathrm{GL}_2(\mathbf F_2)\cong S_3\) has three orbits on the seven
nonzero quadratics: a square, a product of two distinct rational linear
forms, and the irreducible quadratic.  Their stabilizers have orders
\(2,2,6\).  On nonzero tangent vectors their orbit counts are respectively
\(2,2,1\), giving five.  On the three nonzero vectors of
\(W=\operatorname{Sym}^2V/(q)\), the counts are \(3,2,1\): the square
stabilizer acts trivially on \(W\), the split stabilizer swaps the two square
classes, and the irreducible stabilizer is transitive.  Hence

\[
 3+5+6=14.
\]

At the level of a Gorenstein socle lift, the perfect pairing
\(V\times W\to k\) makes multiplication a nondegenerate binary cubic
tensor.  There are four \(\mathrm{GL}_2(\mathbf F_2)\)-orbits of such
tensors; two different cubic orbits can have the same irreducible quadratic
kernel after the top socle is removed.  This is genuine lift data, but it
does not enlarge the fourteen-ring quotient list needed for \(S'\).

The exact \(S'\) sweep on all fourteen rings is now complete.  A uniform
additive-table implementation passed exhaustive \(32^3\) ring-axiom checks,
locality and deformation-range checks, the filtration
\(|\mathfrak m^i|=16,4,1\), the displayed presentation relations, the
four-element socle, the natural two-generator maximal ideal, and the full
64-element syzygy on every ring.  In every case the residual syzygy quotient
is elementary of dimension two, so each coordinate failure query was
unrolled over exactly \(4^3=64\) division representatives.

Across 140 ring/fiber rows, the 25 expected tangent-characteristic rows were
H0-vacuous and 115 were nonvacuous with H0 and S1 SAT.  All 345 coordinate
failure queries were UNSAT; there was no SAT failure, timeout, or unknown.
An independent default rerun reproduced all 14 ring gates and the exact
25-vacuous/115-nonvacuous/345-UNSAT count in a clean raw log.
The independently written ramified presentation

\[
 \mathbf Z_2[\pi,u]/(\pi^2-2,\pi^3,\pi^2u,u^2-\pi^2)
 \cong C(x^2;y^2)
\]

also reproduces its corresponding table result.

See
[`scripts/sprime_length5_pointed_quadratic_sweep_20260710.py`](scripts/sprime_length5_pointed_quadratic_sweep_20260710.py)
and the independent raw rerun
[`scripts/sprime_length5_pointed_quadratic_sweep_reference_check_20260710.log`](scripts/sprime_length5_pointed_quadratic_sweep_reference_check_20260710.log).

## 5. Quotient \((1,3,1)\): four rank-one types

Here \(V\) has dimension three, \(W=\mathfrak m_Q^2\) has dimension one,
and the type-three condition forces multiplication to be a rank-one
symmetric form.  Choose an active vector \(x\) and radical vectors \(u,v\).
The four rings are:

\[
\begin{aligned}
 D_0={}&\mathbf F_2[x,u,v]/
 (x^3,xu,xv,u^2,uv,v^2);\\
 D_a={}&\mathbf Z/8[u,v]/
 (2u,2v,u^2,uv,v^2);\\
 D_r={}&\mathbf Z/4[x,v]/
 (2x,2v,x^3,xv,v^2);\\
 D_2={}&\mathbf Z/4[x,u,v]/
 (x^2-2,x^3,xu,xv,u^2,uv,v^2).
\end{aligned}
\]

They correspond respectively to: \(2\) dying in the quotient; the tangent
class of \(2\) active; the tangent class of \(2\) a radical vector; and
\(2\) spanning the degree-two layer.  There is one rational orbit in each
case: the automorphism group of the rank-one form is transitive on nonzero
radical vectors.

As in the pointed-quadratic case, a higher degree-two component attached to
a tangent representative of \(2\) is removed by shifting that representative
by \(\mathfrak m_Q^2\); no hidden carry remains because
\(\mathfrak m_Q^3=0\).  Characteristic and the filtration order of \(2\),
together with active versus radical tangent placement, separate the four
classes.

At the lift level, the top correction on the two-dimensional radical is a
nondegenerate symmetric bilinear form.  Over \(\mathbf F_2\) it has two
classes, alternating and nonalternating.  Those are distinct length-six lift
types but have the same length-five quotient, so again they do not enlarge
the \(S'\) list.

All four quotient types actually occur.  Explicit length-six Gorenstein
socle lifts are

\[
\begin{aligned}
\widetilde D_0={}&\mathbf F_2[x,u,v]/
 (x^4,xu,xv,uv,u^2-x^3,v^2-x^3),\\
\widetilde D_a={}&\mathbf Z/16[u,v]/
 (2u,2v,uv,u^2-8,v^2-8),\\
\widetilde D_r={}&\mathbf Z/8[x,v]/
 (2x,2v,x^3-4,xv,v^2-4),\\
\widetilde D_2={}&\mathbf Z/4[x,u,v]/
 (x^2-2,xu,xv,uv,u^2-x^3,v^2-x^3).
\end{aligned}
\]

Their socles are generated respectively by \(x^3,8,4,x^3\), and quotienting
by that line gives \(D_0,D_a,D_r,D_2\).

The exact \(S'\) sweep is complete on all four quotient rings.  Their full
32-element ring tables, locality, presentations, filtration
\(|\mathfrak m^i|=16,2,1\), eight-element socles, three-generator maximal
ideals, and 2048-element syzygies all passed exhaustive gates.  The quotient
of the syzygy by \(\operatorname{Soc}(Q)^3\) has dimension two, and all
\(4^3=64\) residual division choices were unrolled.  Of 40 ring/fiber rows,
10 were H0-vacuous and 30 had H0 and S1 SAT; all 90 coordinate failure
queries were UNSAT.  An independent audit and rerun reproduced the result.

See
[`scripts/sprime_rankone_len5_evidence_map_20260710_final.log`](scripts/sprime_rankone_len5_evidence_map_20260710_final.log).

## 6. Square-zero quotient \((1,4)\): both rings closed

There are only two quotient rings:

\[
 E_0=\mathbf F_2[z_1,z_2,z_3,z_4]/(z_1,z_2,z_3,z_4)^2
\]

and

\[
 E_1=\mathbf Z/4[z_1,z_2,z_3]/
 (2z_i, z_iz_j:1\le i,j\le3).
\]

Universal \(S'\) for \(E_0\) is Theorem N.  The exact computation for
\(E_1=B_{000}\) is also complete for all rational fiber forms.  Thus the
entire \((1,4,1)\) length-six stratum is eliminated.

For completeness, a Gorenstein lift is controlled by a nondegenerate
symmetric form on a four-dimensional vector space.  Over \(\mathbf F_2\)
there are two unpointed classes, alternating and nonalternating.  Pointing by
the tangent class of \(2\) refines these lift classes, but killing the top
socle always gives the single mixed square-zero quotient \(E_1\).

## 7. Final reduction and characteristic placement

The total quotient-profile count is

\[
 7+7+14+4+2=34.
\]

All seven principal ring classes and both square-zero rings satisfy \(S'\).
Therefore exactly

\[
 \boxed{7+14+4=25}
\]

additional exact length-five base rings form a sufficient \(S'\) test list
for every residue-\(\mathbf F_2\), length-six minimal counterexample.
All 25 are now closed.  In aggregate their 250 ring/fiber rows comprise 50
H0-vacuous rows and 200 nonvacuous rows with H0 and S1 SAT; all 600 exact
coordinate failure queries are UNSAT.  There are no SAT failures, timeouts,
or unknown verdicts.  Together with the seven principal classes and two
square-zero classes, universal \(S'\) therefore holds on all 34 quotient
isomorphism types in the classification.

By the socle-extension theorem, a length-six minimal counterexample cannot
exist.  Combining this with the previously proved length-at-most-five result
gives, subject to the standard connected--étale/Schoof--Torti reductions and
the exact finite-ring solver verdicts,

\[
 \boxed{\text{Every rank-four group scheme over a residue-}\mathbf F_2
 \text{ Artin local base of length at most six is killed by four.}}
\]

The characteristic positions in the three remaining strata are:

* \((1,2,1,1,1)\): active tangent \(2\) gives quotient characteristic
  \(16\); radical tangent \(2\) gives the two characteristic-four rings
  \(Q_0,Q_1\); degree-two \(2\) gives the two ramified chain carries;
  degree-three \(2\) gives the \(e=3\) split ring; top-socle or zero \(2\)
  gives the equal-characteristic ring.
* \((1,2,2,1)\): tangent \(2\) gives five pointed quadratic types, of
  quotient characteristic four when its square is the quadratic relation
  and characteristic eight otherwise; degree-two \(2\) gives six
  characteristic-four pointed types; top-socle or zero \(2\) gives the
  three equal-characteristic types.
* \((1,3,1,1)\): active tangent \(2\) gives quotient characteristic eight;
  radical tangent \(2\) and degree-two \(2\) give characteristic four;
  top-socle or zero \(2\) gives the equal-characteristic type.

There is no continuous moduli problem at the quotient level over
\(\mathbf F_2\): the twenty-five rings above are an explicit finite list.
There are genuine filtered and rational-form choices in the length-six
Gorenstein lifts (chain carries, four binary-cubic orbits, and alternating
versus nonalternating top forms), but Theorem 7.1 makes those lift parameters
irrelevant once universal \(S'\) is proved on the quotient.  Any stratified
machine verification must nevertheless include all six rational \(xy\) Hopf
fibers and all four \(t^4\) normal forms; the two nonsplit \(xy\) forms cannot
be inferred from the four geometric split pins over \(\mathbf F_2\).
