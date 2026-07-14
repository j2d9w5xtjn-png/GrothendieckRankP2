# Structural frontier at residue \(\mathbf F_2\), base length seven

Universal \(S'\) has now been established on every length-five quotient
needed to exclude residue-\(\mathbf F_2\), length-six minimal
counterexamples.  This note asks what a length-seven minimal base would look
like and which length-six quotient rings should be tested next.

The classifications below are deliberately labelled **complete** or
**partial**.  Over the fixed field \(\mathbf F_2\) every finite-ring problem
has finitely many rational points, but that tautology does not make the
isomorphism classification short.  The compatible-form and filtered-correction
orbit computation in the hardest current stratum has now been completed:
27 quotient classes occur, of which 19 admit the required Gorenstein socle
lift.  The remaining work there is the finite exact Hopf sweep.

## 1. General type lemma

Let \((R,\mathfrak m,k)\), \(k=\mathbf F_2\), be Artin local Gorenstein of
length seven.  Put

\[
 T=\operatorname{Soc}(R),\qquad Q=R/T,qquad
 e=\dim_k\mathfrak m/\mathfrak m^2.
\]

Exactly as at length six,

\[
 \boxed{\dim_k\operatorname{Soc}(Q)=e.}
\]

Indeed,

\[
 \operatorname{Soc}(Q)=(T:\mathfrak m)/T
 =\operatorname{Ann}_R(\mathfrak m^2)/T,
\]

and Gorenstein duality gives
\(\ell(\operatorname{Ann}_R(\mathfrak m^2))=
\ell(R/\mathfrak m^2)=1+e\).

This is a strong filter: except in embedding dimension one, the quotient
\(Q\) is not Gorenstein.  Thus isolated \(S'\) results on Gorenstein
length-six rings do not by themselves address a length-seven minimal base.

## 2. Complete Hilbert-function list

Let \(h_i=\dim_k\mathfrak m^i/\mathfrak m^{i+1}\).  The nonzero layers are
positive, \(h_0=h_s=1\), and their sum is seven.  Macaulay growth and the
type lemma eliminate the two tempting extra sequences:

* \((1,2,1,2,1)\) is impossible because \(h_2=1\) forces
  \(h_3\le1\);
* \((1,2,3,1)\) is impossible because its socle quotient would have
  \(\mathfrak m_Q^3=0\) and \(\dim\mathfrak m_Q^2=3\), hence type at least
  three, whereas the type lemma requires type two.

The complete list of admissible Hilbert functions is therefore

\[
\begin{aligned}
 &(1,1,1,1,1,1,1),\\
 &(1,2,1,1,1,1),\qquad (1,2,2,1,1),\\
 &(1,3,1,1,1),\qquad (1,3,2,1),\\
 &(1,4,1,1),\\
 &(1,5,1).
\end{aligned}
\]

The quotient table is:

| \(H_R\) | \(H_Q\) | type \(Q\) |
|---|---|---:|
| \((1^7)\) | \((1^6)\) | 1 |
| \((1,2,1,1,1,1)\) | \((1,2,1,1,1)\) | 2 |
| \((1,2,2,1,1)\) | \((1,2,2,1)\) | 2 |
| \((1,3,1,1,1)\) | \((1,3,1,1)\) | 3 |
| \((1,3,2,1)\) | \((1,3,2)\) | 3 |
| \((1,4,1,1)\) | \((1,4,1)\) | 4 |
| \((1,5,1)\) | \((1,5)\) | 5 |

This table, rather than killedness of arbitrary length-six bases, is the
input to Theorem 7.1: a length-seven counterexample requires an induced
bialgebra over one of these \(Q\)'s that fails \(S'\).

## 3. Principal quotient \((1^6)\): ten classes

**Status: ring classification complete; \(S'\) sweep in progress.**

Here \(Q\) is a residue-\(\mathbf F_2\) principal ring of length six.  The
coarse characteristic positions are

\[
 2=0,\qquad \operatorname{ord}_{\mathfrak m}(2)=1,2,3,4,5.
\]

Writing

\[
 2=t^e+c_{e+1}t^{e+1}+\cdots+c_5t^5,
 \qquad c_i\in\mathbf F_2,
\]

gives 32 raw coordinate presentations.  All 32 exact 64-element tables were
gated, and all 16 possible target uniformizers were tested for every ordered
pair of presentations.  The result is exactly ten isomorphism classes:

| class | \(e\) | characteristic | relation, with \(t^6=0\) |
|---|---:|---:|---|
| C01 | 1 | 64 | \(2=t\) |
| C02 | 2 | 8 | \(2=t^2\) |
| C03 | 2 | 8 | \(2=t^2+t^5\) |
| C04 | 2 | 8 | \(2=t^2+t^3\) |
| C05 | 2 | 8 | \(2=t^2+t^3+t^4\) |
| C06 | 3 | 4 | \(2=t^3\) |
| C07 | 4 | 4 | \(2=t^4\) |
| C08 | 4 | 4 | \(2=t^4+t^5\) |
| C09 | 5 | 4 | \(2=t^5\) |
| C10 | \(\infty\) | 2 | \(2=0\) |

The orbit audit checks every accepted map on all \(64^2\) addition and
multiplication pairs and proves that every target uniformizer belongs to
exactly one raw presentation.  Thus pure Eisenstein towers alone are not
enough, but the missing carry problem is now a finite ten-ring \(S'\) sweep.

See
[`PRINCIPAL_LENGTH6_CHAIN_CLASSIFICATION_2026-07-10.md`](PRINCIPAL_LENGTH6_CHAIN_CLASSIFICATION_2026-07-10.md).

## 4. Stretched quotient \((1,2,1,1,1)\)

**Status: finite short upper list; filtered isomorphisms not fully reduced.**

The type-two condition supplies a hidden socle line outside
\(\mathfrak m_Q^2\).  Choose an active generator \(x\) and a hidden socle
generator \(y\).  After filtered changes,

\[
 x^2,x^3,x^4\ne0,\quad x^5=0,qquad y\mathfrak m_Q=0.
\]

The split forms are

\[
 P\times_{\mathbf F_2}\mathbf F_2[y]/y^2,
\]

with \(P\) a principal length-five ring.  There are seven isomorphism
classes of such \(P\)'s (represented by eight coordinate presentations in
the completed length-five sweep).

If the tangent class of \(2\) is the hidden direction, write

\[
 2=y+a x^2+b x^3+c x^4.
\]

The coefficient \(c\) is removable by changing \(y\) by the chain socle,
but \((a,b)\in\mathbf F_2^2\) is genuine filtered carry data before changes
of the active uniformizer are considered.  Eliminating \(y\) gives the
uniform presentation

\[
 Q_{a,b}=\mathbf Z[x]/
 (x^5,\ 2x-a x^3-bx^4,\ 4-a x^4),
\qquad a,b\in\mathbf F_2,
\]

interpreted at its nilpotent local maximal ideal.  Some of these four
coordinate forms may be isomorphic after \(x\mapsto x+\) higher terms; that
finite orbit computation is not completed here.  Thus this stratum has at
most eleven immediate representatives and is a manageable exact target.

## 5. Quotient \((1,2,2,1)\): exact compatible-form orbits

**Status: quotient classification complete; exact \(S'\) sweep partial.**

Put

\[
 V=\mathfrak m_Q/\mathfrak m_Q^2,\quad
 W=\mathfrak m_Q^2/\mathfrak m_Q^3,\quad
 U=\mathfrak m_Q^3,
\]

with dimensions \(2,2,1\).  Multiplication consists of

\[
 B:\operatorname{Sym}^2V\twoheadrightarrow W,
 \qquad L:V\otimes W\longrightarrow U,
\]

plus a filtered \(U\)-valued correction to products in
\(\operatorname{Sym}^2V\).  Associativity says that

\[
 (v_1,v_2,v_3)\longmapsto L(v_1,B(v_2,v_3))
\]

is symmetric.  Since \(Q\) has type two, the induced map
\(W\to V^*\) has a one-dimensional kernel; that kernel is the second socle
line of \(Q\).

Thus a ring in this stratum is not determined merely by the quadratic
kernel \(\ker(\operatorname{Sym}^2V\to W)\).  One must classify compatible
pairs \((B,L)\), the filtered \(U\)-correction, and the position of the
initial form of \(2\) in \(V\), \(W\), or \(U\).  Changes of lifts mix these
data.

Over \(\mathbf F_2\) this is a finite computation on vector spaces of
dimensions at most two and has now been completed by exhaustive orbit enumeration.
One must not infer general binary-quartic moduli here.  In fact, type two
forces the catalecticant of the symmetric cubic induced by \((B,L)\) to have
rank one, so that cubic is a pure cube; associativity in a Gorenstein
length-seven lift then forces the top quartic tensor to be a pure fourth
power.

No positive-dimensional or field-independent moduli claim is needed.  The
exact computation found 54 compatible forms and two
\(\mathrm{GL}(V)\times\mathrm{GL}(W)\)-orbits.  Exhausting 131,072 normalized
filtered inputs produced 512 valid adapted presentations.  All 512 passed
their exact 64-element arithmetic gates, and exhaustive positive
isomorphism checks reduced them to 27 quotient-ring classes.  A literal
one-dimensional-socle lift enumeration then retained exactly 19 classes
admitting a length-seven Gorenstein lift.  The terminal evidence is
[`scripts/length6_h1221_type2_orbits_reference_20260710.log`](scripts/length6_h1221_type2_orbits_reference_20260710.log).

The exact Hopf sweep on those 19 classes is underway.  It has now closed 98
of the 190 ring/fiber rows, with five additional coordinate-UNSAT results in
partial rows.  Seven quotient classes are completely closed:
`q20,q21,q22,q23,q24,q25,q27`.

The characteristic-16 class `q24` has five H0-vacuous rows and 15/15
failure-coordinate UNSAT results on its other five rows.  The six-ring batch
`q20,q21,q22,q23,q25,q27` added 25 H0-vacuous and 35 nonvacuous rows, with
all 105 failure coordinates UNSAT.  There was no timeout, OOM, unknown, or
SAT \(S'\)-failure; the six-ring batch peaked at 930.75 MiB RSS.  In
particular, all liftable characteristic-16 classes `q24,q25,q27` are now
eliminated.  See
[`Q24_H1221_SPRIME_RESULT_2026-07-10.md`](Q24_H1221_SPRIME_RESULT_2026-07-10.md)
and [`H1221_BATCH1_RESULT_2026-07-10.md`](H1221_BATCH1_RESULT_2026-07-10.md).

## 6. Rank-one stretched quotient \((1,3,1,1)\)

**Status: complete and closed, seven forms.**

The type-three condition forces a rank-one multiplication on the
three-dimensional tangent space.  There is one active chain direction and a
two-dimensional hidden tangent socle.  Five split forms are

\[
 P\times_{\mathbf F_2}
 \mathbf F_2[u,v]/(u,v)^2,
\]

for the five principal length-four rings \(P\).  The two nonsplit forms are

\[
 Q_0\times_{\mathbf F_2}\mathbf F_2[v]/v^2,qquad
 Q_1\times_{\mathbf F_2}\mathbf F_2[v]/v^2,
\]

where

\[
 Q_0=\mathbf Z/4[x]/(x^4,2x),\qquad
 Q_1=\mathbf Z/4[x]/(x^4,2x-x^3).
\]

Equivalently, these are the seven length-five stretched quotient forms with
one additional annihilated tangent direction.  The automorphism group of
the hidden two-space is transitive on its nonzero vectors, so no further
rational pointing occurs.

The exact \(S'\) sweep on all seven is complete.  Every 64-element ring
passed exhaustive ring, presentation, locality, deformation-range,
filtration \(|\mathfrak m^i|=32,4,2,1\), type-three socle, generator, and
full-syzygy gates.  The quotient of the 8192-element syzygy by
\(\operatorname{Soc}(Q)^3\) has 16 residual classes, so every failure query
covers all \(16^3=4096\) division choices.  The \(B(\mathbf Z/16)\) residual
quotient has order-four elements and was handled by direct cosets, not a
false vector-space assumption.

Across 70 ring/fiber rows, 15 were H0-vacuous and 55 had H0 and S1 SAT; all
165 coordinate failure queries were UNSAT, with no timeout or unknown.  An
independent audit checked all seven presentations and gates and proved the
cached 4096-choice formula term-for-term equivalent to a literal expansion.
Thus the entire \((1,3,1,1,1)\) length-seven stratum is eliminated.

See
[`scripts/sprime_length6_rankone_stretched_seven_stratified_20260710.py`](scripts/sprime_length6_rankone_stretched_seven_stratified_20260710.py).

## 7. Quotient \((1,3,2)\): seventeen radical extensions

**Status: complete and closed.**

Here \(V\) has dimension three, \(W=\mathfrak m_Q^2\) has dimension two,
and \(\mathfrak m_Q^3=0\).  Type three forces multiplication

\[
 \operatorname{Sym}^2V\longrightarrow W
\]

to have a one-dimensional tangent radical.  Quotienting by that radical
gives one of the fourteen length-five \((1,2,2)\) pointed-quadratic rings.

If \(2\) is not the radical tangent vector, the ring is the fiber product of
one of those fourteen rings with a dual-number direction.  If the tangent
class of \(2\) is the radical vector, killing it leaves one of the three
equal-characteristic quadratic-kernel rings; this gives three additional
mixed-characteristic fiber products with \(\mathbf Z/4\).

Hence fourteen plus three, or seventeen, are the complete quotient-ring
isomorphism list in this Hilbert stratum.  A Teter/Gorenstein-liftability
test may delete some from the list relevant to minimal bases, but cannot add
any.

The exact \(S'\) sweep on the full upper list is complete.  All 17 terminal
logs are present.  Across 170 rational ring/fiber rows, 40 were H0-vacuous
and 130 had H0 and S1 SAT; all 390 exact coordinate-failure queries were
UNSAT, with no unknown, error, or SAT failure.  Therefore the entire
\((1,3,2,1)\) length-seven stratum is eliminated, conditional only on the
stated exhaustive 17-ring quotient classification and the standard
minimal-base \(S'\) reduction.  Concatenating the 17 terminal logs in sorted
order has SHA-256
`f6c3d1bcf639dc45b731044bd42131a9fc9a4598f34acf8762c402288512c710`.

## 8. Quotient \((1,4,1)\): four rank-one rings

**Status: complete and closed.**

The tangent space has dimension four and multiplication to the
one-dimensional square has rank one; its radical has dimension three.  The
four characteristic placements give:

\[
\begin{aligned}
 F_0={}&\mathbf F_2[x,u,v,w]/
 (x^3,xu,xv,xw,(u,v,w)^2),\\
 F_a={}&\mathbf Z/8[u,v,w]/
 (2u,2v,2w,(u,v,w)^2),\\
 F_r={}&\mathbf Z/4[x,u,v]/
 (2x,2u,2v,x^3,xu,xv,(u,v)^2),\\
 F_2={}&\mathbf Z/4[x,u,v,w]/
 (x^2-2,x^3,xu,xv,xw,(u,v,w)^2).
\end{aligned}
\]

They are respectively equal characteristic, tangent \(2\) active, tangent
\(2\) radical, and \(2\) in the degree-two line.  The radical automorphism
group is transitive on nonzero rational vectors.  These are the direct
embedding-dimension-four analogues of the four rank-one length-five rings
whose exact \(S'\) sweep is complete.

Their own exact sweep is now complete as well.  All four 64-element tables
passed exhaustive ring, presentation, locality, deformation-range,
filtration, type-four socle, and generator gates.  The full syzygy has
524,288 elements; quotienting by \(\operatorname{Soc}(Q)^4\) leaves eight
residual classes, so every coordinate failure query was unrolled over
\(8^3=512\) divisions.  Of 40 ring/fiber rows, 10 were H0-vacuous and 30
had H0 and S1 SAT; all 90 failure queries were UNSAT, with no timeout or
unknown.  Therefore the entire \((1,4,1,1)\) length-seven stratum is
eliminated.
An independent audit checked every presentation, the full \(64^3\) ring-law
gates, the syzygy cardinality proof, all pin tables, and the 512-case failure
logic; representative reruns reproduced the stated verdicts.

See
[`scripts/sprime_length6_rankone_four_stratified_20260710.py`](scripts/sprime_length6_rankone_four_stratified_20260710.py).

## 9. Square-zero quotient \((1,5)\): two rings

**Status: complete and closed.**

There are exactly two rings:

\[
 G_0=\mathbf F_2[z_1,\ldots,z_5]/(z_1,\ldots,z_5)^2
\]

and

\[
 G_1=\mathbf Z/4[z_1,\ldots,z_4]/
 (2z_i,z_iz_j:1\le i,j\le4).
\]

Theorem N gives universal \(S'\) on \(G_0\).  The exact all-rational-fiber
run on \(G_1\) is also complete.  Exhaustive gates give \(|G_1|=64\),
\(\mathfrak m=\operatorname{Soc}(G_1)\) of order 32, and

\[
 \operatorname{Syz}(2,z_1,\ldots,z_4)=
 \operatorname{Soc}(G_1)^5,
\]

so the residual division quotient is trivial.  Five fiber rows are
H0-vacuous; the other five have H0 and S1 SAT, and all 15 coordinate failure
queries are UNSAT.  An independent audit and full rerun reproduced these
counts.  Thus the entire \((1,5,1)\) length-seven stratum is eliminated.

See
[`scripts/sprime_squarezero_len6_evidence_map_20260710_final.log`](scripts/sprime_squarezero_len6_evidence_map_20260710_final.log).

## 10. Search order and what is genuinely new

With the radical-extension stratum now closed and the compatible-form orbit
problem classified, the best remaining length-six \(S'\) targets are:

1. the remaining rows on the 19 Gorenstein-liftable \((1,2,2,1)\) classes
   of Section 5, especially the other characteristic-16 classes;
2. the at-most-eleven stretched embedding-dimension-two rings of Section 4;
3. the ten classified principal length-six rings of Section 3.

All three tasks are now finite and explicit.  A broad ring sweep in Section
5 is no longer vulnerable to an unclassified-orbit omission: its exact
19-class liftable target list is banked.  The new `q24` result is the first
complete elimination among the most ramified characteristic-16 classes.

Every pinned Hopf computation must continue to use all six rational
\(xy\) special fibers and all four \(t^4\) normal forms.  The conclusions in
this note concern base-ring quotient profiles; they do not permit transfer
between nonsplit rational Hopf fibers.
