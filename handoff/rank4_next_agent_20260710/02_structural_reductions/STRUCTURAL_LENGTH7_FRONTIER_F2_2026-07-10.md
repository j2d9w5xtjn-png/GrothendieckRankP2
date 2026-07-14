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
lift.  Its complete 190-row exact bialgebra-level \(S'\) sweep is now
negative.  The stretched
stratum has also been reduced to exactly eleven quotient classes, leaving
only that active sweep and the ten principal classes on this frontier.

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

**Status: ring classification complete; exact \(S'\) sweep active locally,
with no full conclusion yet.**

The first honest local canary (task 174) ended `unknown` at its 3600-second
S2 timeout and is correctly classified as inconclusive.  Three crash-safe,
source-snapshotted local runs are now active: two full two-ring chunks and an
adaptive first-coordinate pass over later rows.  As of
`2026-07-10T10:10Z`, banked strict evidence closes two `e1_0000` rows as
H0-vacuous and three `e2_001` rows by all three S2 coordinates UNSAT; two
later `e2_110` rows have S2.1 UNSAT but still need i2/i3.  There is no SAT
candidate, solver unknown in these banked chunk logs, or audit error.

Midway SSH, source staging, and the pinned Z3 environment are working, but no
Slurm job ID has been created.  The user deferred submission after controller
and `sbatch --test-only` calls responded slowly.  A later array must contain
only the residual tasks after combining the local evidence.

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

**Status: ring classification complete (exactly eleven classes); exact
\(S'\) sweep in progress.**

Put \(V=\mathfrak m_Q/\mathfrak m_Q^2\).  The one-dimensional layers in
degrees two through four imply that the socle meets the square in exactly
the top layer.  Thus the type-two condition defines the intrinsic hidden
tangent line
\(K=(\operatorname{Soc}(Q)+\mathfrak m_Q^2)/\mathfrak m_Q^2\subset V\).
Choose a socle lift \(y\) of that line and an active tangent lift \(x\)
outside it.  Then

\[
 x^2,x^3,x^4\ne0,\quad x^5=0,qquad y\mathfrak m_Q=0.
\]

If the tangent class of \(2\) is active, take \(x=2\).  If it is zero, the
subring generated by \(x\) is a principal length-five ring.  These cases give
the split forms

\[
 P\times_{\mathbf F_2}\mathbf F_2[y]/y^2,
\]

with \(P\) a principal length-five ring.  There are seven isomorphism
classes of such \(P\)'s (represented by eight coordinate presentations in
the completed length-five sweep), hence seven split quotient classes.

In the remaining case the tangent class of \(2\) is the hidden direction,
and one can write

\[
 2=y+a x^2+b x^3+c x^4.
\]

The coefficient \(c\) is removable by changing \(y\) by the chain socle.
The equations \(yx=0\) and \(2(2)=4\) then force
\(2x=ax^3+bx^4\) and \(4=ax^4\).  Eliminating \(y\) gives

\[
 Q_{a,b}=\mathbf Z[x]/
 (x^5,\ 2x-a x^3-bx^4,\ 4-a x^4),
\qquad a,b\in\mathbf F_2,
\]

interpreted at its nilpotent local maximal ideal.  A complete adapted
generator-change calculation shows that changing
\(x\mapsto x+\epsilon y+\alpha x^2+\beta x^3+\gamma x^4\) changes only the
removable top coefficient and leaves \((a,b)\) fixed.  Thus the four
\(Q_{a,b}\) are pairwise nonisomorphic, and this stratum has exactly eleven
quotient-ring classes.  A universal negative \(S'\) sweep on this full list
does not require a separate Gorenstein-liftability filter.  See
[`STRETCHED_H12111_UPPER_LIST_PROOF_2026-07-10.md`](STRETCHED_H12111_UPPER_LIST_PROOF_2026-07-10.md)
for the carry, additive-group, and generator-change proof.

## 5. Quotient \((1,2,2,1)\): exact compatible-form orbits

**Status: quotient classification and exact \(S'\) sweep complete; closed.**

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

The exact bialgebra-level \(S'\) sweep on all 19 classes is complete.  All
190 ring/fiber rows
are closed: 30 are H0-vacuous, and the other 160 have H0 and S1 SAT with all
480 exact coordinate-failure queries UNSAT.  There was no S2 SAT, solver
unknown, error, or unresolved row.  All 510 terminal case logs pass the
ring/lift/type and full-syzygy gates.  The global measured peak RSS was
1645.00 MiB.

Consequently the entire \((1,2,2,1,1)\) length-seven base profile is
eliminated under the standard minimal-base \(S'\) reduction.  The strict
audit, interrupted-run provenance, resources, and full-universe hashes are
recorded in
[`H1221_COMPLETE_RESULT_2026-07-10.md`](H1221_COMPLETE_RESULT_2026-07-10.md).

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

The compatible-form orbit problem and its complete 19-ring bialgebra-level
\(S'\) sweep are now closed.  The two remaining length-six \(S'\) targets on the
residue-\(\mathbf F_2\), length-seven frontier are:

1. the exactly eleven stretched embedding-dimension-two rings of Section 4;
2. the ten classified principal length-six rings of Section 3.

Both tasks are finite and explicit.  The eleven-ring stretched sweep and
three bounded principal batches are running locally in fresh processes.  The
stretched sweep currently has one genuine S2 timeout, so it is not yet a full
negative result; that coordinate needs a diagnosed longer retry.  A residual
one-coordinate-per-process Slurm array is prepared for later use without
duplicating local successes.  If both complete negatively, all seven possible
length-seven Gorenstein Hilbert profiles will be eliminated.

Every pinned bialgebra-level \(S'\) computation must continue to use all six rational
\(xy\) special fibers and all four \(t^4\) normal forms.  The conclusions in
this note concern base-ring quotient profiles; they do not permit transfer
between nonsplit rational Hopf fibers.
