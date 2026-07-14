# A serious ramified search for a rank-four counterexample

**Date:** 2026-07-09; updated 2026-07-10  
**Question:** Can a finite locally free group scheme of rank four fail to be
killed by four, perhaps over a highly ramified and complicated base?

## Executive verdict

No counterexample was found.

The search produced substantially stronger negative results than the prior
directory state.  The principal conclusions are:

1. **Bounded theorem over residue field \(\mathbf F_2\).** Subject to the
   standard connected--étale/Schoof--Torti reductions already audited in the
   project, and accepting the exact finite-ring Z3 UNSAT verdicts, every
   rank-four finite locally free group scheme over an Artin local base with
   residue field \(\mathbf F_2\) and length at most **six** is killed by four.
2. **The entire first nonprincipal quotient frontier is closed.** The 34
   possible length-five socle-quotient isomorphism types of a length-six
   Gorenstein base were classified.  Universal \(S'\) holds on all of them;
   the 25 previously open nonprincipal rings contributed 250 fiber rows and
   600 exact failure queries, all negative or vacuous.
3. **Five length-seven Hilbert strata are now excluded.** Universal
   \(S'\) holds on the square-zero, rank-one, rank-one stretched,
   17 radical-extension, and complete \((1,2,2,1)\) type-two quotient
   lists.  Thus length-seven bases with Hilbert functions \((1,5,1)\),
   \((1,4,1,1)\), \((1,3,1,1,1)\), \((1,3,2,1)\), or
   \((1,2,2,1,1)\) cannot be counterexamples.
4. **The hardest finite quotient sweep is closed.** Exact orbit
   enumeration for Hilbert function \((1,2,2,1)\) found 27 quotient-ring
   classes, exactly 19 of which have the required length-seven Gorenstein
   lift.  All 190 rational ring/fiber rows are closed: 30 are H0-vacuous,
   and all 480 failure-coordinate queries on the other 160 rows are UNSAT.
   There is no SAT, unknown, error, or unresolved row; peak RSS was
   1645.00 MiB.
5. **Deep explicit ramification did not help.** Direct \([4]\ne e\) searches
   were UNSAT on a validated two-parameter family through length nine, with
   the difficult \(\alpha_2\times\mu_2\) special fiber pinned and every higher
   multiplication and coproduct coefficient free.
6. **Natural construction mechanisms fail for structural reasons.** Every
   rank-two-by-rank-two extension is killed by four, and a general two-sided
   matched Oort--Tate ansatz is killed by four by a direct calculation.
7. **The residue-\(\mathbf F_8\) rational-fiber gap on the tested ramified
   base is closed.** An exhaustive semilinear orbit audit finds six `xy`
   fibers; the old six labels met only five orbits.  The unique missing orbit
   was nonvacuous, but its full bialgebra deformation query over
   \(W(\mathbf F_8)[p]/(p^2-2,p^3)\) made \([4]\ne e\) exactly UNSAT.
8. **A normal rank-two filtration is not automatic, but the resulting new
   obstruction still does not produce a counterexample.** Over
   \(R=\mathbf F_2[a,b]/(a^2,b^2)\) there is an explicit noncommutative
   height-one rank-four group with no normal rank-two subgroup after any
   faithfully flat base change.  Nevertheless its squaring pullback sends
   \(x\mapsto axy\), \(y\mapsto bxy\), and \(xy\mapsto0\), so it is killed
   by four.  More generally every height-one rank-four group scheme over a
   characteristic-two base is killed by four.  The example and this
   generalization now have an independent exhaustive algebra/Hopf audit.
9. **The principal hard branch has an exact trace/rank-one reduction.**  For
   every finite free commutative Hopf algebra over a local ring, the squaring
   pullback has trace exactly one.  Consequently the canonical divided
   doubling operator on the rank-three augmentation ideal is traceless modulo
   the top socle.  If its \(2\times2\) minors vanish, then \(S'\) follows;
   when the leading divided symbol is nonzero, this condition is equivalent
   to \(S'\).  An independent audit found the ring-level
   integral proof and the determinantal argument sound.  What remains is the
   genuinely Hopf-theoretic problem of excluding a valuation-tight
   three-step chain; abstract filtered linear algebra alone cannot exclude
   it.
10. **The full ordinary stretched quotient sweep is terminal, with two
    timeout exceptions.**  Across the exactly eleven
    \((1,2,1,1,1)\) quotient rings, 108 of 110 rows are closed: 83 by all
    three failure coordinates UNSAT and 25 as H0-vacuous.  The remaining
    `s_f2/t4_11/i1` and `q00/t4_11/i1` queries timed out; their other two
    coordinates are UNSAT.  There is no SAT candidate, incomplete row, audit
    error, or OOM in the ordinary sweep.  Thus no counterexample seed was
    found, but the two timeouts prevent calling this stratum closed.
11. **Three natural realizations of the remaining tight chain are now
    excluded.**  In characteristic two, $I^2$ a direct summand together
    with $I^4=0$ already implies $S'$, ruling out every Hopf structure
    on the fixed standard $t^4$ and $xy$ coordinate algebras.  A new
    noncommutative, non-height-one Hopf model over
    $\mathbf F_2[u,v]/(u^2,v^2)$ realizes the coefficient pattern
    $P_2(Y)=uvX$, $P_2(Z)=uvY$, but the factorization $uv=u\cdot v$
    supplies exact kernel witnesses and restores $S'$.  The entire
    associated killed-special-fiber triangular family satisfies $S'$, and
    a narrowly specified minimal monogenic principal ansatz is impossible.
    These results passed an independent proof audit and bounded exhaustive
    checks; fully coupled intervening-layer lifts remain open.

On the **first still possible residue-\(\mathbf F_2\) layer, length seven**, a
counterexample would require a Gorenstein base whose length-six socle quotient
fails \(S'\), no finite flat rank-two normal filtration, and simultaneous
nontrivial deformations of multiplication and coproduct.  Seven Hilbert
profiles are possible at length seven; the square-zero, rank-one, rank-one
stretched, radical-extension, and \((1,2,2,1,1)\) profiles are now closed.
Only the exactly eleven stretched \((1,2,1,1,1)\) quotients and the ten
principal length-six quotients remain on this layer.  No \(S'\)-failure or
Hopf model was found in any tested case.  The new example shows that failure
of the normal filtration is a real phenomenon, but also that it is
insufficient: in equal characteristic a counterexample must additionally
leave the height-one restricted-Lie class.

This is not a resolution of the full conjecture.  The two stated
residue-\(\mathbf F_2\) length-seven sweeps, larger residue fields, and
uniform arbitrary-length arguments remain open.

## 1. Logical framework for a minimal counterexample

Let \(A\) be the coordinate Hopf algebra of a remaining local rank-four group
scheme and put

\[
  \phi=[2]^\#=\mu\Delta,\qquad [4]^\#=\phi^2.
\]

The existing reductions allow one to work over an Artin local ring
\((R,\mathfrak m,k)\) with finite residue field of characteristic two.  In the
hard branch the special fiber is connected and killed by two; after splitting,
its coordinate algebra has one of the two shapes

\[
  k[t]/(t^4),\qquad k[x,y]/(x^2,y^2).
\]

The total coproduct is not assumed cocommutative.  Indeed, any counterexample
must lie in the noncommutative group-scheme branch.

### 1.1 Minimality forces a Gorenstein base

Choose a counterexample of minimal base length.  For every socle line
\(M\subset\operatorname{Soc}(R)\), reduction modulo \(M\) is killed by four,
so the defect

\[
  d=[4]^\#-\eta\epsilon
\]

has image in \(MA\).  If the socle contained two distinct lines \(M,N\), then
freeness would give

\[
  d(A)\subseteq MA\cap NA=(M\cap N)A=0.
\]

Thus a length-minimal counterexample has one-dimensional socle: its base is
Artin Gorenstein.  The socle lies in \(\mathfrak m^2\).

### 1.2 The quotient must fail the stronger invariant \(S'\)

For a killed-by-two special fiber, define

\[
 S'(A/R):\quad
 \phi(I)\subseteq\mathfrak m(\ker\phi\cap I),
\]

where \(I\) is the augmentation ideal.  The project's socle-extension theorem
says that if \(S'\) holds after quotienting by a one-dimensional socle ideal,
then every lift is killed by four.  Consequently, if \(R\) is a minimal
counterexample base and \(M=\operatorname{Soc}(R)\), then

\[
  S'(A/MA\,/\,R/M)\quad\text{must fail}.
\]

This makes \(S'\)-failure on the length-one-smaller quotient the correct
counterexample seed.  Directly checking \([4]=e\) on isolated bases is weaker.

The structural argument and the small-ring classification were independently
audited; see
[`STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md`](STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md).

## 2. The new residue-\(\mathbf F_2\), length-at-most-five theorem

The length-four Gorenstein classification has Hilbert functions
\((1,1,1,1)\) and \((1,2,1)\).  The earlier workspace omitted two chain rings
and three pointed nonprincipal mixed-characteristic rings.  Direct full
bialgebra searches closed all five.

At length five, a Gorenstein ring has Hilbert function

\[
 (1,1,1,1,1),\qquad (1,2,1,1),\qquad (1,3,1).
\]

In the middle case, associativity forces the multiplication form in the
length-four socle quotient to have rank one.  Sorting the position of \(2\)
then reduces every possible length-five Gorenstein base to a one-socle lift of
an already-known \(S'\) ring or one of six missing length-four quotients:

\[
\begin{aligned}
 C_{34}&=\mathbf Z/4[p]/(p^3-2,p^4),\\
 C_{2\mathrm{tw}}&=\mathbf Z/4[p]/(p^2-2p-2),\\
 B_{00}&=\mathbf Z/4[x,y]/(2x,2y,(x,y)^2),\\
 B_1&=\mathbf Z/4[x,y]/(2x,2y,x^2-2,xy,y^2),\\
 C_4&=\mathbf Z/4[y]/(2y,y^3),\\
 C_8&=\mathbf Z/8[y]/(2y,y^2).
\end{aligned}
\]

Exact \(S'\)-failure queries are UNSAT for both algebra shapes on all six
rings, with SAT nonvacuity gates.  For the four nonprincipal rings, the
division syzygy was quotiented by the socle and then exhaustively compared
with the full finite syzygy set.  This made the final formulas
quantifier-free.

The complete banked transcript is
[`scripts/sprime_ramified_length4_six_20260709.log`](scripts/sprime_ramified_length4_six_20260709.log),
and the independently audited implementation is
[`scripts/sprime_ramified_length4_six_20260709.py`](scripts/sprime_ramified_length4_six_20260709.py).

It follows by minimality and the socle-extension theorem that

\[
 \boxed{\text{Every residue-}\mathbf F_2\text{ base of length }\le5
 \text{ is killed by four in rank four.}}
\]

This conclusion is computational in the precise sense that it accepts exact
bit-vector solver UNSAT verdicts.  The ring arithmetic, deformation
ranges, nonvacuity, and syzygy parametrizations all have independent exhaustive
gates.

## 3. Moving the \(S'\) search to length five

A length-six minimal counterexample would have a length-five quotient failing
\(S'\).  The first unstratified query on

\[
 R(2,5)=\mathbf Z_2[p]/(p^2-2,p^5)
\]

timed out in the \(xy\) branch after 1800 seconds.  That timeout was not a SAT
signal.  The successful response was to classify and pin the residue Hopf
fiber while leaving every higher coefficient free.

### 3.1 Rational fibers: an audit correction

An intermediate version used four geometrically split \(xy\) models.  An
independent audit correctly pointed out that over \(\mathbf F_2\) there are
**six rational classes**, not four.  Besides

\[
 \alpha_2^2,\quad W_2[F],\quad \mu_2^2,\quad \mu_2\times\alpha_2,
\]

there are an invertible unipotent twist and an irreducible order-three twist
of \(\mu_2^2\).  Explicit coproduct tables for both were added.  Every final
claim below uses all six classes.  The four-pin intermediate claim was
withdrawn and is not evidence.

For the \(t^4\) algebra, the killed-by-two normal form is parametrized by
\((c_1,c_4)\in\mathbf F_2^2\), giving four cases.  Hence ten fiber strata
exhaust the residue-\(\mathbf F_2\) local branch.

### 3.2 All principal length-five rings satisfy \(S'\)

The following eight presentations cover every principal
residue-\(\mathbf F_2\) ring of length five (seven isomorphism types):

- \(\mathbf F_2[p]/p^5\);
- \(\mathbf Z/32\);
- four ramification-index-two carries
  \[
    p^2=2+2cp+4d,\qquad c,d\in\mathbf F_2;
  \]
- \(\mathbf Z_2[p]/(p^3-2,p^5)\);
- \(\mathbf Z_2[p]/(p^4-2,p^5)\).

Among the four \(e=2\) presentations, \((c,d)=(0,0)\) and \((0,1)\) are
isomorphic via a change of uniformizer; retaining both is a harmless
redundancy and supplies an arithmetic cross-check.

The first two were already UNSAT in the unpinned `s2check_deeper` run.  For
each of the remaining six displayed presentations, all six rational \(xy\) failure queries and
all four \(t^4\) failure queries are UNSAT, with SAT nonvacuity and exhaustive
ring-filtration gates.  The \(e=3\) ring also has an independent unpinned
UNSAT computation.

Therefore \(S'\) is universal over every principal residue-\(\mathbf F_2\)
ring of length five.  Applying the socle-extension theorem gives the new
consequence

\[
 \boxed{\text{No principal residue-}\mathbf F_2\text{ base of length six
 can be a rank-four counterexample.}}
\]

The scripts are

- [`scripts/sprime_ramified_principal_depth5_stratified_20260709.py`](scripts/sprime_ramified_principal_depth5_stratified_20260709.py),
- [`scripts/sprime_ramified_chain_twists_depth5_stratified_20260709.py`](scripts/sprime_ramified_chain_twists_depth5_stratified_20260709.py).

### 3.3 Two nonprincipal length-five rings also satisfy \(S'\)

The same search was made on

\[
 R_5=\mathbf Z/4[p,y]/(p^2-2,2y,py-2p,y^2-2p)
\]

and

\[
 R_{xy}=\mathbf Z/4[x,y]/(2x,2y,xy,y^2-2,x^3-2).
\]

Both have 32 elements, unique socle, and a 64-element one-coordinate division
syzygy.  Exhaustive computation gives

\[
 \dim_{\mathbf F_2}\bigl(\operatorname{Syz}/\operatorname{Soc}^2\bigr)=4.
\]

For \(R_5\), a residual-bit quantified formula solved directly.  For
\(R_{xy}\), its first quantified row returned `unknown` at 600 seconds.  The
finite universal quantifier was then expanded into all
\(16^3=4096\) residual division representatives.  Every resulting query
became UNSAT quickly.

Final result on each ring: for all six \(xy\) classes, all four \(t^4\) normal
forms, and each basis element \(e_i\), \(S'\)-failure is UNSAT and the
corresponding \(S'\)-holds query is SAT.  Thus every one-socle lift of either
ring is killed by four.

The implementation and final consolidated verdict log are

- [`scripts/sprime_ramified_nonprincipal_depth5_stratified_20260709.py`](scripts/sprime_ramified_nonprincipal_depth5_stratified_20260709.py),
- [`scripts/sprime_ramified_depth5_final_20260709.log`](scripts/sprime_ramified_depth5_final_20260709.log).

These two rings do not exhaust all nonprincipal length-five quotients, so this
calculation did not by itself eliminate every length-six base.  The complete
classification and sweep in Section 3.5 now does so.

There is also a structural caveat: if a nonprincipal Artin Gorenstein ring
\(R\) is quotiented by its socle, the type of \(R/\operatorname{Soc}(R)\) is
the embedding dimension of \(R\), hence at least two.  Both \(R_5\) and
\(R_{xy}\) are themselves Gorenstein of type one, so they are **not** the
socle quotients of a minimal nonprincipal length-six Gorenstein base.  Their
\(S'\) closure excludes all one-socle lifts of these exact rings and validates
the method, but it does not reduce the actual minimal-base quotient list.

### 3.4 The square-zero length-five quotient is also closed

The mixed-characteristic square-zero quotient

\[
 B_{000}=\mathbf Z/4[x,y,z]/(2x,2y,2z,(x,y,z)^2)
\]

has \(\mathfrak m=(2,x,y,z)=\operatorname{Soc}(B_{000})\).  The displayed
generators form an \(\mathbf F_2\)-basis of \(\mathfrak m\), so

\[
 \operatorname{Syz}(2,x,y,z)=\operatorname{Soc}(B_{000})^4
\]

and there is no residual division ambiguity.  All six rational \(xy\) and
four \(t^4\) strata were checked.  Some special fibers have no lift to this
mixed-characteristic ring (H0 UNSAT); every nonvacuous stratum has H0 SAT,
\(S'\)-holds SAT, and all three \(S'\)-failure rows UNSAT.  Thus \(S'\) is
universal on \(B_{000}\).

Together with the equal-characteristic square-zero theorem, this excludes the
length-six Gorenstein Hilbert-function profile \((1,4,1)\): its socle quotient
has square-zero maximal ideal and is one of these two characteristic cases.

See
[`scripts/sprime_mixed_squarezero_length5_20260709.py`](scripts/sprime_mixed_squarezero_length5_20260709.py).

### 3.5 The complete length-five quotient list satisfies \(S'\)

The socle quotients of residue-\(\mathbf F_2\), length-six Artin Gorenstein
rings have now been classified into a finite sufficient list.  If
\(Q=R/\operatorname{Soc}(R)\), then

\[
 \dim_{\mathbf F_2}\operatorname{Soc}(Q)=
 \dim_{\mathbf F_2}\mathfrak m_R/\mathfrak m_R^2.
\]

Besides the seven principal isomorphism types and the two square-zero types,
the classification contains

\[
 7\text{ stretched}+14\text{ pointed quadratic}+4\text{ rank-one}=25
\]

nonprincipal rings.  Explicit presentations, completeness proofs, occurrence
witnesses, and orbit counts are given in
[`STRUCTURAL_LENGTH6_QUOTIENTS_F2_2026-07-10.md`](STRUCTURAL_LENGTH6_QUOTIENTS_F2_2026-07-10.md).
There is no unclassified or continuous-moduli gap at this precise length over
\(\mathbf F_2\).

The exact sweep is now complete:

| quotient stratum | rings | fiber rows | H0-vacuous | nonvacuous | failure queries |
|---|---:|---:|---:|---:|---:|
| stretched \((1,2,1,1)\) | 7 | 70 | 15 | 55 | 165 UNSAT |
| pointed quadratic \((1,2,2)\) | 14 | 140 | 25 | 115 | 345 UNSAT |
| rank one \((1,3,1)\) | 4 | 40 | 10 | 30 | 90 UNSAT |
| **total** | **25** | **250** | **50** | **200** | **600 UNSAT** |

Every nonvacuous row has both H0 and an \(S'\)-holds witness SAT.  There are
no SAT failures, timeouts, or unknowns.  Every ring passed exhaustive finite
ring, locality, presentation, filtration, socle, maximal-ideal generator,
and full-syzygy gates.  The failure formulas unroll every residual division
class; in particular, the stretched \(B(\mathbf Z/16)\) row correctly uses a
cyclic order-four residual quotient rather than assuming an
\(\mathbf F_2\)-vector space.

Together with the principal and square-zero cases, universal \(S'\) holds on
all 34 length-five quotient types.  The socle-extension theorem and minimality
therefore give the strengthened bounded result

\[
 \boxed{\text{Every rank-four group scheme over a residue-}\mathbf F_2
 \text{ Artin local base of length }\le6\text{ is killed by four.}}
\]

The main new computational artifacts are

- [`SPRIME_STRETCHED_LENGTH5_STRATIFIED_2026-07-10.md`](SPRIME_STRETCHED_LENGTH5_STRATIFIED_2026-07-10.md),
- [`scripts/sprime_length5_pointed_quadratic_sweep_20260710.py`](scripts/sprime_length5_pointed_quadratic_sweep_20260710.py),
- [`scripts/sprime_length5_pointed_quadratic_sweep_reference_check_20260710.log`](scripts/sprime_length5_pointed_quadratic_sweep_reference_check_20260710.log),
- [`scripts/sprime_rankone_len5_evidence_map_20260710_final.log`](scripts/sprime_rankone_len5_evidence_map_20260710_final.log).

## 4. Direct searches over deep ramified nonprincipal bases

To look for a counterexample rather than only propagate \(S'\), an exact ring
class was built for

\[
 R_{N,L,\theta}=
 \mathbf Z_2[p,u]/(p^2-2,p^N,p^Lu,u^2-\theta).
\]

Every ring used in a verdict passed exhaustive checks of arithmetic, locality,
the maximal-ideal deformation parametrization, and Loewy powers.  The special
fiber was pinned to \(\alpha_2\times\mu_2\), the difficult
mixed-characteristic locus in the current literature.  Above the special
fiber, all multiplication and coproduct coefficients were variable, and the
query imposed all bialgebra axioms and literal \([4]^\#\ne0\).

| \(N\) | \(L\) | tested \(\theta\) | ring size | direct result |
|---:|---:|---|---:|---|
| 4 | 2 | \(0,p^2,p^3\) | 64 | UNSAT each |
| 5 | 2 | \(0,p^3,p^4\) | 128 | UNSAT each |
| 4 | 3 | \(0,p^2,p^3\) | 128 | UNSAT each |
| 5 | 3 | \(0,p^2,p^3,p^4\) | 256 | UNSAT each |
| 6 | 2 | \(p^4\) | 256 | UNSAT |
| 6 | 3 | \(p^3\) | 512 | UNSAT |

The choice \(\theta=p^{N-L}\) is the Gorenstein member of this normal-form
family.  All sanity systems were SAT.  No nonzero fourth-power model occurred.

See
[`scripts/order4sat_ramified_embdim2_len6_20260709.py`](scripts/order4sat_ramified_embdim2_len6_20260709.py)
and
[`scripts/order4sat_ramified_deep_pinned_20260709.log`](scripts/order4sat_ramified_deep_pinned_20260709.log).

These are family exclusions, not a classification of all nonprincipal rings.

## 5. The ramified residue-\(\mathbf F_8\), length-three base

The earlier unstratified query on

\[
 W(\mathbf F_8)[p]/(p^2-2,p^3)
\]

had repeatedly consumed many hours without a verdict.  Pinning the residue
fiber made the relevant queries small:

- the difficult \(\alpha_2\times\mu_2\) row is UNSAT for \([4]\ne e\);
- five additional displayed \(xy\) forms are also UNSAT individually;
- the symbolic \((c_1,c_4)\) normal-form query covering all killed-by-two
  \(t^4\) fibers is UNSAT.
- an exact orbit audit shows that the six old `xy` pins cover only five
  \(\mathbf F_8\)-orbits; the unique missing representative
  \(\left(\begin{smallmatrix}0&1\\1&w\end{smallmatrix}\right)\) has H0 SAT
  and the full bialgebra-level \([4]\ne e\) query UNSAT on the same base.

The scripts are

- [`scripts/order4sat_f8ram_alpha2mu2_pinned_20260709.py`](scripts/order4sat_f8ram_alpha2mu2_pinned_20260709.py),
- [`scripts/order4sat_f8ram_t4_normalform_20260709.py`](scripts/order4sat_f8ram_t4_normalform_20260709.py).

Consequently all six rational `xy` orbits and the symbolic full `t4` family
are negative on this exact ramified base.  The orbit count and missing table
were independently reconstructed with Burnside, stabilizer, direct-duality,
and Hopf gates; see
[`F8_XY_SEMILINEAR_ORBIT_INDEPENDENT_AUDIT_2026-07-10.md`](F8_XY_SEMILINEAR_ORBIT_INDEPENDENT_AUDIT_2026-07-10.md).
The older decisive Z3 log is terminal and hash-verified, but is not fully
hermetic: it omits transitive dependency hashes, the Z3 version, and a
separate child exit-code record.  These are provenance qualifications, not
contradictory computational results.

## 6. Explicit construction mechanisms that cannot work

The independent construction report is
[`EXPLICIT_RANK4_RAMIFIED_CONSTRUCTION_PASS_2026-07-09.md`](EXPLICIT_RANK4_RAMIFIED_CONSTRUCTION_PASS_2026-07-09.md).

### 6.1 A rank-two filtration forces fourth-power triviality

Suppose

\[
 1\to N\to G\to Q\to1
\]

is an exact sequence of finite flat group schemes with \(N,Q\) of rank two.
Both rank-two terms are killed by two.  For every section-valued point,
squaring lands in \(N\), and squaring once more is trivial.  Scheme-theoretic
factorization gives \([4]_G=e\).  Thus products, semidirect products, nonsplit
rank-two extensions, and triangular constructions preserving such a
filtration cannot be counterexamples.

### 6.2 The hoped-for universal rank-two filtration is false

The optional strategy “produce a normal rank-two subgroup fppf locally”
cannot be made universal.  Let

\[
 R=\mathbf F_2[a,b]/(a^2,b^2).
\]

There is a rank-four height-one group whose distribution algebra has

\[
 [X,Y]=aX+bY,\qquad X^{[2]}=bX,\qquad Y^{[2]}=aY.
\]

A normal rank-two subgroup would give a direct-summand Lie-ideal line
containing \(aX+bY\).  Such a line forces either \(b\in(a)\) or
\(a\in(b)\), but these ideals are incomparable; faithful flatness descends
the two forbidden memberships.  Thus no such subgroup appears even fppf
locally.

This is not a counterexample.  If \(1,x,y,z=xy\) is the dual PBW basis, then

\[
 [2]^\#(x)=az,\qquad [2]^\#(y)=bz,\qquad [2]^\#(z)=0,
\]

and hence \([4]^\#=\eta\epsilon\).  The same PBW calculation with
\([X,Y]=uX+vY\) proves that every height-one rank-four group over a
characteristic-two base is killed by four, without assuming commutativity or
a normal subgroup.  See
[`RANK4_NO_NORMAL_RANK2_FILTRATION_2026-07-10.md`](RANK4_NO_NORMAL_RANK2_FILTRATION_2026-07-10.md)
and its independent audit
[`RANK4_NO_NORMAL_RANK2_FILTRATION_AUDIT_2026-07-10.md`](RANK4_NO_NORMAL_RANK2_FILTRATION_AUDIT_2026-07-10.md).

### 6.3 A two-sided matched Oort--Tate ansatz is killed universally

On

\[
 A=R[x,y]/(x^2-ax,y^2-cy),\qquad ab=cd=2,
\]

the full six-cross-term bilinear coproduct ansatz gives relation equations

\[
 ap=ar=cq=cs=0
\]

and coassociativity gives \(uv=qr\).  A direct computation shows that the
only possible fourth-power coefficient is \(acuv\), but

\[
 acuv=acqr=0.
\]

Hence the entire matched family is killed by four over an arbitrary local
base satisfying the stated hypotheses.

### 6.4 Fixed Oort--Tate algebra through depth twenty

On the fixed tensor Oort--Tate algebra over
\(\mathbf Z_2[p]/(p^2-2,p^N)\), all eighteen counital coproduct corrections
were allowed.  For every \(4\le N\le20\):

| query | result |
|---|---|
| bialgebra gate | SAT |
| \([2]\ne e\) | SAT |
| noncocommutative coproduct | UNSAT |
| \([4]\ne e\) | UNSAT |

Analogous fixed-algebra tests at ramification indices three and four through
depth twelve were also negative.  Therefore a counterexample in these towers
must deform multiplication as well as coproduct.

Full multiplication-and-coproduct searches through depth seven were also
negative for \([4]\ne e\) on the four geometric split \(xy\) fibers.  Those
rows are correctly described as split-fiber exclusions; they are not the
source of the six-rational-class theorem above.

### 6.5 Trace and determinantal reduction of the principal obstruction

Let \(R'\) be a principal Artin local ring with maximal ideal \((t)\), where
\(t^{N+1}=0\) and \(\operatorname{ann}(t)=(t^N)\).  Let \(A'/R'\) be a
free rank-four commutative Hopf algebra in the hard branch, let \(I'\) be
its rank-three augmentation ideal, put \(\varphi=[2]^\#\), and write

\[
 \varphi|_{I'}=tB.
\]

Although the division \(B\) need not be unique, it induces a canonical
operator

\[
 \bar B:I'/t^NI'\longrightarrow I'/t^NI'.
\]

A new exact Hopf identity gives

\[
 \operatorname{Tr}_{A'}(\varphi)=1.
\]

The proof is over the base ring itself: dualize to the cocommutative Hopf
algebra, use its finite-projective Frobenius integral coordinates, and apply
the antipode identity to the second Sweedler power.  It does not extrapolate
a field-level indicator formula.  Since the unit summand contributes one,
the identity implies \(t\operatorname{Tr}(B)=0\), hence

\[
 \operatorname{Tr}(B)\in\operatorname{ann}(t)=(t^N),
 \qquad \operatorname{Tr}(\bar B)=0.
\]

For any \(3\times3\) matrix \(C\), every entry of
\(C^2-(\operatorname{tr}C)C\) is a sum of \(2\times2\) minors.  Therefore,
if all \(2\times2\) minors of \(\bar B\) vanish, then
\(\bar B^2=0\), hence \(S'\).  If the leading symbol
\(\bar B\bmod t\) is nonzero, the converse follows as well: a unit entry,
square zero, and trace zero force the image to lie in a free line.  The
zero-leading-symbol branch has to be treated separately over nonreduced
rings.

Suppose in addition that the truncation over \(R'/(t^N)\) satisfies \(S'\).
Then \(\bar B^2\) is divisible by \(t^{N-1}\), and in equal characteristic
its well-defined top coefficient \(\Omega\), characterized by

\[
 \bar B^2=t^{N-1}\widetilde\Omega,
 \qquad \Omega=\widetilde\Omega\bmod t,
\]

is independent of every valid final bialgebra lift of that fixed truncation,
under the standing rank-four fiber hypotheses and a fixed identification.
The corresponding mixed-characteristic assertion remains conditional on a
first-layer polarization identity; the trace theorem itself is
characteristic-independent.

Abstract filtered linear algebra still permits, over \(k[t]/(t^N)\) for
\(N\ge2\), the minimal survivor

\[
 C=E_{12}+t^{N-1}E_{23},\qquad C^2=t^{N-1}E_{13}\ne0.
\]

Thus the remaining issue is sharply localized: can the Hopf axioms realize
this tight three-step chain while preventing its invariant module plane from
being an ideal/coideal flag?  The present argument is a genuine reduction,
not a proof that the chain is impossible, and the displayed matrix is not
itself asserted to arise from a bialgebra.  The full proof, scope
qualifications, optional solver identities, and independent audit are in
[`RELATIVE_TOP_DEFECT_TRACE_RANK_PASS_2026-07-10.md`](RELATIVE_TOP_DEFECT_TRACE_RANK_PASS_2026-07-10.md)
and
[`RELATIVE_TOP_DEFECT_TRACE_RANK_AUDIT_2026-07-10.md`](RELATIVE_TOP_DEFECT_TRACE_RANK_AUDIT_2026-07-10.md).

### 6.6 Hopf realizations of the tight chain

The determinantal reduction isolates a three-step divided-doubling chain,
but realizing its matrix is much harder than writing it down.  Three new
arguments sharpen this point.

First, over a characteristic-two local base, suppose the coordinate Hopf
algebra has augmentation ideal $I$, with $I^2\subset I$ an $R$-direct
summand and $I^4=0$.  Counitality gives
$\varphi(I)\subseteq I^2$, killedness of the special fiber gives
$\varphi(I)\subseteq\mathfrak mI$, and the direct-summand condition gives

\[
 \varphi(I)\subseteq \mathfrak mI^2.
\]

Since $\varphi$ is an algebra endomorphism,
$\varphi(I^2)\subseteq I^4=0$.  Thus $I^2\subseteq\ker\varphi$ and
$S'$ follows.  This excludes every characteristic-two Hopf structure on
the fixed standard algebras $R[T]/T^4$ and
$R[x,y]/(x^2,y^2)$; a survivor must deform the multiplication enough to
make $I^2$ nonsaturated or $I^4$ nonzero.

Second, such nonsaturation really occurs.  Over

\[
 R=\mathbf F_2[u,v]/(u^2,v^2),\qquad c=uv,\quad a=u+uv,
\]

there is a cocommutative distribution Hopf algebra with

\[
 X^2=aX,\quad Y^2=0,\quad YX=XY+cY,
 \qquad
 \Delta Y=Y\otimes1+1\otimes Y+vX\otimes X.
\]

It is free on $1,X,Y,Z=XY$, is noncommutative, and has

\[
 P_2(X)=0,\qquad P_2(Y)=uvX,\qquad P_2(Z)=uvY.
\]

Coefficientwise division suggests $Z\mapsto Y\mapsto X$, although the
actual composite is zero.  On the coordinate algebra,

\[
 \varphi(x)=uv\,y,\qquad \varphi(y)=uv\,z,\qquad \varphi(z)=0,
\]

and $I^2=Rz+(v)y$ is not a direct summand.  Nevertheless

\[
 uv\,y=v(uy),\quad \varphi(uy)=0;
 \qquad
 uv\,z=u(vz),\quad \varphi(vz)=0,
\]

so the full nonprincipal $S'$ condition holds.  This is a concrete warning
that division by a socle generator is not division by the whole maximal
ideal.

Third, the example belongs to a triangular family whose Diamond and
Hopf-stability equations force the same kernel factorizations.  Every member
of that family with killed-by-two special fiber satisfies $S'$.  A separate
equal-characteristic principal calculation also excludes the deliberately
minimal monogenic ansatz

\[
 T^4=\pi^{N-2}(aT+bT^2+dT^3),\qquad
 \varphi(T)=\pi(\beta T^2+\gamma T^3),
\]

assuming $N\ge5$ and $S'$ on the lower truncation.  Primitive-lifting,
trace zero, and product-killing force the critical residue carry to vanish.
This last statement is intentionally narrow: lower matrix layers, a
$T$-component, nonmonogenic multiplication, and general coproducts remain
outside it.

An independent checker exhausted 1,608 valid triangular parameter tuples
over $\mathbf F_2[u,v]/(u^2,v^2)$, including 1,536 killed-fiber cases, and
all 32 first-depth monogenic residue tuples.  The proofs, exact model, scope,
and independent audit are in
[`TIGHT_CHAIN_HOPF_ATTACK_2026-07-10.md`](TIGHT_CHAIN_HOPF_ATTACK_2026-07-10.md)
and
[`TIGHT_CHAIN_HOPF_ATTACK_AUDIT_2026-07-10.md`](TIGHT_CHAIN_HOPF_ATTACK_AUDIT_2026-07-10.md).

## 7. What a surviving counterexample must evade

The accumulated constraints now point to a much more intricate object than a
deep one-parameter deformation.

A residue-\(\mathbf F_2\) counterexample must now have base length at least
seven.  On the first remaining layer it must:

1. have an Artin Gorenstein base of length seven;
2. reduce modulo its socle to a length-six bialgebra failing \(S'\);
3. avoid the closed \((1,5)\), \((1,4,1)\), \((1,3,1,1)\),
   \((1,3,2)\), and \((1,2,2,1)\) quotient profiles;
4. have connected killed-by-two special fiber;
5. be noncommutative in its total group law;
6. have no finite flat rank-two normal subgroup with rank-two quotient;
7. if the total base has characteristic two, not be height one;
8. deform multiplication and coproduct simultaneously;
9. realize a valuation-tight three-step divided-doubling chain while making
   its unavoidable module flag fail every relevant ideal/coideal condition;
10. use interactions not present in the tested \(R_{N,L,\theta}\) family.

The seven possible length-seven Gorenstein Hilbert functions and their
length-six quotient types are classified in
[`STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md`](STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md).
Several strata have complete short lists: seven rank-one stretched rings,
seventeen radical extensions of the pointed-quadratic list, four rank-one
rings, and two square-zero rings.  The mixed square-zero target is already
closed: five of its ten fiber rows are H0-vacuous, the other five have H0 and
S1 SAT, and all 15 failure queries are UNSAT.  The four rank-one quotients
are also closed: 10 of 40 rows are vacuous, 30 have H0 and S1 SAT, and all 90
failure queries are UNSAT.  This eliminates the \((1,5,1)\) and
\((1,4,1,1)\) base profiles.  The seven rank-one stretched quotients are
closed as well: 15 of 70 rows are vacuous, 55 have H0 and S1 SAT, and all 165
failure queries are UNSAT after an exact 4096-choice residual unrolling.  This
also eliminates the \((1,3,1,1,1)\) base profile.

The seventeen radical extensions are now closed too.  Across their 170
fiber rows, 40 are H0-vacuous, 130 have H0 and S1 SAT, and all 390 exact
failure coordinates are UNSAT.  This eliminates the \((1,3,2,1)\) base
profile.

The compatible-form orbit problem for quotient Hilbert function
\((1,2,2,1)\) is no longer open: 131,072 normalized filtered inputs give 512
valid presentations, 27 quotient isomorphism classes, and exactly 19 classes
with a Gorenstein one-socle lift.  Its exact bialgebra-level \(S'\) sweep is
complete: all 190
rows are closed, 30 as H0-vacuous and 160 by all three failure coordinates
UNSAT.  The 510 terminal case logs contain no SAT, unknown, error, or
unresolved row; peak RSS was 1645.00 MiB.  This eliminates the entire
\((1,2,2,1,1)\) base profile.

The remaining residue-\(\mathbf F_2\), length-seven tasks are a ten-class
principal length-six \(S'\) sweep and the exactly eleven stretched
embedding-dimension-two quotients.  The principal classification is
complete: 32 carry presentations collapse to ten classes after an
exhaustive uniformizer-orbit audit.  The stretched classification is also
complete, including all filtered carry and generator-change parameters.
A SAT \(S'\)-failure would be the first credible seed; only then should its
one-socle lifts be searched for a literal \([4]\ne e\) Hopf model.

For larger residue fields, rational forms must be handled explicitly; a
geometric split list does not automatically give an exact finite-ring
UNSAT statement over the original base.

## 8. Evidence discipline and unresolved computations

- No SAT Hopf model with \([4]\ne e\) appeared.
- A SAT failure of \(S'\), had one appeared, would not itself be a
  counterexample; it would only be a lift target.
- The generic \(R(2,6)\) \(xy\) queries timed out at 1800 seconds.  They are
  superseded for that ring by universal \(S'\) on its length-five quotient.
- The first quantified \(R_{xy}\) \(S'\) row timed out at 600 seconds.  Its
  exact 4096-case unrolling is UNSAT, so the timeout has no residual status.
- The four-geometric-pin omission was caught, disclosed, and repaired with
  the two missing rational pin tables before final claims were banked.
- The first pointed-quadratic driver treated an H0-vacuous tangent row as a
  failed sanity gate and stopped.  H0 classification was separated from S1,
  the full run was restarted, and all 140 rows then reached terminal
  classifications.  This was a control-flow issue, not a SAT result.
- A separate complete pointed-quadratic rerun banked a raw log with all 14
  validation gates, 25 H0-vacuous rows, 115 H0/S1-SAT rows, and 345 S2-UNSAT
  rows, with no error or unknown.  Its SHA-256 is
  `8d3d317b54806d3b40a5cbb22233816788a01f8ad818cc68df1061fb7c77d80d`.
- The length-seven mixed square-zero checker and log were independently
  audited and rerun with identical 5-vacuous/5-nonvacuous/15-UNSAT counts.
- The four length-six rank-one quotient tables, full \(64^3\) ring-law gates,
  syzygy cardinality proof, pinning, and 512-case failure logic were
  independently audited; representative reruns reproduced the terminal
  10-vacuous/30-nonvacuous/90-UNSAT counts.
- The seven length-six rank-one stretched tables and syzygy cosets were
  independently audited.  A separately constructed literal 4096-choice
  formula was term-for-term identical to the cached failure formula; all 70
  terminal rows are free of SAT failures, errors, and unknowns.
- All 17 radical-extension logs are terminal.  They contain 40 H0-vacuous
  and 130 nonvacuous rows, with all 390 failure coordinates UNSAT and no
  error or unknown.  Their sorted concatenation has SHA-256
  `f6c3d1bcf639dc45b731044bd42131a9fc9a4598f34acf8762c402288512c710`.
- The exact \((1,2,2,1)\) orbit enumeration gives 27 quotient classes and
  19 Gorenstein-liftable classes.  Every one of its 512 valid adapted
  presentations passed the exact 64-element arithmetic gates.
- The `q24` queue has 20 terminal process logs: five H0-vacuous rows and 15
  coordinate-UNSAT logs closing the other five rows.  No timeout, OOM,
  unknown, or SAT failure occurred; peak measured RSS was 495.31 MiB.  The
  evidence and aggregate hash are recorded in
  [`Q24_H1221_SPRIME_RESULT_2026-07-10.md`](Q24_H1221_SPRIME_RESULT_2026-07-10.md).
- The six-ring batch `q20,q21,q22,q23,q25,q27` has 6/6 terminal queues and
  130/130 terminal case logs.  It closes 25 vacuous and 35 nonvacuous rows;
  all 105 failure coordinates are UNSAT, with no error or unknown.  Peak RSS
  was 930.75 MiB.  Its complete evidence audit and hashes are in
  [`H1221_BATCH1_RESULT_2026-07-10.md`](H1221_BATCH1_RESULT_2026-07-10.md).
- The completed 19-ring \((1,2,2,1)\) universe has 510/510 terminal case
  logs and 190/190 closed rows: 30 H0-vacuous and 160 with all 480 failure
  coordinates UNSAT.  The banked strict auditor and a separate ad hoc
  independent parser run found no SAT, unknown, error, or unresolved row.
  The case-only SHA-256 is
  `84e33365fd4cb1e9629fb20618ade3911880ecfdd3cf9d59a12c20415d29bf12`;
  see
  [`H1221_COMPLETE_RESULT_2026-07-10.md`](H1221_COMPLETE_RESULT_2026-07-10.md).
- A complete filtered carry and generator-change argument shows that the
  stretched \((1,2,1,1,1)\) quotient list has exactly eleven isomorphism
  classes, not merely eleven provisional coordinates; see
  [`STRETCHED_H12111_UPPER_LIST_PROOF_2026-07-10.md`](STRETCHED_H12111_UPPER_LIST_PROOF_2026-07-10.md).
- An exact \(\mathbf F_4\) semilinear-orbit audit found six rational `xy`
  Hopf fibers.  The six old \(\mathbf F_2\)-defined pins cover only five of
  them over \(\mathbf F_4\); the missing valid orbit has representative
  \(\left(\begin{smallmatrix}0&1\\w&1\end{smallmatrix}\right)\).  This is a
  required new test fiber, not an \(S'\)-failure or counterexample.  See
  [`F4_XY_SEMILINEAR_ORBITS_2026-07-10.md`](F4_XY_SEMILINEAR_ORBITS_2026-07-10.md).
- A 66-task fresh-process array now covers those six F4 `xy` orbits and the
  complete 16-coordinate F4 `t4` upper list over
  \(W(\mathbf F_4)[\pi]/(\pi^2-2,\pi^3)\).  Arithmetic, pin, and
  one-coordinate integration canaries pass.  The H0-vacuity control-flow
  defect found by the post-build audit has now been repaired and independently
  retested; the versioned v2 source bundle is ready, but the substantive array
  remains unsubmitted; see
  [`F4_RAMIFIED_SPRIME_STRATIFIED_JOB_2026-07-10.md`](F4_RAMIFIED_SPRIME_STRATIFIED_JOB_2026-07-10.md).
- One honestly labelled local coordinate from that repaired $\mathbf F_4$
  design is now terminal: task 15, the formerly missing orbit
  `xy_a0121 / i1`.  H0 and S1 were SAT, while the exact 64-shift
  `S2.1` query was UNSAT in 3.13 seconds; total elapsed time was 51.16
  seconds and peak RSS 995.19 MiB.  The launch-time auditor initially
  rejected only a macOS `/tmp` versus `/private/tmp` path alias.  A
  reversioned auditor accepts both canonical spellings, rejects unrelated
  paths and all non-path mutations, and admits the original preserved bytes
  without a solver rerun.  Coordinates i2 and i3 are still required before
  this row is closed; see
  [`results/f4_local_task15_xy_a0121_i1_20260710/terminal/task15_postrun_v2_20260710/README.md`](results/f4_local_task15_xy_a0121_i1_20260710/terminal/task15_postrun_v2_20260710/README.md).
- The principal length-six classification exhausts 32 carry presentations,
  every \(64^3\) ring-law gate, and all 16 target uniformizers for every
  ordered presentation pair.  An independent rerun reproduced the ten
  isomorphism classes.  No principal \(S'\) coverage is inferred from the
  classification alone.
- A memory-bounded local principal sweep currently has 54 strictly audited
  terminal coordinate logs: nine are H0-vacuous, thirty-six are exact UNSAT,
  and nine are timeout-unknown, with no SAT or audit error.  One additional case,
  `e1_0000 / xy / mu2mu2_unipotent / i2`, reached Z3's explicit 6144-MiB
  ceiling before producing an H0 verdict and aborted.  It is classified as
  out of memory/software failure and is mathematically inconclusive.  Its
  separately labelled retry used the independently proved redundant trace
  equation at the same memory ceiling, but it too hit that ceiling before an
  H0 verdict and is inconclusive.  The identical local configuration will
  not be tried a third time; this case now requires a materially different
  encoding or a measured higher-memory Slurm allocation.
  A second coordinate of that same row subsequently reached the identical
  coordinate-independent H0 query and OOM-aborted before a pause request
  could take effect.  The entire 0–59 launcher has now exited and cannot
  restart; both OOM artifacts remain excluded from the terminal counts.
- The ordinary stretched \((1,2,1,1,1)\) sweep is complete on all eleven
  ring queues.  Its strict aggregate has 108/110 rows closed (83 by
  three-coordinate UNSAT and 25 H0-vacuous), two timeout-inconclusive rows,
  no incomplete row, no SAT candidate, and no audit error.  The 280 selected
  terminal task logs comprise 253 S2-UNSAT, 25 H0-vacuous, and two unknown;
  peak RSS was 1593.75 MiB.  Two isolated 7200-second retries target exactly
  the two timed-out coordinates without raising their 3072-MiB ceilings.
  Both longer retries also returned timeout-unknown, so neither row is
  closed; the retry failures are computationally inconclusive.
- Bialgebra-level UNSAT is sufficient: in the killed-by-two local branch an
  antipode lifts automatically, and every Hopf algebra is in particular a
  bialgebra.
- The original `certs.m2` relaunch exited without a terminal artifact, but
  its lower-memory replacements completed both branches.  Fresh-process
  direct multiplication independently verified all 21 `xy` and all 24 `t4`
  displayed certificates.  The measured generating runs peaked at about
  8.48 GiB and 7.17 GiB respectively; the obsolete 43-GiB-style rerun is not
  needed for the mathematical conclusion.

## 9. Main artifacts

Structural and synthesis reports:

- [`AUDIT_REPORT_GROTHENDIECK_FINITE_FLAT_GROUP_SCHEMES_2026-07-09.md`](AUDIT_REPORT_GROTHENDIECK_FINITE_FLAT_GROUP_SCHEMES_2026-07-09.md)
- [`STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md`](STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md)
- [`STRUCTURAL_LENGTH6_QUOTIENTS_F2_2026-07-10.md`](STRUCTURAL_LENGTH6_QUOTIENTS_F2_2026-07-10.md)
- [`STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md`](STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md)
- [`Q24_H1221_SPRIME_RESULT_2026-07-10.md`](Q24_H1221_SPRIME_RESULT_2026-07-10.md)
- [`H1221_BATCH1_RESULT_2026-07-10.md`](H1221_BATCH1_RESULT_2026-07-10.md)
- [`H1221_BATCH2_RESULT_2026-07-10.md`](H1221_BATCH2_RESULT_2026-07-10.md)
- [`H1221_COMPLETE_RESULT_2026-07-10.md`](H1221_COMPLETE_RESULT_2026-07-10.md)
- [`STRETCHED_H12111_UPPER_LIST_PROOF_2026-07-10.md`](STRETCHED_H12111_UPPER_LIST_PROOF_2026-07-10.md)
- [`STRETCHED_H12111_COMPLETE_RESULT_2026-07-10.md`](STRETCHED_H12111_COMPLETE_RESULT_2026-07-10.md)
- [`STRETCHED_H12111_RETRY_RESULT_2026-07-10.md`](STRETCHED_H12111_RETRY_RESULT_2026-07-10.md)
- [`F4_XY_SEMILINEAR_ORBITS_2026-07-10.md`](F4_XY_SEMILINEAR_ORBITS_2026-07-10.md)
- [`F4_RAMIFIED_SPRIME_STRATIFIED_JOB_2026-07-10.md`](F4_RAMIFIED_SPRIME_STRATIFIED_JOB_2026-07-10.md)
- [`results/f4_local_task15_xy_a0121_i1_20260710/terminal/task15_postrun_v2_20260710/README.md`](results/f4_local_task15_xy_a0121_i1_20260710/terminal/task15_postrun_v2_20260710/README.md)
- [`PRINCIPAL_LENGTH6_CHAIN_CLASSIFICATION_2026-07-10.md`](PRINCIPAL_LENGTH6_CHAIN_CLASSIFICATION_2026-07-10.md)
- [`RELATIVE_TOP_DEFECT_TRACE_RANK_PASS_2026-07-10.md`](RELATIVE_TOP_DEFECT_TRACE_RANK_PASS_2026-07-10.md)
- [`RELATIVE_TOP_DEFECT_TRACE_RANK_AUDIT_2026-07-10.md`](RELATIVE_TOP_DEFECT_TRACE_RANK_AUDIT_2026-07-10.md)
- [`TIGHT_CHAIN_HOPF_ATTACK_2026-07-10.md`](TIGHT_CHAIN_HOPF_ATTACK_2026-07-10.md)
- [`TIGHT_CHAIN_HOPF_ATTACK_AUDIT_2026-07-10.md`](TIGHT_CHAIN_HOPF_ATTACK_AUDIT_2026-07-10.md)
- [`SPRIME_STRETCHED_LENGTH5_STRATIFIED_2026-07-10.md`](SPRIME_STRETCHED_LENGTH5_STRATIFIED_2026-07-10.md)
- [`RAMIFIED_RANK4_COUNTEREXAMPLE_SEARCH_2026-07-09.md`](RAMIFIED_RANK4_COUNTEREXAMPLE_SEARCH_2026-07-09.md)
- [`EXPLICIT_RANK4_RAMIFIED_CONSTRUCTION_PASS_2026-07-09.md`](EXPLICIT_RANK4_RAMIFIED_CONSTRUCTION_PASS_2026-07-09.md)

Final new logs:

- [`scripts/sprime_ramified_length4_six_20260709.log`](scripts/sprime_ramified_length4_six_20260709.log)
- [`scripts/sprime_ramified_depth5_final_20260709.log`](scripts/sprime_ramified_depth5_final_20260709.log)
- [`scripts/sprime_rankone_len5_evidence_map_20260710_final.log`](scripts/sprime_rankone_len5_evidence_map_20260710_final.log)
- [`scripts/sprime_length5_pointed_quadratic_sweep_reference_check_20260710.log`](scripts/sprime_length5_pointed_quadratic_sweep_reference_check_20260710.log)
- [`scripts/sprime_squarezero_len6_evidence_map_20260710_final.log`](scripts/sprime_squarezero_len6_evidence_map_20260710_final.log)
- [`scripts/sprime_length6_rankone_four_stratified_20260710.py`](scripts/sprime_length6_rankone_four_stratified_20260710.py)
- [`scripts/sprime_length6_rankone_stretched_seven_stratified_20260710.py`](scripts/sprime_length6_rankone_stretched_seven_stratified_20260710.py)
- [`scripts/order4sat_ramified_deep_pinned_20260709.log`](scripts/order4sat_ramified_deep_pinned_20260709.log)
- [`scripts/order4sat_ramified_gorenstein_len4_20260709.log`](scripts/order4sat_ramified_gorenstein_len4_20260709.log)

## Bottom line

The sustained disproof attempt did not find a rank-four counterexample.  It
did show that “take a very ramified DVR quotient” is no longer a credible
strategy over residue \(\mathbf F_2\).  Subject to the standard reductions
and acceptance of the exact finite-ring UNSAT verdicts stated in the
executive summary, **every residue-\(\mathbf F_2\) Artin-local base of length
at most six is excluded**, not merely the principal ones, and fixed
Oort--Tate constructions remain killed through much greater depth.  A first
remaining residue-\(\mathbf F_2\) counterexample must begin at length seven,
be Gorenstein, lack a rank-two filtration, and have a length-six
\(S'\)-violating socle quotient outside the five already-closed
strata--hence, on that first layer, in either the principal or stretched
quotient profile.  At larger minimal length the same statement holds with a
correspondingly longer quotient.  Finding a first genuine \(S'\)-failure is
now the sharpest computational target.
