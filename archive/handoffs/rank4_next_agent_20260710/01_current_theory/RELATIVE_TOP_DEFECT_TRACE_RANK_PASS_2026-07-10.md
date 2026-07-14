# Relative top-defect rigidity and a trace/rank-one reduction

**Date:** 2026-07-10  
**Scope:** a fresh theory pass on the principal relative $S'$-defect for
rank-four finite flat group schemes.  No solver result is asserted in this
note.  Proofs, conditional reductions, and counterexample heuristics are
labelled separately.

The standing notation is that $A$ is the commutative coordinate Hopf algebra,
$I=\ker(\varepsilon)$, and

\[
  \varphi=[2]^\#=\mu\Delta.
\]

The special fiber $H$ is local and killed by two, of algebra shape
$k[t]/t^4$ or $k[x,y]/(x^2,y^2)$.  The residue field $k$ is perfect of
characteristic two when the $xy$ classification is used.

This note respects the correction in
`AUDIT_REPORT_GROTHENDIECK_FINITE_FLAT_GROUP_SCHEMES_2026-07-09.md`:
a literal globally chosen “$(\varphi/t)^2=0$ exactly” is not invariant.  All
statements below take place modulo the top socle, where division by $t$ is
choice-independent.

## 1. The invariant divided operator

Let $(R',\mathfrak m)$ be a principal Artin local ring with

\[
  \mathfrak m=(t),\qquad t^{N+1}=0,\qquad t^N\ne0,
  \qquad \operatorname{ann}(t)=(t^N),
\]

and residue field $k$ of characteristic two.  Let

\[
  R=R'/(t^N).
\]

Let $A'/R'$ be a free rank-four bialgebra with killed-by-two special fiber,
and write $I'=\ker(\varepsilon:A'\to R')$.  Lemma 1.3 of
`THEORY_order4.md` gives

\[
  \varphi(I')\subseteq tI'.
\]

Choose an $R'$-linear division $B:I'\to I'$ with

\[
  tB=\varphi|_{I'}.
\]

The choice is unique modulo $t^N\operatorname{End}_{R'}(I')$.  Hence it
defines a canonical operator

\[
  \bar B:I'/t^NI'\longrightarrow I'/t^NI'.
\]

Proposition 7.5.1 immediately gives the invariant form of the principal
defect:

\[
  S'(A'/R')
  \quad\Longleftrightarrow\quad
  \bar B^2=0.                                      \tag{1.1}
\]

Indeed, for a basis vector $e$, $B(e)$ is a division of
$\varphi(e)$, and

\[
  \varphi(B(e))=tB^2(e).
\]

This vanishes exactly when $B^2(e)\in t^NI'$.

Assume now that $S'(A/R)$ holds for the truncation.  The same calculation
one level down gives

\[
  B^2(I')\subseteq t^{N-1}I'\pmod {t^NI'}.
\]

Thus there is a well-defined $k$-linear top defect

\[
  \Omega_B:I_H\longrightarrow I_H,
  \qquad
  B^2\equiv t^{N-1}\widetilde{\Omega_B}\pmod {t^N}.
                                                        \tag{1.2}
\]

This is the Ω of `THEORY_order4.md` §15: multiplying (1.2) by $t$
gives

\[
  \varphi(B(e))=t^N\widetilde{\Omega_B(e)}.
\]

Consequently $S'(A'/R')$ is equivalent to $\Omega_B=0$.

## 2. Proof: the top $S'$-defect is independent of the top lift

The ordinary $[4]$-obstruction is already known to be independent of the
top lift (`THEORY_order4.md`, Theorem 5.1).  That theorem does not by itself
control $S'$, which is stronger than killedness.  The following is the
corresponding rigidity statement for the divided $S'$-defect.

### Proposition 2.1 (top-layer rigidity of Ω, equal characteristic)

Fix a bialgebra $A/R$ as above and suppose $S'(A/R)$ holds.  Let
$A'_1,A'_2$ be two free rank-four bialgebra lifts of $A$ to $R'$.
Normalize them on the same free module, with the same unit and counit, as in
the proof of Theorem 5.1.  Then, under the induced identification of their
special fibers,

\[
  \boxed{\Omega_{A'_1}=\Omega_{A'_2}.}
\]

The assertion is unconditional here in equal characteristic under the
standing fiber hypotheses (including the perfectness proviso for the $xy$
classification).  A precise conditional mixed-characteristic version is
recorded after the proof; the Witt-carry condition in that version is not
known uniformly.

#### Proof

After the normalization, the two multiplications and comultiplications differ
by $t^N$-valued maps.  Taking their difference in each bialgebra axiom kills
all quadratic terms, because $t^N\mathfrak m=0$.  Reduction to the special
fiber therefore gives homogeneous first-order bialgebra data

\[
  (m,\delta)
\]

on $H$.  Let

\[
  \chi=(1\otimes\mu_H)\delta+m\Delta_H:I_H\to I_H
\]

be its first-order doubling symbol.  If $B_i$ is a division of
$\varphi_i$, then

\[
  B_2-B_1\equiv t^{N-1}\widetilde\chi\pmod {t^N}.
                                                        \tag{2.2}
\]

For $N\ge2$, squaring (2.2) gives

\[
  B_2^2-B_1^2
  \equiv t^{N-1}(B_0\chi+\chi B_0)\pmod {t^N},
  \qquad B_0:=\bar B\bmod t;
                                                        \tag{2.3}
\]

the quadratic difference term is in $t^{2N-2}\operatorname{End}(I')$,
which is contained in $t^N\operatorname{End}(I')$.

In equal characteristic, $B_0=\psi$ is the first-order symbol of the common
truncation.  Lemma 2.1 of
`order4_fifth_push_relative_defect.md`, audited as `THEORY_order4.md`
§15.3, proves pairwise nilpotence for any two first-order symbols of the
same rank-four fiber:

\[
  \psi\chi=\chi\psi=0.
\]

Hence the right side of (2.3) vanishes.

Comparing (1.2) proves equality of the two Ω maps.  When $N=1$, write
the two first symbols as $\psi_1$ and
$\psi_2=\psi_1+\chi$.  Pairwise nilpotence, including the self-pairs,
gives $\psi_1^2=\psi_2^2=0$, so the same conclusion holds.  □

### Conditional mixed-characteristic version

The same calculation works in mixed characteristic if the common leading
divided symbol $B_0=\bar B\bmod t$ satisfies

\[
  B_0\chi+\chi B_0=0                             \tag{2.4}
\]

for every homogeneous first-order symbol $\chi$ arising as the difference
of two top lifts.  A sufficient condition is

\[
  B_0=\tau\,\mathrm{id}+\psi,
  \qquad \tau=\overline{2/t}\in k,
\]

with $\psi$ in the homogeneous first-order symbol space $T$: pairwise
nilpotence gives $\psi\chi=\chi\psi=0$, and the scalar contribution is
$2\tau\chi=0$ in residue characteristic two.

The decomposition into an arithmetic scalar and a deformation term is the
expected first-layer form, but over a general mixed-characteristic tower the
Witt carries do **not** presently show that the deformation term belongs to
$T$.  Thus Proposition 2.1 must not be quoted unconditionally in mixed
characteristic.  It is unconditional for an exact mixed ring only after
(2.4), or an equivalent first-layer polarization identity, has been proved
there.  The exact residue-$\mathbf F_2$ rings covered by Theorem G provide
computational instances; `THEORY_order4.md` §15.4(ii) records the general
mixed-characteristic gap.

### What Proposition 2.1 does and does not say

In its unconditional equal-characteristic scope, it says that Ω depends
only on

1. the truncated bialgebra $A/R$, and
2. the fixed principal extension $R'\twoheadrightarrow R$,

not on the point of the affine space of valid top-layer lifts.  An isomorphism
of truncations conjugates Ω by the induced automorphism of $I_H$, so its
vanishing is intrinsic.

It follows that one may impose any convenient normalization of the top
structure constants **provided a valid lift with that normalization exists**.
One may not set arbitrary top constants to zero: the order-$N$ bialgebra
equations are affine equations with lower-layer carries, and the normalized
point still has to solve them.  Proposition 2.1 says that moving among their
solutions cannot change Ω; it does not produce a solution with zero top
layer.

This explains why a counterexample seed, if present, is a lower-layer carry
invariant rather than a freely adjustable final coefficient.

## 3. Proof: trace of squaring from Frobenius coordinates

There is an automatic trace identity which does not appear in the previous
layer calculations.

### Proposition 3.1 (Hopf-square trace)

Let $R$ be a commutative local ring and let $A/R$ be a finite free
**commutative** Hopf algebra.  Then

\[
  \boxed{\operatorname{Tr}_A([2]^\#)=1.}             \tag{3.1}
\]

#### Proof

Put $K=A^\vee$.  Then $K$ is a finite free cocommutative Hopf algebra,
and the dual of the Sweedler square on $A$ is the Sweedler square $P_2$
on $K$.  Hence the two maps have the same trace.

Because $R$ is local, $\operatorname{Pic}(R)=0$.  Pareigis's
finite-projective Hopf-integral theorem (*When Hopf algebras are Frobenius
algebras*, J. Algebra 18 (1971), Proposition 3, Theorem 1, and Corollary 1)
makes $K$ a Frobenius algebra; Theorem 3 identifies the resulting integral
line.  In the Frobenius-coordinate formulation of
Kadison--Stolin, *An approach to Hopf algebras via Frobenius coordinates II*,
Proposition 3.8, there are a Frobenius left integral
$\psi:K\to R$ and a left norm $N\in K$ such that

\[
  \psi(N)=1,
\]

and the dual bases for $\psi$ are

\[
  x=N_{(2)},\qquad y=S^{-1}(N_{(1)}).              \tag{3.2}
\]

Since $K$ is cocommutative, $S^{-1}=S$.  The ordinary dual-basis trace
formula for a finite projective module therefore gives, for every
$F\in\operatorname{End}_R(K)$,

\[
  \operatorname{Tr}_R(F)
  =\sum\psi\!\left(S(N_{(1)})F(N_{(2)})\right).    \tag{3.3}
\]

Take $F=P_2$.  Coassociativity and the antipode identity give

\[
 \sum S(N_{(1)})N_{(2)}\otimes N_{(3)}=1\otimes N.
                                                        \tag{3.4}
\]

Multiplying the two tensor factors and applying $\psi$ now yields

\[
 \operatorname{Tr}_R(P_2)
 =\sum\psi\!\left(S(N_{(1)})N_{(2)}N_{(3)}\right)
 =\psi(N)=1.                                         \tag{3.5}
\]

This is an exact calculation over $R$: no extension of scalars, field
argument, eigenvalue decomposition, or indicator theory is being used.
Duality gives (3.1).  □

**Dependency note.**  The only imported ingredient is the
Pareigis/Kadison--Stolin finite-projective Frobenius system (3.2).  The rest
is the categorical dual-basis trace and the Hopf antipode identity (3.4).
Shimizu's Proposition 3.13 gives a compatible field-level indicator
interpretation, but is not needed for the ring-level proof.  The fact that
$g^2=g$ has only the unit solution is not, by itself, enough to prove a trace
formula over a nonreduced base.

### Corollary 3.2 (the divided operator is traceless modulo the top socle)

In the principal setting of §1, the special-fiber antipode lifts across the
nilpotent maximal ideal, so Proposition 3.1 applies to $A'$.  Write
$A'=R'1\oplus I'$.  The squaring map fixes $1$, preserves $I'$, and
$\varphi|_{I'}=tB$.  Therefore

\[
  1=\operatorname{Tr}_{A'}(\varphi)
   =1+t\operatorname{Tr}_{I'}(B),
\]

so

\[
  \operatorname{Tr}(B)\in\operatorname{ann}(t)=(t^N).
\]

Equivalently,

\[
  \boxed{\operatorname{Tr}(\bar B)=0
  \quad\text{on }I'/t^NI'.}                          \tag{3.6}
\]

This part is characteristic-independent.  In mixed characteristic the trace
zero is achieved by cancellation between the arithmetic term
$\tau\mathrm{id}$ and the deformation term; neither term should be set to
zero separately.

### Corollary 3.3 (solver-facing diagonal identity)

Let $A$ be free of rank four with an augmentation-adapted basis
$1,e_1,e_2,e_3$, and write

\[
  \varphi(e_j)=\sum_{i=1}^3 \varphi[i][j]e_i.
\]

Then Proposition 3.1 gives the exact, redundant equation

\[
  \boxed{\varphi[1][1]+\varphi[2][2]+\varphi[3][3]=0.} \tag{3.7}
\]

This may be inserted directly into the rank-four solver cores.  The needed
hypothesis is that the encoded commutative finite-free bialgebra is Hopf.
In the present searches that follows from the Hopf special fiber: over an
Artin local base, a lift of the special-fiber antipode is a convolution
inverse modulo the nilpotent maximal ideal, and the usual finite geometric
series corrects it to an actual convolution inverse.  Thus no extra antipode
variables are needed.

### Corollary 3.4 (a stronger modular-character identity)

Keep $K=A^\vee$, and for $a\in K$ let $R_a$ denote right multiplication
by $a$.  Then

\[
  \boxed{\tau(a):=\operatorname{Tr}_K(R_a\circ P_2)}       \tag{3.8}
\]

is an algebra homomorphism $K\to R$.  Equivalently, the element of
$A=K^\vee$ represented by $\tau$ is group-like.

Indeed, the same Frobenius-coordinate trace formula gives

\[
 \tau(a)
 =\sum\psi\!\left(S(N_{(1)})N_{(2)}N_{(3)}a\right)
 =\psi(Na).
\]

For a left norm, $Na=N\,m(a)$, where $m:K\to R$ is the modular function;
hence $\tau(a)=m(a)$ because $\psi(N)=1$.  The modular function is a
character.  Formula (3.7) is the specialization $a=1$.

This gives a larger optional family of redundant solver equations: compute
the four values (3.8) from the coproduct and the matrix of $\varphi$, then
impose that the resulting dual element has counit one and coproduct equal to
its tensor square.  No new existential variables are required.  Whether
these higher-degree equations improve the hard searches is an experimental
question.

For the exact array convention in `scripts/s2check.py` and the principal
length-six driver,

\[
 \varphi(e_j)=\sum_r \mathtt{phi[j][r]}\,e_r,
 \qquad
 \Delta(e_r)=\sum_{p,q}\mathtt{DE[r][4*p+q]}\,e_p\otimes e_q.
\]

If $(f^0,f^1,f^2,f^3)$ is the dual basis of $K$, then

\[
 P_2(f^r)=\sum_j\mathtt{phi[j][r]}\,f^j,
 \qquad
 f^j f^a=\sum_{\ell}\mathtt{DE[\ell][4*j+a]}\,f^\ell.
\]

Therefore the correctly indexed implementation of (3.8) is

\[
 \boxed{
 \mathtt{tau[a]}
 =\sum_{r,j}\mathtt{phi[j][r]}
                 \mathtt{DE[r][4*j+a]}.}             \tag{3.9}
\]

The group-like equations, in the same convention, are

\[
 \sum_a \mathtt{tau[a]DE[a][4*p+q]}
 =\mathtt{tau[p]tau[q]}\qquad(0\le p,q\le3),         \tag{3.10}
\]

together with $\mathtt{tau[0]}=1$.  The latter reduces to
$\sum_{i=0}^3\mathtt{phi[i][i]}=1$, hence to (3.7).  Formula (3.9) was
checked directly against the construction of `phi` and `DE` in
`s2check.build_blocks`; swapping the first index of `DE` would be a
transpose error.

## 4. A determinantal reduction of the principal lemma

For a $3\times3$ matrix $C=(c_{ij})$ over any commutative ring,

\[
  \big(C^2-(\operatorname{tr}C)C\big)_{ij}
  =\sum_k
  \big(c_{ik}c_{kj}-c_{ij}c_{kk}\big).               \tag{4.1}
\]

Each summand in (4.1) is a $2\times2$ minor (the terms with repeated rows
are zero).  Hence:

### Lemma 4.1 (rank one plus trace zero)

If all $2\times2$ minors of $C$ vanish, then

\[
  C^2=(\operatorname{tr}C)C.
\]

In particular, if $\operatorname{tr}C=0$, then $C^2=0$.  □

Apply this to the canonical $\bar B$ over $R'/(t^N)$.  Corollary 3.2
supplies the trace hypothesis for free.  Thus:

### Corollary 4.2 (principal rank-one target)

For rank four, over every principal Artin local base in the hard branch,

\[
  \boxed{
  \text{all }2\times2\text{ minors of }\bar B\text{ vanish}
  \quad\Longrightarrow\quad S'(A'/R').}
                                                        \tag{4.2}
\]

This replaces three raw entries of $\bar B^2$ per cotangent generator by
the geometric assertion that the divided doubling operator has
scheme-theoretic determinantal rank at most one.

The first-order theorem proves (4.2)'s hypothesis modulo $t$: every
first-order symbol has rank at most one and trace zero.  What is **not yet
proved** is persistence of all the minors through arbitrary depth.

### Lemma 4.3 (equivalence when the leading symbol is nonzero)

Let $S$ be a local ring, $C\in M_3(S)$, and suppose $C$ has a unit
entry.  If

\[
  C^2=0,\qquad \operatorname{tr}C=0,
\]

then every $2\times2$ minor of $C$ is zero.

#### Proof

View $C$ as a differential on $S^3$.  A unit entry gives $v$ such that
$u=Cv$ is unimodular.  Then $Cu=0$.  To justify the asserted splitting,
choose $\alpha\in(S^3)^\vee$ with $\alpha(u)=1$, put
$\beta=\alpha\circ C$, and replace $\alpha$ by
$\alpha-\alpha(v)\beta$.  The resulting $\alpha,\beta$ restrict to the
dual basis of $u,v$, so $Su\oplus Sv$ is a free direct summand.  On that
summand $C(v)=u,C(u)=0$.  The quotient is free of rank one;
its induced differential is multiplication by a scalar $r$.  In a basis
adapted to this splitting, $r=\operatorname{tr}C=0$.  The equation
$C^2=0$ then forces the remaining image into $Su$.  Thus
$\operatorname{im}C\subseteq Su$, and all $2\times2$ minors vanish.
□

Consequently, if the first symbol $\bar B\bmod t$ is nonzero, it has a
unit entry and, using (3.6),

\[
  S'(A'/R')
  \quad\Longleftrightarrow\quad
  \text{all }2\times2\text{ minors of }\bar B\text{ vanish}.   \tag{4.3}
\]

The zero-first-symbol branch remains separate: there is then no unit entry,
and square-zero traceless matrices over a nonreduced ring can have nonzero
minors.  For example, over $S=k[x,y]/(x^2,y^2)$ in characteristic two,

\[
  C=\operatorname{diag}(x,y,x+y)
\]

has $C^2=0$ and $\operatorname{tr}C=0$, while its upper-left
$2\times2$ minor is $xy\ne0$.

## 5. Why the existing suspension countermodels do not refute this route

The printed $s=6$ suspension countermodels in
`scripts/s6_suspension_model_d6_rerun.log` disprove separate vanishing of
the shifted tail.  They do **not** disprove (4.2): their leading operator is
the nonzero rank-one matrix $E_{12}$, their full divided operator is
square-zero in the displayed model, and its trace is zero layer by layer.
Lemma 4.3 therefore forces its full $2\times2$ minors to vanish.

This is consistent with the central lesson of `THEORY_order4.md` §15.8.5:
the individual suspended words can be nonzero even when the complete
operator retains rank one and squares to zero.  A minors proof would have to
preserve the coupled edge–tail cancellation; it cannot prove the suspended
summands separately.

Nor does the first-order image-line statement by itself prove the full
minors assertion.  Abstractly, over $k[t]/t^2$, let

\[
  N(x)=z,\quad N(y)=N(z)=0,
  \qquad M(y)=y,\quad M(x)=M(z)=0.
\]

Then $C=N+tM$ has $C^2=0$, but it has a nonzero $2\times2$ minor and
$\operatorname{tr}C=t$.  Thus the trace theorem is genuinely load-bearing;
rank-one persistence is not a formal consequence of the $D_s$ identities
alone.  This abstract operator is **not asserted to arise from a bialgebra**.

## 6. The exact linear-algebra shape of a possible counterexample

Trace zero plus all lower $S'$ identities still does not force the new top
identity.  For $N\ge2$, the minimal model is

\[
  C=E_{12}+t^{N-1}E_{23}
  \quad\text{over }k[t]/t^N.
                                                        \tag{6.1}
\]

It satisfies

\[
  \operatorname{tr}C=0,
  \qquad C^2=t^{N-1}E_{13}\ne0,
\]

while every shorter truncation is square-zero.  Exactly one top
$2\times2$ minor is nonzero.  This is a valuation-tight three-step chain:

\[
  e_3\xmapsto{,t^{N-1},}e_2\xmapsto{,1,}e_1.
\]

After allowing general valuations it becomes

\[
  e_3\xmapsto{,t^a,}e_2
  \xmapsto{,t^b,}e_1,
  \qquad a+b=N-1.
                                                        \tag{6.2}
\]

This is the precise principal-base counterexample mechanism left by the
linear algebra.  In equal characteristic, Proposition 2.1 adds an important
constraint: changing the final valid bialgebra lift cannot remove **all** top
minors, because that would make $C^2=0$ while the nonzero Ω is invariant.
The location of an individual minor may change.  The same conclusion holds
in mixed characteristic only when the polarization condition (2.4) is known.

The chain has an invariant rank-two **module** plane.  Therefore, to evade
the rank-two-filtration theorem of
`RANK4_SERIOUS_RAMIFIED_COUNTEREXAMPLE_PASS_2026-07-09.md`, a genuine Hopf
model would have to arrange that this plane is not simultaneously an
algebra ideal/coideal defining a finite flat normal rank-two subgroup.  In
other words, the remaining mechanism is not a new matrix shape; it is the
failure of the unavoidable matrix flag to be Hopf-theoretic.  This requires
simultaneous, coupled deformations of multiplication and coproduct, exactly
as the finite evidence indicates.

## 7. A filtration-free class which is nevertheless killed by four

The absence of a normal rank-two subgroup is not, by itself, a
counterexample mechanism.  There is a broad height-one calculation which
contains the explicit example of
`RANK4_NO_NORMAL_RANK2_FILTRATION_2026-07-10.md`.

### Proposition 7.1 (rank-two restricted Lie calculation)

Let $R$ be a commutative ring of characteristic two.  Let $L$ be a free
rank-two restricted Lie algebra with ordered basis $X,Y$, and assume its
restricted enveloping algebra $D=u_R(L)$ is finite free with the restricted
PBW basis

\[
  1,\quad X,\quad Y,\quad Z:=XY.
\]

(For example, this holds for a free restricted Lie algebra satisfying the
usual restricted PBW hypotheses.)  Write

\[
  [X,Y]=uX+vY,\qquad u,v\in R.
\]

Let $A=D^\vee$, with dual basis $1,x,y,z$.  Then

\[
  A\simeq R[x,y]/(x^2,y^2),\qquad z=xy,
\]

and its doubling map satisfies

\[
  \boxed{\varphi(x)=u z,\qquad
         \varphi(y)=v z,\qquad
         \varphi(z)=0.}                              \tag{7.1}
\]

In particular $\varphi^2=0$: the associated rank-four height-one group
scheme is killed by four.

#### Proof

The elements $X,Y$ are primitive.  In characteristic two,

\[
  \Delta_D(Z)=Z\otimes1+X\otimes Y+Y\otimes X+1\otimes Z.
\]

The coalgebra table gives $x^2=y^2=0$ and $xy=z$ in the dual algebra.
The Sweedler square on $D$ is

\[
  P_2(X)=P_2(Y)=0,
\]

and

\[
  P_2(Z)=XY+YX=[X,Y]=uX+vY,
\]

where subtraction equals addition in characteristic two.  Dualizing $P_2$
gives (7.1), and a second application is zero.  □

This statement is not already present in `THEORY_order4.md`; that file uses
restricted Lie algebras to classify killed-by-two **commutative** special
fibers, whereas Proposition 7.1 allows the total restricted Lie algebra to
be nonabelian.  The explicit base

\[
  R=\mathbf F_2[a,b]/(a^2,b^2),\qquad
  [X,Y]=aX+bY
\]

from `RANK4_NO_NORMAL_RANK2_FILTRATION_2026-07-10.md` has no rank-one
direct-summand Lie ideal, even fppf locally, yet (7.1) kills it by four.
Thus a surviving counterexample must evade both structures simultaneously:
it must have no flat normal rank-two filtration **and** its divided squaring
must escape the single image line $Rz$ far enough to form the tight chain
of §6.

## 8. Derivation/coderivation audit of Ω

### Proved

The audited relative-defect lemma gives

\[
  \Omega(I_H^2)=0.
\]

Thus Ω is a point derivation and factors through $I_H/I_H^2$.  Proposition
2.1 adds top-layer rigidity.

### Not proved, and not formal

There is no formal reason for Ω to be a coderivation.  The fourth-power map
is not a group homomorphism for a noncommutative group:

\[
  (gh)^4\ne g^4h^4
\]

without commutator correction terms.  Dualizing this word identity produces
precisely the coassociativity-dependent carries seen in the $xy$, $s=3$
and $s=4$ proofs.  One must not impose a primitive-image condition on Ω
without first killing those corrections.

Even a hypothetical primitive-image theorem would not finish the problem by
representation theory alone.  Nonzero maps

\[
  I_H/I_H^2\longrightarrow\operatorname{Prim}(H)
\]

exist in all split fibers except $\mu_2\times\mu_2$: for example
$t\mapsto t^2$ in the $t^4$ fiber, arbitrary cotangent-to-primitive maps
for $\alpha_2^2$, $y\mapsto x$ for $W_2[F]$, and $x\mapsto y$ for
$\mu_2\times\alpha_2$.  Thus “derivation plus coderivation” would close only
the split $\mu_2^2$ case, not the theorem.

## 9. Net progress and remaining lemma

The principal relative problem now has the following invariant form.

**Proved in this pass:**

1. Ω is independent of all valid top-layer choices (Proposition 2.1) in
   equal characteristic.  The identical mixed-characteristic conclusion is
   conditional on the first-layer polarization identity (2.4); this is a
   genuine Witt-carry gap, not a formal extension.
2. The divided doubling operator is automatically traceless modulo the top
   socle (Corollary 3.2), via the Hopf-square trace formula.
3. If its $2\times2$ minors vanish, then $S'$ follows (Corollary 4.2); when
   the first symbol is nonzero this minors condition is equivalent to $S'$.

**Still open:** prove that the bialgebra axioms kill the top determinantal
minor, or equivalently rule out the tight chain (6.2), at arbitrary depth.
The statement must use multiplication and coproduct together.  It is false
for abstract filtered endomorphisms, and the suspension data says it cannot
be obtained by splitting the edge and tail sums.

**Plausible counterexample mechanism:** a deep, possibly very ramified base
on which the divided doubling operator acquires the tight chain (6.2), while
the associated rank-two module plane fails every ideal/coideal/normality
condition.  The completed finite searches show that this mechanism does not
occur in the tested principal, stretched, and ramified families; they do not
yet give a uniform proof that it is impossible.
