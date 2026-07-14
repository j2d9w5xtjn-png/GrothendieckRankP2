# Independent audit of the no-normal-rank-two example

**Date:** 2026-07-10  
**Object audited:** `RANK4_NO_NORMAL_RANK2_FILTRATION_2026-07-10.md`  
**Verdict:** the construction and the fppf-local obstruction are valid after
one minor Diamond-lemma presentation repair.  No mathematical defect was
found in the claimed example.

## 1. Corrections made to the source note

The original Diamond-lemma paragraph mentioned only the mixed overlaps
`YXX` and `YYX`.  There are four critical words:

\[
 X^3,\qquad Y^3,\qquad YX^2,\qquad Y^2X.
\]

All four resolve.  The first two use \(b^2=a^2=0\), respectively, and the
source already contained the calculation for the third and indicated the
fourth.  The list in the source note has been repaired.

The phrase “free rank-two restricted Lie algebra” was also changed to
“restricted Lie algebra whose underlying module is free of rank two.”  This
avoids the incorrect possible reading “free object in the category of
restricted Lie algebras.”  Finally, the squaring equalizer is now described
as the equalizer with the *constant map* to the identity section.

These are presentation repairs, not changes to the construction or result.

## 2. Ring, PBW, and Hopf-algebra audit

For

\[
 R=\mathbf F _2[a,b]/(a^2,b^2),
\]

the basis \(1,a,b,ab\) gives length four,
\(\mathfrak m^2=(ab)=\operatorname {Soc}(R)\), and
\(\mathfrak m^3=0\).  In particular, \(a\) and \(b\) are nonzero and the
ideals \((a)\) and \((b)\) are incomparable.

The three reductions

\[
 X^2\rightsquigarrow bX,qquad
 Y^2\rightsquigarrow aY,qquad
 YX\rightsquigarrow XY+aX+bY
\]

terminate and the four critical overlaps resolve.  Since the reductions are
monic over \(R\), the normal words \(1,X,Y,XY\) form an \(R\)-basis.  The
resulting multiplication table is associative.  Declaring \(X,Y\) primitive
preserves each relation: the square relations are primitive in
characteristic two, and the cross terms in the coproduct of
\(YX+XY+aX+bY\) cancel in pairs.  The declared antipode respects the
relations as an anti-homomorphism.  Thus \(D\) really is a cocommutative
rank-four Hopf algebra.

Independent dualization gives exactly the source note's algebra,
coproduct, and antipode on \(A=D^\vee\).  In particular,

\[
 A=R[x,y]/(x^2,y^2),\qquad z=xy,
\]

and reduction modulo \((a,b)\) is the standard Hopf algebra of
\(\alpha _2^2\).  Every one of the \(16^3=4096\) elements of the
augmentation ideal squares to zero, so the relative Frobenius is the zero
homomorphism.

## 3. Normal-subgroup and fppf audit

Suppose \(H\subseteq G\) is finite locally free of rank two, and write
\(B=\mathcal O(H)\).  The counit splitting is an actual direct-sum
decomposition

\[
 B=R\oplus J
\]

with \(J\) invertible of rank one.  The map on augmentation ideals is
surjective.  Since all elements of \(I_A\) square to zero, all elements of
\(J\) do as well.  Locally writing \(J=Re\) then gives \(J^2=(e^2)=0\).
Consequently

\[
 I_A/I_A^2\twoheadrightarrow J/J^2=J
\]

is a split surjection of finite locally free modules.  Its dual identifies
\(\operatorname {Lie}(H)\) with a rank-one direct summand of
\(\operatorname {Lie}(G)\).  If \(H\) is normal, differentiating
conjugation makes this line a Lie ideal.  No restricted-Lie assertion is
needed at this point; ordinary Lie-ideal stability is already necessary.

For a unimodular vector \(v=rX+sY\), put \(w=aX+bY\).  A complementary
vector \(u\) satisfies

\[
 [u,v]=\det(u,v)w,
\]

where the determinant is a unit.  Thus \(Rv\) can be an ideal only if
\(w\in Rv\), equivalently

\[
 as+br=0.
\]

If \(r\) is a unit this forces \(b\in(a)\), and if \(s\) is a unit it
forces \(a\in(b)\).  Both are false.  Exhaustion of all 192 unimodular
vectors in \(R^2\) independently confirms that none satisfies the wedge
equation.

The base-change argument is also sound.  Given a faithfully flat
\(R\)-algebra \(R'\), choose a prime of \(R'\) over \(\mathfrak m\).  The
localized map from the local ring \(R\) is flat and local, hence faithfully
flat.  The putative invertible Lie line becomes free and has a unimodular
generator.  The same dichotomy forces \(b\in aR'_{\mathfrak p}\) or
\(a\in bR'_{\mathfrak p}\); faithful flatness descends this membership to
\(R\), a contradiction.  This proves the claimed absence after every fppf
cover, not merely over \(R\) itself.

## 4. Power map, equalizer, and duality

Direct multiplication of the displayed coproduct gives

\[
 \phi=[2]^\#:\quad x\mapsto az,\quad y\mapsto bz,\quad z\mapsto0.
\]

Hence \(\phi^2=\eta\epsilon\).  This means that the fourth-power scheme map
is constant at the identity.  The qualification in the source is important:
for a noncommutative group scheme, the second- and fourth-power maps need not
be group homomorphisms.

The equalizer of the squaring map and the constant identity map is

\[
 A/(az,bz)=R\{1,x,y\}\oplus(R/\mathfrak m)\{z\}.
\]

It is not flat.  As an additional finite-ring check, it has cardinality
\(16^3\cdot2=8192=2^{13}\), which is not the cardinality \(16^n\) of a
finite free \(R\)-module.  Since a finite flat module over this Artin local
ring is free, this is decisive.

The Cartier-duality warning is also correct.  The coordinate algebra \(A\)
is commutative but its coproduct is not cocommutative, so \(G\) is
noncommutative.  The linear dual \(D\) is a noncommutative algebra and hence
cannot be the coordinate algebra of an affine Cartier-dual group scheme.

## 5. Universal rank-two height-one fourth-power lemma

The fourth-power computation is not special to this example.

**Lemma.** Let \(R\) be any commutative \(\mathbf F _2\)-algebra and let
\(L\) be a restricted Lie algebra whose underlying \(R\)-module is finite
locally free of rank two.  Let

\[
 G=\operatorname {Spec}\bigl(U^{[2]}(L)^\vee\bigr).
\]

Then the fourth-power map on \(G\) is the constant identity map.

**Proof.** The assertion is Zariski local, so choose a basis \(X,Y\) and
write

\[
 [X,Y]=uX+vY.
\]

The restricted PBW theorem gives the basis \(1,X,Y,Z=XY\) of
\(D=U^{[2]}(L)\), independent of the coefficients of the restricted
2-operation.  Its dual algebra is

\[
 A=R[x,y]/(x^2,y^2),\qquad z=xy.
\]

The relation \(YX=Z+uX+vY\) and duality of multiplication and coproduct show
that, after applying \(\mu_A\), all restricted-power terms vanish because
they produce \(x^2\) or \(y^2\), while all terms involving a dual factor
\(z\) vanish because \(xz=yz=z^2=0\).  The only surviving commutator terms
give

\[
 [2]^\#(x)=uz,\qquad [2]^\#(y)=vz,
 \qquad [2]^\#(z)=0.
\]

The last equality also follows from the four terms
\(z\otimes1,1\otimes z,x\otimes y,y\otimes x\), whose products cancel in
characteristic two.  A second application kills \(x,y,z\), proving
\([4]^\#=\eta\epsilon\).  \(\square\)

Under the standard height-one correspondence (SGA 3, Exposé
VII\(_A\), §§5 and 7), finite locally free group schemes of height one and
order \(2^n\) over a characteristic-two scheme correspond to locally free
restricted Lie algebras of rank \(n\).  Therefore **every** finite locally
free height-one group scheme of rank four over an arbitrary
characteristic-two base satisfies the lemma.  No freeness of a globally
chosen basis is required: use local bases and descend the equality of the
two scheme maps.

The exact hypotheses are thus: the base has characteristic two, the group is
finite locally free of rank four, and its relative Frobenius is the trivial
homomorphism.  Commutativity of the group is not required.

## 6. Reproducible bounded verification

The standard-library verifier

`scripts/audit_rank4_no_normal_rank2_filtration_20260710.py`

checks:

- all ring identities used for the Artin Gorenstein base;
- all 64 basis associativity identities in \(D\) and all four critical
  overlaps;
- multiplicativity, coassociativity, cocommutativity, counits, and antipodes;
- exact dualization to the displayed coproduct on \(A\);
- all 4096 augmentation-ideal squares;
- the square and fourth-power maps;
- all 192 unimodular vectors in the Lie obstruction; and
- the equalizer cardinality.

It terminates in under a second and prints `AUDIT PASS` only after every
assertion.  The deterministic output is in
`scripts/audit_rank4_no_normal_rank2_filtration_20260710.log`.
The manifest
`scripts/audit_rank4_no_normal_rank2_filtration_20260710.sha256` records

\[
\begin{array}{ll}
\text{script:}&
\texttt{153c45b16792f727f59f378196272ed644ae09a9e03ced017fa6fb44de095fbc},\\
\text{log:}&
\texttt{0565d3fa94ad950281849a9496f88af7e285998d87188044be5f718a23a35bc6}.
\end{array}
\]

