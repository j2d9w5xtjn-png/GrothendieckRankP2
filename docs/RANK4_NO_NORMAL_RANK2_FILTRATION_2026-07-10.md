# A rank-four height-one group with no fppf-local normal rank-two subgroup

**Date:** 2026-07-10  
**Status:** explicit hand construction and obstruction proof  
**Purpose:** test the proposed strategy that every rank-four group scheme with
killed-by-two special fiber should acquire a normal rank-two subgroup fppf
locally.

## 1. Result

That proposed filtration statement is false, even over a very small Artin
Gorenstein base.

Let

\[
 R=\mathbf F _2[a,b]/(a^2,b^2).
\]

This is a local Artin Gorenstein ring of length four, with

\[
 \mathfrak m=(a,b),\qquad \mathfrak m^2=(ab)
 =\operatorname {Soc}(R),\qquad \mathfrak m^3=0.
\]

There is a finite locally free height-one group scheme \(G/R\) of rank four
such that

1. \(G_{\mathbf F _2}\simeq\alpha _2^2\), so its special fiber is connected
   and killed by two;
2. \(G\) has no finite locally free normal subgroup of rank two, even after
   any faithfully flat base change on \(R\);
3. nevertheless \(G\) is killed by four.

Thus the rank-two-filtration route cannot prove the rank-four conjecture in
this generality.  This example is **not** a counterexample to Grothendieck's
conjecture.  It instead gives a precise mechanism by which the desired
filtration can fail: the infinitesimal commutator can point simultaneously
in two incomparable nilpotent directions.

## 2. The distribution Hopf algebra

Let \(D\) be generated as an \(R\)-algebra by \(X,Y\), subject to

\[
 X^2=bX,\qquad Y^2=aY,\qquad
 YX=XY+aX+bY.
\]

Declare \(X\) and \(Y\) primitive:

\[
 \Delta_D(X)=X\otimes1+1\otimes X,
 \qquad
 \Delta_D(Y)=Y\otimes1+1\otimes Y,
\]

with counit zero on \(X,Y\) and antipode \(S_D(X)=X\),
\(S_D(Y)=Y\).  The defining relations are Hopf-stable in characteristic two.
The three monic rewriting rules above have normal words

\[
 1,\quad X,\quad Y,\quad Z:=XY.
\]

There are four overlap ambiguities, with words \(X^3,Y^3,YX^2,Y^2X\),
and all are resolved using \(a^2=b^2=0\).  The first two are immediate.  For
example,

\[
 YX^2=bXY+abX+b^2Y=bZ+abX
\]

whether one first reduces \(X^2\) or \(YX\), and the analogous calculation
holds for \(Y^2X\).  Hence \(D\) is finite free of rank four on the displayed
basis.  Equivalently, \(D\) is the restricted enveloping algebra of the
restricted Lie algebra whose underlying \(R\)-module is free of rank two,

\[
 L=RX\oplus RY,\qquad [X,Y]=aX+bY,
 \qquad X^{[2]}=bX,\quad Y^{[2]}=aY.
\]

Let

\[
 A=D^\vee=\operatorname {Hom}_R(D,R),
 \qquad G=\operatorname {Spec}(A).
\]

Since \(D\) is cocommutative, \(A\) is a commutative finite free Hopf algebra
of rank four.

## 3. Explicit coordinate Hopf algebra

Let \(1,x,y,z\) be the basis dual to \(1,X,Y,Z\).  The coalgebra of \(D\)
shows that, as an augmented algebra,

\[
 A=R[x,y]/(x^2,y^2),\qquad z=xy,qquad
 I=(x,y,z).
\]

For reference, multiplication in \(D\) additionally gives

\[
\begin{array}{c|ccccc}
 &XY&YX&XZ&ZX&ZY\\ \hline
 &Z&Z+aX+bY&bZ&abX&aZ
\end{array}
\]

and

\[
 YZ=abY,\qquad Z^2=abZ.
\]

Dualizing this table gives the following completely explicit coproduct:

\[
\begin{aligned}
 \Delta(x)={}&x\otimes1+1\otimes x
   +b\,x\otimes x+a\,y\otimes x+ab\,z\otimes x,\\
 \Delta(y)={}&y\otimes1+1\otimes y
   +a\,y\otimes y+b\,y\otimes x+ab\,y\otimes z,\\
 \Delta(z)={}&z\otimes1+1\otimes z+x\otimes y+y\otimes x
   +b\,x\otimes z+a\,z\otimes y+ab\,z\otimes z.
\end{aligned}
\]

The counit kills \(x,y,z\), and the antipode is

\[
 S_A(x)=x+az,\qquad S_A(y)=y+bz,\qquad S_A(z)=z.
\]

Modulo \((a,b)\), the first two generators are primitive.  Therefore

\[
 G_{\mathbf F _2}=\alpha _2\times\alpha _2.
\]

Also every element of \(I\) has square zero.  Thus the relative Frobenius of
\(G\) is zero: \(G\) is a height-one group scheme over \(R\).

## 4. The Lie obstruction to a normal subgroup

The cotangent space is free:

\[
 I/I^2=R\bar x\oplus R\bar y,
\]

and its dual Lie algebra is

\[
 \operatorname {Lie}(G)=RX\oplus RY,\qquad [X,Y]=aX+bY.
\]

We first record an elementary module lemma.  Put

\[
 w=aX+bY.
\]

If \(M=Rv\subset L\) is a rank-one direct summand and \(u,v\) is a basis of
\(L\), then

\[
 [u,v]=\det(u,v)w.
\]

Consequently \(M\) can be a Lie ideal only if \(w\in M\).  Write
\(v=rX+sY\), where \(r,s\) generate the unit ideal.  If
\(w=\lambda v\), then, since \(R\) is local, either \(r\) or \(s\) is a
unit.  If \(r\) is a unit, then

\[
 b=a r^{-1}s\in(a),
\]

which is false.  If \(s\) is a unit, the same argument gives
\(a\in(b)\), also false.  Indeed

\[
 (a)=\langle a,ab\rangle_{\mathbf F _2},\qquad
 (b)=\langle b,ab\rangle_{\mathbf F _2}
\]

are incomparable ideals.  Hence \(L\) has no rank-one direct-summand Lie
ideal.

Now suppose that \(H\hookrightarrow G\) were a finite locally free normal
subgroup of rank two.  Write \(B=\mathcal O(H)\).  It is a rank-two quotient
of \(A\).  The counit splitting first gives

\[
 B=R\oplus J
\]

with the augmentation ideal \(J\) an invertible \(R\)-module of rank one.
Every element of \(J\) is the image of an element of \(I\), hence has square
zero.  Locally choose a generator \(e\) of \(J\); then \(e^2=0\), and
therefore \(J^2=0\).  The quotient \(A\twoheadrightarrow B\)
induces a surjection

\[
 I/I^2\twoheadrightarrow J/J^2=J.
\]

Dualizing embeds \(\operatorname {Lie}(H)=J^\vee\) as a rank-one direct
summand of \(\operatorname {Lie}(G)\).  Normality of \(H\) implies that this
line is a Lie ideal, by differentiating the conjugation action.  This
contradicts the preceding module lemma.

Therefore \(G\) has no finite locally free normal rank-two subgroup over
\(R\).

## 5. What the subgroup parameter scheme sees

This obstruction is visible before imposing all the restricted-Lie or Hopf
conditions.  In the projective line \(\mathbf P(L)\) parametrizing
rank-one direct summands, the closed locus of Lie-ideal lines is defined by

\[
 (aX+bY)\wedge v=0.
\]

On the chart \(v=X+sY\), its equation is

\[
 b=as,
\]

and on the chart \(v=rX+Y\), its equation is

\[
 a=br.
\]

After reduction modulo \(\mathfrak m\), both equations vanish identically:
every line in \(L_{\mathbf F _2}\) is an ideal, as expected for the abelian
special fiber.  Over \(R\), however, neither chart has a point after a
faithfully flat extension, by incomparability of \((a)\) and \((b)\).
The actual normal-subgroup functor maps into this closed locus, so it cannot
have a flat point either.

This is the elementary local model for the Hilbert-scheme failure: a proper
subgroup parameter space may have a large nonempty special fiber while all
of those points are vertical and obstructed.  Nonemptiness on the special
fiber alone therefore gives no fppf-local subgroup.

## 6. The obstruction survives fppf base change

Let \(R\to R'\) be faithfully flat.  Ideal membership descends under a
faithfully flat map:

\[
 b\in aR'\Longrightarrow b\in(a),\qquad
 a\in bR'\Longrightarrow a\in(b).
\]

Indeed, this follows from injectivity of
\(R/(a)\to R'/aR'\) and \(R/(b)\to R'/bR'\).

If a normal rank-two subgroup existed after this base change, one could
localize \(R'\) at a prime over \(\mathfrak m\).  The resulting local flat
map from the Artin local ring \(R\) is still faithfully flat.  The Lie line
would then be generated by \(rX+sY\) with one coefficient a unit.  Repeating
the argument of Section 4 would force one of the two forbidden containments
above.
Thus no such subgroup exists after any faithfully flat, and hence after any
fppf, base change.

## 7. Direct fourth-power calculation

Let

\[
 \phi=[2]^\#=\mu\circ\Delta:A\longrightarrow A.
\]

Here \([2]:G\to G\) denotes the squaring power map \(g\mapsto g^2\).
Because \(G\) is noncommutative, this is a scheme map but not a group
homomorphism.  Using \(x^2=y^2=xz=yz=z^2=0\), the displayed coproduct gives

\[
 \phi(x)=az,\qquad \phi(y)=bz,\qquad \phi(z)=0.
\]

Therefore

\[
 [4]^\#=\phi^2=\eta\epsilon.
\]

Here \([4]\) is likewise the fourth-power map \(g\mapsto g^4\), obtained by
composing the squaring map with itself; no homomorphism property is being
used.

The example is killed by four even though the rank-two extension argument is
unavailable.

## 8. Frobenius, the squaring equalizer, and duality

The other canonical candidates do not recover a rank-two subgroup in this
example.

First, the relative Frobenius is zero, so

\[
 \ker(F_{G/R})=G
\]

has rank four rather than rank two.

Second, the scheme-theoretic equalizer of \([2]\) and the constant map to the
identity section has coordinate algebra

\[
 A/(az,bz)
 \simeq R\{1,x,y\}\oplus (R/\mathfrak m)\{z\}.
\]

It is not flat over \(R\).  Moreover, for a noncommutative group scheme the
squaring map is not a group homomorphism, so this equalizer has no automatic
subgroup structure in the first place.  This gives a concrete Fitting-module
warning: the most obvious squaring “kernel” acquires a residue-field summand
instead of a finite locally free rank-two piece.

Finally, Cartier duality cannot be applied to the total group scheme.  The
coproduct above is not cocommutative—for example the
\(a\,y\otimes x\) term of \(\Delta(x)\) has no matching
\(a\,x\otimes y\) term—so \(G\) is noncommutative.  Its linear dual \(D\)
has noncommutative multiplication and is not the coordinate algebra of a
Cartier dual group scheme.  Although the special fiber
\(\alpha _2^2\) is commutative and self-dual, that special-fiber duality does
not extend across this deformation.

## 9. Consequences for the remaining search

The example rules out the following hoped-for theorem:

> A rank-four finite locally free group scheme over a local Artin ring, whose
> special fiber is killed by two, acquires a finite flat normal subgroup of
> rank two fppf locally.

It also shows that restricting to a Gorenstein base does not repair the
statement.  The failure occurs because the commutator vector
\(aX+bY\) does not lie in any unimodular line when \((a)\) and \((b)\) are
incomparable.  This mechanism is unavailable over a chain ring at the level
of this elementary Lie obstruction, but it is already present on the
nonprincipal Hilbert-function \((1,2,1)\) base above.

The useful conclusion is therefore negative but sharp: subgroup/Hilbert
scheme arguments must control flatness and liftability of a subgroup, not
merely produce an invariant line on the special fiber.  A special-fiber line
can become a purely vertical point of the subgroup parameter scheme, and
faithfully flat extension cannot remove the associated ideal-membership
obstruction.
