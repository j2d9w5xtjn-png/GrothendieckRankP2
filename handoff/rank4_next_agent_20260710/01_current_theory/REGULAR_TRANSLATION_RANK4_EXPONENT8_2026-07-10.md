# Regular translation at rank four: the unconditional exponent improves to 8

**Date:** 2026-07-10  
**Status:** theorem-strength hand proof, independently audited. This
strengthens REGULAR_TRANSLATION_RANK4_EXPONENT16_2026-07-10.md. It still
does **not** prove Grothendieck's killed-by-order conjecture in rank four.

## 1. Theorem

Let \(G/S\) be a finite locally free group scheme of constant rank four.
The group scheme need not be commutative. Then

\[
  \boxed{[8]_G=e.}
\]

Equivalently, on an affine chart \(S=\operatorname{Spec}R\) with
\(A=\mathcal O(G)\),

\[
  [8]^\#=\eta\varepsilon.
\]

The coordinate algebra \(A\) is commutative, as always for an affine group
scheme; its coproduct need not be cocommutative.

## 2. Inputs from the exponent-16 argument

Let

\[
 q=[2]^\#,\qquad p=q^2=[4]^\#,\qquad
 e=\eta\varepsilon,\qquad D=p-e.
\]

Let \(T\) be universal right translation, and put

\[
 \chi=\operatorname{Tr}(T),\qquad \delta=\det(T),\qquad
 I=\ker\varepsilon.
\]

The earlier report proves

\[
 a\chi=\varepsilon(a)\chi,\qquad \delta^2=1,
\]

and derives the characteristic-polynomial coefficient

\[
 c_2=2\chi-1-\delta
\]

and the fourth-power identity

\[
 D=(1+\delta)(q-e).                              \tag{2.1}
\]

The present proof adds one trace calculation. No division by two is used.

## 3. Squaring the regular character

The integral identity applied to \(a=\chi\), together with
\(\varepsilon(\chi)=4\), gives

\[
 \chi^2=4\chi.                                   \tag{3.1}
\]

Coassociativity identifies translation by the square of the universal
element with the square of its translation matrix:

\[
 (\operatorname{id}\otimes q)(T)=T^2.
\]

Taking trace therefore gives

\[
 q(\chi)=\operatorname{Tr}(T^2).                 \tag{3.2}
\]

This step does not assert that \(q\) is a Hopf map. It only uses the
coefficient identity for universal translation.

Newton's identity for a rank-four matrix says

\[
 \operatorname{Tr}(T^2)=\chi^2-2c_2.
\]

Using (3.1) and \(c_2=2\chi-1-\delta\), one obtains

\[
\begin{aligned}
 q(\chi)
 &=4\chi-2(2\chi-1-\delta)\\
 &=2(1+\delta).                                  \tag{3.3}
\end{aligned}
\]

## 4. The fourth-power defect is killed by two

Put \(c=\chi-4\). Since \(q\) fixes base scalars, (3.3) gives

\[
 q(c)=2(\delta-1).                               \tag{4.1}
\]

For \(a\in I\), the integral identity says \(a\chi=0\), and hence

\[
 ac=-4a.
\]

Apply the \(R\)-algebra map \(q\). With (4.1), this becomes

\[
 2(\delta-1)q(a)=-4q(a),
\]

or equivalently

\[
 2(1+\delta)q(a)=0.                              \tag{4.2}
\]

On \(I\), equation (2.1) reads \(D(a)=(1+\delta)q(a)\). Thus (4.2) proves
\(2D=0\) on \(I\). The map \(D\) vanishes on base scalars, so

\[
 \boxed{2D=0\text{ on all of }A.}                \tag{4.3}
\]

## 5. The eighth-power word

The determinant character is group-like, so

\[
 q(\delta)=\mu\Delta(\delta)=\delta^2=1.
\]

Applying \(q\) to (2.1) gives, for every \(a\in A\),

\[
\begin{aligned}
 q(D(a))
 &=q(1+\delta)\,q\bigl(q(a)-e(a)\bigr)\\
 &=2\bigl(p(a)-e(a)\bigr)\\
 &=2D(a)=0.
\end{aligned}
\]

Therefore \(q\circ D=0\). Since \(p=e+D\),

\[
 [8]^\#=q^3=q\circ p=q\circ(e+D)=e.
\]

This proves the theorem.

## 6. Sharpened obstruction ledger

The fourth-power defect now satisfies all of

\[
 D(I)\subseteq I^2,\qquad D(I^2)=0,\qquad D^2=0,\qquad
 2D=0,\qquad qD=0.
\]

It is also killed by \(1+\delta\), because

\[
 (1+\delta)D=(1+\delta)^2(q-e)=2(1+\delta)(q-e)=2D=0.
\]

If \(2\) is a nonzerodivisor on the base, it is a nonzerodivisor on the
finite locally free module \(A\). Equation \(2D=0\) then gives \(D=0\).
Thus the rank-four conjecture holds on such a base, and any counterexample
must be supported on genuine base 2-torsion.

Let \(J\) be the ideal generated equivalently by the values of
\(\operatorname{Id}-S\) or of \(q-e\), as in
RANK4_CONORMAL_DIRECT4_ATTACK_2026-07-10.md. The new result strengthens the
conormal ledger to

\[
 (1+\delta)J^2=0,\qquad
 2(1+\delta)J=0.
\]

Consequently

\[
 M=(1+\delta)J
\]

is annihilated by \(2\), by \(1+\delta\), and by \(J\). It is naturally an
\(A/(2,1+\delta,J)\)-module: a nonzero rank-four defect is a linear
conormal class supported simultaneously on the characteristic-two,
determinant-one, 2-torsion locus.

The inverse relation from the exponent-16 report also gives \(D=q-qS\).
Hence \(D\circ S=-D=D\), where the last equality uses \(2D=0\).
Equivalently \(P_4\circ S=P_4\), so the fourth and negative-fourth power
words agree; this gives a second short route from \(2D=0\) to \([8]=e\).

The desired rank-four conjecture is still the further assertion
\((1+\delta)J=0\). In residue characteristic two, the new factor of two
does not by itself remove the tight conormal class. Thus exponent eight is
a genuine unconditional improvement, but not a proof of \([4]_G=e\).
