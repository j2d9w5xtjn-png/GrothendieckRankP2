# Independent audit of the conormal reduction and the Torti specialization

**Date:** 2026-07-10  
**Verdict:** green relative to the established inputs in
REGULAR_TRANSLATION_RANK4_EXPONENT16_2026-07-10.md. The new result is an
exact obstruction reduction, not a proof of killedness by four.

## 1. Dependency scope

Write \(P_r=[r]^\#\), \(q=P_2\), \(p=P_4\), \(e=P_0\),
\(D=p-e\), and \(d=\delta\). This audit accepts the exponent-16 report's
proved inputs

\[
 d^2=1,\qquad
 (T^2-\operatorname{Id})(T^2-d\operatorname{Id})=0,\qquad
 E_r(T^j)=P_{r+j}.
\]

The evaluation convention was rechecked: if
\(T^j(a)=\sum a_{(1)}\otimes P_j(a_{(2)})\), then applying \(E_r\) gives
\(\sum P_r(a_{(1)})P_j(a_{(2)})=P_{r+j}(a)\). This remains valid for
negative \(r\) and a noncommutative group scheme, because powers of one
element add.

This audit did not independently reconstruct the Pareigis/Kadison--Stolin
finite-projective Hopf--Frobenius theorem underlying the earlier report's
three Frobenius identities.

## 2. Cubic-word calculation

Apply \(E_{-1}\) to
\(T^4-(1+d)T^2+d\operatorname{Id}=0\). This gives

\[
 P_3-(1+d)\operatorname{Id}+dS=0,
\]

and hence \(P_3=(1+d)\operatorname{Id}-dS\). Put
\(U(a)=a-S(a)\). Then \(P_3(a)=a+dU(a)\), while
\(U(ab)=aU(b)+bU(a)-U(a)U(b)\). Multiplicativity of \(P_3\) and
\(d^2=1\) give

\[
 (1+d)U(a)U(b)=0.
\]

This calculation is integral. Only in characteristic two may \(1+d\) be
written as \(d-1\).

## 3. Equality of the two ideals

In the convolution algebra of endomorphisms of \(A\),

\[
 q=\operatorname{Id}\star\operatorname{Id},\qquad
 e=\operatorname{Id}\star S.
\]

Therefore

\[
 q-e=\operatorname{Id}\star(\operatorname{Id}-S),\qquad
 (q-e)\star S=\operatorname{Id}-S.
\]

Expanding values proves equality of the generated ideals

\[
 J=(\operatorname{im}(\operatorname{Id}-S))
  =(\operatorname{im}(q-e))\subset A.
\]

Consequently \((1+d)J^2=0\). From
\(D=(1+d)(q-e)\) and generation of \(J\) by the values of \(q-e\),

\[
 D=0\quad\Longleftrightarrow\quad(1+d)J=0.
\]

If \(B=A/J\), multiplication induces a well-defined surjective
\(B\)-linear map

\[
 \theta_d:J/J^2\longrightarrow(1+d)J,\qquad
 \bar j\longmapsto(1+d)j.
\]

The values of \(q-e\) generate \(J/J^2\), and \(D\) factors through
\(\theta_d\). Thus the rank-four conjecture is equivalent to
\(\theta_d=0\). Nothing in the argument proves this last vanishing. In
particular, it is invalid to infer \((1+d)J=0\) from
\((1+d)J^2=0\), or to identify \(J\) with the augmentation ideal.

## 4. Torti specialization

The peer-reviewed source is Emiliano Torti, “Lagrange's theorem for a class
of finite flat group schemes over local Artin rings,” Documenta Mathematica
(published 16 December 2025), DOI
<https://doi.org/10.4171/DM/1055>. The preprint is
<https://arxiv.org/abs/2411.12129>.

Torti's Theorems 1.3 and 4.3 cover every deformation of

\[
 G_\lambda=\alpha_p\rtimes_\lambda\mu_{p^m},
 \qquad 1\leq\lambda\leq p^m-1,
\]

and conclude killedness by the order. Taking
\((p,m,\lambda)=(2,1,1)\) gives exactly the noncommutative
\(\alpha_2\rtimes\mu_2\) rank-four branch. The conclusion descends after a
faithfully flat residue extension if the fiber is initially a nonsplit form.

Both the preprint and published proof end with an overstrong printed claim
that \(p^m\) kills the classified deformation. For \(m=1\) this contradicts
the paper's own earlier calculation. The rank-four killed-by-order conclusion
is nevertheless checked directly from the classified law:

\[
 (x,y)\circ(x',y')=
 ((1+y)x'+x+a\pi xx',\;y+y'+yy'),\qquad x^2=y^2=0.
\]

It gives

\[
 [2](x,y)=(xy,0),\qquad [4](x,y)=(0,0).
\]

Therefore the branch is killed by four, but it is generally not killed by
two. Torti's theorem does not cover the local--local
\(\alpha_2^2\), \(W_2[F]\), or \(t^4\) branches.
