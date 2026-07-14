# A focused Hopf attack on the tight three-step chain

**Date:** 2026-07-10  
**Scope:** the remaining matrix mechanism in
RELATIVE_TOP_DEFECT_TRACE_RANK_PASS_2026-07-10.md. This note does not
claim a proof of Grothendieck's conjecture, and the example below is not a
counterexample. It records three rigorous exclusions, one explicit Hopf
realization of an apparent nonprincipal chain, and the precise gaps that
remain.

## 1. Summary of the pass

Let \(A\) be the commutative coordinate Hopf algebra,
\(I=\ker\varepsilon\), and \(\varphi=[2]^\#=\mu\Delta\). On a principal
equal-characteristic base, write \(\varphi|_I=\pi B\). The abstract survivor
is

\[
 B=E_{12}+\pi^{N-1}E_{23},\qquad
 B^2=\pi^{N-1}E_{13}\ne0.
\]

The conclusions of this pass are:

1. If \(I^2\) is a direct summand and \(I^4=0\), then \(S'\) holds over
   every local characteristic-two base. Thus every ansatz with fixed
   coordinate algebra \(R[T]/T^4\) or \(R[x,y]/(x^2,y^2)\) is excluded
   from the tight-chain problem, without using coassociativity.
2. There is an explicit noncommutative rank-four group over the Gorenstein
   ring \(R=\mathbf F _2[u,v]/(u^2,v^2)\) for which the dual Sweedler square
   has the two basis arrows \(P_2(Z)=uvY\) and \(P_2(Y)=uvX\).
   Coefficientwise division of those two formulas by the socle element
   \(uv\) gives a three-step matrix with nonzero square, although
   \(P_2(uvY)=0\). Nevertheless the correct
   nonprincipal \(S'\) condition holds: the two copies of \(uv\) split as
   \(u\cdot v\), and the intermediate vectors can be chosen in the kernel.
3. The preceding example belongs to a triangular Hopf family. Throughout
   the killed-by-two-special-fiber part of that family, the same equations
   which make the commutator Hopf-stable supply explicit \(S'\) witnesses.
   Hence this natural nonprincipal attempt cannot be modified into a
   counterexample merely by choosing a more pathological annihilator ideal.
4. On a principal base, the most economical monogenic realization
   \(T^4=\pi^{N-2}r(T)\),
   \(\varphi(T)=\pi(\beta T^2+\gamma T^3)\), is impossible at the critical
   layer. Hopf compatibility makes \(r\bmod\pi\) primitive. In the only
   branch capable of supplying the first critical edge, the audited trace
   identity and the product-killing property of the top defect force every
   residue coefficient of \(r\) to vanish; the other branch has zero
   divided square at the top layer.

What remains is a genuinely coupled mechanism with intervening layers in
both multiplication and coproduct, or a less triangular nonprincipal
coalgebra. The bare matrix \(E_{12}+\pi^{N-1}E_{23}\) substantially
understates those requirements.

## 2. A square-ideal criterion for \(S'\)

### Proposition 2.1

Let \((R,\mathfrak m)\) be a local ring of characteristic two and let \(A/R\)
be a finite free commutative augmented bialgebra. Assume that its special
fiber is killed by two, so

\[
 \varphi(I)\subseteq\mathfrak m I.
\]

If

\[
 I^2\subset I\text{ is an }R\text{-direct summand},\qquad I^4=0,
\]

then

\[
 \boxed{\varphi(I)\subseteq
 \mathfrak m(\ker\varphi\cap I).}
\]

In other words, \(S'\) holds.

#### Proof

Counitality writes, for \(g\in I\),

\[
 \Delta(g)=g\otimes1+1\otimes g+w(g),\qquad w(g)\in I\otimes I.
\]

Since \(2=0\),

\[
 \varphi(g)=\mu\Delta(g)=\mu w(g)\in I^2.
\]

The direct-summand hypothesis gives

\[
 \mathfrak mI\cap I^2=\mathfrak mI^2,
\]

and therefore \(\varphi(I)\subseteq\mathfrak mI^2\). Finally, because
\(\varphi\) is an algebra endomorphism,

\[
 \varphi(I^2)\subseteq\varphi(I)^2\subseteq(I^2)^2=I^4=0.
\]

Thus \(I^2\subseteq\ker\varphi\cap I\), proving the assertion. \(\square\)

### Consequences

For the fixed augmented algebras (with the displayed variables in the
augmentation ideal)

\[
 R[T]/T^4,
 \qquad R[x,y]/(x^2,y^2),
\]

the square ideals are respectively \(R\{T^2,T^3\}\) and \(R\{xy\}\), and
their squares vanish. Hence every characteristic-two Hopf structure on
either fixed algebra satisfies \(S'\). A surviving tight chain must make
at least one of the following happen:

* \(I^2\) ceases to be saturated or a direct summand; or
* \(I^4\) becomes nonzero.

On the dual cocommutative Hopf algebra \(D=A^\vee\), put
\(J=\{f\in D:f(1)=0\}\). This has a useful interpretation:

\[
 \operatorname {Prim}(D)
 =\{f\in J:f(I^2)=0\}\simeq (I/I^2)^\vee.
\]

Thus non-saturation of \(I^2\) can manifest dually as failure of the
primitive module to lift as a saturated summand. The explicit model in the
next section exhibits this phenomenon, but also shows why it does not by
itself violate \(S'\).

## 3. An explicit nonprincipal Hopf chain which still satisfies \(S'\)

Put

\[
 R=\mathbf F _2[u,v]/(u^2,v^2),\qquad
 c=uv,\qquad a=u+uv.
\]

This is local Artin Gorenstein of length four, with
\(\mathfrak m=(u,v)\) and socle \((c)=\mathfrak m^2\).

Define an \(R\)-algebra \(D\) on generators \(X,Y\) by

\[
 X^2=aX,\qquad Y^2=0,\qquad
 YX=XY+cY,
\]

and write \(Z=XY\). The normal words are

\[
 1,\ X,\ Y,\ Z.
\]

The only nontrivial overlap \(YX^2\) is consistent because

\[
 c(a+c)=cu=u^2v=0;
\]

the \(Y^2X\) overlap is zero. Thus \(D\) is free of rank four. The useful
remaining products are

\[
 XZ=aZ,\qquad ZX=uZ,\qquad
 YZ=ZY=Z^2=0.
\]

Declare

\[
\begin{aligned}
 \Delta_D(X)&=X\otimes1+1\otimes X,\\
 \Delta_D(Y)&=Y\otimes1+1\otimes Y+vX\otimes X.
\end{aligned}
\]

Then multiplicativity gives

\[
 \Delta_D(Z)=Z\otimes1+1\otimes Z+X\otimes Y+Y\otimes X;
\]

the two apparent extra terms are both
\(vaX\otimes X=cX\otimes X\) and cancel in characteristic two. The
relations are Hopf-stable:

* \(X^2-aX\) is primitive;
* the reduced coproduct of \(YX+XY+cY\) is
  \(cvX\otimes X=uv^2X\otimes X=0\);
* the square of \(\Delta_D(Y)\) is zero because \(v^2=cv=0\).

Coassociativity is immediate for \(X\), and for \(Y\) it is the standard
two-cocycle identity for \(X\otimes X\). An antipode is

\[
 S_D(X)=X,\qquad S_D(Y)=Y+cX,\qquad S_D(Z)=Z+cY.
\]

Therefore \(D\) is a finite free cocommutative Hopf algebra. Its second
Sweedler power \(P_2=\mu_D\Delta_D\) is

\[
 \boxed{P_2(X)=0,\qquad P_2(Y)=cX,\qquad P_2(Z)=cY.}       \tag{3.1}
\]

In particular \(P_2^2=0\), but formally dividing (3.1) by the nonzero
socle element \(c\) produces the three-step chain
\(Z\mapsto Y\mapsto X\).

### Coordinate description and the exact \(S'\) witnesses

Let \(A=D^\vee\), with basis \(1,x,y,z\) dual to \(1,X,Y,Z\). Its
augmented algebra is

\[
 x^2=vy,\qquad y^2=0,\qquad xy=z,\qquad xz=yz=z^2=0.
\]

Thus \(I^2=Rz+(v)y\) is not a direct summand; this is precisely the branch
not covered by Proposition 2.1. Dualizing the multiplication of \(D\)
gives

\[
\begin{aligned}
 \Delta_A(x)&=x\otimes1+1\otimes x+a\,x\otimes x,\\
 \Delta_A(y)&=y\otimes1+1\otimes y+c\,y\otimes x,\\
 \Delta_A(z)&=z\otimes1+1\otimes z+x\otimes y+y\otimes x
              +a\,x\otimes z+u\,z\otimes x.
\end{aligned}
\]

The coproduct is noncocommutative. Modulo \((u,v)\), the group is
\(\alpha_2^2\). It is not height one over \(R\), since \(x^2=vy\ne0\).
From (3.1),

\[
 \varphi(x)=cy,\qquad
 \varphi(y)=cz,\qquad
 \varphi(z)=0.                                      \tag{3.2}
\]

Nevertheless \(S'\) holds, with explicit witnesses:

\[
 cy=v(uy),\qquad \varphi(uy)=uc\,z=0,
\]

and

\[
 cz=u(vz),\qquad \varphi(vz)=0.
\]

The error in treating (3.2) as a counterexample would be to use the
principal formula \(B=\varphi/c\). Here \(cR=\mathfrak m^2\), not
\(\mathfrak m\), and the definition of \(S'\) uses all of
\(\mathfrak m=(u,v)\). The factorization \(c=uv\) repairs the apparent
nonzero divided square.

The exact finite checker
scripts/audit_tight_chain_hopf_model_20260710.py verifies associativity on
all 64 basis triples, all bialgebra and antipode identities, (3.1), (3.2),
noncommutativity, the special fiber, and the displayed \(S'\) witnesses.

## 4. The triangular family is automatically \(S'\)

The preceding construction is not an isolated accident. Let \(R\) be a
local ring of characteristic two, and consider the triangular presentation

\[
 X^2=aX,\qquad Y^2=dY,\qquad YX=XY+cY,
\]

with

\[
 \Delta(X)=X\otimes1+1\otimes X,
 \qquad
 \Delta(Y)=Y\otimes1+1\otimes Y+sX\otimes X.        \tag{4.1}
\]

The Diamond overlap \(YX^2\) and Hopf-stability of the commutator impose

\[
 c(a+c)=0,\qquad cs=0.                              \tag{4.2}
\]

The \(Y^2X\) overlap and Hopf-stability of \(Y^2-dY\) impose

\[
 cd=0,\qquad s(d+sa^2)=0.                           \tag{4.3}
\]

Under (4.2)--(4.3), the normal basis is \(1,X,Y,Z=XY\), (4.1) defines a
cocommutative bialgebra, and an antipode is

\[
 S(X)=X,\qquad S(Y)=Y+saX,\qquad
 S(Z)=Z+cY+sa^2X.
\]

Thus this is in fact a Hopf family. Its second Sweedler power is

\[
 P_2(X)=0,\qquad P_2(Y)=saX,\qquad P_2(Z)=cY.       \tag{4.4}
\]

Write \(h=a+c\). Equations (4.2) say \(ch=cs=0\), and hence

\[
 sa=s(c+h)=sh.
\]

Dualizing (4.4) gives

\[
 \varphi(x)=sh\,y,\qquad \varphi(y)=cz,\qquad\varphi(z)=0.
\]

Assume that the special fiber is killed by two. By the displayed formulas,
this is equivalent to

\[
 c\in\mathfrak m,\qquad sh\in\mathfrak m.
\]

If \(s\in\mathfrak m\), then

\[
 sh\,y=s(hy),\qquad \varphi(hy)=hc\,z=0,
\]

and \(cz=c(z)\) with \(z\in\ker\varphi\). If instead
\(s\notin\mathfrak m\), then \(s\) is a unit. The equation \(cs=0\) gives
\(c=0\), and \(sh\in\mathfrak m\) gives \(h\in\mathfrak m\). In this case

\[
 sh\,y=h(sy),\qquad \varphi(sy)=scz=0,
 \qquad \varphi(y)=0.
\]

Thus every member of this triangular family with killed-by-two special
fiber satisfies \(S'\). It may display a nonzero product of two elements of
\(\operatorname {ann}(c)\), as the example \(h=u,s=v,c=uv\) does, but that
same factorization gives the required kernel division.

On a principal chain ring this obstruction is even sharper. If the first
edge is a unit divided edge, \(c=\pi u\) with \(u\) a unit, then (4.2) puts
both \(s\) and \(h\) in \(\operatorname {ann}(\pi)\). This annihilator is
the square-zero socle of the chain ring, so \(sh=0\) and
\(P_2(Y)=shX=0\). The most obvious distribution-algebra
realization of \(E_{12}+\pi^{N-1}E_{23}\) is therefore impossible.

## 5. Excluding the minimal monogenic principal ansatz

This section treats the coordinate-algebra version of the same minimal
attempt. It is deliberately scoped: intervening lower layers are not
allowed.

Let \(k\) be a field of characteristic two and let

\[
 R'=k[\pi]/\pi^{N+1},\qquad N\ge5,\qquad q=\pi^{N-2},
\]

and suppose

\[
 A=R'[T]/(T^4-q\,r(T)),\qquad
 r(T)=aT+bT^2+dT^3,                                \tag{5.1}
\]

is an augmented bialgebra whose special fiber is a killed-by-two Hopf
algebra of \(t^4\) shape. (The antipode lifts across the nilpotent maximal
ideal, so \(A\) itself is Hopf.) Assume
the proposed minimal divided-square form

\[
 \varphi(T)=\pi v,\qquad v=\beta T^2+\gamma T^3,    \tag{5.2}
\]

and assume the lower truncation \(A/\pi^N A\) satisfies \(S'\), so the
audited top-defect product lemma applies.

Because \(q^2=0\), applying \(\Delta\) to (5.1) gives

\[
 q\bigl(\Delta(r)-r\otimes1-1\otimes r\bigr)=0.     \tag{5.3}
\]

Indeed, in characteristic two the fourth power of
\(\Delta(T)=T\otimes1+1\otimes T+w\) is the sum of the fourth powers. The
two counital terms give \(q(r\otimes1+1\otimes r)\), while every fourth
power from \(w\in I\otimes I\) contains \(q^2\) and vanishes. Since the
monic presentation makes \(A\otimes A\) free over \(R'\), reducing (5.3)
modulo \(\pi\) shows that

\[
 r_0=a_0T+b_0T^2+d_0T^3
\]

is primitive in the special-fiber Hopf algebra. In the notation of
THEORY_order4.md, Lemma 12.3.1,

\[
 d_0=a_0c_1,\qquad a_0c_4=0.                       \tag{5.4}
\]

Let \(B=\varphi/\pi\), considered modulo \(\pi^N\). A direct calculation
from (5.1)--(5.2) gives

\[
 B(T^2)=\pi^{N-1}
 \bigl(\beta_0^2r_0+\gamma_0^2a_0T^3\bigr),
 \qquad B(T^3)=0                                   \tag{5.5}
\]

modulo \(\pi^N\). Suppose first that \(\beta_0\ne0\). The exact Hopf trace
identity \(\operatorname {tr}(B)=0\bmod\pi^N\) applied to (5.5) reads

\[
 \pi^{N-1}\beta_0^2b_0=0\pmod {\pi^N}
\]

and forces

\[
 b_0=0.                                             \tag{5.6}
\]

Moreover,

\[
 B^2(T^2)=\pi^{N-1}\beta_0^2a_0
 (\beta_0T^2+\gamma_0T^3).
\]

The top defect kills the product class \(T^2\). The coefficient of \(T^2\)
in the displayed value is \(\beta_0^3a_0\), so \(a_0=0\). Equation
(5.4) then gives \(d_0=0\). Together with (5.6), this says \(r_0=0\): the
putative critical algebra deformation actually starts one layer deeper and
cannot produce the required top edge. If \(\beta_0=0\), then
\(\beta\in\pi R'\), the leading symbol lands in \(kT^3\), and (5.5) gives
\(\beta B(T^2)+\gamma B(T^3)=0\bmod\pi^N\). Thus
\(B^2(T)=0\) at the top layer.

Thus the isolated monogenic realization of the tight chain is impossible.
The argument is genuinely Hopf-theoretic: an arbitrary augmented algebra
does admit the tempting data

\[
 T^4=\pi^{N-2}T^3,\qquad \varphi(T)=\pi T^2,
\]

for which \(B(T)=T^2\), \(B(T^2)=\pi^{N-1}T^3\), and \(B^2\ne0\). Equation
(5.3), followed by the trace and product-defect identities, is what
prevents this algebra endomorphism from being the squaring map in the
stated Hopf ansatz.

## 6. Remaining gap and next mathematical target

The exclusions above do not cover a general principal lift. In general,

\[
 B=B_0+\pi B_1+\cdots+\pi^{N-1}B_{N-1},
\]

and the top coefficient of \(B^2\) contains all coupled terms
\(B_iB_{N-1-i}\). A basis change which makes the matrix look like a bare
two-edge chain need not preserve a monogenic multiplication normal form.
Likewise, a nonprincipal distribution coalgebra can have several reduced
coproduct tensors; then the commutator need not have the triangular form of
Section 4.

A genuine survivor must therefore evade all of the following
simultaneously:

1. the square-ideal criterion, by making \(I^2\) non-saturated or
   \(I^4\ne0\);
2. the triangular factorization which automatically supplies kernel
   divisions;
3. primitive-lift constraints such as (5.3);
4. the exact trace identity;
5. the fact that the top defect kills products.

The most promising hand target is now a filtered primitive-lifting theorem:
control the torsion in

\[
 D/\operatorname {Prim}(D),
 \quad\text{dually, the failure of }I^2\subset I\text{ to be saturated},
\]

together with the nonzero \(I^4\) carry. The explicit example proves that
primitive non-saturation alone is real, even over a length-four Gorenstein
base, but also shows that its simplest annihilator pattern is absorbed by
\(S'\). Any counterexample mechanism must couple that torsion to additional
lower layers rather than merely making the base more ramified.
