# The monogenic $t^4$ frontier after the regular-translation pass

**Date:** 2026-07-10  
**Status:** hand lemmas and a calibrated obstruction analysis. No proof of
killedness by four and no counterexample is claimed.

## 1. Every $t^4$ lift is monogenic

Let $(R,\mathfrak m,k)$ be local and let $A/R$ be a free augmented algebra
of rank four with

\[
 A\otimes_R k\simeq k[t]/t^4.
\]

Choose $T\in I=\ker\varepsilon$ lifting $t$. Nakayama's lemma shows that
$1,T,T^2,T^3$ is an $R$-basis. Consequently there are unique
$a,b,d\in\mathfrak m$ such that

\[
 \boxed{A\simeq R[T]/(T^4-aT-bT^2-dT^3).}       \tag{1.1}
\]

The powers of the augmentation ideal are particularly explicit:

\[
 I=(T),\qquad
 I^2=(T^2)=(a)T\oplus RT^2\oplus RT^3,          \tag{1.2}
\]

where the sum is with respect to the displayed free basis. Hence

\[
 I/I^2\simeq R/(a).                              \tag{1.3}
\]

If $X\in A^\vee$ is dual to $T$, then a functional is primitive exactly
when it vanishes on $1$ and $I^2$. Thus

\[
 \boxed{\operatorname{Prim}(A^\vee)=\operatorname{ann}(a)X.} \tag{1.4}
\]

All primitive nonsaturation in the monogenic branch is therefore controlled
by the one coefficient $a$.

If $A$ is Hopf and $\phi=[2]^\#$, then $\ker\phi$ and
$\mathfrak m\ker\phi$ are ideals. Since $I=(T)$, the strengthened
condition $S'$ is equivalent to the single membership

\[
 \phi(T)\in\mathfrak m\ker\phi.                  \tag{1.5}
\]

## 2. The first quartic-relation layer is primitive

Assume now

\[
 R=k[\pi]/\pi^M,\qquad \operatorname{char}k=2,
\]

and that (1.1) is a Hopf algebra. Let

\[
 v=\min\{v_\pi(a),v_\pi(b),v_\pi(d)\}
\]

be finite, and write

\[
 T^4=\pi^v r_0(T)\pmod {\pi^{v+1}},\qquad
 r_0=a_0T+b_0T^2+d_0T^3.
\]

### Proposition 2.1

The element $r_0$ is primitive in the special-fiber Hopf algebra.

### Proof

Write

\[
 \Delta T=T\otimes1+1\otimes T+w,\qquad w\in I\otimes I.
\]

In characteristic two, Frobenius gives

\[
 (\Delta T)^4=T^4\otimes1+1\otimes T^4+w^4.
\]

Each tensor leg of every term of $w^4$ contains a fourth power of an
augmentation element. Reducing it with (1.1) introduces a factor $\pi^v$
in each leg. Thus $w^4$ is divisible by $\pi^{2v}$, which is zero modulo
$\pi^{v+1}$. Comparing the preceding equality with
$\Delta(T^4)=\pi^v\Delta_0(r_0)$ in the free tensor module, dividing by
$\pi^v$, and reducing modulo $\pi$ gives

\[
 \Delta_0(r_0)=r_0\otimes1+1\otimes r_0.
\]

This proves the proposition. $\square$

For the special $t^4$ coproduct with parameters $(c_1,c_4)$, the
primitive classification in `THEORY_order4.md`, Lemma 12.3.1, now gives

\[
 d_0=a_0c_1,\qquad a_0c_4=0.                    \tag{2.1}
\]

In particular, a pure $T^3$ term can never be the first nonzero quartic
relation layer. This extends the earlier top-only monogenic exclusion: any
surviving tight chain must use at least two coupled relation layers.

## 3. A trace-depth constraint on the linear coefficient of doubling

Continue in equal characteristic two and write

\[
 \phi(T)=\rho T+\sigma T^2+\tau T^3,qquad
 J=(a,b,d).
\]

The killed special fiber puts $\rho,\sigma,\tau\in\mathfrak m$. Since
$\phi$ is an algebra map, its three augmentation columns are
$\phi(T),\phi(T)^2,\phi(T)^3$. In characteristic two,

\[
 [T^2]\phi(T)^2=\rho^2\pmod {J\mathfrak m^2},
\qquad
 [T^3]\phi(T)^3=\rho^3\pmod {J\mathfrak m^3}.
\]

The exact Hopf-square trace theorem says
$\operatorname{Tr}_I(\phi)=0$. It follows that

\[
 \rho(1+\rho+\rho^2)\in J\mathfrak m^2.
\]

The factor in parentheses is a unit, so

\[
 \boxed{\rho\in J\mathfrak m^2.}                \tag{3.1}
\]

Independently, the characteristic-two inclusion $\phi(I)\subset I^2$,
together with (1.2), gives

\[
 \boxed{\rho\in aR.}                            \tag{3.2}
\]

Thus the $T$-component omitted by the earlier minimal ansatz is both an
$a$-multiple and two maximal-ideal orders deeper than the quartic
deformation ideal. Equations (2.1), (3.1), and (3.2) are useful restrictions,
but they do not cancel arbitrary inhomogeneous carries from several lower
layers.

There is also a constraint on the relative top defect. On a principal
equal-characteristic step with $S'$ below, write
$B^2=\pi^{N-1}\Omega$ modulo the top layer. The exact trace theorem gives
$\operatorname{Tr}(B)=0$; in characteristic two,

\[
 \operatorname{Tr}(B^2)=\operatorname{Tr}(B)^2=0.
\]

The product-defect lemma gives $\Omega(T^2)=\Omega(T^3)=0$. Hence the trace
is the coefficient of $T$ in $\Omega(T)$, and

\[
 \boxed{\Omega(T)\in kT^2+kT^3.}                 \tag{3.3}
\]

This removes the cotangent component of the image but still permits the
tight arrow $T\mapsto T^3$.

## 4. A second modular-trace character

Let $K=A^\vee$, let $P=P_2$ be its second Sweedler power, and let $m$
be its modular character. The audited trace theorem gives

\[
 \tau_R(u)=\operatorname{Tr}(R_uP)=m(u).
\]

Apply the same theorem to $K^{\mathrm{op}}$. Cocommutativity gives
$P_2^{\mathrm{op}}=P_2$, while right multiplication in the opposite
algebra is left multiplication in $K$. Therefore

\[
 \boxed{\operatorname{Tr}(L_uP)
       =m(Su)=\operatorname{Tr}(R_{S(u)}P).}      \tag{4.1}
\]

In the array convention of `scripts/s2check.py`, the new left character is

\[
 \boxed{\sigma[a]=\sum_{r,j}\mathtt{phi[j][r]}
                 \mathtt{DE[r][4a+j]}.}          \tag{4.2}
\]

It is group-like and can be added as a redundant exact solver identity. Its
right-handed companion has `DE[r][4*j+a]`, as recorded in
`RELATIVE_TOP_DEFECT_TRACE_RANK_PASS_2026-07-10.md`, (3.9).

## 5. Why scalar trace identities still miss the tight chain

On a principal step, a top perturbation of the divided operator has the
form

\[
 B\longmapsto B+\pi^{N-1}E.
\]

The undivided map $\phi=\pi B$ changes only by $\pi^NE$. The ordinary
and modular character identities therefore see only a linear contraction of
$E$, required to be primitive. Their quadratic cross with the leading
operator lies one valuation too high.

The divided defect, by contrast, changes by

\[
 \pi^{N-1}(B_0E+EB_0).
\]

For the additive $t^4$ fiber, the abstract choice

\[
 B_0(T)=T^2,\qquad E(T^2)=T^3
\]

has

\[
 (B_0E+EB_0)(T)=T^3\ne0,
\]

while all scalar trace constraints survive. The corresponding augmented
algebra model

\[
 T^4=\pi^{N-2}T^3,\qquad \phi(T)=\pi T^2
\]

fails exactly at Hopf stability: with the additive coproduct its defect is

\[
 \pi^{N-2}(T^2\otimes T+T\otimes T^2)\ne0.
\]

Thus the next proof must use the full relation-stability equation, coupling
multiplication and coproduct. Trace, determinant, characteristic-polynomial,
and primitive-image conditions alone cannot rule out the valuation-tight
chain.
