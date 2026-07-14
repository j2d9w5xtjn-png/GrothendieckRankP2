# Regular translation at rank four: an unconditional exponent-16 theorem

**Date:** 2026-07-10  
**Status:** theorem-strength hand argument, with a bounded independent finite
screen. This does **not** prove Grothendieck's killed-by-order conjecture.

## 1. Result

Let $G/S$ be a finite locally free affine group scheme of constant rank
four. The group scheme need not be commutative. Then

\[
  \boxed{[16]_G=e.}
\]

Equivalently, on an affine chart $S=\operatorname{Spec}R$ with
$A=\mathcal O(G)$,

\[
  [16]^\#=\eta\varepsilon:A\longrightarrow A.
\]

Here $\eta:R\to A$ is the unit and $\varepsilon:A\to R$ the counit.

The desired rank-four case of Grothendieck's conjecture is the stronger
identity $[4]_G=e$, which remains open on the local--local fibers described
in `THEORY_order4.md`, §17.4.

This promotes the provisional regular-translation route in
`grothendieck_rank4_agent_handoff_20260710.zip` to a theorem through its
claimed exponent-16 consequence. It does not promote that note's unproved
killed-by-four conclusion.

## 2. The regular character and determinant

The assertion is local on $S$, so write $S=\operatorname{Spec}R$ and
assume that $A$ is free of rank four. Put $I_A=\ker\varepsilon$. Let

\[
 \widetilde T:A\otimes_R A\longrightarrow A\otimes_R A,
 \qquad \widetilde T(a\otimes b)=\Delta(a)(1\otimes b),
\]

be the universal right-translation automorphism, linear over the second copy
of $A$. Write $T\in\operatorname{End}_R(A)\otimes_R A$ for its matrix, with
the first copy of $A$ as the rank-four module and the second as the
coefficient ring. Set

\[
 \chi=\operatorname{Tr}(T),\qquad
 \delta=\det(T)\in A.
\]

Thus $\varepsilon(\chi)=4$, while $\delta$ is group-like and
$\varepsilon(\delta)=1$.

### Proposition 2.1 (three Frobenius identities)

One has

\[
 a\chi=\varepsilon(a)\chi\quad(a\in A),\qquad
 S(\chi)=\chi,\qquad \delta^2=1.                 \tag{2.1}
\]

#### Proof

A finite-projective Hopf algebra is Frobenius locally on the base. By the
finite-projective results of
[Pareigis](https://epub.ub.uni-muenchen.de/7111/1/7111.pdf) and the dual
coordinate formula of
[Kadison--Stolin, Proposition 3.8](https://arxiv.org/abs/math/0103019), choose a
Frobenius integral $\psi:A\to R$ and a norm $N\in A$, normalized by
$\psi(N)=1$, with Frobenius dual-basis tensor

\[
 \sum N_{(2)}\otimes S^{-1}(N_{(1)}).
\]

Because the coordinate algebra $A$ is commutative, $S^{-1}=S$. Taking
the partial trace of $\Delta$ in these coordinates gives

\[
 \begin{aligned}
 \chi
 &=\sum \psi\!\left(S(N_{(1)})N_{(2)}\right)N_{(3)}\\
 &=\psi(1)N,
 \end{aligned}
\]

where the second equality uses

\[
 \sum S(N_{(1)})N_{(2)}\otimes N_{(3)}=1\otimes N.
\]

Since $aN=\varepsilon(a)N$, this proves the first identity. The equality
$\varepsilon(\chi)=4$ also follows directly by specializing $T$ at the
identity, where it is the identity operator on a rank-four module.

For the remaining identities put $\lambda=\psi\circ S$. The opposite-side
integral identity is

\[
 (\lambda\otimes\operatorname{id})\Delta(a)=\lambda(a)1.
\]

This follows from the defining integral identity for $\psi$ by applying the
antipode and using $S^2=\operatorname{id}$.

The form

\[
 B(a,b)=\lambda(ab)
\]

is perfect and symmetric: perfection is the finite-projective Hopf--Frobenius
theorem, and symmetry uses commutativity of the coordinate algebra. It is
translation-invariant, because

\[
 \sum\lambda(a_{(1)}b_{(1)})a_{(2)}b_{(2)}
 =(\lambda\otimes\operatorname{id})\Delta(ab)
 =\lambda(ab)1.
\]

In matrices,

\[
 T^{\mathsf t}BT=B.
\]

Consequently $T^{-1}=B^{-1}T^{\mathsf t}B$. Taking trace and determinant
gives

\[
 \operatorname{Tr}(T^{-1})=\operatorname{Tr}(T),\qquad
 \det(T)^2=1.
\]

Universal inverse translation is obtained by applying the antipode to the
coefficients, so the trace equality is $S(\chi)=\chi$. This proves (2.1).
$\square$

The argument is local only to trivialize the integral line and the underlying
finite projective module. The identities therefore glue over an arbitrary
base.

## 3. The regular-translation polynomial

Write the characteristic polynomial of $T$ as

\[
 X^4-\chi X^3+c_2X^2-c_3X+\delta.
\]

Proposition 2.1 gives

\[
 c_3=\delta\operatorname{Tr}(T^{-1})
     =\delta\chi=\chi;
\]

the final equality uses $\delta\chi=\varepsilon(\delta)\chi=\chi$.
Translation fixes the constant function, so $X=1$ is a root and hence

\[
 c_2=2\chi-1-\delta.
\]

Cayley--Hamilton now reads

\[
 T^4-\chi T^3+(2\chi-1-\delta)T^2-\chi T+\delta\operatorname{Id}=0.
\]

Every entry of $T^j-\operatorname{Id}$ lies in $I_A$. The integral
identity $I_A\chi=0$ therefore cancels the three $\chi$-terms together and
leaves

\[
 \boxed{(T^2-\operatorname{Id})
        (T^2-\delta\operatorname{Id})=0.}  \tag{3.1}
\]

No reducedness or commutativity of the group scheme is used here.

## 4. The fourth-power defect

Put

\[
 q=[2]^\#,\qquad p=[4]^\#=q\circ q,\qquad e=\eta\varepsilon.
\]

For $r\in\mathbf Z$, put $P_r=[r]^\#$, with
$P_{-r}=P_r\circ S$, and define

\[
 E_r:A\otimes_R A\longrightarrow A,\qquad
 E_r(a\otimes b)=P_r(a)b.
\]

Applied coefficientwise to the translation matrices, the group law gives
$E_r(T^j)=P_{r+j}$. Taking $r=0$ in (3.1) gives

\[
 p-(1+\delta)q+\delta e=0.                \tag{4.1}
\]

Taking $r=-2$, so that $P_{-2}=q\circ S$, gives

\[
 q+\delta qS=(1+\delta)e.                 \tag{4.2}
\]

For $a\in I_A$, (4.2) says

\[
 qS(a)=-\delta q(a).
\]

Since both $qS$ and $q$ are algebra maps and $\delta^2=1$, applying this
to a product $ab$, $a,b\in I_A$, in the two possible ways gives

\[
 (1+\delta)q(a)q(b)=0.                    \tag{4.3}
\]

Define

\[
 D=p-e=(1+\delta)(q-e).                   \tag{4.4}
\]

Equation (4.3) implies

\[
 D(I_A^2)=0.                              \tag{4.5}
\]

There is a complementary image bound. Since
$c:=\chi-4\in I_A$, the integral identity gives, for $a\in I_A$,

\[
 4a=-ac\in I_A^2.
\]

The cotangent map of the fourth-power word is multiplication by four, so

\[
 p(a)\equiv4a\pmod {I_A^2}.
\]

It follows that

\[
 D(I_A)\subseteq I_A^2.                   \tag{4.6}
\]

Combining (4.5) and (4.6) gives $D\circ D=0$. Moreover
$e\circ D=D\circ e=0$, and hence

\[
 [16]^\#=p\circ p=(e+D)\circ(e+D)=e.
\]

This proves the theorem.

The same formulas show that $D$ is an augmentation derivation, is killed
by $4$, has square-zero image, and factors as

\[
 I_A/I_A^2\longrightarrow I_A^2.
\]

These restrictions are substantial, but nonzero maps of this kind exist for
abstract rank-four augmented algebras. They do not imply $D=0$ without a
further Hopf-theoretic input.

## 5. Why the determinant does not finish rank four

In characteristic two, (4.4) becomes

\[
 D=(\delta-1)q\quad\text{on }I_A.
\]

It is tempting to hope that $\delta=1$ on every local--local hard fiber.
That is false, even for a commutative group scheme. Let

\[
 R=\mathbf F_2[c]/(c^3),\qquad
 A=R[x]/(x^4),
\]

and put

\[
 \Delta(x)=x\otimes1+1\otimes x+cx\otimes x.
\]

This is a Hopf algebra: the group law

\[
 F(X,Y)=X+Y+cXY
\]

is associative; directly,

\[
 F(F(X,Y),Z)=F(X,F(Y,Z))
 =X+Y+Z+c(XY+XZ+YZ)+c^2XYZ.
\]

Equivalently, $1+cF(X,Y)=(1+cX)(1+cY)$; the direct expansion is included
because $c$ is a zero-divisor. The relation $x^4=0$ is Hopf-stable. The
antipode is

\[
 S(x)=x+cx^2+c^2x^3.
\]

Its special fiber is the local--local, killed-by-two group $\alpha_4$.
Universal translation is

\[
 x\longmapsto g+(1+cg)x.
\]

On the basis $1,x,x^2,x^3$, its determinant is

\[
 \delta=(1+cg)^{1+2+3}=1+c^2g^2\ne1,
 \qquad \delta^2=1.
\]

Here $q(x)=cx^2$, so $q^2(x)=0$: the group is killed by four, as it must
be by Deligne's commutative theorem. The example shows that proving
$\delta=1$ cannot be the missing local--local argument; one must instead
prove the cancellation of $(\delta-1)q$.

It also rules out a symplectic shortcut. A right-invariant Frobenius
functional is

\[
 \lambda(1)=0,\qquad \lambda(x)=c^2,\qquad
 \lambda(x^2)=c,\qquad \lambda(x^3)=1.
\]

Its invariant perfect symmetric form satisfies
$B(x,x)=\lambda(x^2)=c\ne0$, so it is not alternating. The invariant
integral line is free of rank one; multiplying by a unit cannot make this
value vanish.

## 6. Bounded exact screen

The bounded exact script

`scripts/audit_rt_hf_triangular_family_20260710.py`

imports the already independent family checker and then constructs the
universal translation matrix for all 1,608 valid members of the triangular
Hopf family over
$\mathbf F_2[u,v]/(u^2,v^2)$. It checks (2.1), group-likeness of the
determinant, and (3.1) exactly. Its final three output lines are

```text
HF1/HF2/HF3 and RT: PASS (1608 valid triangular Hopf tuples)
local-local determinant screen: 0 nontrivial / 1088 tuples
FINITE SCREEN PASS
```

SHA-256:
`0a3c77d52148ec18064de2c63e6ae19f66e1c5061fe83cbd7ee3582a2ea02324`.
Its dependency
`scripts/audit_tight_chain_family_independent_20260710.py` has SHA-256
`9e68a0567d8209845cf6645e294270683764f9cc3ff9217e7fcebc070b5aa627`.

The zero determinant count is only a fact about that triangular family; the
example in §5 shows that it is not a universal local--local theorem.

## 7. Remaining rank-four obstruction

The new theorem packages the unresolved killed-by-four assertion as

\[
 \boxed{D=(\delta-1)q=0}
\]

in equal characteristic two. In the principal deformation setups, write
$q|_{I_A}=\phi=tB$. Then

\[
 D|_{I_A}=\phi^2=t^2B^2,
\]

whereas $S'$ asks for the one-division-stronger vanishing $tB^2=0$; the
map $\Omega$ records the top coefficient of $B^2$. This is the
valuation-tight cotangent-to-square seed isolated in
`RELATIVE_TOP_DEFECT_TRACE_RANK_PASS_2026-07-10.md` and
`TIGHT_CHAIN_HOPF_ATTACK_2026-07-10.md`.

The next proof must use multiplication--coproduct compatibility. Trace,
determinant, the Frobenius pairing, and abstract filtered linear algebra do
not by themselves kill the defect. A failure of the stronger condition
$S'$ remains only a seed; it must be lifted one more socle layer and tested
directly for $D\ne0$ before it is a counterexample.
