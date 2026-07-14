# Independent audit: a mixed-characteristic rank-four counterexample

**Date:** 2026-07-10  
**Verdict:** confirmed by a second source path and a second filtered-elimination
implementation.  The universal `alpha2^2` cubic jet gives a finite flat
rank-four group scheme which is not killed by four.  Thus Grothendieck's
killed-by-order conjecture over arbitrary bases is false.

## 1. Counterexample statement

Let

\[
 P=\mathbf Z_{(2)}[p_0,\ldots,p_{44}],\qquad
 \mathfrak q=(2,p_0,\ldots,p_{44}).
\]

On the free module

\[
 A_P=P\{1,e_1,e_2,e_3\},
\]

use the 18 multiplication and 27 reduced-coproduct variables in
`m2/universal_local_rank4.m2`, branch `a2a2`.  At the closed point, the
multiplication is

\[
 e_1e_2=e_3
\]

with every other product of two augmentation-basis elements zero, and

\[
 \begin{aligned}
 \Delta(e_1)&=e_1\otimes1+1\otimes e_1,\\
 \Delta(e_2)&=e_2\otimes1+1\otimes e_2,\\
 \Delta(e_3)&=e_3\otimes1+1\otimes e_3
              +e_1\otimes e_2+e_2\otimes e_1.
 \end{aligned}
\]

This is the coordinate Hopf algebra of `alpha2^2` over `F2`.  Let
`I` be the ideal of the 189 integral associativity, coproduct-multiplicativity,
and coassociativity equations, and put

\[
 B=P/(I+\mathfrak q^4).
\]

Then `A_B` is a finite free rank-four Hopf algebra over the finite Artin local
ring `B`, and

\[
 [4]^\#\ne\eta\varepsilon.
\]

More precisely, if target `3(i-1)+(r-1)` is the coefficient of `e_r` in
`[4]^#(e_i)`, targets 2 and 5 are nonzero in `B`.  Their degree-three classes
have the respective canonical representatives

\[
 \begin{aligned}
 m_{11}^{1}c_{111}(c_{112}+c_{121}),\\
 m_{11}^{1}c_{111}(c_{212}+c_{221}).
 \end{aligned}
\]

## 2. Independence from the first auditor

The new checker is

```text
scripts/independent_audit_mixed_a2a2_export.py
```

It does **not** import `scripts/audit_universal_rank4_quadratic.py`.  It parses
the exact integer polynomials exported directly by Macaulay2, stores its own
sparse integer polynomials, implements its own high-pivot elimination while
carrying exact integer residuals, and constructs and checks its own dual
functionals.

An additional one-off source comparison parsed the Macaulay2 export and the
first Python reconstruction separately.  Through all terms relevant modulo
`q^4` there were zero coefficient differences:

| objects | count | differing objects | canonical payload SHA-256 |
|---|---:|---:|---|
| equations | 189 | 0 | `44d1aba916bf3d92b33aa80a172c8844c68b37e08ccfc2b88be364c45b5dab35` |
| targets | 9 | 0 | `932b164803910084778552d82619d7c929ccec252cec8164defccbc4a25b87f5` |

The comparison retained exact integer coefficients for every monomial of
ordinary variable degree at most three.  Higher variable-degree terms lie in
`q^4` automatically.  Thus coefficients such as 2, 4, 6, 8, 12, and 16 were
compared before any initial-form reduction.

## 3. The mixed `q`-degree convention

For an integer term `c p^alpha`, the checker uses

\[
 \operatorname{ord}_{\mathfrak q}(c p^\alpha)
   =v_2(c)+|\alpha|.
\]

Its degree-`d` initial form is

\[
 \tau^{v_2(c)}p^\alpha
   \in \mathbf F_2[\tau,p_0,\ldots,p_{44}]_d,
 \qquad \tau=\operatorname{in}(2).
\]

Integer polynomials are added before `v_2` is taken.  Hence every 2-adic carry
is retained.  In particular, `tau` is a genuine forty-sixth degree-one
generator; it is not treated as an independent parameter in the exact ring.

The filtered recursion is the following general lemma.  Suppose exact ideal
elements `C_d` span the degree-`d` initials of `I`.  Row-reduce their initials,
retaining exact pivot lifts `G_d` and the exact residual from every constant
`F2` relation.  Then degree `d+1` is spanned by

\[
 2G_d,\quad p_jG_d\ (0\le j<45),\quad
 \text{all exact constant-relation residuals}.
\]

Indeed, reduce the coefficients of an arbitrary ideal combination modulo
`q`: its constant residues give precisely a constant relation, while its
positive-order parts are linear combinations of `2,p_0,...,p_44` times the
preceding initial space.  This proves exhaustiveness inductively, not merely
generation of a convenient subset.

## 4. Independent ranks and dual certificates

The checker obtains:

```text
linear columns/rank/relations 46 31 158
quadratic columns/rank/relations 1081 974 610
cubic columns/candidates/nonzero/rank 17296 45414 45402 16787
```

The 45,414 cubic candidates are exactly

\[
 46\cdot974+610.
\]

The first auditor used different exact pivot lifts and therefore had 45,400
nonzero candidates rather than 45,402; the candidate span and its rank are
the invariants.  Both implementations give rank 16,787 and the same canonical
dual certificates.

For target 2, the independent checker gives a dual of support 38 and SHA-256

```text
1d8738d672e98ddd690657b14821e52e2d2445551a9e9d5b556440d66eac527f
```

For target 5, it gives a dual of support 38 and SHA-256

```text
505bbba3120840f5644bf5b0b4ec0fdedf0861cd702fdddb6240fdad84f11dbd
```

For each target, the checker regenerates all 45,414 cubic ideal candidates
and verifies that the displayed dual annihilates **every candidate**, including
the zero candidates, while taking value one on the target residual.  It also
checks that the other seven targets reduce to zero modulo `I+q^4`.

Thus the two nonmembership statements are exact linear certificates in
`q^3/q^4`; they are not Groebner timeouts or heuristic normal forms.

## 5. Why this is a Hopf counterexample

First, every generator of `I` lies in `q`, because the pinned closed fiber is
a bialgebra.  Since

\[
 I+\mathfrak q^4\subseteq\mathfrak q,
 \qquad
 \sqrt{I+\mathfrak q^4}=\mathfrak q,
\]

`B` is local with residue field `F2`.  It is Artinian and finite because
`q^4=0` in `B`; in particular `16=0` and only variable monomials of degree at
most three remain, with the corresponding 2-power coefficient bounds.

Second, the 189 equations give an associative unital commutative algebra, a
counital coassociative coproduct, and multiplicativity of that coproduct.
The underlying module remains the explicitly free module `B^4`.  Hence `A_B`
is a finite free rank-four bialgebra.

Third, let `C=End_B(A_B)` with convolution multiplication.  The identity
endomorphism reduces modulo the maximal ideal to a convolution unit because
the closed fiber is the Hopf algebra of `alpha2^2`.  A unit modulo the maximal
ideal of the finite `B`-algebra `C` lifts to a unit: equivalently, lift the
closed-fiber inverse and invert the resulting `1+mC` error by a finite geometric
series.  Its convolution inverse is an antipode.  Therefore `A_B` is Hopf.

Finally, `[2]^#=m\circ\Delta` and `[4]^#=([2]^#)^2`.  A certified nonzero
augmentation coordinate of `[4]^#` means `[4]^#` is not `eta epsilon`.
Consequently `Spec(A_B)` is a finite locally free group scheme of order four
which is not killed by four.

## 6. Exact reproduction

Generate the branch-0 integral export.  This is only chart construction and
printing; it launches no Groebner basis computation and took about five seconds
on the audit Mac.

```bash
env RANK4_BRANCH=0 \
    RANK4_INTEGRAL=1 \
    RANK4_EXPORT_POLYS=1 \
    M2 --script m2/universal_local_rank4.m2 \
    > /tmp/m2_rank4_export.txt
```

Then run the independent checker:

```bash
python3 -m py_compile scripts/independent_audit_mixed_a2a2_export.py
python3 scripts/independent_audit_mixed_a2a2_export.py \
    /tmp/m2_rank4_export.txt
```

The decisive output is:

```text
linear columns/rank/relations 46 31 158
quadratic columns/rank/relations 1081 974 610
cubic columns/candidates/nonzero/rank 17296 45414 45402 16787
target 0: member modulo q^4
target 1: member modulo q^4
target 2: NONMEMBER; remainder=[(0, 18, 19), (0, 18, 21)]; dual_support=38; rows_checked=45414; dual_sha256=1d8738d672e98ddd690657b14821e52e2d2445551a9e9d5b556440d66eac527f
target 3: member modulo q^4
target 4: member modulo q^4
target 5: NONMEMBER; remainder=[(0, 18, 28), (0, 18, 30)]; dual_support=38; rows_checked=45414; dual_sha256=505bbba3120840f5644bf5b0b4ec0fdedf0861cd702fdddb6240fdad84f11dbd
target 6: member modulo q^4
target 7: member modulo q^4
target 8: member modulo q^4
```

The tuple indices use `p_0=m11_1`, `p_18=c111`, `p_19=c112`,
`p_21=c121`, `p_28=c212`, and `p_30=c221`.

## 7. Frozen hashes

```text
43d0be4f325a599a530bd87cc3653b119fae23a9ad61a2cb67b24ad975f32522  scripts/independent_audit_mixed_a2a2_export.py
ad55eab4fa40aa31cd39fcccbbfc7f6f97fd2f2aa01398ffc8c3cc7cf3546b89  m2/universal_local_rank4.m2
73c7befdb01a23c8622dc58d61fc77bc78c8566437b868e1507905b070f2207f  scripts/audit_universal_rank4_quadratic.py
686c35c91b74af2a414dd119024411266fb0056865dd1d19676c20485f93b6b7  /tmp/m2_rank4_export.txt
```

The `/tmp` export hash includes the Macaulay2 gate preamble as well as the 189
equation and nine target lines.
