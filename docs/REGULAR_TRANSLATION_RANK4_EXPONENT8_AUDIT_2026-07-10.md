# Independent proof audit: the rank-four exponent-8 theorem

**Date:** 2026-07-10  
**Verdict:** green.

The audit checked every new identity over an arbitrary commutative base
ring. It found no division by two, no sign error, no misuse of the square
word as a group homomorphism, and no assumption that the group scheme is
commutative.

## 1. Translation trace convention

Choose a basis \(a_j\) of \(A\) and write

\[
 \Delta(a_j)=\sum_i a_i\otimes T_{ij}.
\]

Coassociativity, followed by multiplication of the two coefficient factors,
gives

\[
 (\operatorname{id}\otimes q)(T)=T^2.
\]

Hence

\[
 q(\chi)=\operatorname{Tr}(T^2).
\]

This is a coefficient identity. It remains valid although \(q=[2]^\#\) is
not a Hopf map when the group scheme is noncommutative.

## 2. Newton calculation

For the characteristic polynomial

\[
 X^4-\chi X^3+c_2X^2-c_3X+\delta,
\]

Newton's identity is

\[
 \operatorname{Tr}(T^2)=\chi^2-2c_2.
\]

The established integral identity gives
\(\chi^2=\varepsilon(\chi)\chi=4\chi\), and the established coefficient
formula is \(c_2=2\chi-1-\delta\). Therefore

\[
 q(\chi)=4\chi-2(2\chi-1-\delta)=2(1+\delta).
\]

## 3. Two-torsion of the defect

For \(c=\chi-4\),

\[
 q(c)=2(\delta-1).
\]

If \(a\in I=\ker\varepsilon\), then \(a\chi=0\), so \(ac=-4a\).
Applying the algebra map \(q\) yields

\[
 2(\delta-1)q(a)=-4q(a),
\]

and hence \(2(1+\delta)q(a)=0\). Since
\(D=(1+\delta)(q-e)\), this proves \(2D=0\) on \(I\), and therefore on all
of \(A\).

## 4. Eighth power

Group-likeness gives \(q(\delta)=\delta^2=1\). Therefore

\[
\begin{aligned}
 q(D(a))
 &=q(1+\delta)\,q(q(a)-e(a))\\
 &=2(p(a)-e(a))\\
 &=2D(a)=0.
\end{aligned}
\]

Since \(p=q^2=e+D\),

\[
 [8]^\#=q^3=q\circ p=q\circ(e+D)=e.
\]

The composition order causes no problem: both orders are literally \(q^3\),
and repeated squaring is the eighth-power word even in a noncommutative
group.

## 5. Scope

The theorem proves \([8]_G=e\), not \([4]_G=e\). The remaining defect is a
2-torsion square-zero conormal class. The audit accepts the finite-projective
Hopf--Frobenius identities already proved and audited in
REGULAR_TRANSLATION_RANK4_EXPONENT16_2026-07-10.md; it independently checked
the new trace and word-composition steps recorded above.
