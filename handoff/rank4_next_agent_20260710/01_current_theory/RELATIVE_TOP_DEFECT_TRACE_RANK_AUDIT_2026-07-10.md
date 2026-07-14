# Audit of the relative top-defect trace/rank pass

**Date:** 2026-07-10  
**Audited file:** `RELATIVE_TOP_DEFECT_TRACE_RANK_PASS_2026-07-10.md`  
**Verdict:** **GREEN, with the stated scope.**  Propositions 2.1 and 3.1 and
Lemmas 4.1 and 4.3 are correct after the precision edits recorded below.  I
found no counterexample to any of them.  They do not prove persistence of the
determinantal rank-one condition, which remains the substantive open step.

## 1. Top-lift invariance

For $N\ge2$, if two normalized top lifts differ by the homogeneous
first-order doubling symbol $\chi$, then

\[
 B_2-B_1=t^{N-1}\widetilde\chi\pmod {t^N}
\]

and hence

\[
 B_2^2-B_1^2
 =t^{N-1}(B_0\chi+\chi B_0)\pmod {t^N},
 \qquad B_0=B_i\bmod t.
\]

The quadratic term has valuation at least $2N-2\ge N$.  In equal
characteristic, $B_0$ is the first-order symbol of the common truncation,
and the audited pairwise-nilpotence theorem gives both composites zero.  For
$N=1$, each lift is itself first order and its divided symbol squares to
zero.  Thus the top coefficient of $B_i^2$, namely $\Omega$, is independent
of the valid top lift.

This conclusion is limited to the standing rank-four fiber hypotheses,
including the perfect-residue-field proviso used for the $xy$ classification.
It is not an unconditional mixed-characteristic statement: there one still
needs $B_0\chi+\chi B_0=0$.  It also asserts invariance only of $\Omega$
(up to conjugacy under a changed identification), not of the full divided
operator or of any particular minor.  The audited note now uses $B_0$ rather
than overloading $\bar B$ at this point.

## 2. Exact trace identity over a local ring

The ring-level proof is sound and does not rely on extending a field-level
indicator formula.  For $K=A^\vee$, Pareigis's finite-projective Hopf-module
theorem and $\operatorname{Pic}(R)=0$ provide an integral Frobenius functional
$\psi$ and a left norm $N$ with $\psi(N)=1$.  Kadison--Stolin, Proposition
3.8, gives dual bases

\[
 N_{(2)},\qquad \bar S(N_{(1)}),\qquad \bar S=S^{-1}.
\]

Consequently

\[
 \operatorname{Tr}(F)
 =\sum\psi\bigl(\bar S(N_{(1)})F(N_{(2)})\bigr)
\]

for every finite-projective endomorphism $F$.  Since $K$ is cocommutative,
$S^{-1}=S$, and for $F=P_2$ the antipode identity gives

\[
 \sum S(N_{(1)})N_{(2)}\otimes N_{(3)}=1\otimes N.
\]

Therefore $\operatorname{Tr}(P_2)=\psi(N)=1$ exactly in $R$, and duality
gives $\operatorname{Tr}_A([2]^\#)=1$.  The citation was sharpened to
Pareigis Proposition 3, Theorem 1, Corollary 1 (with Theorem 3 identifying
the integral line), and Kadison--Stolin Proposition 3.8.  The resulting
$\operatorname{Tr}(\bar B)=0$ calculation is valid in mixed as well as equal
characteristic once the bialgebra has an antipode; the nilpotent lifting
argument supplies that antipode in the present setting.

The stronger formula
$a\mapsto\operatorname{Tr}(R_a\circ P_2)=\psi(Na)$ is also correct: right
multiplication on the left-integral line defines the modular character.

## 3. Determinantal lemmas

Lemma 4.1 is the entrywise identity

\[
 (C^2-(\operatorname{tr}C)C)_{ij}
 =\sum_k(c_{ik}c_{kj}-c_{ij}c_{kk}),
\]

a sum of $2\times2$ minors.  It is valid over every commutative ring.

Lemma 4.3 is also correct.  A unit entry supplies $v$ with $u=Cv$
unimodular.  From $C^2=0$, $Cu=0$.  The patched proof explicitly constructs
functionals splitting $Su\oplus Sv$ from $S^3$.  The induced differential on
the rank-one quotient has scalar equal to $\operatorname{tr}C$, hence zero;
one more application of $C^2=0$ shows $\operatorname{im}C\subset Su$, so all
minors vanish.

Both extra hypotheses in Lemma 4.3 are genuinely load-bearing:

* without trace zero, the $N+tM$ example already in the audited note has a
  unit entry, is square-zero, and has a nonzero minor;
* without a unit entry, over
  $S=\mathbf F_2[x,y]/(x^2,y^2)$ the matrix
  $\operatorname{diag}(x,y,x+y)$ is square-zero and traceless but has minor
  $xy\ne0$.

The second example has been added to the audited note.  It confirms that the
zero-leading-symbol branch cannot be folded into Lemma 4.3 by abstract
linear algebra.

As a finite sanity check, I exhaustively scanned all $4^9$ matrices in
$M_3(\mathbf F_2[\epsilon]/\epsilon^2)$.  Exactly 336 had a unit entry,
square zero, and trace zero; none had a nonzero $2\times2$ minor.  This is
only a counterexample screen, not part of the proof.

## 4. Calibrated conclusion

The audit establishes a real reduction, not the conjecture.  On a principal
base, trace zero is automatic; determinantal rank at most one implies $S'$;
and, when the leading symbol is nonzero, it is equivalent to $S'$.  What is
still missing is a Hopf-theoretic reason that all top minors vanish.  The
tight three-step chain in the audited note remains a valid abstract
counterexample mechanism, and the present arguments do not rule out its
realization over a sufficiently complicated or ramified Hopf base.
