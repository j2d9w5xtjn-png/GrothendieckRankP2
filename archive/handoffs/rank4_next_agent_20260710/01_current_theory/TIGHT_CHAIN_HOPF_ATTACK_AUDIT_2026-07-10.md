# Independent audit of the tight-chain Hopf attack

**Date:** 2026-07-10  
**Source audited:** `TIGHT_CHAIN_HOPF_ATTACK_2026-07-10.md`  
**Verdict:** **PASS after precision edits.** The square-ideal criterion, the
explicit nonprincipal Hopf model, its exact \(S'\) witnesses, the triangular
family exclusion, and the scoped monogenic principal exclusion are correct
under their stated hypotheses. None of them proves the general rank-four
case, and the explicit model is not a counterexample.

This was an independent mathematical audit, not merely a rerun of the
source checker. I rederived the identities below and also ran a separate
bounded exhaustive checker.

## 1. Proposition 2.1

The proof is correct.

For \(g\in I\), the counit splitting \(A=R1\oplus I\) gives

\[
 \Delta(g)=g\otimes1+1\otimes g+w(g),\qquad w(g)\in I\otimes I.
\]

In characteristic two, \(\varphi(g)=\mu w(g)\in I^2\). Killedness of the
special fiber gives \(\varphi(I)\subseteq\mathfrak mI\). If
\(I=I^2\oplus C\), then

\[
 \mathfrak mI\cap I^2=\mathfrak mI^2,
\]

so \(\varphi(I)\subseteq\mathfrak mI^2\). Commutativity is used exactly
where claimed: it makes \(\mu\Delta\) an algebra endomorphism. Hence

\[
 \varphi(I^2)\subseteq\varphi(I)^2\subseteq I^4=0,
\]

and \(I^2\subseteq\ker\varphi\cap I\). This proves
\(\varphi(I)\subseteq\mathfrak m(\ker\varphi\cap I)\).

The consequences for \(R[T]/T^4\) and
\(R[x,y]/(x^2,y^2)\) are correct for their standard augmentations. The
source now states that augmentation convention explicitly. The dual formula

\[
 \operatorname{Prim}(A^\vee)
 =\{f:f(1)=0,\ f(I^2)=0\}
 \simeq\operatorname{Hom}_R(I/I^2,R)
\]

is also correct. The source appropriately says that non-saturation *can*
manifest as non-saturation of primitives; a converse over an arbitrary
nonreduced local ring would have been too strong.

## 2. Explicit model over \(\mathbf F_2[u,v]/(u^2,v^2)\)

Put \(c=uv\), \(a=u+c\), and

\[
 X^2=aX,\qquad Y^2=0,\qquad YX=XY+cY,
 \qquad Z=XY.
\]

### Algebra

The two relevant Diamond overlaps close:

* the two reductions of \(YX^2\) differ by
  \(c(a+c)Y=cuY=0\);
* both reductions of \(Y^2X\) are zero.

The normal words are therefore \(1,X,Y,Z\), and direct reduction gives

\[
 XZ=aZ,\quad ZX=(a+c)Z=uZ,\quad
 YZ=ZY=Z^2=0.
\]

Thus the algebra is free of rank four.

### Coalgebra and antipode

For

\[
 \Delta X=X\otimes1+1\otimes X,qquad
 \Delta Y=Y\otimes1+1\otimes Y+vX\otimes X,
\]

multiplication gives

\[
 \Delta Z=Z\otimes1+1\otimes Z+X\otimes Y+Y\otimes X.
\]

The two omitted-looking terms both have coefficient \(va=c\) and cancel.
The defining relations are stable because the only residual coefficients
are \(cv=0\), \(v^2=0\), and \(c(a+c)=0\). Coassociativity of the extra
term is the elementary cocycle identity for \(X\otimes X\).

The displayed antipode

\[
 S(X)=X,qquad S(Y)=Y+cX,qquad S(Z)=Z+cY
\]

satisfies both convolution identities on all four basis elements. Thus
\(D\) is genuinely a finite free cocommutative Hopf algebra.

### Sweedler square, dual algebra, and \(S'\)

Direct multiplication of each coproduct gives

\[
 P_2(X)=0,qquad P_2(Y)=cX,qquad P_2(Z)=cY,qquad P_2^2=0.
\]

Dualizing gives exactly

\[
 x^2=vy,\quad y^2=0,\quad xy=z,\quad xz=yz=z^2=0
\]

and the three coproduct formulas in the source. In particular

\[
 I^2=Rz+(v)y
\]

is not a direct summand. Reduction modulo \((u,v)\) gives the Hopf algebra
of \(\alpha_2^2\), while the total group is noncommutative because the
coordinate coproduct is not cocommutative.

The doubling map is

\[
 \varphi(x)=cy,qquad\varphi(y)=cz,qquad\varphi(z)=0.
\]

The source witnesses are exact:

\[
 cy=v(uy),\quad \varphi(uy)=uc\,z=0;
 \qquad
 cz=u(vz),\quad \varphi(vz)=0.
\]

They prove the full submodule membership for all of \(I\), not merely
killedness. Dividing both arrows by the socle generator \(c\) instead is
not the \(S'\) test because \((c)=\mathfrak m^2\ne\mathfrak m\).

## 3. Triangular family

For

\[
 X^2=aX,\quad Y^2=dY,\quad YX=XY+cY,
 \quad
 \Delta Y=Y\otimes1+1\otimes Y+sX\otimes X,
\]

the four stated equations are exactly the needed ones:

* the \(YX^2\) overlap contributes \(c(a+c)Y\);
* the \(Y^2X\) overlap contributes \(cdY\);
* Hopf stability of the commutator contributes \(csX\otimes X\);
* after \(cs=0\), stability of \(Y^2-dY\) contributes
  \(s(d+sa^2)X\otimes X\).

They are sufficient for the normal basis \(1,X,Y,Z\), multiplicativity,
and coassociativity. The source now records the missing explicit antipode:

\[
 S(X)=X,qquad S(Y)=Y+saX,qquad
 S(Z)=Z+cY+sa^2X.
\]

Writing \(h=a+c\), one has \(ch=cs=0\), \(sa=sh\), and

\[
 \varphi(x)=shy,qquad\varphi(y)=cz,qquad\varphi(z)=0.
\]

The source originally displayed witnesses only under the sufficient
condition \(c,s\in\mathfrak m\), while its summary claimed the whole
killed-special-fiber family. The repaired proof is complete. Killedness of
the special fiber is equivalent to \(c,sh\in\mathfrak m\):

* if \(s\in\mathfrak m\), use
  \(shy=s(hy)\), \(\varphi(hy)=hcz=0\), and \(cz=c(z)\);
* if \(s\) is a unit, \(cs=0\) gives \(c=0\), while
  \(sh\in\mathfrak m\) gives \(h\in\mathfrak m\); then
  \(shy=h(sy)\) and \(\varphi(sy)=0\).

Thus every killed-special-fiber member of this triangular family satisfies
\(S'\). On a finite principal chain ring, \(c=\pi u\) with \(u\) a unit
puts \(s,h\in\operatorname{ann}(\pi)\), the square-zero socle, so
\(sh=0\). The claimed principal two-edge exclusion follows.

## 4. Minimal monogenic principal ansatz

This exclusion is correct but deliberately narrow. Its hypotheses are:

* equal characteristic \(R'=k[\pi]/\pi^{N+1}\), \(N\ge5\);
* the monic algebra relation
  \(T^4=\pi^{N-2}(aT+bT^2+dT^3)\);
* the exact form
  \(\varphi(T)=\pi(\beta T^2+\gamma T^3)\), with no \(T\)-component;
* a killed-by-two Hopf special fiber of \(t^4\) shape; and
* \(S'\) on the truncation modulo \(\pi^N\), so the audited top-defect
  product lemma is available.

Let \(q=\pi^{N-2}\). Since \(N\ge5\), \(q^2=0\). In the fourth power of
the reduced coproduct, every tensor monomial contains one factor of \(q\)
from each tensor factor and hence a factor \(q^2\). Therefore

\[
 q(\Delta r-r\otimes1-1\otimes r)=0.
\]

The monic presentation makes \(A\otimes A\) free. Since
\(\operatorname{ann}(q)=(\pi^3)\), reduction modulo \(\pi\) makes
\(r_0\) primitive. Lemma 12.3.1 of `THEORY_order4.md` then gives

\[
 d_0=a_0c_1,qquad a_0c_4=0.
\]

The algebra calculation is also correct. Modulo \(\pi^N\),

\[
 B(T^2)=\pi^{N-1}
 (\beta_0^2r_0+\gamma_0^2a_0T^3),
 \qquad B(T^3)=0.
\]

If \(\beta_0\ne0\), the only diagonal coefficient is
\(\pi^{N-1}\beta_0^2b_0\). The exact Hopf trace identity forces
\(b_0=0\). Moreover

\[
 \Omega(T^2)=\beta_0^2a_0
 (\beta_0T^2+\gamma_0T^3).
\]

The product-killing theorem gives \(\Omega(T^2)=0\), and its \(T^2\)
coefficient forces \(a_0=0\). Primitivity then gives \(d_0=0\), so
\(r_0=0\) and the critical carry disappears. If \(\beta_0=0\), then
\(\beta\in\pi R'\), so

\[
 B^2(T)=\beta B(T^2)+\gamma B(T^3)=0\pmod {\pi^N}.
\]

Thus neither branch realizes the tight chain within this ansatz.

The conclusion must not be enlarged to arbitrary principal lifts: lower
matrix layers, a \(T\)-component, a nonmonogenic multiplication, or a more
general coproduct are outside the argument. The trace and product-defect
inputs are dependencies proved and audited elsewhere; this audit checked
their use here, not a new proof of those results.

## 5. Bounded computational checks

The source checker
`scripts/audit_tight_chain_hopf_model_20260710.py` exhausts all basis
identities for the explicit model: 64 associativity triples, all 16
multiplicativity pairs, coassociativity, counits, both antipode
convolutions, the Sweedler square, the special fiber, and the two \(S'\)
witnesses. It prints `AUDIT PASS`.

The independent checker
`scripts/audit_tight_chain_family_independent_20260710.py` does not import
the source checker. It produced:

```text
triangular family: PASS (1608 valid parameter tuples; 1536 killed-fiber tuples)
monogenic N=5 formulas: PASS (32 residue tuples)
INDEPENDENT AUDIT PASS
```

The first line exhausts all \((a,c,d,s)\) in
\(\mathbf F_2[u,v]/(u^2,v^2)\) satisfying (4.2)--(4.3), checking the
algebra, bialgebra, antipode, and \(P_2\) formulas, plus the case-split
\(S'\) witnesses whenever the special fiber is killed by two. The second
line exhausts all residue coefficients in the first monogenic depth
\(N=5\) and checks (5.5) and the displayed formula for \(B^2(T^2)\).

These finite checks corroborate the proofs; they are not substitutes for
the arbitrary-ring arguments.

## 6. Calibrated conclusion

No counterexample was found in the audited scope. More positively, the
note rigorously excludes three broad-looking but structurally restricted
mechanisms:

1. fixed standard square-zero fourth-power coordinate algebras with
   split \(I^2\);
2. the full killed-special-fiber triangular distribution family; and
3. the stated minimal monogenic principal carry.

The explicit nonprincipal model is valuable evidence that primitive
non-saturation and an apparent coefficientwise three-step chain really can
occur over a ramified/nonprincipal base. Its exact kernel factorizations
also show why that phenomenon alone is insufficient. A genuine survivor
would still need coupled lower multiplication/coproduct layers or a
nontriangular annihilator pattern. This is a substantive narrowing, not a
resolution of Grothendieck's conjecture.
