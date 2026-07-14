# Exact type-two classification in Hilbert stratum \((1,2,2,1)\) over \(\mathbf F_2\)

## Scope and result

This note completes the finite compatible-form and carry computation left
open in Section 5 of
`STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md`.  It does not alter that
master report.  The object classified is a commutative local ring \(Q\) of
length six, residue field \(\mathbf F_2\), Hilbert function

\[
 H_Q=(1,2,2,1),
\]

and Cohen--Macaulay type two.  Isomorphisms are unital ring isomorphisms;
no choice of generators, filtration lifts, or position of \(2\) is retained.

The exact result is:

\[
 \boxed{\text{There are 27 isomorphism classes of such }Q.}
\]

Exactly 19 of the 27 occur as

\[
 Q\simeq R/\operatorname{Soc}(R)
\]

for a length-seven local Artin Gorenstein ring \(R\) with residue
\(\mathbf F_2\).  The remaining eight do not admit such a lift.

The computation and its independent arithmetic gates are in
`scripts/length6_h1221_type2_orbits_reference_20260710.py`.  The
classification is finite-field specific.  It makes no moduli claim over
other fields.

## 1. The two compatible-form orbits

Write

\[
 V=\mathfrak m/\mathfrak m^2,\qquad
 W=\mathfrak m^2/\mathfrak m^3,\qquad
 U=\mathfrak m^3,
\]

so that \(\dim(V,W,U)=(2,2,1)\).  The graded multiplication is a surjection

\[
 B:\operatorname{Sym}^2V\longrightarrow W
\]

and a bilinear map

\[
 L:V\otimes W\longrightarrow U.
\]

Associativity says that

\[
 C(v_1,v_2,v_3)=L(v_1,B(v_2,v_3))
\]

is symmetric.  Type two says that \(W\to V^*\), \(w\mapsto L(-,w)\),
has rank one.  Consequently \(C\) is a nonzero rank-one symmetric cubic.
Over \(\mathbf F_2\), after choosing \(x,y\) with
\(\ell(x)=1,\ell(y)=0\), it is \(\ell^3\).

The line \(\ker B\) must be killed by contraction against \(C\), hence has
no \(x^2\) term.  It is one of

\[
 \langle y^2\rangle,\quad \langle xy\rangle,\quad
 \langle xy+y^2\rangle.
\]

The stabilizer \(x\mapsto x+y,\ y\mapsto y\) fixes the first line and
interchanges the latter two.  Thus there are exactly two compatible
\((B,L)\)-orbits.  With bases \(a,b\) of \(W\) and \(u\) of \(U\), use:

\[
\begin{array}{c|rrrr}
 &x^2&xy&y^2&xa\\ \hline
 A&a&b&0&u\\
 B&a&0&b&u.
\end{array}
\]

All omitted graded products are zero.  As a separate finite gate, the
script enumerates all 42 surjective \(B\)'s and all 16 bilinear \(L\)'s.
Exactly 54 pairs satisfy rank one and associativity; their
\(\mathrm{GL}_2(\mathbf F_2)\times\mathrm{GL}_2(\mathbf F_2)\)-orbits have
sizes 18 and 36 and are precisely \(A\) and \(B\).

## 2. Filtered corrections and every possible carry

Choose an adapted polycyclic basis

\[
 1,x,y,a,b,u.
\]

Every element then has a unique binary expansion in these six elements.
The most general filtered products, before changing lifts, are

\[
\begin{array}{ll}
A:&x^2=a+r u,\quad xy=b+s u,\quad y^2=t u,\quad xa=u,\\[2mm]
B:&x^2=a+r u,\quad xy=s u,\quad y^2=b+t u,\quad xa=u,
\end{array}
\tag{2.1}
\]

where \((r,s,t)\in\mathbf F_2^3\); every other product of positive-degree
basis elements is zero.

The complete additive carry datum is

\[
\begin{aligned}
 2&=d_0\in\langle x,y,a,b,u\rangle,\\
 2x=d_1,\quad 2y=d_2&\in\langle a,b,u\rangle,\\
 2a=d_3,\quad 2b=d_4&\in\langle u\rangle,\qquad 2u=0.
\end{aligned}
\tag{2.2}
\]

There are

\[
 2^5\,2^3\,2^3\,2\,2=8192
\]

raw carry systems.  Together with the two compatible forms and eight
corrections, this gives 131,072 inputs.  Conversely, every ring in the
stratum admits such a basis: choose bases successively in the four
filtration layers.  Since each layer is killed by \(2\), its double lies in
the next layer, giving exactly (2.2).  Thus this is an exhaustive
parameterization, not a restricted presentation family.

For each input the script imposes:

1. descent of multiplication through every additive relation
   \(2e_i=d_i\);
2. associativity on all triples of additive generators;
3. the exact ideal powers of sizes \(32,8,2,1\);
4. socle size four and locality.

Exactly 512 adapted presentations survive.  They give 512 distinct labelled
64-element tables.

## 3. Exhausting changes of lifts and ring isomorphisms

There are exactly

\[
 |\mathrm{GL}_2(\mathbf F_2)|\,|\mathfrak m^2|^2
 =6\cdot8^2=384
\]

ordered tangent generating pairs \((X,Y)\) in each retained ring.  Every
unital isomorphism maps one such pair to one such pair.

For each pair the script chooses, functorially, the first two independent
elements among \(X^2,XY,Y^2\) as the \(W\)-basis and the first nonzero
\(V W\)-product as the \(U\)-basis.  It then records all six doubling
relations and all 21 unordered basis products.  This is a complete based
ring code.  Taking its minimum over all 384 pairs therefore gives a complete
unpointed isomorphism invariant.

The 512 minima produce 27 classes.  Every one of the 485 positive
identifications was also checked independently on all \(64^2\) addition
and multiplication pairs.  Distinct minima cannot be isomorphic, because
an isomorphism transports a tangent pair and the functorially derived
basis to a pair with the same complete code.

## 4. The 27 quotient rings

In the table, the correction column is \((r,s,t)\) from (2.1).  The carry
column lists

\[
 (2,\ 2x,\ 2y,\ 2a,\ 2b);
\]

an omitted entry is zero.  Products not specified in (2.1) are zero.
The final hexadecimal number is an explicit Gorenstein-lift witness in the
encoding of Section 5; a dash means that no lift exists.

| ID | form | \((r,s,t)\) | \((2,2x,2y,2a,2b)\) | char. | G-lift | witness |
|---:|:---:|:---:|:---|---:|:---:|:---:|
| 1 | B | 000 | \((0,0,0,0,0)\) | 2 | yes | \(\mathtt{b000}\) |
| 2 | A | 000 | \((0,0,0,0,0)\) | 2 | no | -- |
| 3 | A | 001 | \((0,0,0,0,0)\) | 2 | yes | \(\mathtt{b000}\) |
| 4 | A | 000 | \((y,b,0,0,0)\) | 4 | no | -- |
| 5 | B | 000 | \((b,0,0,0,0)\) | 4 | yes | \(\mathtt{b004}\) |
| 6 | B | 001 | \((b,0,0,0,0)\) | 4 | yes | \(\mathtt{b406}\) |
| 7 | B | 000 | \((a,u,0,0,0)\) | 4 | yes | \(\mathtt{b008}\) |
| 8 | B | 000 | \((a+b,u,0,0,0)\) | 4 | yes | \(\mathtt{b00c}\) |
| 9 | B | 100 | \((a,u,0,0,0)\) | 4 | yes | \(\mathtt{b008}\) |
| 10 | B | 100 | \((a+b,u,0,0,0)\) | 4 | yes | \(\mathtt{b00c}\) |
| 11 | A | 000 | \((b,0,0,0,0)\) | 4 | no | -- |
| 12 | A | 000 | \((a,u,0,0,0)\) | 4 | no | -- |
| 13 | A | 000 | \((a+b,u,0,0,0)\) | 4 | no | -- |
| 14 | A | 100 | \((a,u,0,0,0)\) | 4 | no | -- |
| 15 | A | 001 | \((b,0,0,0,0)\) | 4 | yes | \(\mathtt{b004}\) |
| 16 | A | 001 | \((a,u,0,0,0)\) | 4 | yes | \(\mathtt{b008}\) |
| 17 | A | 001 | \((a+b,u,0,0,0)\) | 4 | yes | \(\mathtt{be08}\) |
| 18 | B | 000 | \((u,0,0,0,0)\) | 4 | yes | \(\mathtt{b002}\) |
| 19 | A | 000 | \((u,0,0,0,0)\) | 4 | no | -- |
| 20 | A | 001 | \((u,0,0,0,0)\) | 4 | yes | \(\mathtt{b002}\) |
| 21 | B | 000 | \((y,0,b,0,0)\) | 8 | yes | \(\mathtt{b010}\) |
| 22 | B | 010 | \((y,u,b,0,0)\) | 8 | yes | \(\mathtt{b818}\) |
| 23 | A | 001 | \((y,b,u,0,0)\) | 8 | yes | \(\mathtt{b010}\) |
| 24 | B | 000 | \((x,a,0,u,0)\) | 16 | yes | \(\mathtt{b020}\) |
| 25 | B | 000 | \((x+y,a,b,u,0)\) | 16 | yes | \(\mathtt{b030}\) |
| 26 | A | 000 | \((x,a,b,u,0)\) | 16 | no | -- |
| 27 | A | 001 | \((x,a,b,u,0)\) | 16 | yes | \(\mathtt{b020}\) |

The table contains 3 equal-characteristic rings, 17 characteristic-four
rings, 3 characteristic-eight rings, and 4 characteristic-sixteen rings.
There is no characteristic 32 or 64 possibility in this Hilbert stratum.

## 5. Exact Gorenstein-liftability test

Let \(z\) denote a proposed new top socle generator.  A filtered
one-dimensional extension has six possible top corrections to

\[
 2,\ 2x,\ 2y,\ 2a,\ 2b,\ 2u
\]

and twelve possible top corrections to the products

\[
\begin{split}
 &(x^2,xy,y^2),\\
 &(xa,xb,ya,yb),\\
 &(xu,yu),\\
 &(a^2,ab,b^2).
\end{split}
\]

Thus there are 18 binary variables.  Since \(z\mathfrak m=0\) and \(2z=0\),
all descent and associativity equations in the top coefficient are affine
linear over \(\mathbf F_2\).  For every one of the 27 quotient
representatives, their matrix has rank 11 and an affine solution space of
dimension seven, hence 128 based associative top extensions.

The quotient socle is \(\langle b,u\rangle\).  Such an extension is
Gorenstein exactly when the product map

\[
 \langle b,u\rangle\longrightarrow
 \operatorname{Hom}_{\mathbf F_2}(\mathfrak m/\mathfrak m^2,\langle z\rangle)
\]

is injective.  The script evaluates this condition on every point of each
seven-dimensional affine solution space.  It finds:

* 32 Gorenstein assignments for every form-B representative;
* 64 Gorenstein assignments for every form-A representative with \(t=1\);
* no Gorenstein assignment for a form-A representative with \(t=0\).

These are counts of assignments in a fixed adapted extension basis, not
isomorphism counts of the length-seven rings.

There is also a short intrinsic explanation for the obstruction.  For form
A, modulo the new top line,

\[
 x^2=a+r u,\qquad xy=b+s u,\qquad y^2=t u,\qquad xa=u.
\]

Associativity gives \(yu=0\).  If \(\alpha\) is the coefficient of \(z\) in
\(xu\) and \(\gamma\) the coefficient in \(bx\), the product pairing of
the quotient-socle basis \(u,b\) against \(x,y\) has matrix

\[
 \begin{pmatrix}
 \alpha&0\\
 \gamma&t\alpha
 \end{pmatrix}.
\]

It can have rank two only when \(t=1\).  If \(t=0\), a nonzero lift of the
two-dimensional quotient socle remains in the socle of the extension, so
the extension cannot be Gorenstein.

For form B, \(xy=s u\) and \(y^2=b+t u\).  The corresponding matrix has the
shape

\[
 \begin{pmatrix}
 \alpha&0\\
 t\alpha&\delta
 \end{pmatrix},
\]

where the top correction \(\delta\) in \(by\) is free; taking
\(\alpha=\delta=1\) gives rank two.  The finite solver supplies compatible
carry and product corrections in every row of form B and every row of form
A with \(t=1\).

For every positive row, the script constructs the displayed witness and
checks on the resulting 128-element table:

* all associativity and distributivity identities;
* ideal-power sizes \(64,16,4,2,1\);
* socle exactly \(\{0,z\}\);
* quotient by \(\langle z\rangle\) equal to the stated 64-element \(Q\) on
  every addition and multiplication pair.

For every negative row, all affine extension solutions are exhausted and
the rank-two socle condition fails.

### Witness-mask convention

Bits \(0,\ldots,5\) of the hexadecimal witness add \(z\), respectively, to

\[
 2,\ 2x,\ 2y,\ 2a,\ 2b,\ 2u.
\]

Bits \(6,\ldots,17\) add \(z\), respectively, to

\[
 x^2,xy,y^2,xa,xb,ya,yb,xu,yu,a^2,ab,b^2.
\]

Together with the corresponding row of the quotient table, this specifies
the full 128-element lift presentation.

## 6. Reproduction and boundaries

Run:

\[
 \texttt{python3 scripts/length6\_h1221\_type2\_orbits\_reference\_20260710.py}.
\]

The script needs only the Python standard library.  Its terminal output
reports all search, orbit, extension-rank, and liftability counts.

This closes the ring-classification and Gorenstein-liftability problem in
the \((1,2,2,1)\), type-two stratum over \(\mathbf F_2\).  It does not prove
\(S'\) for the 19 relevant quotients and does not classify isomorphism
classes of their length-seven Gorenstein lifts.
