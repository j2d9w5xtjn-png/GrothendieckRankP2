# A rigidity argument for the remaining rank-four locus in Grothendieck's annihilation conjecture

## Scope

Let \(G\) be a finite locally free group scheme of degree \(4\). The handoff reduces the remaining rank-four difficulty to mixed-characteristic deformations whose closed fiber is
\[
G_k\simeq \alpha _2\times \mu _2.
\]
No commutativity of the deformation is assumed.

The main observation below eliminates that locus: every finite-flat deformation of this particular fiber is automatically commutative. Once commutativity is known, the standard norm-cycle argument shows that a finite locally free commutative group scheme of degree \(n\) is killed by \(n\).

The argument also recovers the rank-two filtration sought in the handoff.

---

## 1. The commutative case by the norm cycle

### Proposition 1
Let \(G/S\) be a finite locally free **commutative** group scheme of constant degree \(n\). Then \([n]_G=0\).

### Proof
Work affinely, with \(S=\operatorname{Spec}R\) and \(G=\operatorname{Spec}A\), where \(A\) is finite locally free of rank \(n\) over \(R\).

The determinant norm
\[
a\longmapsto \det(m_a:A\to A)
\]
is a multiplicative homogeneous polynomial law of degree \(n\). Because \(A\) is locally free, this law gives a canonical section
\[
\sigma_{G/S}:S\longrightarrow \operatorname{Sym}^n_S(G),
\]
the norm cycle of the finite flat scheme \(G/S\). It is functorial under base change and fixed by every automorphism of \(G/S\): invariance follows from
\[
m_{\varphi(a)}=\varphi\,m_a\,\varphi^{-1}
\]
for an algebra automorphism \(\varphi\) of \(A\).

Since \(G\) is commutative, the \(n\)-fold product \(G^n\to G\) is symmetric and therefore factors through a morphism
\[
\Sigma_n:\operatorname{Sym}^n_S(G)\longrightarrow G.
\]
Put \(c=\Sigma_n(\sigma_{G/S})\in G(S)\).

After any base change \(T\to S\), translation by any \(g\in G(T)\) is an automorphism of \(G_T/T\), so it fixes the norm cycle. Translating all \(n\) entries of a symmetric cycle adds \(ng\) to their sum. Hence
\[
c_T=c_T+ng.
\]
Cancellation in the group gives \(ng=0\). Taking the universal point proves \([n]_G=0\). \(\square\)

---

## 2. Flat block rigidity for finite algebras

### Lemma 2
Let \((R,\mathfrak m,k)\) be an Artin local ring, and let \(B\) be an associative unital \(R\)-algebra that is finite free of rank \(4\). Suppose
\[
B_k:=B/\mathfrak mB\simeq B_0\times B_1
\]
as \(k\)-algebras, with \(\dim_k B_0=\dim_k B_1=2\). Then \(B\) is commutative.

### Proof
Let \(\bar e=(1,0)\in B_k\). Since \(\mathfrak mB\) is nilpotent, the idempotent \(\bar e\) lifts to an idempotent \(e\in B\). Set \(f=1-e\).

The Peirce pieces
\[
eBe,\qquad eBf,\qquad fBe,\qquad fBf
\]
are images of commuting idempotent \(R\)-linear endomorphisms of the free module \(B\), hence are finite projective direct summands. Their reductions satisfy
\[
\bar e B_k\bar f=0,\qquad \bar f B_k\bar e=0
\]
because \(\bar e\) is central in \(B_k\). Thus
\[
(eBf)/\mathfrak m(eBf)=0,\qquad (fBe)/\mathfrak m(fBe)=0.
\]
Nakayama's lemma gives \(eBf=fBe=0\). Consequently \(e\) is central and
\[
B\simeq eB\times fB.
\]
Each factor is finite free of rank \(2\) over the local ring \(R\). Every unital rank-two algebra over a commutative local ring is commutative: its identity extends to a basis \((1,x)\), so all elements are polynomials of degree at most one in the single element \(x\). Therefore both factors, and hence \(B\), are commutative. \(\square\)

### General form
The same proof shows: in a finite-flat algebra over a local nilpotent thickening, a central block idempotent of the closed fiber lifts centrally. In particular, if every lifted block has rank at most two, the whole algebra is commutative.

---

## 3. Rigidity of the \(\alpha _2\times\mu _2\) locus

### Proposition 3
Let \((R,\mathfrak m,k)\) be an Artin local ring with \(\operatorname{char}k=2\). Let \(G/R\) be a finite locally free group scheme of degree \(4\), not assumed commutative. If
\[
G_k\simeq \alpha _2\times\mu _2,
\]
then \(G\) is commutative. Consequently \(G\) is killed by \(4\).

### Proof
Write \(A=\mathcal O(G)\) and take the finite-module dual
\[
H=A^\vee=\operatorname{Hom}_R(A,R).
\]
For an arbitrary finite locally free group scheme, \(H\) is an associative unital algebra: its multiplication is dual to the coproduct on \(A\). It is finite free of rank \(4\). No commutativity of \(G\) is being assumed here.

Base change commutes with finite duality, so
\[
H_k\simeq \mathcal O(G_k)^\vee.
\]
The closed fiber is commutative, and therefore its finite dual is the coordinate algebra of its Cartier dual. In characteristic two,
\[
\alpha _2^D\simeq\alpha _2,
\qquad
\mu _2^D\simeq \underline{\mathbf Z/2\mathbf Z}.
\]
Hence
\[
H_k
\simeq
\mathcal O\!\left(\alpha _2\times\underline{\mathbf Z/2\mathbf Z}\right)
\simeq
k[u]/(u^2)\times k[u]/(u^2).
\]
Lemma 2 applies and shows that \(H\) is commutative.

Multiplication on \(H=A^\vee\) is dual to comultiplication on \(A\). Since \(A\) is finite projective, commutativity of \(H\) is equivalent to cocommutativity of the coproduct on \(A\), which is exactly commutativity of the group scheme \(G\). Proposition 1 now gives \([4]_G=0\). \(\square\)

### Why this is stronger than a first-order calculation
The proof is independent of the length of \(R\), of the ramification of \(2\), and of any socle-divisibility condition. It rules out all noncommutative finite-flat deformations of the indicated closed fiber at once.

---

## 4. The rank-two filtration also lifts

After Proposition 3, \(G\) is commutative and its Cartier dual is \(G^D=\operatorname{Spec}H\). The central idempotent constructed in Lemma 2 splits the underlying finite flat scheme \(G^D\) into two open-and-closed pieces of rank two. The piece containing the identity is a finite locally free subgroup \(K\subset G^D\) of rank two. Its quotient has rank two. Cartier duality gives an exact sequence
\[
0\longrightarrow (G^D/K)^D
\longrightarrow G
\longrightarrow K^D
\longrightarrow 0,
\]
whose kernel and quotient both have rank two.

Thus the filtration sought in the handoff exists on this locus; it is obtained only after proving commutativity, rather than by solving the original subgroup-lifting equations directly.

---

## 5. A useful square-zero check

### Lemma 4
Let \(R\) be a ring, \(J\subset R\) an ideal with \(J^2=0\), and \(X=\operatorname{Spec}A\) an affine pointed \(R\)-scheme with \(A\) flat over \(R\). Let \(I\) be its augmentation ideal. If a pointed endomorphism \(f:X\to X\) becomes the constant identity map modulo \(J\), then \(f\circ f\) is the constant identity map.

### Proof
The point splits \(A=R\oplus I\). Since \(f\) is pointed and trivial modulo \(J\),
\[
f^*(I)\subseteq I\cap JA=JI.
\]
Therefore
\[
(f\circ f)^*(I)=f^*(f^*(I))\subseteq f^*(JI)
=Jf^*(I)\subseteq J^2I=0.
\]
\(\square\)

Applied to the squaring map, this says that every square-zero deformation of an exponent-two group is automatically of exponent at most four, without any commutativity hypothesis. It is a useful independent check on the smallest Artin cases.

---

## 6. Consequence for the handoff

The handoff reports that, after the minimal-counterexample and special-fiber reductions, the only unresolved rank-four branch is the mixed-characteristic deformation of \(\alpha _2\times\mu _2\). Proposition 3 closes exactly that branch and bypasses the condition \(S'\).

Therefore:

> **Conditional rank-four conclusion.** If the handoff's prior case-exhaustion proposition and its proofs for the other special-fiber types are correct, then every finite locally free group scheme of degree four is killed by four.

The new argument itself is unconditional. What remains before calling the full rank-four theorem publication-ready is an audit of only the pre-existing case-exhaustion step and the already-claimed proofs of the other fibers; no further deformation calculation is needed at \(\alpha _2\times\mu _2\).

---

## 7. Broader structural lesson

For a finite locally free group scheme \(G\), the algebra \(\mathcal O(G)^\vee\) is often more useful than attempting Cartier duality before commutativity is known. Over an Artin local base, flatness prevents distinct central blocks of its closed fiber from coupling through nilpotent off-diagonal Peirce terms. Thus representation-theoretic block decompositions of the closed-fiber dual algebra can force commutativity of the entire deformation.

For higher degree, a productive induction target is therefore:

1. decompose the closed-fiber dual algebra into central blocks;
2. lift those blocks centrally by flat Peirce rigidity;
3. handle each block separately;
4. use the norm-cycle argument on blocks whose deformation is forced commutative, and subgroup/quotient induction on the remaining blocks.
