# Structure theory for Grothendieck's question at order 4 (session 3)

**Date:** 2026-07-08 (session 3). Companion to `REPORT_order4.md` (computational
results) and `HANDOFF_NEXT.md` (operations). This file contains **proofs**, not
computations; every lemma here is proved in full unless explicitly flagged
`[FLAG]`. The guiding idea (suggested by the user this session) is to compare the
square-zero deformation theory of commutative and noncommutative group schemes.
That idea is correct, and it is made precise in Theorem 5.1 / Corollary 5.3 below.

**Summary of what this file establishes.**

1. (§3) Grothendieck's question for order $n$ over **arbitrary base schemes**
   reduces to Artin local rings with **finite residue field**. Consequently
   imperfect residue fields never need to be considered — this removes standing
   risk G.4 of the handoff.
2. (§2, §4) Over an Artin local base with residue characteristic 2, in the branch
   "fiber killed by 2" (the only open branch after the connected–étale and Schoof
   reductions), the failure of $[4]=e$ across a square-zero extension is a single
   *point-derivation obstruction* $d$ living on the special fiber, and it vanishes
   for free unless the extension ideal sits inside $\mathfrak m^2$ (this re-proves
   the relevant case of Schoof's $m^p=pm=0$ theorem in three lines, and settles
   every "first-order" direction).
3. (§5) **Rigidity theorem:** $d$ does not depend on the chosen lift. Hence a
   noncommutative deformation is killed by 4 **as soon as any deformation killed
   by 4 exists** — in particular as soon as a commutative/cocommutative one does
   (Deligne). This is the precise sense in which "noncommutative deformation
   theory = commutative deformation theory" for this problem.
4. (§6) The obstruction is computed by the **associated graded of the squaring
   map**: $d = \sum_{\alpha,\beta} (t_\alpha t_\beta)\otimes \psi_\beta\psi_\alpha$.
   All computational results (Theorems A, B, E of the report) become instances of
   the *polarized identities* $\psi_\alpha\psi_\beta+\psi_\beta\psi_\alpha = 0$,
   $\psi_\alpha^2 = 0$. The new script `len3gen.m2` proves them universally in
   embedding dimension $\le 2$, equal characteristic (all $\mathbb F_2$-algebras
   $k$ at once).
5. (§7) A single clean statement (**S′: kernel factorization of the squaring
   map**) implies, by the socle induction, the full order-4 conjecture over all
   bases. S′ is proved here at length $\le 2$ and is equivalent to the
   certificate identity $\psi^2=0$ there; its propagation is the one remaining
   theoretical gap, stated precisely as Open Lemma 7.4.
6. (§8) Every rank-4 bialgebra with fiber killed by 2 over an Artin local ring is
   **automatically a Hopf algebra** (antipode for free; on the fiber $S=\mathrm{id}$).
   So the bialgebra-level computations lose no generality *and* gain no generality:
   they are exactly group-scheme statements in this branch.

Throughout: $R$ is a commutative ring, $A$ a **bialgebra** over $R$ which is a
finite locally free (usually free) $R$-module: $A$ is a commutative $R$-algebra
with multiplication $\mu$, unit $1$, and carries a coassociative counital
comultiplication $\Delta: A\to A\otimes_R A$ which is a map of $R$-algebras, with
counit $\varepsilon: A \to R$. We write $I = \ker\varepsilon$ (augmentation
ideal), so $A = R\cdot 1 \oplus I$ as $R$-modules. Over a local $R$, $I$ is free.
The $n$-th (pointwise!) power map is
$[n]^\# = \mu^{(n)}\circ\Delta^{(n)}: A\to A$; it is the map on coordinate rings
of $g\mapsto g^n$, hence an $R$-**algebra endomorphism** of the commutative
algebra $A$ (even when the group law is noncommutative, i.e. $\Delta$ is not
cocommutative), and $[4]^\# = [2]^\#\circ[2]^\#$ (powers of one element).
We abbreviate $\varphi := [2]^\# = \mu\circ\Delta$. "Killed by $n$" means
$[n]^\# = \eta\varepsilon$ (equivalently $[n]^\#(I)=0$), where
$\eta: R \to A$ is the unit. Counitality gives $\varepsilon\circ[n]^\# =
\varepsilon$ for all $n$.

---

## 1. Two elementary but load-bearing lemmas

**Lemma 1.1 (Sweedler normal form).** For $g\in I$:
$\Delta g = g\otimes 1 + 1\otimes g + w$ with $w \in I\otimes_R I$.

*Proof.* Decompose $\Delta g$ in $A\otimes A = R(1{\otimes}1)\oplus I{\otimes}1
\oplus 1{\otimes}I\oplus I{\otimes}I$ as $r(1\otimes 1) + a\otimes 1 + 1\otimes b
+ w$. Applying $\varepsilon\otimes\mathrm{id}$ and the counit axiom gives
$r + b = g$ in $R\oplus I$, so $r = 0$, $b = g$; symmetrically $a = g$. $\square$

**Lemma 1.2 (linear term of the power map).** For every $n\ge 1$, every base
ring $R$, every finite free bialgebra $A/R$, and every $g \in I$:
$$[n]^\#(g) \equiv n\,g \pmod{I^2}.$$

*Proof.* By Lemma 1.1 and induction on $n$, $\Delta^{(n)}(g) = \sum_{i=1}^n
1\otimes\cdots\otimes g\otimes\cdots\otimes 1 + (\text{terms in the span of
tensors with at least two factors in } I)$: applying $\Delta$ to a slot equal to
$1$ gives $1\otimes 1$; applying it to a slot in $I$ gives, by Lemma 1.1, terms
with the same or larger number of $I$-slots. Applying $\mu^{(n)}$ sends the first
sum to $ng$ and the second into $I^2$. $\square$

In particular **in residue characteristic 2 with $2 = 0$ in $R$:**
$\varphi(I)\subseteq I^2$ (this is the identity behind report §2); in mixed
characteristic $\varphi(g) = 2g + (I^2\text{-terms})$.

**Lemma 1.3 (fiber condition localizes the image).** Let $(R,\mathfrak m,k)$ be
local, $A$ finite free over $R$, and suppose the special fiber $H := A\otimes_R k$
is killed by 2, i.e. $\varphi_H = \eta\varepsilon$. Then
$$\varphi(I) \subseteq \mathfrak m I .$$

*Proof.* $\varepsilon\varphi = \varepsilon$ gives $\varphi(I)\subseteq I$.
Formation of $\varphi$ commutes with base change, so for $g \in I$ the image of
$\varphi(g)$ in $H$ is $\varphi_H(\bar g) = 0$; thus $\varphi(g) \in
\mathfrak m A\cap I = \mathfrak m I$ (use $A = R1\oplus I$, both summands free).
$\square$

**Proposition 1.4 (square-zero maximal ideal: free case).** Let $(R,\mathfrak m)$
be local with $\mathfrak m^2 = 0$, and let $A$ be a finite free $R$-bialgebra
(any rank) whose fiber is killed by $m$. Then $A$ is killed by $m^2$.

*Proof.* As in Lemma 1.3 (whose proof used nothing about rank or about the
number 2), $[m]^\#(I)\subseteq\mathfrak m I$; then
$[m^2]^\#(I) = [m]^\#([m]^\#(I)) \subseteq [m]^\#(\mathfrak m I) =
\mathfrak m\,[m]^\#(I)\subseteq \mathfrak m^2 I = 0$, and $[m^2]^\#$ fixes
$R\cdot 1$. $\square$

*Remarks.* (i) For order 4 and fiber killed by 2 this recovers the case of
Schoof's theorem ($m^p = pm = 0$, Compositio 128 (2001)) that our branch needs —
and does not even use $2\mathfrak m = 0$. (ii) It shows that all "first-order"
deformation directions are harmless; the entire problem lives at second order
and deeper, matching the computations (the $\epsilon^2$-digit is where the
$[4]^\#$ coefficients live).

---

## 2. Automatic antipodes in the killed-by-2 branch

**Lemma 2.1.** (a) If a finite-dimensional bialgebra $H$ over a field is killed
by 2 ($\varphi_H = \eta\varepsilon$), then $S = \mathrm{id}_H$ is an antipode:
$H$ is a Hopf algebra. (b) If $(R',\mathfrak m')$ is Artin local and $A'$ a
finite free $R'$-bialgebra whose fiber $H$ admits an antipode, then $A'$ admits
an antipode: $A'$ is Hopf.

*Proof.* (a) The antipode axiom for $S=\mathrm{id}$ reads
$\mu(\mathrm{id}\otimes\mathrm{id})\Delta = \varphi_H = \eta\varepsilon$, which
is the hypothesis; and $\mathrm{id}$ is an algebra map. (Conceptually: killed by
2 means every point satisfies $g = g^{-1}$.)
(b) $\operatorname{End}_{R'}(A')$ with the convolution product
$f*g = \mu(f\otimes g)\Delta$ is an associative unital $R'$-algebra with unit
$\eta\varepsilon$, and an antipode is precisely a two-sided convolution inverse
of $\mathrm{id}_{A'}$ (for commutative $A'$, a convolution inverse of the
identity is automatically an algebra map, being $[-1]^\#$-like; alternatively,
one checks $S$ is an algebra map from uniqueness of convolution inverses — for
the purpose of "the group scheme has inverses", convolution invertibility is the
definition that matters). Reduction mod $\mathfrak m'$ is a map of convolution
algebras $\operatorname{End}_{R'}(A') \to \operatorname{End}_{k}(H)$ with
nilpotent kernel $\mathfrak m'\operatorname{End}_{R'}(A')$ ($\mathfrak m'$ is
nilpotent), and $\mathrm{id}_H$ is convolution-invertible by hypothesis. Units
lift along nilpotent ideals. $\square$

**Consequence.** In the branch "fiber killed by 2" the bialgebra-level SAT/M2
computations *are* group-scheme statements: every object in the search space is
automatically a Hopf algebra. ("No antipode needed" in the report is not a
strengthening but an equivalence.)

---

## 3. Reduction of arbitrary bases to Artin local rings with finite residue field

**Theorem 3.1.** Fix $n\ge 1$. Suppose every finite locally free group scheme
of order $n$ over every **Artin local ring with finite residue field** is killed
by $n$. Then every finite locally free group scheme of order $n$ over an
**arbitrary base scheme** is killed by $n$.

*Proof.* Killedness is local, so let $G = \operatorname{Spec} A$ over
$S=\operatorname{Spec} R_0$, and (localizing further) assume $A$ free of rank
$n$. Let $\delta := [n]^\# - \eta\varepsilon \in \operatorname{End}_{R_0}(A)$;
we must show $\delta = 0$. All structure constants of
$(\mu,\Delta,\varepsilon,S)$ in a chosen basis are finitely many elements of
$R_0$; let $R_1\subseteq R_0$ be the $\mathbb Z$-subalgebra they generate, and
$A_1$ the induced bialgebra over $R_1$, so $\delta = \delta_1\otimes_{R_1}R_0$.
It suffices to prove $\delta_1 = 0$. $R_1$ is a finitely generated
$\mathbb Z$-algebra. Suppose some matrix coefficient $f\in R_1$ of $\delta_1$
is nonzero. Choose a maximal ideal $\mathfrak m \supseteq \operatorname{ann}(f)$
(possible: $\operatorname{ann}(f)\neq R_1$). By the general Nullstellensatz for
finitely generated $\mathbb Z$-algebras, $\kappa := R_1/\mathfrak m$ is a
**finite field**. In the noetherian local ring $R_{1,\mathfrak m}$, $f\neq 0$,
so by Krull's intersection theorem there is $N$ with
$f \notin \mathfrak m^N R_{1,\mathfrak m}$. Then
$\bar R := R_{1,\mathfrak m}/\mathfrak m^N$ is an Artin local ring with residue
field $\kappa$ finite, the image of $f$ in $\bar R$ is nonzero, and $A_1\otimes
\bar R$ is a finite free bialgebra of order $n$ over $\bar R$; by hypothesis its
$\delta$ vanishes, i.e. $f \mapsto 0$ in $\bar R$ — contradiction. $\square$

**Proposition 3.2 (residue characteristic prime to the order).** Let $R$ be
Artin local with residue field $\kappa$, and $G$ finite locally free of order
$n$ with $\operatorname{char}\kappa \nmid n$ (including $\operatorname{char} 0$).
Then $G$ is killed by $n$.

*Proof.* Over $\kappa$, the connected component $G^0_\kappa$ has order a power
of $\operatorname{char}\kappa$ (or is trivial in characteristic 0), and this
order divides $n$; so $G_\kappa$ is étale. Then $\omega_{G/R}\otimes\kappa =
\omega_{G_\kappa} = 0$, so $\omega_{G/R}=0$ by Nakayama and $G$ is étale over
$R$. After the faithfully flat base change to a local extension with separably
closed residue field (killedness descends), the étale group scheme over the
henselian base is a constant group scheme on a finite group $\Gamma$ of order
$n$; by Lagrange every $\gamma\in\Gamma$ has $\gamma^n = e$, so the scheme map
$[n]$ is the identity section. $\square$

**Corollary 3.3.** For $n = 4$: Grothendieck's question over all bases reduces
to Artin local rings $(R,\mathfrak m,\kappa)$ with $\kappa$ a **finite field of
characteristic 2** — in particular $\kappa$ perfect, so the fiber-shape theorem
(local killed-by-2 fibers have coordinate algebra $\kappa[x,y]/(x^2,y^2)$ or
$\kappa[t]/t^4$) always applies after the connected–étale and Schoof reductions
of `REPORT_order4.md` Corollary C (steps 1 and 3). *The imperfect-residue-field
caveat (report §5, handoff risk G.4) is hereby retired.*

*(The connected–étale step needs $R$ henselian — Artin local is; the appeal to
Schoof 2001 Thm 1.2 for fibers not killed by 2 remains a `[FLAG]` to check
against the paper, as recorded in the handoff §G.2.)*

---

## 4. The obstruction across a socle extension

From now on $(R',\mathfrak m',\kappa)$ is Artin local of residue characteristic
2, $M\subseteq R'$ an ideal with $\mathfrak m'M = 0$ and $\dim_\kappa M = 1$
("socle line"), $R := R'/M$. Let $A'$ be a free rank-4 bialgebra over $R'$ whose
fiber $H = A'\otimes\kappa$ is **killed by 2**, and let $A := A'\otimes_{R'}R$.
Assume (inductively over length) that $A$ is killed by 4. Define
$$d := [4]^\#_{A'} - \eta\varepsilon\ :\ A' \to A' .$$

**Lemma 4.1 (shape of the obstruction).**
(i) $d$ is $R'$-linear, $d(R'1)=0$, $\varepsilon\circ d = 0$;
(ii) $d(A')\subseteq MA' \cong M\otimes_\kappa H$ and $d(\mathfrak m'A') = 0$,
so $d$ factors through $H$;
(iii) $d(ab) = \varepsilon(a)d(b)+\varepsilon(b)d(a)$; hence $d$ vanishes on
$I'^2$ and defines an element
$$d \in \operatorname{Hom}_\kappa(I_H/I_H^2,\ I_H)\otimes_\kappa M .$$
(iv) $d(I')\subseteq \mathfrak m'^2 I'$; and if moreover $2 = 0$ in $R'$, then
$d(I')\subseteq \mathfrak m'^2 I'^2$.

*Proof.* (i) $[4]^\#$ and $\eta\varepsilon$ are $R'$-linear algebra
endomorphisms fixing $1$, and $\varepsilon[4]^\#=\varepsilon$.
(ii) $d\equiv 0 \bmod M$ because $A$ is killed by 4 and $[4]^\#$ commutes with
base change; $d(\lambda a) = \lambda d(a) \in \lambda MA' = 0$ for
$\lambda\in\mathfrak m'$ since $\mathfrak m'M=0$; $MA'\cong M\otimes_\kappa H$
by freeness and $\mathfrak m'M=0$.
(iii) $[4]^\#(ab) = [4]^\#(a)[4]^\#(b) = (\varepsilon(a)+da)(\varepsilon(b)+db)$
and $da\cdot db \in (MA')^2 = M^2(\cdots) = 0$.
(iv) By Lemma 1.3, $\varphi'(I')\subseteq\mathfrak m'I'$, so
$[4]^\# = \varphi'\circ\varphi'$ maps $I'$ into
$\varphi'(\mathfrak m'I') = \mathfrak m'\varphi'(I')\subseteq\mathfrak m'^2I'$.
If $2=0$: by Lemma 1.2, $\varphi'(I')\subseteq I'^2$, so $\varphi'(g) = \sum_i
a_ib_i$ with $a_i,b_i\in I'$, and $d(g) = \sum_i\varphi'(a_i)\varphi'(b_i)\in
(\mathfrak m'I')^2 = \mathfrak m'^2I'^2$. $\square$

**Proposition 4.2 (free vanishing).** If $M\cap\mathfrak m'^2 = 0$ then $d=0$.

*Proof.* $d(I')\subseteq MA'\cap\mathfrak m'^2I'\subseteq
(M\cap\mathfrak m'^2)A' = 0$, using freeness of $A'$ componentwise. $\square$

So the only dangerous socle lines are those inside $\mathfrak m'^2$ — the
obstruction is a genuinely **second-order** phenomenon (consistent with
Proposition 1.4).

**Proposition 4.3 (Gorensteinization).** Let $J\subseteq R'$ be an ideal maximal
with respect to $J\cap M = 0$. Then $d = 0$ if and only if the corresponding
obstruction for $A'\otimes R'/J$ over $R'/J$ vanishes; and $R'/J$ has
one-dimensional socle (namely the image of $M$).

*Proof.* Formation of $[4]^\#$ commutes with base change, so the obstruction
over $R'/J$ is the reduction of $d$; since $d$ has values in $MA'$ and
$MA'\cap JA' = (M\cap J)A' = 0$, the reduction map is injective on the values of
$d$. Maximality of $J$ makes $M$ an essential ideal of $R'/J$: any nonzero ideal
meets $M$, so any minimal ideal equals $M$, i.e. the socle is $M$. $\square$

Thus in the socle induction we may and do assume: **$\operatorname{soc}(R')=M$
is one-dimensional and $M\subseteq\mathfrak m'^2$.**

---

## 5. Rigidity of the obstruction, and the commutative comparison

This section is the precise form of the session's guiding idea.

**Theorem 5.1 (rigidity).** In the setting of §4, the obstruction $d$ depends
only on the bialgebra $A$ over $R$ (and on $R'\to R$), **not on the choice of
lift** $A'$: if $A'_1, A'_2$ are two free rank-4 bialgebras over $R'$ equipped
with isomorphisms $A'_i\otimes_{R'}R \cong A$, then $d_1 = d_2$ under the
canonical identification below.

*Proof.* **Normalization.** Choose a basis $1, \bar e_1,\bar e_2,\bar e_3$ of
$A$ with $\bar e_i \in I_A$. In each $A'_i$, lift to a basis $1, e_1^{(i)},
e_2^{(i)}, e_3^{(i)}$ with $e_j^{(i)}\in I'_i := \ker\varepsilon'_i$ (possible:
$I'_i \to I_A$ is surjective). Let $\vartheta: A'_1 \to A'_2$ be the
$R'$-module isomorphism matching these bases. Then $\vartheta$ reduces to
$\mathrm{id}_A$, $\vartheta(1)=1$, and $\varepsilon'_2\circ\vartheta =
\varepsilon'_1$. Transport the second structure to the module $A' := A'_1$;
after transport we have two bialgebra structures $(\mu_1,\Delta_1)$,
$(\mu_2,\Delta_2)$ on the same free module $A'$, with the **same** unit and
counit, agreeing modulo $MA'$.

**Comparison.** Set $m := \mu_2-\mu_1$ and $\delta := \Delta_2 - \Delta_1$.
Both are $R'$-linear with values in $M\cdot(-)$, hence kill
$\mathfrak m'\cdot(-)$ and factor through the fiber:
$m: H\otimes H\to M\otimes H$, $\delta: H \to M\otimes(H\otimes H)$.
Then, writing $\varphi_i = \mu_i\Delta_i$,
$$\varphi_2 = (\mu_1+m)(\Delta_1+\delta) = \varphi_1 + \zeta,\qquad
\zeta := (1_M\otimes\mu_H)\circ\delta + m\circ\Delta_H,$$
because $\mu_2$ acts on $M$-valued elements through $\mu_H$, $m$ sees only the
fiber of $\Delta_1$, and $m\circ\delta = 0$ ($m$ kills $M$-multiples). The map
$\zeta: A'\to M\otimes H$ kills $\mathfrak m'A'$.

**Squaring.** $[4]_2^\# = \varphi_2\varphi_2 = \varphi_1\varphi_1 +
\varphi_1\zeta + \zeta\varphi_1 + \zeta\zeta$. Now:
$\zeta\zeta = 0$ ($\zeta$ has values in $MA'$ and kills $MA'$);
$\zeta\varphi_1|_{I'} = 0$ (Lemma 1.3: $\varphi_1(I')\subseteq\mathfrak m'I'$,
killed by $\zeta$);
and $\varphi_1\zeta = (1_M\otimes\varphi_H)\circ\zeta =
(1_M\otimes\eta\varepsilon)\circ\zeta = \eta\circ\bar\zeta$ where $\bar\zeta :=
(1_M\otimes\varepsilon)\circ\zeta$ — this is where "**fiber killed by 2**"
enters: $\varphi_H = \eta\varepsilon$. Hence on $I'$:
$$d_2 = d_1 + \eta\circ\bar\zeta .$$
Apply $1_M\otimes\varepsilon$: by Lemma 4.1(i) both sides have
$\varepsilon\circ d_i = 0$, so $\bar\zeta|_{I'} = 0$ and $d_2 = d_1$.

**Independence of the normalization.** Two normalized identifications differ by
an automorphism $u = \mathrm{id} + \theta$ of $A'$ with $\theta$ $R'$-linear,
$M$-valued, $\theta(1)=0$. Conjugating $d_2$ by $u$ changes it by
$d_2\theta$-type and $\theta d_2$-type terms, and both vanish: $d_2(MA')=0$ and
$\theta(MA')=0$. $\square$

**Remark 5.2.** The proof used only: $\mathfrak m'M = 0$; fiber killed by 2. It
did not use $\dim M = 1$, commutativity/cocommutativity anywhere, or the rank.
It works verbatim for order $p^2$ with fiber killed by $p$, writing
$\varphi_p = [p]^\#$ and expanding the $p$-fold product ($\zeta$ becomes the sum
over which tensor slot carries the $M$-valued difference; all cross terms die
for the same reasons).

**Corollary 5.3 (commutative comparison; the session's guiding idea).** In the
setting of §4, suppose the bialgebra $A/R$ admits **at least one** lift $A''$
over $R'$ which is killed by 4 — for instance a **cocommutative** lift (then
$\operatorname{Spec} A''$ is a commutative finite flat group scheme by Lemma 2.1,
hence killed by 4 by **Deligne's theorem**). Then **every** lift $A'$ of $A$ —
however noncommutative — is killed by 4.

*Proof.* Rigidity: $d_{A'} = d_{A''} = 0$. $\square$

**Remark 5.4 (deformation-theoretic reading).** Corollary 5.3 says: *at the last
infinitesimal step, the killed-by-4 obstruction cannot distinguish
noncommutative deformations from commutative ones.* If, in addition, commutative
finite flat group schemes are unobstructed along square-zero extensions
(`[FLAG]`: this is classical deformation theory à la Illusie — via the co-Lie
complex, or via Raynaud's local embedding into abelian schemes; the exact
citation must be verified before use), then whenever $A/R$ is cocommutative,
a cocommutative lift exists, and Corollary 5.3 kills every deformation of every
**commutative** $(A/R)$. What rigidity alone does *not* handle is a
noncocommutative $A/R$ with no commutative companion; those are exactly the
configurations the certificates of §6 handle.

**Remark 5.5 (why the identity-based route is still needed).** One might hope
to iterate Corollary 5.3 down a whole composition series. The obstruction: at
lower levels the "difference of two lifts" is no longer $M$-valued, and the
error terms in Theorem 5.1 no longer vanish. Rigidity is genuinely a
*top-layer* statement. The graded analysis of §6 is the correct multi-layer
replacement.

---

## 6. The graded structure of the obstruction: $d = $ "$\psi^2$"

Keep the setting of §4 (socle line $M\subseteq\mathfrak m'^2$,
$\operatorname{soc} R' = M$).

**Lemma 6.1 (filtration raising and the symbol of $\varphi'$).**
$\varphi'(\mathfrak m'^jI')\subseteq\mathfrak m'^{j+1}I'$ for all $j\ge 0$, and
the map induced by $\varphi'$ on the first graded piece,
$$\bar\varphi\ :\ I_H \longrightarrow (\mathfrak m'/\mathfrak m'^2)\otimes_\kappa I_H,$$
is well defined ($\kappa$-linear), where we identify
$\mathfrak m'I'/\mathfrak m'^2I' = (\mathfrak m'/\mathfrak m'^2)\otimes I_H$ by
freeness. Moreover the induced maps on all higher graded pieces are determined
by $\bar\varphi$ through the multiplication of
$\operatorname{gr}_{\mathfrak m'}(R')$: $\operatorname{gr}^j(\varphi')(\lambda\otimes h) =
\lambda\cdot\bar\varphi(h)$.

*Proof.* Lemma 1.3 plus $R'$-linearity: $\varphi'(\lambda h) =
\lambda\varphi'(h)$. $\square$

**Theorem 6.2 (obstruction = polarized square of the symbol; case
$\mathfrak m'^3 = 0$).** Assume $\mathfrak m'^3 = 0$. Choose a basis
$(t_\alpha)_\alpha$ of $V:=\mathfrak m'/\mathfrak m'^2$ and write
$\bar\varphi = \sum_\alpha t_\alpha\otimes\psi_\alpha$ with
$\psi_\alpha: I_H\to I_H$ $\kappa$-linear. Then, as maps $I_H \to
\mathfrak m'^2\otimes I_H$ (note $\mathfrak m'^2\supseteq M$ and
$\mathfrak m'^3=0$ makes the products below well defined):
$$d \;=\; \sum_{\alpha,\beta} (t_\beta t_\alpha)\otimes\psi_\beta\psi_\alpha
\;=\; \sum_{\alpha<\beta} (t_\alpha t_\beta)\otimes(\psi_\alpha\psi_\beta +
\psi_\beta\psi_\alpha)\; +\; \sum_\alpha t_\alpha^2\otimes\psi_\alpha^2 .$$

*Proof.* For $g\in I'$ write $\varphi'(g) = \sum_\alpha t_\alpha\widetilde{
\psi_\alpha(g)} + r$ with $r\in\mathfrak m'^2I'$ (definition of the symbol;
tildes are lifts along $I'\to I_H$). Apply $\varphi'$ again:
$\varphi'(r)\in\mathfrak m'^3I' = 0$, and $\varphi'(t_\alpha\widetilde{
\psi_\alpha g}) = t_\alpha\varphi'(\widetilde{\psi_\alpha g}) = \sum_\beta
t_\alpha t_\beta\widetilde{\psi_\beta\psi_\alpha(g)} + t_\alpha\cdot(\mathfrak
m'^2 I') $, and $t_\alpha\mathfrak m'^2 = 0$. Since $d = \varphi'\varphi'$ on
$I'$, the formula follows; the second expression symmetrizes using
commutativity of $R'$. $\square$

**Consequences and translations.**

* **Curvilinear case** ($\mathfrak m'$ principal, $R'$ of length 3, e.g.
  $k[\epsilon]/\epsilon^3$, $W(\kappa)/8$, $\mathbb Z[\pi]/(\pi^2-2,\pi^3)$ and
  their unramified extensions): $d = t^2\otimes\psi^2$. So each length-3
  theorem of the report **is** the statement $\psi^2 = 0$ for every realizable
  symbol $\psi$, and conversely. Theorem A (arbitrary $\mathbb F_2$-algebra $k$)
  is exactly "$\psi^2=0$" in equal characteristic; Theorem B gives it over the
  mixed-characteristic length-3 rings with $\kappa = \mathbb F_2,\mathbb F_4$
  (and $W(\mathbb F_8)/8$). In equal characteristic the symbol is
  $\psi = \mu_1\Delta_0 + \mu_0\Delta_1$ (first-order Gerstenhaber–Schack data
  of the deformation $A$ of $H$); in the unramified mixed case it acquires the
  extra summand $\mathrm{id}_{I_H}$ from the $2g$-term of Lemma 1.2 (over
  $\mathbb Z/8$: $t = 2$, and $\varphi(g) = 2g+\cdots$ contributes to the
  first layer); in the ramified case $2 = \pi^2$ lands in layer 2 and the symbol
  is again purely deformation-theoretic. The certificates confirm $\psi^2=0$
  in all three regimes — a conceptual proof should explain the first two
  uniformly ("$\psi$ is a square-zero perturbation of $0$ resp. of the
  identity"…), which is subtle precisely because in mixed characteristic
  cancellation, not vanishing, makes $\psi^2=0$.

* **Polarized identities.** For non-principal $\mathfrak m'$, Theorem 6.2 shows
  the needed statement is the two-variable polarization
  $$\psi_\alpha\psi_\beta + \psi_\beta\psi_\alpha = 0\ (\alpha\neq\beta),\qquad
  \psi_\alpha^2 = 0,$$
  for every realizable *pair* of symbol components. The new computation
  **`scripts/len3gen.m2`** proves exactly this in equal characteristic: it runs
  the ideal-membership search over the **universal embedding-dimension-2 base**
  $R = k[s,t]/(s,t)^3$, $k$ an arbitrary $\mathbb F_2$-algebra. Since every
  equal-characteristic Artin local $\mathbb F_2$-algebra with
  $\mathfrak m^3 = 0$ and $\dim\mathfrak m/\mathfrak m^2\le 2$ is a base-change
  of a quotient of this $R$, and ideal-membership certificates specialize along
  both operations, success of `len3gen` closes **all such bases at once**
  (subsuming Theorem A, which is the quotient $t = 0$).

* **Why embedding dimension 2 does not formally give embedding dimension
  $\ge 3$.** One would like to detect the socle of an arbitrary
  $(\mathfrak m^3=0)$-base through its embdim-$\le2$ quotients. This fails for
  Gorenstein bases: if $\operatorname{soc} = \mathfrak m^2 = \kappa x$ is
  one-dimensional with multiplication form $B(u,v)$ (and quadratic/Frobenius
  diagonal $Q(v) = v^2/x$) of trivial radical, then for **any** nonzero
  $U\subseteq V$ the ideal generated by $U$ contains
  $(B(U,V)+Q(U))x \neq 0$, i.e. every proper quotient kills the socle. So each
  embedding dimension is a genuinely new statement. However:

**Proposition 6.3 (finiteness per nilpotency degree).** Fix $\nu\ge 2$. There is
a single finite Gröbner computation whose success implies: every free rank-4
bialgebra with killed-by-2 fiber of one of the two shapes, over **every**
equal-characteristic Artin local $\mathbb F_2$-algebra $R$ with
$\mathfrak m^\nu = 0$, is killed by 4. Namely the ideal-membership computation
over the universal base $k[t_1,\dots,t_{45}]/\mathfrak m^\nu$ ($45 = 27+18$,
the number of comultiplication and multiplication structure constants).

*Proof.* Let $A$ be such a bialgebra over $R$. Choose a coefficient field
$\kappa\subseteq R$ (Cohen; equal characteristic, $R$ complete since Artin).
Each structure constant $x$ splits as $x = [\bar x] + (x - [\bar x])$ with
$x - [\bar x]\in\mathfrak m$; the fiber-shape normalization puts the
$\kappa$-parts in the standard form, so $A$ is defined over the
$\kappa$-subalgebra $R_0\subseteq R$ generated by the $45$ elements
$x - [\bar x]\in\mathfrak m$. $R_0$ is Artin local with
$\operatorname{embdim}\le 45$ and $\mathfrak m_0^\nu = 0$, hence a base change
of a quotient of the universal ring, and killedness ascends along
$R_0\to R$. $\square$

So the only *infinite* direction left is the nilpotency degree $\nu$ — the
"depth" of the deformation — which is exactly what §7 addresses. (In practice
$45$ is far from optimal; the symbol $\bar\varphi$ has at most
$\dim\operatorname{Hom}(I_H/I_H^2, I_H)\le 6$ independent components, and a
sharper bound should come out of the certificate structure.)

## 6.5 The polarization route to all embedding dimensions at $\mathfrak m^3=0$ (session 4; audit of the GPT-5.5 Pro theory push)

An external theory handoff (`order4_theory_push_handoff.md`, GPT-5.5 Pro)
proposed the following argument. The argument is **correct as an
implication**, but its input audit fails against the banked results as they
stood; the corrected accounting is below.

**Remark 6.5.1 (Theorem 6.2 is unconditional).** The proof of Theorem 6.2
never uses the §4 socle-step setting in which it was stated: it uses only
$\mathfrak m'^3 = 0$, freeness, and $\varphi'(\mathfrak m^jI)\subseteq
\mathfrak m^{j+1}I$ (Lemma 1.3/6.1, i.e. the fiber killed by 2). So for
*every* equal- or mixed-characteristic Artin local $R$ with
$\mathfrak m^3=0$ and every free rank-4 bialgebra with killed-by-2 fiber,
$$[4]^\# \;=\; \eta\varepsilon\; +\; \sum_{\alpha,\beta}(t_\beta t_\alpha)
\otimes\psi_\beta\psi_\alpha \quad\text{on } I.$$

**Theorem 6.5.2 (polarization; conditional).** Let $k$ be a field of
characteristic 2 and assume:
$(\star)$ for **every** commutative $k$-algebra $k'$ and **every** first-order
deformation of either killed-by-2 fiber shape over $k'[e]/e^2$ (bialgebra
axioms and fiber2 at first order; *no liftability assumption*), the divided
squaring symbol satisfies $\psi^2 = 0$.
Then every free rank-4 bialgebra with local killed-by-2 fiber over every
equal-characteristic Artin local $k$-algebra $R$ with $\mathfrak m^3 = 0$ —
**arbitrary embedding dimension** — is killed by 4.

*Proof (following the GPT handoff §2, hypotheses corrected).* Choose a
coefficient field $k\subseteq R$ (Cohen) and $t_1,\dots,t_n\in\mathfrak m$
inducing a basis of $\mathfrak m/\mathfrak m^2$. For any $k$-algebra $k'$
and $\lambda\in (k')^n$, the $k$-algebra map $R\to R/\mathfrak m^2 =
k\oplus\mathfrak m/\mathfrak m^2\to k'[e]/e^2$, $t_\alpha\mapsto
\lambda_\alpha e$, base-changes $A$ to a first-order deformation over
$k'[e]/e^2$ with symbol $\psi_\lambda = \sum_\alpha\lambda_\alpha
\psi_\alpha$ (symbols commute with base change, Lemma 6.1). Taking
$k' = k[\lambda_1,\dots,\lambda_n]$, hypothesis $(\star)$ makes
$\psi_\lambda^2 = 0$ a polynomial identity in the $\lambda_\alpha$, whose
coefficients are exactly $\psi_\alpha^2 = 0$ and $\psi_\alpha\psi_\beta +
\psi_\beta\psi_\alpha = 0$. Remark 6.5.1 then kills the obstruction term by
term (diagonal by squares, off-diagonal in symmetric pairs). $\square$

**Audit finding (why $(\star)$ was NOT banked).** The GPT handoff cited
"Theorem A / the dual-number theorem" as $(\star)$. But Theorem A lives at
$\epsilon^3$, and by Proposition 7.3(ii) it yields $\psi^2=0$ only for
first-order deformations **that lift to $k[\epsilon]/\epsilon^3$** — and the
$\lambda$-quotients in the proof above have no reason to lift (first-order
deformations are obstructed à la Gerstenhaber). $(\star)$ is a strictly
stronger, genuinely new input. Status of $(\star)$:
* $k' = \mathbb F_2$ (SAT): **proved this session** — the $\epsilon^2$ rows
  of Theorem 7.5.2 (`s2check.log`) are exactly the unconditional statement.
* arbitrary $k'$ (ideal membership): `scripts/symbolsq.m2` (launched this
  session; J = first-order associativity + $\Delta$-multiplicativity +
  fiber2, coassociativity-free pass first) — **check `symbolsq.log` for
  `DONE symbolsq` and the membership verdict before citing $(\star)$ or
  Theorem 6.5.2's conclusion as a theorem.**

**Consequence if `symbolsq` lands.** Equal-characteristic $\mathfrak m^3=0$
is closed in **all embedding dimensions** (superseding the embdim-2 goal of
`len3gen.m2`, which then becomes an independent audit), and the running
embdim-3 plan is moot. The remaining equal-char direction is depth $\nu\ge4$:
either Conjecture 7.5.4 (S′-universality), or the GPT handoff's equivalent
**homogeneous-symbol lemma** (every graded symbol $\theta_r$ of $\varphi$
lies in the totally square-zero first-order symbol space $T$); in mixed
characteristic the symbol space must be enlarged by the initial form of 2
($\theta = \tau\cdot\mathrm{id} + \psi$, cf. the §6.2 bullet on $\mathbb
Z/8$), so the two regimes stay separate — consistent with the handoff's §7.

---

## 7. The kernel-factorization statement S′ and the socle induction

**Definition.** For a free rank-4 bialgebra $A$ over an Artin local $R$ with
fiber killed by 2, say **S′($A/R$)** holds if
$$\varphi_A(I) \ \subseteq\ \mathfrak m\cdot(\ker\varphi_A\cap I).$$

S′ implies $[4]^\#_A = \eta\varepsilon$ ($\varphi^2(I)\subseteq\mathfrak
m\,\varphi(\ker\varphi) = 0$) but is stronger: it locates the image of the
squaring map inside $\mathfrak m$-multiples of its kernel.

**Theorem 7.1 (S′ propagates killedness through every socle step).** Let
$R'\to R = R'/M$ be a socle step as in §4 and $A'$ any free rank-4 bialgebra
over $R'$ with fiber killed by 2, $A := A'\otimes R$. If S′($A/R$) holds, then
$A'$ is killed by 4.

*Proof.* Let $g\in I'$. The reduction of $\varphi'(g)$ mod $MA'$ is
$\varphi_A(\bar g) = \sum_i\bar\lambda_i\bar h_i$ with
$\bar\lambda_i\in\mathfrak m$ and $\bar h_i\in\ker\varphi_A\cap I_A$
(by S′). Lift: $\varphi'(g) = \sum_i\lambda_i h_i + w$ with
$\lambda_i\in\mathfrak m'$, $h_i\in I'$ lifting $\bar h_i$, and
$w\in MA' = M\otimes H$. Apply $\varphi'$:
1. $\varphi'(h_i)$ reduces to $\varphi_A(\bar h_i) = 0$, so
   $\varphi'(h_i)\in MA'$, whence
   $\lambda_i\varphi'(h_i)\in\mathfrak m'MA' = 0$.
2. $w = \sum_j m_j\otimes c_j$: $\varphi'(w) = \sum_j m_j\otimes\varphi_H(c_j) =
   \big(\sum_j m_j\varepsilon(c_j)\big)\,1$ (fiber killed by 2). Applying
   $\varepsilon$ to $\varphi'(g)$: $0 = \varepsilon\varphi'(g) =
   \sum_i\lambda_i\varepsilon(h_i) + \sum_j m_j\varepsilon(c_j) =
   \sum_j m_j\varepsilon(c_j)$ (the $h_i$ were chosen in $I'$). So
   $\varphi'(w) = 0$.
Hence $[4]^\#_{A'}(g) = \varphi'(\varphi'(g)) = 0$. $\square$

**Corollary 7.2.** Suppose S′($A/R$) holds for every Artin local $R$ with
finite residue field of characteristic 2 and every free rank-4 bialgebra $A/R$
with killed-by-2 fiber **that lifts one more socle step** (only those instances
are ever used). Then — combining §3, §4, the connected–étale/Schoof reductions
— every finite locally free group scheme of order 4 over **every base scheme**
is killed by 4.

**Proposition 7.3 (S′ at the bottom of the tower).**
(i) S′($H/\kappa$) always holds ($\varphi_H(I)=0$).
(ii) For $R = k[\epsilon]/\epsilon^2$ (equal characteristic):
S′($A/R$) $\iff$ $\psi^2 = 0$ for the symbol $\psi$ of $A$. In particular,
**Theorem A implies S′($A/k[\epsilon]/\epsilon^2$) for every $A$ that lifts to
$k[\epsilon]/\epsilon^3$** — which is every $A$ the induction ever consumes at
this level with curvilinear continuation.

*Proof of (ii).* Here $\varphi(g) = \epsilon\widetilde{\psi(\bar g)}$ up to
$\epsilon\cdot$(choices), and $\epsilon v\in\epsilon(\ker\varphi\cap I)$ for
$v\in I$ iff $v$ can be corrected by $\operatorname{ann}(\epsilon)$-elements
into $\ker\varphi$; since $\varphi(v+\epsilon u) = \epsilon\psi(\bar v)$, this
is possible iff $\psi(\psi(\bar g)) = 0$. For the second sentence: if $A$ lifts
to $A''$ over $k[\epsilon]/\epsilon^3$, Theorem A gives $[4]_{A''} =
\eta\varepsilon$, and Theorem 6.2 (curvilinear case) evaluates its top layer as
$\epsilon^2\psi^2$, forcing $\psi^2 = 0$. $\square$

**Open Lemma 7.4 (the remaining theoretical gap).** *In the setting of Theorem
7.1, does S′($A/R$) (plus, if needed, liftability of $A'$ one further step)
imply S′($A'/R'$)?* Equivalently: given that $\varphi'(I')\subseteq
\ker\varphi'\cap\mathfrak m'I'$ (which Theorem 7.1 provides), can the
factorization $\varphi'(I')\subseteq\mathfrak m'(\ker\varphi'\cap I')$ be
arranged? The proof of Theorem 7.1 produces
$\varphi'(I')\subseteq\mathfrak m'\widetilde K + M\otimes I_H$ where $K =
\ker\varphi_A\cap I_A$; the defect is measured by the $M\otimes I_H$-components
of $\varphi'(\widetilde K)$, i.e. by a map $\beta: K \to M\otimes I_H$ (well
defined because changing the lift changes $\varphi'(\tilde h)$ by $M\otimes
\kappa 1$ only). The lemma asks whether the total expression can be regrouped
so that $\beta$-contributions cancel. **Status:** true in every computed
instance (all length-$\le3$ theorems; $\epsilon^4,\epsilon^5$ SAT; these are
exactly the curvilinear instances of the lemma at depths $\le 4$); no proof,
no counterexample. This single lemma now carries the entire remaining depth
direction of the problem.

**Evidence discipline** (handoff golden rule 2): Theorem E ($\epsilon^4,
\epsilon^5$, SAT) verifies the *consequences* of Open Lemma 7.4 at those
depths for $\kappa=\mathbb F_2$; it does not verify the lemma itself. The
running `search_eps45.m2` would upgrade those depths to arbitrary $k$.

---

## 7.5 The S′-universality reformulation (session 4)

Session 4 probed whether the hypothesis Open Lemma 7.4 tries to *propagate* is
simply **universal** — true of every object in the branch, with no liftability
hypothesis at all.

**Definition.** Say **S′ is universal over $R$** if every free rank-4
bialgebra $A/R$ with local fiber of one of the two shapes, killed by 2,
satisfies S′($A/R$): $\varphi(I)\subseteq\mathfrak m(\ker\varphi\cap I)$.

**Proposition 7.5.1 (defect characterization, curvilinear case).** Let
$(R,\mathfrak m)$ be Artin local with $\mathfrak m = (t)$ principal, $A$ free
rank-4 with fiber killed by 2. Then:
(i) each $\varphi(e_i)$ admits a division $v_i\in I$ with $t\,v_i =
\varphi(e_i)$;
(ii) $\varphi(v_i)$ does not depend on the choice of division;
(iii) S′($A/R$) $\iff$ $\varphi(v_i) = 0$ for $i = 1,2,3$.
So over curvilinear bases S′ is the vanishing of a well-defined **polynomial
defect** $\delta_i := \varphi(\varphi(e_i)/t)$ in the structure constants.

*Proof.* (i) Lemma 1.3 gives $\varphi(e_i)\in\mathfrak m I = tI$
coordinatewise ($I$ free). (ii) Two divisions differ by $u = \sum_r u_r e_r$
with $u_r\in\operatorname{ann}(t)$; then $\varphi(u) = \sum_r u_r\varphi(e_r)
\in \operatorname{ann}(t)\cdot tI = 0$, again by Lemma 1.3. (iii) The solution
set of $t k = \varphi(e_i)$, $k\in I$, is exactly $v_i +
\operatorname{ann}(t)I$; S′ at $e_i$ says some solution lies in $\ker\varphi$,
which by (ii) is equivalent to $\varphi(v_i)=0$; and S′ on all of $I$ follows
from the basis case since $\mathfrak m(\ker\varphi\cap I)$ is a submodule.
$\square$

**Theorem 7.5.2 (S′ IS universal over ALL curvilinear 2-rings of length ≤ 4
with residue field $\mathbb F_2$; SAT).** S′ is universal over the eight rings
$$\mathbb F_2[\epsilon]/\epsilon^N\ (N=2,3,4),\qquad
\mathbb Z/4,\ \mathbb Z/8,\ \mathbb Z/16,\qquad
\mathbb Z[\pi]/(\pi^2-2,\pi^3),\ \mathbb Z[\pi]/(\pi^2-2,\pi^4)$$
(both fiber shapes each — **16/16 queries UNSAT, `DONE s2check`**;
`scripts/s2check.py`, `s2check.log`; five encoding gates passed, including a
machine check of the coset-completeness argument of 7.5.1(iii), and every
per-ring gateR/S1 gate OK). In particular ($\epsilon^2$ case):
$\psi^2 = 0$ for **every** first-order deformation, liftable or not —
strengthening Proposition 7.3(ii), whose liftability hypothesis is now known
to be unnecessary at this depth for $k=\mathbb F_2$.

**Corollary 7.5.3 (new bases, one socle step up).** Let $R$ be any ring of
Theorem 7.5.2 and $R'$ **any** Artin local ring with an ideal $M$,
$\mathfrak m'M = 0$, $\dim_{\mathbb F_2} M = 1$, $R'/M\cong R$. Then every
free rank-4 bialgebra over $R'$ with killed-by-2 local fiber is killed by 4
(Theorem 7.1), hence — Lemma 2.1 — every such group scheme. This covers, e.g.:
* all local $\mathbb F_2$-algebras $R'$ of length 4 (resp. 5) admitting a
  socle line with quotient $\mathbb F_2[\epsilon]/\epsilon^3$ (resp.
  $\epsilon^4$) — non-curvilinear ones included; no direct search covered
  these;
* mixed-characteristic non-principal-$\mathfrak m$ rings such as
  $\mathbb Z/4[y]/(y^2, 2y)$ (socle line $(y)$, quotient $\mathbb Z/4$) — the
  §B.2 targets of the handoff, reached **without** new ring classes;
* every length-4 extension of $\mathbb Z/8$ and of the ramified length-3 ring,
  and every length-5 extension of $\mathbb Z/16$ and of
  $\mathbb Z[\pi]/(\pi^2-2,\pi^4)$ — in particular **$\mathbb Z/32$** (socle
  line $(16)$) and the ramified length-5 ring
  **$\mathbb Z[\pi]/(\pi^2-2,\pi^5)$** (socle line $(\pi^4)$), i.e. handoff
  §B.3, for free.

**Conjecture 7.5.4 (S′-universality; supersedes Open Lemma 7.4 as the
target).** S′ is universal over every Artin local ring with finite residue
field of characteristic 2.

**Reduction.** Conjecture 7.5.4 $\Rightarrow$ (K) for order 4, by induction on
length: over a field S′ is trivial ($\varphi(I)=0$); for $R'$ of length
$\ell$, pick a socle line $M$, apply Theorem 7.1 to $R'\to R'/M$ with
S′($A\otimes R'/M$) supplied by universality at length $\ell-1$. (Then §3
reduces arbitrary bases, and the connected–étale/Schoof reductions of
Corollary C handle the non-killed-by-2 fibers, with the standing flag G.2.)
Note what changed: Open Lemma 7.4 asked for *propagation* of S′ along the
tower; universality needs no tower bookkeeping and is checkable ring by ring —
and per depth it is **one finite ideal-membership computation** at
arbitrary-$k$ strength, by Proposition 7.5.1: the defect $\delta_i$ is
polynomial in the structure constants (`scripts/s2gen.m2` is this run at
$\epsilon^3$; the analogue of Proposition 6.3 bounds the embedding dimension
per depth). The missing infinite direction is, as before, uniformity in the
depth — but the statement to prove is now a *pointwise identity*, not an
induction step.

**Caveat.** The probe covers principal $\mathfrak m$ only; the encoding of
"S′ fails" over non-principal $\mathfrak m$ needs the syzygy coset of
$(s,t)$ rather than $\operatorname{ann}(t)^3$ and was not implemented. For
Conjecture 7.5.4 to close (K), the non-principal case is *required* (the
induction passes through arbitrary Artin local quotients). An embdim-2
probe (base $\mathbb F_2[x,y]/(x^2,y^2)$ or $\mathbb F_2[x,y]/(x,y)^3$) is
the natural next evidence point.

**Remark 7.5.5 (no purely module-theoretic proof; from the GPT-5.5 Pro
handoff §5, verified).** S′-universality cannot hold for abstract square-zero
filtered endomorphisms: on $I' = R'e_1\oplus R'e_2$ over $R' =
k[\epsilon]/\epsilon^3$, the map $\Phi'(e_1)=\epsilon e_2$,
$\Phi'(e_2)=\epsilon^2e_1$ has $\Phi'^2 = 0$ and satisfies S′ after reduction
to $k[\epsilon]/\epsilon^2$, yet $\epsilon e_2\notin\epsilon(\ker\Phi'\cap
I')$: any $k = e_2 + \epsilon^2 u$ has $\Phi'(k) = \epsilon^2e_1\neq0$. So
every proof of Conjecture 7.5.4 must use the bialgebra structure — per the
ablation results, $\Delta$-multiplicativity + associativity are the inputs to
spend.

---

## 8. What the axioms are for: the ablation experiment

A hand proof of $\psi^2=0$ must use some subset of: associativity of the
deformed multiplication (A), multiplicativity of $\Delta$ (M), coassociativity
(C), fiber killed by 2 (F). The new script **`scripts/ablate.py`** drops one
block at a time over $\mathbb F_2[\epsilon]/\epsilon^3$ and asks Z3 whether
$[4]^\#\neq 0$ becomes satisfiable. Gates: the full system must reproduce
`sat` at level 1 and `unsat` with $[4]^\#\neq0$ (else the block bookkeeping is
wrong). Reading: a `sat` under ablation of block X exhibits a
"pseudo-bialgebra" violating only X with $[4]^\#\neq0$, i.e. **X is
load-bearing** and no proof avoiding X can exist.

**Results (2026-07-08, `scripts/ablate.log`; all four gates passed, both fiber
shapes, base $\mathbb F_2[\epsilon]/\epsilon^3$):**

| dropped block | query | verdict |
|---|---|---|
| — (full system) | A+M+C+F + $[4]^\#{\neq}0$ | `unsat` (gate; reproduces Thm B) |
| coassociativity | A+M+F + $[4]^\#{\neq}0$ | **`unsat` — coassociativity is NOT needed** |
| $\Delta$-multiplicativity | A+C+F + $[4]^\#{\neq}0$ | **`sat` — M is load-bearing** (pseudo-bialgebra witnesses printed in the log) |
| associativity | M+C+F + $[4]^\#{\neq}0$ | **`unsat` — associativity is NOT needed** |
| fiber2 | A+M+C + $[4]^\#{\neq}0$ | `unsat` (gate; = Theorem B′ instance) |

So at length 3 the vanishing of $[4]^\#$ follows from **counitality +
$\Delta$-multiplicativity** together with *either* associativity *or*
coassociativity *or* the fiber condition — and $\Delta$-multiplicativity cannot
be dispensed with. The follow-up `scripts/ablate2.py` (**complete**, gates reproduced) descends
the lattice below M. Full verdict table over $\mathbb F_2[\epsilon]/\epsilon^3$
("unsat" = the listed axioms already force $[4]^\#=0$):

| axiom set | fiber $k[x,y]/(x^2,y^2)$ | fiber $k[t]/t^4$ |
|---|---|---|
| M alone | sat | sat |
| M+F | sat | **unsat** |
| **M+A** | **unsat** | **unsat** |
| M+C | sat | **unsat** |

**Conclusion.** The minimal axiom set that works for *both* fiber shapes is
$\{\Delta\text{-multiplicativity},\ \text{associativity}\}$. Sharpened
statement — **now PROVED for arbitrary $\mathbb F_2$-algebras $k$**
(`scripts/minassoc.m2`, `minassoc.log`, `DONE minassoc` 2026-07-08: all 21
$xy$-fiber coefficients in J at `DegreeLimit` 5, all 24 $t^4$-fiber
coefficients at `DegreeLimit` 6, J = associativity + $\Delta$-multiplicativity
equations only; gates 16.1/16.2 pass. Recorded as **Theorem F** in
`REPORT_order4.md`):

> **Target Lemma.** Let $R=k[\epsilon]/\epsilon^3$, let $A'$ be a free rank-4
> **commutative associative** counital $R$-algebra whose fiber is
> $k[x,y]/(x^2,y^2)$ or $k[t]/t^4$, and let $\Delta:A'\to A'\otimes A'$ be any
> **multiplicative, counitally normalized** linear map (no coassociativity, no
> condition on the fiber of $\varphi$). Then $(\mu\Delta)^2 = \eta\varepsilon$.

*(The Target Lemma is a theorem as of session 4 — the skeleton below is kept
because a **hand** proof, read off the `minassoc` certificates, remains the
route to the depth-uniform statement.)*

**Hand-proof skeleton for the Target Lemma (xy-fiber), from this session's
analysis** — each step is proved, the last is not:
1. $\varphi := \mu\Delta$ is an $R$-algebra endomorphism (M + A +
   commutativity), and $\varphi(I')\subseteq I'^2$ (Lemma 1.2, $2=0$),
   $\varepsilon\varphi = \varepsilon$.
2. $I'^2$ is spanned over $R$ by the products $e_ie_j$, so
   $\varphi^2(g) = \sum \rho_{ij}\,\varphi(e_i)\varphi(e_j)$: it suffices to
   control the nine products $\varphi(e_i)\varphi(e_j)$.
3. *Counit kills scalars*: for $u\in I'$ with $u^2 = \epsilon s$, applying
   $\varepsilon$ gives $\epsilon\varepsilon(s)=0$, so the deformed squares
   satisfy $e_i^2 \in \epsilon I'$ (after absorbing an $\epsilon^2$-scalar),
   and likewise the $\epsilon$-parts of $\varphi(e_i)$ can be taken in $I'$.
4. Writing $w := e_1e_2$ (lift of $xy$), one has $w^2 = e_1^2e_2^2 \in
   \epsilon^2 I'\cdot I'$-terms (char 2 + step 3), $I'^3\subseteq\epsilon I'$
   (fiber $I_H^3=0$), and $\varphi(e_i) = \rho_i w + \epsilon c_i$ with
   $c_i\in I'$: consequently **every** product
   $\varphi(e_i)\varphi(e_j)\in\epsilon^2\cdot(\text{explicit }I'\text{-classes})$
   — the obstruction is concentrated in the top layer, with explicit fiber
   representatives $\bar\rho_i\bar\rho_j\,\overline{v_1v_2} +
   \bar\rho_j(\overline{c_iw/\epsilon}) + \bar\rho_i(\overline{c_jw/\epsilon})
   + \bar c_i\bar c_j$ where $e_i^2 = \epsilon v_i$.
5. *(Open step)* Show the fiber classes of step 4 vanish using the
   $\Delta$-multiplicativity relations $\Delta(e_ie_j)=\Delta e_i\,\Delta e_j$
   expanded in structure constants ($\varphi(e_i) = \sum_{jk}c_{ijk}e_je_k$,
   so $\rho_i,c_i$ are explicit in the $c_{ijk}$ and the deformed
   multiplication table). This is a finite computation in the fiber $H$ — the
   right target for reading off the `minassoc.m2` certificates. Reading for
the hand proof: the identity $\psi^2=0$ is a statement about **multiplicative
counital comultiplications on a (possibly non-associative!) commutative
deformation of the fiber algebra** — coassociativity, which is where the
Gerstenhaber–Schack cocycle formalism spends most of its complexity, can be
discarded. Any conceptual proof should therefore be sought in the interplay
of $\Delta(ab)=\Delta a\,\Delta b$ with the two fiber shapes alone.

---

## 9. Uniformity in $p$ (order $p^2$), and what is special about 4

Everything in §§1–7 was written to be $p$-uniform:

* Lemmas 1.1–1.3, Proposition 1.4: hold verbatim with $2\rightsquigarrow p$,
  $4\rightsquigarrow p^2$, $\varphi\rightsquigarrow[p]^\#$ (an algebra
  endomorphism for any bialgebra with commutative underlying algebra).
* Lemma 2.1(a) fails for odd $p$ ($S=\mathrm{id}$ needs $g=g^{-1}$); (b) holds.
  For odd $p$, killed-by-$p$ order-$p^2$ group schemes over a field need not be
  commutative in general rank, but at order $p^2$... `[FLAG: for odd p the
  classification of killed-by-p fibers of order p^2 over a perfect field must be
  re-derived before porting Corollary C step 2]`.
* Theorem 3.1, Proposition 3.2: any $n$.
* §4, §5 (rigidity), §6 (graded structure), §7 (S′): verbatim for order $p^2$
  with fiber killed by $p$ (Remark 5.2). The *atomic identities*
  ($\psi_\alpha\psi_\beta+\psi_\beta\psi_\alpha=0$, $\psi_\alpha^2=0$, Open
  Lemma 7.4) need per-$p$ certificates; handoff §E.3 records the $p=3$ port
  plan, including $[3]^\# = \mu^{(3)}\Delta^{(3)}$ (not $[2]\circ$ anything).

What is special about $p=2$: killed-by-2 fibers are automatically commutative
*and* cocommutative ($(gh)^2=e \Rightarrow gh=hg$ functorially), which is what
makes the two fiber shapes exhaustive and Lemma 2.1(a) available.

---

## 10. Session-3 additions to the computational pipeline

| script | what it decides | validation gates |
|---|---|---|
| `scripts/len3gen.m2` | ideal membership over the **universal embdim-2 base** $k[s,t]/(s,t)^3$, both fiber shapes, fiber2 on; success $\Rightarrow$ polarized $\psi$-identities $\Rightarrow$ killed-by-4 over every equal-char Artin local base with $\mathfrak m^3=0$, $\dim\mathfrak m/\mathfrak m^2\le2$, arbitrary $k$ (subsumes Theorem A) | 16.1; 16.2 in the $s^2$ direction; **new** 16.2′ in the mixed $st$ direction — all three must print 0 violations before the GB results count |
| `scripts/ablate.py` | which axiom blocks are load-bearing for the length-3 identity (guides any hand proof of $\psi^2=0$) | gate0 `sat`, gate1 `unsat` (reproduces Theorem B); `ablF` must reproduce B′'s `unsat` |

Reading discipline for both: same as the handoff (partial GB results are proofs
for the coefficients they reduce; a `sat` in `ablate` is a pseudo-bialgebra,
never a counterexample).

## 11. Precise status after this session's theory

Let **(K)** denote: "every finite locally free group scheme of order 4 over
every base scheme is killed by 4".

**(K) is implied by** the conjunction of:
1. Open Lemma 7.4 (kernel factorization propagates), **or** per-depth
   certificates for all $\nu$ (each depth is finite by Proposition 6.3, but
   there are infinitely many depths);
2. the mixed-characteristic length-3 identities for all finite residue fields
   (curvilinear $\psi^2=0$): known for $\kappa = \mathbb F_2,\mathbb F_4$, and
   $W(\mathbb F_8)/8$; the running `z8search.m2` (all $\mathbb Z/8$-algebras)
   and the ramified analogue would close all unramified/ramified length-3 at
   once; plus their depth-$\ge4$ mixed analogues ($\mathbb Z/16$ etc., in
   `order4sat_beyond`), subject again to item 1;
3. the `[FLAG]`ed classical inputs: Schoof 2001 Thm 1.2 as stated over any
   Artin local base (handoff §G.2), and (only for the optional Remark 5.4)
   unobstructedness of commutative finite flat group schemes.

**Unconditionally proved as of this session** (given the report's banked
computations and modulo only flag 3a): killed-by-4 holds over every Artin local
ring of length $\le 3$ with residue field $\mathbb F_2, \mathbb F_4$ (Cor. C),
over $\mathbb F_2[\epsilon]/\epsilon^{4},\epsilon^5$, over all equal-char
bases covered by Theorem A, and — new, once `len3gen.m2` finishes and its
gates pass — over every equal-characteristic base with $\mathfrak m^3=0$ and
embedding dimension $\le 2$, for arbitrary $k$; moreover the global-to-local
Theorem 3.1 converts each such family into a statement about arbitrary
(non-local, non-noetherian) bases whose local Artin quotients fall in the
family.

*(Superseded in part by §12, session 8: the equal-characteristic
$\mathfrak m^3 = 0$ case is now closed in ALL embedding dimensions, by hand.)*

---

## 12. The first-order symbol theorem (session 8): $\psi^2 = 0$ unconditionally, by hand

This section proves, by hand, the unconditional first-order input $(\star)$
of Theorem 6.5.2 — the statement `symbolsq.m2` was launched to decide — for
every fiber bialgebra defined over a perfect field. Combined with the
polarization theorem 6.5.2 (banked, session 4) this **closes the
equal-characteristic case $\mathfrak m^3 = 0$ in all embedding dimensions.**
Every lemma below was machine-gated before being recorded:
`scripts/firstorder_gates.py` (log `firstorder_gates.log`,
`ALL FIRSTORDER GATES PASSED`, 51/51, 0 FAIL) checks each lemma-level claim
as a Z3 UNSAT statement over $\mathbb F_2[\epsilon]/\epsilon^2$ and
$\mathbb F_4[\epsilon]/\epsilon^2$ (the latter catching semilinearity
slips), plus pinned-fiber checks of each case computation; the base ring
$\mathbb F_4[\epsilon]/\epsilon^2$ was added to `ringcheck.py` CASES
(`OK` line: 16 elts, residue $\mathbb F_4$, chain $[4,1]$) and the full
battery re-passed: `ringcheck_s8.log` ends in `ALL RING CHECKS PASSED`
(verified in-session).

### 12.1 Setting and normal forms

Fix a commutative $\mathbb F_2$-algebra $k'$ and let $H$ be one of the two
fiber algebras $k'[x,y]/(x^2,y^2)$ (basis of $I = I_H$: $x, y, z := xy$) or
$k'[t]/t^4$ (basis $t, t^2, t^3$), equipped with a comultiplication $\Delta_0$
making it a bialgebra **killed by 2**: $\mu_0\Delta_0 = \eta\varepsilon$.
Write $\Delta_0 g = g\otimes 1 + 1\otimes g + w_0(g)$ for $g \in I$
(Lemma 1.1), $w_0(g) \in I \otimes I$.

Let $A$ be a free rank-4 bialgebra over $R = k'[e]/e^2$ with fiber $H$
(fiber2 condition; no liftability hypothesis). Choosing a basis of
$I_A = \ker\varepsilon_A$ lifting the basis of $I_H$ identifies
$A = H \oplus eH$ and splits the structure maps:
$\mu = \mu_0 + e\mu_1$, $\Delta = \Delta_0 + e\Delta_1$ with
$$\mu_1: I\otimes I \to I \ \text{symmetric},\qquad \Delta_1: I \to I\otimes I,$$
both normalizations automatic: $\mu_1(1,-) = 0$ since $1$ is the exact unit,
$\varepsilon\mu_1 = 0$ since $I_A$ is an ideal, $\Delta_1(1) = 0$ and
$\Delta_1(I)\subseteq I\otimes I$ by counitality (Lemma 1.1 applied over $R$),
and $\mu_1$ symmetric by commutativity of $A$. The **symbol** is
$$\psi := \text{the } e\text{-digit of } \varphi = \mu\Delta \text{ on } I,
\qquad \varphi(g) = e\,\psi(g),\qquad
\boxed{\psi(g) = \mu_0(\Delta_1 g) + \mu_1(w_0 g)}$$
(the $2g$-term dies, $\mu_0 w_0 = 0$ is fiber2, $\mu_1$ kills the
$g\otimes 1 + 1\otimes g$ part by normalization and symmetry).

**Lemma 12.1.1 (point-derivation property).** $\varepsilon\psi = 0$ and
$\psi(I_H^2) = 0$ (products in the FIBER algebra $H$).

*Proof.* $\varphi$ is an $R$-algebra endomorphism of $A$ (§0 conventions).
For $a, b \in H \subseteq A$: $a\cdot_A b = \mu_0(a,b) + e\mu_1(a,b)$, so
$\varphi(a\cdot_A b) = \varepsilon(ab)1 + e\,\psi(\mu_0(a,b))$ using
$\varepsilon\mu_1 = 0$; while $\varphi(a)\varphi(b) =
\varepsilon(a)\varepsilon(b)1 + e[\varepsilon(a)\psi(b) +
\varepsilon(b)\psi(a)]$. Hence $\psi(\mu_0(a,b)) = \varepsilon(a)\psi(b) +
\varepsilon(b)\psi(a)$, which vanishes on $I\cdot I$. $\square$

**Lemma 12.1.2 (automatic cocommutativity of the fiber).** Any killed-by-2
bialgebra $H$ over any commutative ring is cocommutative; in particular
$\tau w_0 = w_0$.

*Proof.* $S = \mathrm{id}$ is an antipode (Lemma 2.1(a), any base), so
$\operatorname{Spec} H$ is a group functor in which every point equals its own
inverse: $gh = (gh)^{-1} = h^{-1}g^{-1} = hg$. Yoneda. $\square$

### 12.2 The two workhorse identities

**Lemma 12.2.1 (diagonal primitivity).** Let $a \in I$ with $a^2 = 0$ in $H$.
Then
$$\Delta_0\,\mu_1(a,a) \;=\; \mu_1(a,a)\otimes 1 + 1\otimes\mu_1(a,a) + S(a),
\qquad S(a) := (\mu_1\otimes\mu_0 + \mu_0\otimes\mu_1)(1\tau 1)(w_0a\otimes w_0a).$$
In particular $\mu_1(a,a)$ is $\Delta_0$-**primitive** whenever $S(a) = 0$.

*Proof.* Apply $\Delta(\alpha\cdot_A\alpha) = (\Delta\alpha)(\Delta\alpha)$
with $\alpha = a$: the left side is $\Delta(e\mu_1(a,a)) =
e\,\Delta_0\mu_1(a,a)$ (as $a^2 = 0$); on the right, the $A\otimes A$-square
of $\Delta_0a + e\Delta_1a$ has $e$-digit $=$ [cross terms
$\Delta_1a\cdot\Delta_0a + \Delta_0a\cdot\Delta_1a = 0$, equal in the
commutative ring $H\otimes H$, char 2] $+$ [the $\mu_1$-legged part of
$(\Delta_0a)^{\cdot 2}$] $= \Gamma(a,a) :=
(\mu_1\otimes\mu_0+\mu_0\otimes\mu_1)(1\tau 1)(\Delta_0a\otimes\Delta_0a)$.
Expand $\Delta_0 a = a\otimes 1 + 1\otimes a + w_0a$ and use the
normalizations $\mu_1(1,-) = \mu_1(-,1) = 0$: the $(a\otimes 1, a\otimes 1)$
and $(1\otimes a, 1\otimes a)$ pairs give $\mu_1(a,a)\otimes 1 +
1\otimes\mu_1(a,a)$; the mixed pairs $(a\otimes 1, 1\otimes a)$ die by
normalization; each cross pair of $a\otimes 1$ (resp. $1\otimes a$) against a
Sweedler term $b_1\otimes b_2$ of $w_0a$ appears **twice** with the same value
$\mu_1(a,b_1)\otimes b_2$ (resp. $b_1\otimes\mu_1(a,b_2)$) — once from each
order — by symmetry of $\mu_1$, so cancels in char 2; the
$(w_0a, w_0a)$-part is $S(a)$ by definition. $\square$

**Lemma 12.2.2 (symmetric-pair cancellation).** For $g \in I$ write
$w_0g = \sum_{p\le q}\lambda_{pq}\,(e_p\otimes e_q + e_q\otimes e_p)
+ \sum_p \lambda_{pp}... $ — precisely, expanding $w_0g = \sum_{p,q}
\lambda_{pq}e_p\otimes e_q$ with $\lambda_{pq} = \lambda_{qp}$
(Lemma 12.1.2):
$$\mu_1(w_0 g) = \sum_p \lambda_{pp}\,\mu_1(e_p, e_p).$$
*Proof.* Off-diagonal pairs contribute $2\lambda_{pq}\mu_1(e_p,e_q) = 0$
($\mu_1$ symmetric, char 2). $\square$

So the possibly-non-$I^2$ part of $\psi(g)$ is a $k'$-combination of the
**diagonal values** $\mu_1(e_p,e_p)$, which Lemma 12.2.1 locates among the
$\Delta_0$-primitives whenever the relevant $S$-terms vanish.

**Lemma 12.2.3 ($S \equiv 0$ for the $xy$ fiber).** If $H =
k'[x,y]/(x^2,y^2)$ then $S(a) = 0$ for every $a \in I$ (note every $a\in I$
has $a^2 = 0$ there).

*Proof.* Write $w_0a = \sum w_{pq}e_p\otimes e_q$, $w$ symmetric. The first
half of $S(a)$ is $\sum_{p,q,r,s}w_{pq}w_{rs}\,\mu_1(e_p,e_r)\otimes e_qe_s$.
In this $H$, $e_qe_s \ne 0$ only for $\{q,s\} = \{1,2\}$ (value $z$), so the
coefficient of $\mu_1(e_p,e_r)\otimes z$ is $w_{p1}w_{r2} + w_{p2}w_{r1}$,
symmetric in $(p,r)$: the $p \ne r$ terms cancel in pairs against
$\mu_1(e_r,e_p) = \mu_1(e_p,e_r)$, and the $p = r$ terms are
$2w_{p1}w_{p2} = 0$. The second half is the mirror image. $\square$

**Lemma 12.2.4 (first-order coassociativity).** For $g \in I$:
$$(w_0\otimes 1)\Delta_1 g + (1\otimes w_0)\Delta_1 g
= (\Delta_1\otimes 1)w_0 g + (1\otimes\Delta_1)w_0 g .$$
*Proof.* Take the $e$-digit of $(\Delta\otimes 1)\Delta g =
(1\otimes\Delta)\Delta g$ and cancel the fourteen terms that appear on both
sides, exactly as in the order-0 computation before §8 (the order-0 identity
is $(w_0\otimes 1)w_0 = (1\otimes w_0)w_0$). $\square$

**Lemma 12.2.5 (Hochschild relations, $xy$ fiber).** First-order
associativity of $\mu$ gives, for all $a,b,c \in H$,
$a\mu_1(b,c) + \mu_1(ab,c) + \mu_1(a,bc) + \mu_1(a,b)c = 0$. Taking
$(a,b,c) = (x,x,y)$, $(y,y,x)$, $(z,x,y)$ yields
$$\mu_1(x,z) = x\mu_1(x,y) + y\mu_1(x,x),\quad
\mu_1(y,z) = y\mu_1(x,y) + x\mu_1(y,y),\quad
\boxed{\mu_1(z,z) = 0}.$$
*Proof of the last:* $z\mu_1(x,y) + \mu_1(zx,y) + \mu_1(z,z) + \mu_1(z,x)y
= 0$ with $zx = 0$; substitute the first relation:
$\mu_1(z,x)y = (x\mu_1(x,y) + y\mu_1(x,x))y = z\mu_1(x,y)$ (using $y^2 = 0$,
$yz=0$, associativity of $H$), which cancels the first term. $\square$

### 12.3 The $t^4$ fiber: $\psi(I) \subseteq I^2$, with no classification input

**Lemma 12.3.1 (shape of $\Delta_0$, axiomatic, any $k'$).** For
$H = k'[t]/t^4$: (i) $w_0t \in
\operatorname{span}\{t\circ t^2,\ t\circ t^3,\ t^2\circ t^3,\ t^2\otimes t^2,\
t^3\otimes t^3\}$ where $u\circ v := u\otimes v + v\otimes u$ — the
$t\otimes t$ coefficient is killed exactly by fiber2 ($\mu_0w_0 = 0$); every
such $w_0t$ automatically satisfies $(\Delta_0t)^4 = 0$, so multiplicativity
is free. (ii) $t^2$ is primitive: $w_0(t^2) = 0$ (square $\Delta_0t$ in char
2 and use $w^2 = 0$, which holds term by term). (iii) Writing $w_0t =
c_1\,t\circ t^2 + c_2\,t\circ t^3 + c_3\,t^2\circ t^3 + c_4\,t^2\otimes t^2 +
c_5\,t^3\otimes t^3$, one has $w_0(t^3) = t\circ t^2 + c_1\,t^2\circ t^3$
(from $\Delta_0t^3 = \Delta_0t\,\Delta_0t^2$), and coassociativity of
$\Delta_0$ forces
$$c_2 = 0,\qquad c_5 = 0,\qquad c_3 = c_1^2 .$$
(iv) Consequently the primitives of $H$ are
$$\operatorname{Prim}(H) = \{\,at + bt^2 + ac_1t^3\ :\ a\,c_4 = 0\,\}.$$

*Proof.* (i), (ii) are the computations displayed. For (iii): the
coassociativity of $\Delta_0$ at $t$ reads $(w_0\otimes 1)w_0t =
(1\otimes w_0)w_0t$ with $w_0t^2 = 0$ and $w_0t^3$ as computed; expanding in
the monomial basis of $I^{\otimes 3}$, the coefficient of
$t\otimes t\otimes t^2$ is $c_2$ (unique source: $t\otimes w_0t^3$), the
coefficient of $t\otimes t^2\otimes t^3$ is $c_5$ (unique source:
$w_0t^3\otimes t^3$), and the coefficient of $t\otimes t^2\otimes t^2$ is
$c_1^2 + c_3$ (sources: $w_0t\otimes t^2$ via its $t\circ t^2$-term, and
$w_0t^3\otimes t^2$ via its $t\circ t^2$-term); all remaining coefficients
cancel identically. For (iv): $w_0(at+bt^2+ct^3) = a\,w_0t + c\,w_0t^3$ has
$t\circ t^2$-coefficient $ac_1 + c$, $t^2\circ t^3$-coefficient
$c_1(ac_1+c)$, and $t^2\otimes t^2$-coefficient $ac_4$. $\square$

**Theorem 12.3.2 ($t^4$ fiber, unconditional, any $k'$, any $\Delta_0$).**
Every first-order deformation as in §12.1 with fiber $k'[t]/t^4$ satisfies
$$\psi(I) \subseteq I^2\quad\text{and}\quad \psi(I^2) = 0;\qquad
\text{in particular } \psi^2 = 0 .$$

*Proof.* $\psi(t^2) = \psi(t^3) = 0$ by Lemma 12.1.1 ($t^2, t^3 \in I^2$
are fiber products). For $\psi(t) = \mu_0(\Delta_1t) + \mu_1(w_0t)$: the
first summand is in $I^2$; by Lemmas 12.2.2 and 12.3.1(iii) the second is
$c_4\,\mu_1(t^2,t^2)$ ($c_5 = 0$). By Lemma 12.2.1 at $a = t^2$ — where
$S(t^2) = 0$ because $w_0t^2 = 0$ — $\mu_1(t^2,t^2) =: at + bt^2 + ct^3$ is
primitive, so $ac_4 = 0$ and $c = ac_1$ by 12.3.1(iv). Then
$$c_4\,\mu_1(t^2,t^2) = (c_4a)t + c_4b\,t^2 + (c_4a)c_1t^3 = c_4b\,t^2 \in
I^2 .$$
So $\psi(I) \subseteq I^2$, and $\psi^2 = 0$ follows from
$\psi(I^2) = 0$. $\square$

*(Machine gates: `t4 P3`, `P4`, `P5a/b`, `P7` and the pinned checks
`PIN-aF2`, `PIN-c4` — the latter confirming both that the $c_4\ne0$ family
of $\Delta_0$'s exists (sanity `sat`) and that the $a c_4 = 0$ mechanism
kills the $t$-component there.)*

### 12.4 The $xy$ fiber: classification over the algebraic closure + descent

**Lemma 12.4.1 (split classification).** Let $\kappa$ be an algebraically
closed field of characteristic 2. Every killed-by-2 bialgebra structure
$\Delta_0$ on $H_0 = \kappa[x,y]/(x^2,y^2)$ is isomorphic to exactly one of:
$$\begin{array}{llll}
(1)\ \alpha_2\times\alpha_2: & w_0x = 0, & w_0y = 0, & w_0z = x\circ y;\\
(2)\ W_2[F]: & w_0x = 0, & w_0y = x\otimes x, & w_0z = x\circ y;\\
(3)\ \mu_2\times\mu_2: & w_0x = x\otimes x, & w_0y = y\otimes y, &
w_0z = x\circ y + x\circ z + y\circ z + z\otimes z;\\
(4)\ \mu_2\times\alpha_2: & w_0x = x\otimes x, & w_0y = 0, &
w_0z = x\circ y + x\circ z.
\end{array}$$
($w_0z$ is determined by multiplicativity: $\Delta_0z =
\Delta_0x\,\Delta_0y$.)

*Proof.* $G := \operatorname{Spec}H_0$ is commutative (12.1.2) and killed by
2. Every element of $I$ squares to zero, so the relative Frobenius of $G$
vanishes and $G$ has height $\le 1$; by the height-one correspondence
(Demazure–Gabriel II §7; SGA3 VII$_A$ 7.2–7.4) $G \leftrightarrow$ its
2-dimensional restricted Lie algebra $(\mathfrak g, \xi)$, abelian since $G$
is commutative, with $\xi$ the 2-operation — a Frobenius-semilinear
endomorphism of $\mathfrak g$. Over $\bar\kappa = \kappa$, semilinear
endomorphisms of a 2-dimensional space are classified by rank and the induced
behavior on the image line: $\xi = 0$; $\xi$ nilpotent of rank 1; $\xi$
bijective ($\simeq \mathrm{id}$ by Lang's theorem for $GL_2$); $\xi$ of rank
1 with $\xi(\operatorname{im}\xi) = \operatorname{im}\xi$ ($\simeq$ the
idempotent model, again normalizing by Lang on the image line). These give
(1), (2), (3), (4) respectively. The four are pairwise non-isomorphic (e.g.
by $\dim\operatorname{Prim}$ and unipotence). $\square$

**Lemma 12.4.2 (primitives of the four models).**
$\operatorname{Prim} = \operatorname{span}(x,y),\ \kappa x,\ 0,\ \kappa y$
in cases (1), (2), (3), (4) respectively (over any base extension: formation
of $\operatorname{Prim} = \ker w_0$ commutes with flat base change since
$w_0$ is a matrix over the field of definition). Direct check from the
$w_0$-tables: e.g. in (2), $w_0(px+qy+rz) = q\,x\otimes x + r\,x\circ y$.

**Theorem 12.4.3 ($xy$ fiber).** Let $\kappa$ be a perfect field of
characteristic 2, $\Delta_0$ a killed-by-2 structure on
$H_\kappa := \kappa[x,y]/(x^2,y^2)$, $k'$ any commutative $\kappa$-algebra.
Then every first-order deformation as in §12.1 of $H = H_\kappa\otimes k'$
satisfies $\psi^2 = 0$.

*Proof.* **Descent.** $k'' := k'\otimes_\kappa\bar\kappa$ is faithfully flat
over $k'$, and $\psi_{k''} = \psi\otimes 1$, so we may replace $k'$ by $k''$
and $\Delta_0$ by an isomorphic split model (Lemma 12.4.1); transporting the
whole deformation along the isomorphism conjugates $\psi$, preserving
$\psi^2 = 0$. So assume $\Delta_0 \in \{(1),(2),(3),(4)\}$, $k' \supseteq
\bar\kappa$.

By Lemmas 12.2.2, 12.2.5 and 12.2.1+12.2.3 (all diagonal $\mu_1(a,a)$,
$a \in I$, are primitive; $\mu_1(z,z) = 0$):
$$\psi(x) \equiv \mu_1(w_0x)_{\mathrm{diag}},\qquad
\psi(y) \equiv \mu_1(w_0y)_{\mathrm{diag}} \pmod{I^2},$$
with the non-$I^2$ parts lying in $\operatorname{Prim}(\Delta_0)$, and
$\psi(z) = 0$, $\psi(I^2) = 0$ (12.1.1).

*Case (1).* $w_0x = w_0y = 0$: $\psi(I) \subseteq I^2$, done.

*Case (3).* $\mu_1(x,x), \mu_1(y,y) \in \operatorname{Prim} = 0$, so again
$\psi(I) \subseteq I^2$. (Gate `PIN-mu2mu2`: indeed $x\cdot_A x = 0$
identically there.)

*Case (2).* $\psi(x) = \mu_0\Delta_1x$ and $\mu_1(x,x) = \lambda x$
($\operatorname{Prim} = k''x$). Coassociativity (12.2.4) at $g = x$, whose
right side vanishes ($w_0x = 0$), reads $\sum_{i,j}(\Delta_1x)_{ij}
[w_0e_i\otimes e_j + e_i\otimes w_0e_j] = 0$; the coefficient of
$x\otimes x\otimes x$ is $(\Delta_1x)_{yx} + (\Delta_1x)_{xy}$ (sources:
$w_0y = x\otimes x$ in leg 1, and in leg 2), so $\mu_0\Delta_1x =
[(\Delta_1x)_{xy} + (\Delta_1x)_{yx}]\,z = 0$: $\psi(x) = 0$ exactly. Then
$\psi(y) = \mu_0\Delta_1y + \lambda x$ and $\psi^2(y) =
\psi(\mu_0\Delta_1 y) + \lambda\psi(x) = 0$. (Gate `PIN-W2F`: $\varphi(e_1)
= 0$ identically; $\mu_1(x,x) \in k\,x$; and $\lambda \ne 0$ is realizable —
non-vacuity `sat`.)

*Case (4).* Mirror image: $\mu_1(x,x) = \lambda y$
($\operatorname{Prim} = k''y$), $\psi(y) = \mu_0\Delta_1y$. Coassociativity
at $g = y$ (right side vanishes, $w_0y = 0$): with $w_0x = x\otimes x$ and
$w_0z = x\circ y + x\circ z$, the coefficients of $x\otimes x\otimes y$,
$y\otimes x\otimes x$, $x\otimes y\otimes x$ give
$(\Delta_1y)_{xy} = (\Delta_1y)_{xz} = (\Delta_1y)_{zx} = (\Delta_1y)_{yx}$,
whence $\mu_0\Delta_1y = [(\Delta_1y)_{xy} + (\Delta_1y)_{yx}]z = 0$:
$\psi(y) = 0$ exactly, and $\psi^2(x) = \psi(\mu_0\Delta_1x) +
\lambda\psi(y) = 0$. (Gate `PIN-mu2a2`.) $\square$

### 12.5 The theorem and its consequences

**Theorem 12.5.1 (first-order symbol theorem; "Theorem I" of the report).**
Let $\kappa$ be a perfect field of characteristic 2, $H_\kappa$ a rank-4
killed-by-2 bialgebra over $\kappa$ whose underlying algebra is
$\kappa[x,y]/(x^2,y^2)$ or $\kappa[t]/t^4$, and $k'$ any commutative
$\kappa$-algebra. Then every free rank-4 bialgebra over $k'[e]/e^2$ with
fiber $H_\kappa\otimes k'$ (no liftability hypothesis) has $\psi^2 = 0$.
For the $t^4$ algebra the conclusion holds with no perfectness or
field-of-definition hypothesis at all ($\Delta_0$ arbitrary over arbitrary
$k'$), in the stronger form $\psi(I)\subseteq I^2$.

This is exactly hypothesis $(\star)$ of Theorem 6.5.2 in the only generality
that theorem consumes (the fiber there is defined over the residue field,
which is perfect after the Theorem 3.1 reduction). Hence:

**Corollary 12.5.2 (equal characteristic, $\mathfrak m^3 = 0$, all embedding
dimensions).** Every free rank-4 bialgebra with local killed-by-2 fiber over
every equal-characteristic Artin local ring $(R,\mathfrak m,\kappa)$ with
$\mathfrak m^3 = 0$ and perfect residue field is killed by 4. Consequently
(Lemma 2.1, connected–étale, Tate–Oort, and — for fibers not killed by 2 —
the Schoof reduction carrying flag G.2, exactly as in Corollary C) **every
finite locally free group scheme of order 4 over every Artin local
$\mathbb F_2$-algebra with $\mathfrak m^3 = 0$ and finite residue field is
killed by 4**, with no restriction on the embedding dimension; and via
Theorem 3.1 the same holds over any base scheme all of whose finite-residue
Artin local quotients satisfy $\mathfrak m^3 = 0$ in equal characteristic 2.

**Corollary 12.5.3 (hand reproof of Theorems A and F at $\epsilon^3$, and of
the length-3 equal-char part of Corollary C).** Immediate from 12.5.2 —
the first hand proof of the facts that started the project.

**What 12.5.1 retires or demotes.**
* `len3gen.m2` (universal embdim-2) and the planned embdim-3 analogue:
  subsumed for the group-scheme question; now audit-only.
* `symbolsq.m2`: its verdict would extend 12.5.1's $xy$ half to fiber
  structures over arbitrary (imperfect) coefficient rings — content the
  group-scheme question never consumes (Theorem 3.1); audit-only.
* The remaining `order4sat_f8` queries ($\mathbb F_8[\epsilon]/\epsilon^3$):
  instances of 12.5.2; the job (dead as of session 8) is not worth
  relaunching.
* `Ext(FatPoint3)` $= \mathbb F_4[x,y]/(x,y)^3$ in `order4sat_beyond`:
  instance of 12.5.2; demoted to the audit tail of the job list.

### 12.6 The layer-symbol reformulation of curvilinear S′ (the depth program)

**Proposition 12.6.1.** Let $R = k'[\epsilon]/\epsilon^N$ (equal
characteristic), $A$ free rank-4 with killed-by-2 fiber, presented as in
§12.1 with $\mu = \sum_j\epsilon^j\mu_j$, $w = \sum_l\epsilon^l w_l$. Define
the **layer symbols** $\Psi_n := \sum_{j+l=n}\mu_j\circ w_l : I_H \to I_H$
($n \ge 1$; $\Psi_1 = \psi$ of the truncation $A/\epsilon^2$). Then
$\varphi(g) = \sum_{n\ge1}\epsilon^n\widetilde{\Psi_n(g)}$ and, with
$\delta_i$ the S′-defect of Proposition 7.5.1,
$$\delta_i \;=\; \sum_{s\ge2}\epsilon^{s-1}
\Big[\textstyle\sum_{m+n=s}\Psi_m\Psi_n\Big](e_i) \pmod{\epsilon^N},$$
so that
$$\text{S}'(A/R) \iff \sum_{m+n=s}\Psi_m\Psi_n = 0 \text{ on } I_H
\text{ for all } 2 \le s \le N,\qquad
[4]^\#_A = \eta\varepsilon \iff \text{the same for } s \le N-1 .$$

*Proof.* $\varphi(\epsilon^k h) = \epsilon^k\varphi(h)$ and
$\mu_0w_0 = 0$ give the expansion of $\varphi$; $v_i =
\sum_n \epsilon^{n-1}\widetilde{\Psi_n(e_i)}$ is a valid division of
$\varphi(e_i)$ by $\epsilon$, and $\delta_i = \varphi(v_i)$ is
division-independent (7.5.1(ii)); expand again. A layer
$\epsilon^{s-1}(\cdot)$ vanishes iff its $H$-coefficient does, for
$s-1 \le N-1$. $\square$

**Corollary 12.6.2 ($s = 2$ for every tower).** Theorem 12.5.1 applied to
the truncation $A/\epsilon^2$ gives $\Psi_1^2 = 0$ for EVERY $A$ over EVERY
$k'[\epsilon]/\epsilon^N$ (fiber over a perfect field). This is the $s = 2$
identity; killedness over $\epsilon^3$ is exactly $s = 2$ (whence 12.5.3).

**The depth program, restated.** Curvilinear equal-char S′-universality
(the equal-char curvilinear case of Conjecture 7.5.4) is now the family of
identities $\sum_{m+n=s}\Psi_m\Psi_n = 0$, $s \ge 3$. The obstruction-theory
data available at layer $s$: $(\mu_s, w_s)$ satisfy the order-$s$ bialgebra
axioms with Gerstenhaber-type carries in the lower layers; the layer-$s$
analogue of Lemma 12.1.1 is
$$\Psi_s(\mu_0(a,b)) = \sum_{\substack{l+n=s\\ l,n\ge1}}\Psi_n(\mu_l(a,b))
+ \sum_{\substack{m+n+l=s\\ m,n\ge1,\ l\ge0}}\mu_l(\Psi_ma,\Psi_nb)
\qquad(a,b\in I),$$
so for the $t^4$ fiber $\Psi_2(I^2) \subseteq \Psi_1(I) + I^4 \subseteq
I^2$: the layers do NOT kill $I^2$, only move it, and $s = 3$ genuinely
requires the layer-2 analogues of the two workhorse identities (12.2.1 with
carries; 12.2.4 at order 2). **Session-9 update: the $s = 3$ identity is
now PROVED for the $t^4$ fiber — §12.6.4.** Remaining: $s = 3$ for the
$xy$ fiber, then the $s \ge 4$ family; success for all $s$ would close
equal-characteristic curvilinear bases of every length, and with the
(still open) non-principal-$\mathfrak m$ version, all of equal
characteristic via the socle induction of §7.

**12.6.3 Beachhead for $s = 3$, $t^4$ fiber (session 8, partial — three
layer-2 identities proved, statement NOT yet closed).** Notation:
$w = \sum\epsilon^lw_l$, $\mu = \sum\epsilon^j\mu_j$,
$Y := w_1(t^2)$, $u := \mu_1(t^2,t^2) = at + bt^2 + ac_1t^3$ with
$ac_4 = 0$ (Theorem 12.3.2 applied to $A/\epsilon^2$),
$v := \mu_2(t^2,t^2)$.

1. *($m_1$-cross-cancellation.)* In the $\epsilon^2$-digit of
   $\Delta(t^2\cdot t^2) = (\Delta t^2)^2$, the mixed
   $m_1$-terms $m_1(X,Y) + m_1(Y,X)$ ($X = \Delta_0t^2 = t^2\otimes 1 +
   1\otimes t^2$) vanish identically by symmetry of $\mu_1$ — even though
   $Y$ is not symmetric. Likewise the $(\mu_1\otimes\mu_1)$-part of
   $m_2(X,X)$ vanishes by normalization.
2. *(Layer-2 diagonal identity at $t^2$.)* Consequently
   $$w_0(v) = \Delta_1(u) + Y\cdot_0 Y$$
   — i.e. $v$ is primitive up to two computable defects. Matching the
   $t^2\otimes t^2$-coefficient against 12.3.1(iv) gives
   $c_4\,v_t = [\Delta_1u + Y^{\cdot_0 2}]_{t^2\otimes t^2}$, the layer-2
   analogue of the $ac_4 = 0$ mechanism.
3. *(First-order $\Delta$-multiplicativity at $(t,t)$ determines $Y$.)*
   $$Y = \Delta_0(\mu_1(t,t)) + \Gamma(t,t),\qquad
   \Gamma(t,t) = (\mu_1\otimes\mu_0+\mu_0\otimes\mu_1)(1\tau1)
   (\Delta_0t\otimes\Delta_0t),$$
   so $Y$ — hence both defects in (2) — is expressible in layer-1 data.
   Also proved en route (Hochschild): $\mu_1(t^3,t^3) = at^3$,
   $\mu_1(t,t^3)_t = a$, $\mu_1(t^2,t^3)_t = 0$, so
   $$(\Psi_2 t)_t = p\,\beta_{11} + q(\beta_{12}+\beta_{21})
   + a(\beta_{13}+\beta_{31}+\beta_{22}) + c_4v_t,$$
   $\beta = $ matrix of $w_1(t)$, $p = \mu_1(t,t)_t$, $q = \mu_1(t,t^2)_t$.
   The open computation: substitute (3) into (2), use the order-1
   coassociativity (12.2.4) relating $w_1t$ to $w_1t^2, w_1t^3$, and decide
   whether $(\Psi_2t)_t = 0$ (the layer-2 analogue of $\psi(I)\subseteq
   I^2$) or only the full $s = 3$ sum cancels.

   **Probe outcome (`scripts/s3probe.py`, run session 8, `DONE`):** over
   $\mathbb F_2[\epsilon]/\epsilon^3$, "$\varphi(e_1)$ has an
   $e_1$-component" is **`sat`** (t⁴ fiber; likewise the $xy$/
   $\alpha_2{\times}\alpha_2$-pinned probe): $(\Psi_2t)_t \ne 0$ is
   realizable, so the layer-1 mechanism does NOT persist per-symbol; the
   $s = 3$ identity (true — Theorem G at $\epsilon^3$) holds only through
   cancellation inside $\Psi_1\Psi_2 + \Psi_2\Psi_1$. Useful positive:
   "$\varphi(I^2)$ has an $e_1$-component" is **`unsat`** — candidate lemma
   $\Psi_n(I^2) \subseteq I^2$. Since $\Psi_1$ kills $I^2$ and
   $\Psi_1(I)\subseteq I^2$, both summands of the $s=3$ sum land in $I^2$:
   $\Psi_1\Psi_2(g) = (\Psi_2g)_t\,\Psi_1(t)$ and $\Psi_2\Psi_1(g) \in
   \Psi_2(I^2) \subseteq I^2$ — the hand proof must show these two
   $I^2$-valued terms are EQUAL (char 2). That target is now closed:
   **§12.6.4 below.**

### 12.6.4 The $s = 3$ theorem for the $t^4$ fiber (session 9, by hand, machine-gated)

Throughout: $k'$ a commutative $\mathbb F_2$-algebra, $H = k'[t]/t^4$ with
an arbitrary counital multiplicative coassociative $\Delta_0$ killed by 2
(fiber2), $A$ a free rank-4 bialgebra over $R = k'[\epsilon]/\epsilon^3$
with fiber $H$ — **no liftability, no perfectness, no field of definition**
(the $t^4$ story stays fully axiomatic, as in 12.3). Basis of $I_A$ lifting
$t, t^2, t^3$; layers $\mu = \mu_0 + \epsilon\mu_1 + \epsilon^2\mu_2$,
$w = w_0 + \epsilon w_1 + \epsilon^2 w_2$, with the §12.1 normalizations at
every layer ($\mu_j$ symmetric, $\mu_j(1,-) = 0$, $w_l(I) \subseteq
I\otimes I$ — same proofs, since $1$ is the exact unit and $\varepsilon_A$
is exact projection in the chosen basis). Every displayed lemma below is a
Z3 gate in `scripts/s3gates.py` (log `s3gates.log`), run over
$\mathbb F_2[\epsilon]/\epsilon^3$ AND
$\mathbb F_4[\epsilon]/\epsilon^3$ — gate labels quoted as [G·].

**Notation.** $w_0t = c_1\,t{\circ}t^2 + c_1^2\,t^2{\circ}t^3 +
c_4\,t^2{\otimes}t^2$, $w_0t^2 = 0$, $w_0t^3 = t{\circ}t^2 +
c_1\,t^2{\circ}t^3$ (the 12.3.1 normal form; [G2]).
$\beta := w_1t$, $Y := w_1t^2$, $\Theta := w_1t^3$ (matrices, entries
$\beta_{jk}$ etc.). $\mu_1(t,t) = pt + p_2t^2 + p_3t^3$,
$q := \mu_1(t,t^2)_t$, $u := \mu_1(t^2,t^2) = at + bt^2 + ac_1t^3$ with
$ac_4 = 0$ (Theorem 12.3.2 on $A/\epsilon^2$; [G1b, G1c]),
$v := \mu_2(t^2,t^2)$. By 12.2.2 and the normal form,
$$\Psi_1t = \mu_0(w_1t) + \mu_1(w_0t) = Bt^2 + Ct^3,\qquad
B = \beta_{11} + c_4b,\quad C = \beta_{12} + \beta_{21},$$
and $\Psi_1(t^2) = \Psi_1(t^3) = 0$ (12.1.1; [G1a]).
$\lambda := pc_1 + p_3 + ac_1^2$.

**Step 1 (layer-2 multiplicativity).** For $a', b' \in I_H$,
$$\Psi_2(\mu_0(a',b')) = \Psi_1(\mu_1(a',b')) + \mu_0(\Psi_1a', \Psi_1b')$$
(the $\epsilon^2$-digit of $\varphi(a'\cdot_A b') = \varphi(a')\varphi(b')$;
$\varphi(x) \in \epsilon I_A$ makes the right product contribute only
$\mu_0$ of the two $\epsilon$-digits). With $(a',b') = (t,t), (t,t^2)$ and
$\Psi_1(I^2) = 0$, $(\Psi_1t)^2 \in I^4 = 0$:
$$\boxed{\Psi_2(t^2) = p\,\Psi_1(t),\qquad \Psi_2(t^3) = q\,\Psi_1(t)}
\qquad\text{[G7]}$$
— in particular $\Psi_2(I^2) \subseteq I^2$ with **zero** $t$-component,
sharpening probe Q2 of 12.6.3.

**Step 2 (shape of $Y$).** The $\epsilon$-digit of $\Delta(t\cdot_A t) =
(\Delta t)^2$ reads $w_1(t^2) + \Delta_0(\mu_1(t,t)) = \Gamma(t,t)$, and the
12.2.1 expansion of $\Gamma(t,t)$ (valid verbatim at $a = t$, $t^2 \ne 0$ —
only the LHS changes) gives $\Gamma(t,t) = \mu_1(t,t)\otimes 1 + 1\otimes
\mu_1(t,t) + S(t)$, whence $Y = w_0(\mu_1(t,t)) + S(t)$. Direct evaluation
of $S(t) = (\mu_1\otimes\mu_0 + \mu_0\otimes\mu_1)(1\tau1)(w_0t\otimes w_0t)$
on the normal form: the only surviving pairs are $(t^2{\otimes}t,
t^2{\otimes}t)$ and its mirror (all others have $\mu_0$-leg of degree
$\ge 4$ or cancel in symmetric pairs), so $S(t) = c_1^2(u\otimes t^2 +
t^2\otimes u) = c_1^2[a\,t{\circ}t^2 + ac_1\,t^2{\circ}t^3]$. Adding
$w_0(\mu_1(t,t)) = p\,w_0t + p_3\,w_0t^3$:
$$\boxed{Y = \lambda\,w_0(t^3) + pc_4\,t^2{\otimes}t^2}\qquad\text{[G3]}$$

**Step 3 (degenerate layer-2 diagonal identity).** Since every entry of $Y$
is decomposable of leg-degrees $(1,2),(2,1),(2,3),(3,2),(2,2)$, the
char-2 square $Y^2$ in $H\otimes H$ is a sum of squares each containing a
$t^4$-leg: $Y^2 = 0$. The $\epsilon^2$-digit of $\Delta(t^2\cdot_A t^2) =
(\Delta t^2)^2$ (12.6.3 items (1)-(2)) therefore collapses to
$$w_0(v) = w_1(u).$$
Extract the $t^2{\otimes}t^2$-coefficient: on the left $c_4v_t$ ($w_0t^3$
has no such entry); on the right $[w_1u]_{t^2\otimes t^2} = a\beta_{22} +
b\,[Y]_{22} + ac_1[\Theta]_{22} = a\beta_{22} + pbc_4 + ac_1\cdot qc_4$,
using $[Y]_{22} = pc_4$ (Step 2) and $[\Theta]_{22} = qc_4$ [G5], the latter
from the $\epsilon$-digit of $\Delta(t\cdot_A t^2) = \Delta t\,\Delta t^2$:
$$\Theta = w_0(\mu_1(t,t^2)) + X_0Y + \beta Z_0 + Q',\qquad
X_0 = \Delta_0t,\ Z_0 = \Delta_0t^2,$$
$Q' = \sum_{(w_0t)}[\mu_1(\omega_1,t^2)\otimes\omega_2 + \omega_1\otimes
\mu_1(\omega_2,t^2)]$, whose $t^2{\otimes}t^2$-coefficients are $qc_4$, $0$,
$0$, $0$ respectively (the $X_0Y$-contribution is $2\lambda = 0$; the $Q'$
ones cancel in mirror pairs). With $ac_4 = 0$:
$$\boxed{c_4v_t = a\beta_{22} + pbc_4}\qquad\text{[G6]}$$

**Step 4 ($\beta_{13} = \beta_{31}$).** Order-1 coassociativity (12.2.4):
$(w_0\otimes 1)\beta + (1\otimes w_0)\beta = (w_1\otimes 1)w_0t +
(1\otimes w_1)w_0t$. Coefficient of $t\otimes t\otimes t^2$: left
$= c_1\beta_{11} + \beta_{13}$ (sources: $t^{(1)}\otimes w_0t^{(j)}$ with
$j = 1, 3$; no $w_0$ has a $t{\otimes}t$-entry), right $= c_1\beta_{11} +
c_1^2\Theta_{11} + c_1\lambda$ (sources: $c_1\beta\otimes t^2$,
$c_1^2\Theta\otimes t^2$, $c_1 t\otimes Y$ via $[Y]_{12} = \lambda$).
Coefficient of $t^2\otimes t\otimes t$: left $= c_1\beta_{11} + \beta_{31}$,
right $= c_1\lambda + c_1\beta_{11} + c_1^2\Theta_{11}$ (sources:
$c_1Y\otimes t$ via $[Y]_{21} = \lambda$, $c_1t^2\otimes\beta$,
$c_1^2t^2\otimes\Theta$). Hence
$$\boxed{\beta_{13} = c_1\lambda + c_1^2\Theta_{11} = \beta_{31}}
\qquad\text{[G4a-c]}$$

**Step 5 (Hochschild values).** First-order associativity
$a'\mu_1(b',c') + \mu_1(a'b',c') + \mu_1(a',b'c') + \mu_1(a',b')c' = 0$ at
$(t,t,t^2)$, $(t,t^2,t^2)$, $(t,t^2,t^3)$ gives
$$\mu_1(t,t^3) = u + t\mu_1(t,t^2) + t^2\mu_1(t,t),\quad
\mu_1(t^2,t^3) = tu + \mu_1(t,t^2)t^2,\quad \mu_1(t^3,t^3) = at^3,$$
so $\mu_1(t,t^3)_t = a$, $\mu_1(t^2,t^3)_t = 0$, $\mu_1(t^3,t^3)_t = 0$
[G10].

**Step 6 (assembly).** $\Psi_2t = \mu_0(w_2t) + \mu_1(w_1t) + \mu_2(w_0t)$;
the first lies in $I^2$; the third is $c_4v$ by symmetric-pair cancellation
(12.2.2 applies to $\mu_2$ verbatim). Taking $t$-components with Step 5:
$$(\Psi_2t)_t = p\beta_{11} + q(\beta_{12}{+}\beta_{21}) +
a(\beta_{13}{+}\beta_{31}) + a\beta_{22} + c_4v_t
\overset{\text{Step 3}}{=} p(\beta_{11}{+}bc_4) + qC +
a(\beta_{13}{+}\beta_{31}) \overset{\text{Step 4}}{=} pB + qC.
\qquad\text{[G8]}$$

**Theorem 12.6.4.1 ($s = 3$, $t^4$ fiber, unconditional).** For every $A$
as above,
$$\Psi_1\Psi_2 + \Psi_2\Psi_1 = 0 \text{ on } I_H.$$

*Proof.* For $g \in I_H$ write $g = g_t\,t + (\text{$I^2$-part})$. By Step 1
the $I^2$-part contributes $t$-componentlessly to $\Psi_2g$ and is killed by
$\Psi_1$; hence $\Psi_1\Psi_2(g) = g_t\,(\Psi_2t)_t\,\Psi_1(t) =
g_t(pB{+}qC)\Psi_1t$ (Step 6), while $\Psi_2\Psi_1(g) =
g_t[B\,\Psi_2(t^2) + C\,\Psi_2(t^3)] = g_t(Bp{+}Cq)\Psi_1t$ (Step 1). Char
2. $\square$ [G9: the identity as digit matrices, unsat over both rings]

**Corollary 12.6.4.2 (towers).** For every $N \ge 3$ and every free rank-4
bialgebra $A$ over $k'[\epsilon]/\epsilon^N$ with killed-by-2 $t^4$-shaped
fiber, the $s = 3$ layer identity holds: $\Psi_1, \Psi_2$ depend only on the
truncation $A/\epsilon^3$, which is a bialgebra over $k'[\epsilon]/\epsilon^3$.

**Corollary 12.6.4.3 (S′ at $\epsilon^3$, arbitrary $k'$, $t^4$ fiber).**
By 12.6.1 (S′ $\iff$ $s = 2, 3$ identities at $N = 3$), 12.6.2 ($s = 2$ =
Theorem 12.3.2) and 12.6.4.1: **S′ holds for every free rank-4 bialgebra
with killed-by-2 $t^4$-shaped local fiber over $k'[\epsilon]/\epsilon^3$,
every commutative $\mathbb F_2$-algebra $k'$.** This is the $t^4$ half of
the statement `s2gen.m2` was launched to decide (its gate is still
unconfirmed; this supersedes that half by hand), and the first
arbitrary-$k'$ S′ statement at depth 3. Via Theorem 7.1 it gives: every
socle-line lift over every socle-line extension $R'$ of
$k'[\epsilon]/\epsilon^3$ (curvilinear or not, e.g.
$k'[\epsilon,y]/(y^2, y\epsilon, \epsilon^3)$) of such an $A$ is killed by
4.

**Corollary 12.6.4.4 (killedness over $\epsilon^4$, arbitrary $k'$, $t^4$
fiber).** By 12.6.1 (killedness at $N = 4$ $\iff$ $s \le 3$): every free
rank-4 bialgebra over $k'[\epsilon]/\epsilon^4$ with killed-by-2
$t^4$-shaped local fiber is killed by 4. This settles by hand the $t^4$
branch of `search_eps45.m2`'s $\epsilon^4$ target (its $xy$ branch — 24/30
coefficients proved so far — remains the open computational half), and
upgrades the $t^4$ half of Theorem E at $\epsilon^4$ from exact-$\mathbb
F_2$ to arbitrary $k'$.

**Remark 12.6.4.5 (coassociativity ablation at $s = 3$).** Discovery gate
`G9nc` (both rings): the $s = 3$ identity remains **unsat with
coassociativity dropped entirely** (axioms A+M+fiber2 only) — the
minassoc/Theorem-F minimal-axiom pattern persists at layer 2 on exact
rings. The hand proof above is NOT coassociativity-free (Steps 2-4 use the
$w_0$ normal form and order-1 coassociativity), so a leaner proof exists in
principle; do not spend time on it unless the $s \ge 4$ induction needs it.
Also noted: discovery gate N5 says $a\,\beta_{13}\,B = 0$ identically over
$\mathbb F_2$ while $a\beta_{13} \ne 0$ is realizable (N3) — the dangerous
term is doubly protected; the proof above uses only the
$\beta_{13} = \beta_{31}$ route.

**What remains for curvilinear equal-char S′-universality.** (i) The $s =
3$ identity for the **$xy$ fiber** — **RESOLVED session 10: §12.6.5 below
(Theorem 12.6.5.1).** (ii) The $s \ge 4$ family; the natural
formulation of the induction step is the **relative first-order lemma** of
the second external handoff (§13 below): over a base satisfying S′, the
top-layer divided-$[4]$ defect of a socle-line lift vanishes. Steps 1-6
above are exactly the $s = 3$ instance of that relative statement and
should be the template.

### 12.6.5 The $s = 3$ theorem for the $xy$ fiber (session 10, by hand, machine-gated)

This resolves item (i) above. Throughout: $\kappa$ a **perfect** field of
characteristic 2, $\Delta_0$ a killed-by-2 bialgebra structure on
$H_\kappa = \kappa[x,y]/(x^2,y^2)$, $k'$ a commutative $\kappa$-algebra,
$H = H_\kappa \otimes_\kappa k'$, and $A$ a free rank-4 bialgebra over
$R = k'[\epsilon]/\epsilon^3$ with fiber $H$ (fiber2; **no liftability**).
Layers and normalizations as in 12.6.4. Basis $e_1 = x$, $e_2 = y$,
$e_3 = z := xy$ of $I = I_H$; $I^2 = k'z$, $I^3 = 0$, and **every element
of $I$ squares to zero** ($x^2 = y^2 = z^2 = 0$ and cross terms carry a
factor 2). Write $c_g := (w_1g)_{12} + (w_1g)_{21}$ (the $z$-coefficient of
$\mu_0(w_1g)$) and $c^{(2)}_g := (w_2g)_{12} + (w_2g)_{21}$. Machine gates:
`scripts/s3xy2gates.py` → `s3xy2gates.log` (lemma-level, labels [H·], [A·],
[B·], [C·], [E·] quoted below), plus the endpoint battery
`scripts/s3xygates.py`; both over $\mathbb F_2[\epsilon]/\epsilon^3$ AND
$\mathbb F_4[\epsilon]/\epsilon^3$.

**Theorem 12.6.5.1 ($s = 3$, $xy$ fiber).** For every $A$ as above,
$$\Psi_1\Psi_2 + \Psi_2\Psi_1 = 0 \text{ on } I_H .$$

The proof occupies the rest of this subsection. Two universal lemmas first
(no classification input; they hold for arbitrary $\Delta_0$ over arbitrary
$k'$).

**Lemma 12.6.5.2 (X1: squares are $\Psi_1$-invisible).** For every
$a \in I$: $\Psi_1(\mu_1(a,a)) = 0$. [Gate H3]

*Proof.* Layer-2 multiplicativity (Step 1 of 12.6.4, fiber-agnostic) at
$(a,a)$: since $\mu_0(a,a) = a^2 = 0$,
$0 = \Psi_2(\mu_0(a,a)) = \Psi_1(\mu_1(a,a)) + \mu_0(\Psi_1a, \Psi_1a)$,
and $\mu_0(\Psi_1a,\Psi_1a) = (\Psi_1a)^2 = 0$ because every element of $I$
squares to zero. $\square$

**Lemma 12.6.5.3 (X2: layer-2 diagonal identity).** For every $a \in I$:
$$w_0(\mu_2(a,a)) \;=\; w_1(\mu_1(a,a)) + S_2(a) + T_{11}(a),$$
$$S_2(a) := (\mu_2\otimes\mu_0 + \mu_0\otimes\mu_2)(1\tau1)(w_0a\otimes w_0a),
\qquad T_{11}(a) := (\mu_1\otimes\mu_1)(1\tau1)(w_0a\otimes w_0a).$$

*Proof.* $\epsilon^2$-digit of $\Delta(a\cdot_A a) = (\Delta a)^2$ with
$a\cdot_A a = \epsilon\mu_1(a,a) + \epsilon^2\mu_2(a,a)$ ($a^2 = 0$ in
$H$). LHS digit $= w_1(\mu_1(a,a)) + \mu_2(a,a)\otimes1 +
1\otimes\mu_2(a,a) + w_0(\mu_2(a,a))$. On the right, with $\Delta a = X_0 +
\epsilon X_1 + \epsilon^2 X_2$ ($X_0 = \Delta_0a$, $X_l = w_la$ for
$l \ge 1$): the $\mu_{\otimes0}$-cross terms $(X_0,X_2)+(X_2,X_0)$ cancel
($\mu_0$ commutative, char 2); $\mu_{\otimes0}(X_1,X_1) = (w_1a)^2 = 0$
(each square $e_j^2\otimes e_k^2$ vanishes and cross terms double); the
$\mu_{\otimes1}$-cross terms $(X_0,X_1)+(X_1,X_0)$ cancel because
$\Gamma_1(u,v) = (\mu_1\otimes\mu_0+\mu_0\otimes\mu_1)(1\tau1)(u\otimes v)$
is symmetric in $(u,v)$; and $\mu_{\otimes2}(X_0,X_0)$ expands by the
12.2.1 computation (with $\mu_2$ resp. $\mu_1\otimes\mu_1$ in place of
$\mu_1$; unit-legged pairs die by normalization, mixed pairs cancel in
symmetric pairs) to $\mu_2(a,a)\otimes1 + 1\otimes\mu_2(a,a) + S_2(a) +
T_{11}(a)$. Cancel and conclude. $\square$

Note the contrast with 12.6.3(2): in the $t^4$ fiber the analogous carry
$Y^2$ vanished by leg-degree; here $(w_1a)^2 = 0$ because ALL basis squares
vanish — the $xy$ fiber is even more degenerate at layer 2.

**Standing layer-1 facts** (12.1.1, 12.2.2, 12.2.5, gates H1, H2):
$\Psi_1(z) = 0$ and $\Psi_1(I^2) = 0$; $\mu_1(x,z), \mu_1(y,z) \in I^2$ and
$\mu_1(z,z) = 0$; $\mu_1(x,x), \mu_1(y,y) \in \operatorname{Prim}(H)$
(diagonal primitivity 12.2.1 + $S \equiv 0$, 12.2.3 — the derivation is
unchanged over $\epsilon^3$ since $x^2 = 0$ removes the $w_1$-term from the
LHS); and Step 1 at $z = \mu_0(x,y)$ [gate H4]:
$$\Psi_2(z) = \Psi_1(\mu_1(x,y)) + \Psi_1(x)\Psi_1(y).$$
Consequently, modulo $I^2$, for $g \in \{x, y\}$:
$$\Psi_2(g) \;\equiv\; (w_1g)_{11}\,\mu_1(x,x) + (w_1g)_{22}\,\mu_1(y,y)
+ c_g\,\mu_1(x,y) + \mu_2(w_0g) \pmod{I^2}$$
($\mu_0(w_2g) \in I^2$; the $\mu_1(\cdot,z)$ and $\mu_1(z,z)$ entries of
$\mu_1(w_1g)$ land in $I^2$; symmetric-pair cancellation 12.2.2 applies to
$\mu_1$ AND $\mu_2$ verbatim). Since $\Psi_1$ kills $I^2$, Lemma X1 gives
the **universal composite formula**
$$\Psi_1\Psi_2(g) = c_g\,\Psi_1(\mu_1(x,y)) + \Psi_1(\mu_2(w_0g)),
\qquad g \in \{x,y\}. \tag{12.6.5.a}$$

**The $z$-row is free.** $\Psi_2\Psi_1(z) = \Psi_2(0) = 0$, and
$\Psi_1\Psi_2(z) = \Psi_1(\Psi_1\mu_1(x,y)) + \Psi_1(\Psi_1x\,\Psi_1y) =
\Psi_1^2(\mu_1(x,y)) + 0 = 0$ by the $s = 2$ identity (Cor. 12.6.2) and
$\Psi_1(I^2) = 0$ (in every case below $\Psi_1x\,\Psi_1y = 0$ outright).

**Descent.** Exactly as in 12.4.3: $k'' = k'\otimes_\kappa\bar\kappa$ is
faithfully flat over $k'$, the base-changed $\Delta_0$ is conjugate to a
split model of 12.4.1, conjugation transports the deformation and the
$\Psi_i$, and vanishing of $\Psi_1\Psi_2 + \Psi_2\Psi_1$ descends. So
assume $\Delta_0$ is one of $(1)\ \alpha_2{\times}\alpha_2$, $(2)\ W_2[F]$,
$(3)\ \mu_2{\times}\mu_2$, $(4)\ \mu_2{\times}\alpha_2$, over
$k' \supseteq \bar\kappa$.

**Case (1), $\alpha_2\times\alpha_2$** ($w_0x = w_0y = 0$, $w_0z =
x{\circ}y$; $\operatorname{Prim} = \langle x,y\rangle$). Here $\Psi_1g =
\mu_0(w_1g) = c_gz \in I^2$ [gate A1] and $\mu_2(w_0g) = 0$ for
$g \in \{x,y\}$. So by (12.6.5.a) and H4:
$$\Psi_1\Psi_2(g) = c_g\Psi_1(\mu_1(x,y)) =
\Psi_2(c_gz) = \Psi_2\Psi_1(g)$$
(the product term of H4 is $c_xc_yz^2 = 0$). Both composites are EQUAL;
char 2. [Endpoint gate A9] $\square$

**Case (3), $\mu_2\times\mu_2$** ($w_0x = x{\otimes}x$, $w_0y =
y{\otimes}y$; $\operatorname{Prim} = 0$). Diagonal primitivity forces
$\mu_1(x,x) = \mu_1(y,y) = 0$ [C1]; then X2 at $a \in \{x,y\}$ has
$w_1(\mu_1(a,a)) = 0$, $S_2(a) = 0$ (each term carries a $\mu_0(a,a) = 0$
leg) and $T_{11}(a) = \mu_1(a,a)\otimes\mu_1(a,a) = 0$, so
$\mu_2(a,a) \in \operatorname{Prim} = 0$ [C2]. Hence $\mu_2(w_0g) = 0$,
$\Psi_1g = c_gz$ [C3], and the case-(1) computation applies verbatim.
[Endpoint C9] $\square$

**Case (2), $W_2[F]$** ($w_0x = 0$, $w_0y = x{\otimes}x$, $w_0z =
x{\circ}y$; $\operatorname{Prim} = k'x$). Diagonal primitivity:
$\mu_1(x,x) = \lambda x$, $\mu_1(y,y) = \nu x$ [B2]. Order-1
coassociativity (12.2.4 in matrix form) at $g = x$ and $g = y$, expanded
against the $w_0$-table, yields [B3, and the $x{\otimes}x{\otimes}x$ /
$x{\otimes}y{\otimes}y$ / $y{\otimes}x{\otimes}y$ coefficients at $g = y$]:
$$c_x = 0;\quad (w_1x)_{22} = (w_1x)_{13} = (w_1x)_{31},\quad
(w_1x)_{23} = (w_1x)_{32} = (w_1x)_{33} = 0;\quad \boxed{c_y = 0}$$
— so $\Psi_1x = 0$ and $\Psi_1y = \lambda x$ **exactly** [B1]; the
vanishing of the $I^2$-part of $\Psi_1y$ sharpens 12.4.3 case (2). X2 at
$a = x$ ($w_0x = 0 \Rightarrow S_2 = T_{11} = 0$) reads
$w_0(\mu_2(x,x)) = \lambda\,w_1x$; matching against
$w_0(d_1x{+}d_2y{+}d_3z) = d_2\,x{\otimes}x + d_3\,x{\circ}y$ gives
$$d_2 = \lambda(w_1x)_{11},\qquad \lambda(w_1x)_{22} = 0 \quad\text{[B4]},$$
and X2 at $a = y$ ($S_2(y) = 0$ — its $\mu_0(x,x)$-legs vanish —
$T_{11}(y) = \lambda^2 x{\otimes}x$) gives at the $(2,2)$-entry
$$\nu(w_1x)_{22} = 0 \quad\text{[B5]}.$$
Order-2 coassociativity at $g = x$ (12.6.4-style matrix form; $w_0x = 0$
kills the $w_2$-legged RHS), coefficient of $x\otimes x\otimes x$: the
$w_2x$-part contributes $c^{(2)}_x$, and the quadratic carry
$\sum_j (w_1x)_{j1}(w_1e_j)_{11} + \sum_k (w_1x)_{1k}(w_1e_k)_{11}$
collapses to $c_x(w_1y)_{11} + [(w_1x)_{31}{+}(w_1x)_{13}](w_1z)_{11} = 0$
by the layer-1 relations; hence $c^{(2)}_x = 0$ [B6] — the layer-1
coassociativity-extraction mechanism of 12.4.3 case (2) persists at layer
2. Now assemble. $\Psi_2x = \mu_0(w_2x) + \mu_1(w_1x)$ has $x$-component
$\rho = \lambda(w_1x)_{11} + \nu(w_1x)_{22}$, $y$-component $0$, and
$z$-component $c^{(2)}_x + [(w_1x)_{13}{+}(w_1x)_{31}](m_2{+}\lambda) +
[(w_1x)_{23}{+}(w_1x)_{32}]m_1 = 0$ (B3 makes both brackets vanish; $m_i$
:= components of $\mu_1(x,y)$, via the Hochschild values $\mu_1(x,z) =
(m_2{+}\lambda)z$, $\mu_1(y,z) = m_1z$). So $\Psi_2x = \rho x$, and:
* $g = x$: $\Psi_2\Psi_1(x) = \Psi_2(0) = 0$ and $\Psi_1\Psi_2(x) =
  \rho\,\Psi_1x = 0$. ✓
* $g = y$: by (12.6.5.a) with $c_y = 0$, $\Psi_1\Psi_2(y) =
  \Psi_1(\mu_2(x,x)) = d_1\Psi_1x + d_2\Psi_1y = d_2\lambda x =
  \lambda^2(w_1x)_{11}x$; while $\Psi_2\Psi_1(y) = \lambda\Psi_2x =
  \lambda\rho x = [\lambda^2(w_1x)_{11} + \lambda\nu(w_1x)_{22}]x =
  \lambda^2(w_1x)_{11}x$ by B5. Equal; char 2. ✓
* $g = z$: $\Psi_2z = \Psi_1(\mu_1(x,y)) = m_2\lambda x$, and
  $\Psi_1\Psi_2(z) = m_2\lambda\Psi_1x = 0 = \Psi_2\Psi_1(z)$. ✓
[Endpoint B9; non-vacuity BN1-3: $\lambda \ne 0$, $\nu \ne 0$, even
$\lambda\nu \ne 0$ are realizable — the B4/B5 cancellations are
load-bearing, not vacuous.] $\square$

**Case (4), $\mu_2\times\alpha_2$** ($w_0x = x{\otimes}x$, $w_0y = 0$,
$w_0z = x{\circ}y + x{\circ}z$; $\operatorname{Prim} = k'y$). Diagonal
primitivity: $\mu_1(x,x) = \lambda y$, $\mu_1(y,y) = \nu y$ [E2]. Order-1
coassociativity at $g = x$ (RHS $= w_1x\otimes x + x\otimes w_1x$),
coefficients of $x{\otimes}x{\otimes}y$, $y{\otimes}x{\otimes}x$,
$x{\otimes}y{\otimes}x$: $(w_1x)_{13} = (w_1x)_{31} = 0$ and
$\boxed{c_x = 0}$ [E3] — so $\Psi_1x = \lambda y$ **exactly** (sharpening
12.4.3 case (4)) and $\Psi_1y = 0$ [E1, via the $g = y$ extraction E4]:
$$c_y = 0;\quad (w_1y)_{12} = (w_1y)_{21} = (w_1y)_{13} = (w_1y)_{31};\quad
(w_1y)_{23} = (w_1y)_{32} = (w_1y)_{33} = 0.$$
X2 at $a = x$ ($S_2(x) = 0$, $T_{11}(x) = \lambda^2y{\otimes}y$):
$w_0(\mu_2(x,x)) = \lambda w_1y + \lambda^2 y{\otimes}y$; matching against
$w_0(d_1x{+}d_2y{+}d_3z) = d_1x{\otimes}x + d_3(x{\circ}y + x{\circ}z)$:
$$d_1 = \lambda(w_1y)_{11},\qquad \lambda(w_1y)_{22} = \lambda^2
\quad\text{[E5]},$$
and X2 at $a = y$ ($w_0y = 0$): $w_0(\mu_2(y,y)) = \nu w_1y$, whose
$(2,2)$-entry gives $\nu(w_1y)_{22} = 0$ [E6]. (Combining:
$\nu\lambda^2 = 0$ [E8] — the "dangerous product" is dead, though the
assembly below only uses E6.) Order-2 coassociativity at $g = y$
($w_0y = 0$), coefficients of $x{\otimes}x{\otimes}y$,
$y{\otimes}x{\otimes}x$, $x{\otimes}y{\otimes}x$: eliminating the
$w_2y$-entries as at layer 1 and cancelling the quadratic
$(w_1,w_1)$-carries via E4 and $c_x = 0$ leaves $c^{(2)}_y = 0$ [E7].
Assemble. $\Psi_2y = \mu_0(w_2y) + \mu_1(w_1y)$ has $x$-component $0$
($\mu_1(x,x), \mu_1(y,y) \in k'y$; $c_y = 0$), $y$-component
$\lambda(w_1y)_{11} + \nu(w_1y)_{22}$, and $z$-component $c^{(2)}_y +
[(w_1y)_{13}{+}(w_1y)_{31}]m_2 + [(w_1y)_{23}{+}(w_1y)_{32}](m_1{+}\nu)
= 0$ (E4, E7; here $\mu_1(x,z) = m_2z$, $\mu_1(y,z) = (m_1{+}\nu)z$). So:
* $g = x$: $\Psi_1\Psi_2(x) = \Psi_1(\mu_2(x,x)) = d_1\Psi_1x + d_2\Psi_1y
  = d_1\lambda y = \lambda^2(w_1y)_{11}y$ by (12.6.5.a) with $c_x = 0$;
  $\Psi_2\Psi_1(x) = \lambda\Psi_2y = [\lambda^2(w_1y)_{11} +
  \lambda\nu(w_1y)_{22}]y = \lambda^2(w_1y)_{11}y$ by E6. Equal. ✓
* $g = y$: $\Psi_2\Psi_1(y) = \Psi_2(0) = 0$; $\Psi_1\Psi_2(y) =
  \Psi_1(\mu_2(w_0y)) + c_y(\cdots) = 0$. ✓
* $g = z$: $\Psi_2z = \Psi_1(\mu_1(x,y)) = m_1\lambda y$;
  $\Psi_1\Psi_2(z) = m_1\lambda\Psi_1(y) = 0$. ✓
[Endpoint E9; non-vacuity EN1-3 — in particular $\lambda(w_1y)_{11} \ne 0$
is realizable, i.e. $\mu_2(x,x)$ GENUINELY escapes $I^2$ at layer 2: the
layer-1 case mechanism does not persist verbatim, matching probe Q3 of
12.6.3.] $\square$

This proves Theorem 12.6.5.1. $\blacksquare$

**Corollary 12.6.5.4 (towers).** For every $N \ge 3$ and every free rank-4
bialgebra over $k'[\epsilon]/\epsilon^N$ with killed-by-2 $xy$-shaped fiber
defined over a perfect subfield, the $s = 3$ identity holds ($\Psi_1,
\Psi_2$ depend only on $A/\epsilon^3$).

**Corollary 12.6.5.5 (S′ at $\epsilon^3$, BOTH fibers).** With Theorem K
(12.6.4.1) and $s = 2$ (Cor. 12.6.2): **S′ holds for every free rank-4
bialgebra with killed-by-2 local fiber over $k'[\epsilon]/\epsilon^3$** —
for the $t^4$ fiber with arbitrary $\Delta_0$ over arbitrary $k'$, for the
$xy$ fiber whenever the fiber is defined over a perfect subfield of $k'$
(always true in the group-scheme application, where $k'$ is the residue
field itself, via Thm 3.1). This is the FULL statement `s2gen.m2` was
launched to decide, now proved by hand; `s2gen` is retired to audit-only.
Via Thm 7.1: every socle-line lift of such an $A$ over every socle-line
extension of $k'[\epsilon]/\epsilon^3$ (non-curvilinear included) is
killed by 4.

**Corollary 12.6.5.6 (killedness over $\epsilon^4$, BOTH fibers).** By
12.6.1 (killedness at $N = 4$ $\iff$ $s \le 3$): every free rank-4
bialgebra over $k'[\epsilon]/\epsilon^4$ with killed-by-2 local fiber
(same field-of-definition proviso for $xy$) is killed by 4. This settles
by hand the ENTIRE $\epsilon^4$ target of `search_eps45.m2` (its $xy$
branch stood at 24/30 coefficients); eps45's $\epsilon^4$ stage is now
audit-only.

**Remark 12.6.5.7 (layer-1 sharpenings found en route).** In the split
cases with a $w_0$-source (2)/(4), the $I^2$-part of $\Psi_1$ dies:
$\psi(y) = \lambda x$ exactly in $W_2[F]$, $\psi(x) = \lambda y$ exactly
in $\mu_2{\times}\alpha_2$ (order-1 coassociativity against the
$w_0$-table; gates B1/E1). So $\psi(I) \subseteq \operatorname{Prim}(H)$
in cases (2), (3), (4), while in case (1) $\psi(I) \subseteq I^2$. Not
used beyond this section, but they make the $s \ge 4$ bookkeeping lighter.
PARTIALLY SETTLED (session 13, `s4xycert.log`, BOTH `ell != 0 realizable`
rows read — a lesson in the Frobenius/nilpotent trap): over
$\mathbb F_2[\epsilon]/\epsilon^4$ the row is `unsat`, but over the
dual-number ring $(\mathbb F_2[u]/u^2)[\epsilon]/\epsilon^4$ it is `sat`.
So in case (3) $\mu_2^2$ ($\operatorname{Prim} = 0$) the constraint on the
image-line functional is $\ell^2 = 0$, NOT $\ell = 0$: over reduced $k'$
the case is triangularly trivial at first order, but over general $k'$
a nonzero nilpotent $\ell$ survives — the fourth note's Lemma A (assuming
only image-in-$k'z$) is genuinely needed at arbitrary-$k'$ strength.
An $\mathbb F_2$-point gate alone would have licensed the false "$\ell =
0$" claim; the dual-number battery exists precisely to catch this.

**Remark 12.6.5.7b (coassociativity ablation at $s = 3$ — the fibers
DIFFER; session 10, `s3xygates.log`).** Discovery gate `GX9nc` over
$\mathbb F_2[\epsilon]/\epsilon^3$: for the $xy$ fiber the $s = 3$
identity is **violated** (`sat`) when coassociativity is dropped
(A+M+fiber2 only) — the OPPOSITE of the $t^4$ fiber, where `G9nc` is
`unsat` over both rings (12.6.4.5). So the minassoc/Theorem-F pattern
does NOT persist at layer 2 for the $xy$ fiber: the coassociativity
extractions in the case-(2)/(4) proofs above (B3/B6, E3/E4/E7) are
genuinely load-bearing, not an artifact of the proof route. Contrast with
layer 1, where the endpoint $[4]^\# = 0$ at $\epsilon^3$ needed no
coassociativity for either fiber (ablate/Theorem F) — the S′-level
identities are more axiom-hungry than the killedness endpoint, and
differently so per fiber. Any leaner-axiom program at $s \ge 3$ must
treat the fibers asymmetrically.

**Remark 12.6.5.8 (what the $s \ge 4$ induction inherits).** The proof
pattern that survived both fibers at $s = 3$: (i) layer-$s$
multiplicativity turns $I^2$-inputs into lower-layer data (Step 1 / X1);
(ii) the layer-$s$ diagonal identity degenerates because the quadratic
carries are squares that die in char 2 (X2; $Y^2 = 0$ resp.
$(w_1a)^2 = 0$); (iii) order-$(s{-}1)$ coassociativity extraction at the
same monomials as layer 1, with the quadratic $(w_1,w_1)$-carries
cancelling via the layer-1 relations (B6/E7 — this is the part to watch
at $s = 4$, where the carries are $(w_1,w_2)$-mixed and need the layer-2
relations); (iv) the two X2-instances at $x$ and $y$ jointly kill the
dangerous product ($\nu\lambda^2$, E8). The relative first-order lemma
(§13.2) should be provable by exactly this template.

### 12.6.6 Beachhead for $s = 4$ (session 10; formulas derived, theorem NOT claimed)

Everything below is proved as displayed but the $s = 4$ identity itself is
**not** yet closed; these are the inputs a session attacking it should
start from. Over $R = k'[\epsilon]/\epsilon^N$ ($N \ge 4$), layers
$\mu_0,\dots,\mu_3$, $w_0,\dots,w_3$ enter; the target is
$\Psi_1\Psi_3 + \Psi_2\Psi_2 + \Psi_3\Psi_1 = 0$.

**(a) Layer-3 multiplicativity** ($\epsilon^3$-digit of $\varphi(a\cdot_Ab)
= \varphi(a)\varphi(b)$; cross $\mu_0$-pairs of unequal digits cancel):
$$\Psi_3(\mu_0(a,b)) = \Psi_2(\mu_1(a,b)) + \Psi_1(\mu_2(a,b))
+ \mu_0(\Psi_1a,\Psi_2b) + \mu_0(\Psi_2a,\Psi_1b) + \mu_1(\Psi_1a,\Psi_1b).$$
At $(a,a)$ with $a^2 = 0$ (xy fiber: every $a \in I$): the $\mu_0$-cross
terms cancel in char 2, leaving
$$0 = \Psi_2(\mu_1(a,a)) + \Psi_1(\mu_2(a,a)) + \mu_1(\Psi_1a,\Psi_1a)$$
— the layer-3 analogue of X1. For the $t^4$ fiber at $(t,t)$:
$\Psi_3(t^2) = \Psi_2(\mu_1(t,t)) + \Psi_1(\mu_2(t,t)) + B^2u + C^2at^3$
(with $\Psi_1t = Bt^2{+}Ct^3$, $u = \mu_1(t^2,t^2)$; Hochschild
$\mu_1(t^3,t^3) = at^3$).

**(b) All mixed-digit cross pairs die.** Each $\mu_\otimes^{(m)} :=
\sum_{i+j=m}(\mu_i\otimes\mu_j)(1\tau1)$ is SYMMETRIC in its two
arguments ($\mu_i$ symmetric each layer), so in the $\epsilon^s$-digit of
$(\Delta a)^2$ every pair $(X_i, X_j)$ with $i \ne j$ cancels in char 2.
Only the diagonal terms $\mu_\otimes^{(s-2i)}(w_ia, w_ia)$ survive:

**Layer-$s$ diagonal identity** (any fiber, $a \in I$ with $a^2 = 0$):
$$\sum_{l+n=s,\ n\ge1} w_l(\mu_n(a,a)) \;=\;
\sum_{i\ge1,\ 2i\le s} \mu_\otimes^{(s-2i)}(w_ia,\,w_ia)
\;+\; \mu_\otimes^{(s)}(w_0a,\,w_0a)\big|_{\text{non-unit part}},$$
where the $i = 0$ term is expanded 12.2.1-style (unit-legged pairs give
the $\mu_s(a,a)\otimes1 + 1\otimes\mu_s(a,a)$ that cancels against the
LHS's $\Delta_0$-term; mixed pairs cancel). $s = 2$ recovers X2; $s = 3$
reads
$$w_0\mu_3(a,a) + w_1\mu_2(a,a) + w_2\mu_1(a,a) =
\Gamma_1(w_1a, w_1a) + \textstyle\sum_{i+j=3}(\mu_i\otimes\mu_j)(1\tau1)
(w_0a\otimes w_0a).$$

**(c) $\Gamma$-vanishing for the $xy$ fiber (proved; gate this before
using).** For EVERY $W \in I\otimes I$ (symmetric or not):
$$\mu_\otimes^{(0)}(W,W) = W\cdot_0W = 0,\qquad
\Gamma_1(W,W) := (\mu_1\otimes\mu_0{+}\mu_0\otimes\mu_1)(1\tau1)(W{\otimes}W) = 0,$$
$$(\mu_2\otimes\mu_0{+}\mu_0\otimes\mu_2)(1\tau1)(W{\otimes}W) = 0,\qquad
(\mu_1\otimes\mu_1)(1\tau1)(W{\otimes}W) =
\textstyle\sum_{p,q}W_{pq}^2\,\mu_1(e_p,e_p)\otimes\mu_1(e_q,e_q).$$
*Proof sketch:* in the first three, the coefficient of
$\mu_i(e_p,e_r)\otimes z$ is $W_{p1}W_{r2} + W_{p2}W_{r1}$ — symmetric in
$(p,r)$, so off-diagonal terms cancel against $\mu_i(e_r,e_p)$ and
diagonal terms double; for the last, swap-pairs cancel and the
Frobenius-diagonal survives. (The 12.2.3 argument, freed from the
symmetric-$W$ hypothesis: it only needs the two ARGUMENTS equal.)
Consequence: for the $xy$ fiber the layer-3 diagonal identity collapses to
$$w_0\mu_3(a,a) + w_1\mu_2(a,a) + w_2\mu_1(a,a) =
\textstyle\sum_{p,q}(w_0a)_{pq}^2\,
\mu_1(e_p,e_p)\otimes\mu_1(e_q,e_q)\big|_{\text{(that's the } i{=}0,\
(\mu_1,\mu_1)\text{ term)}} + (\mu_2{\leftrightarrow}\mu_0\ i{=}0
\text{ terms, which vanish by the same argument at } W = w_0a).$$
In the split cases $w_0a \in \{0, x{\otimes}x\}$ for $a \in \{x,y\}$, so
the right side is $0$ or $\mu_1(x,x)\otimes\mu_1(x,x)$ — one Frobenius
term, exactly as at $s = 3$. **The $xy$ fiber looks EASIER than $t^4$ at
$s = 4$** (for $t^4$ the $\Gamma_1(w_1t, w_1t)$ carry does not vanish
identically and must be computed from the $Y$-shape).

**(d) Suggested route.** Do $s = 4$ RELATIVELY (assume the $s \le 3$
identities — proved unconditionally — and S′ of the truncation; prove the
top identity), i.e. prove the relative first-order lemma (§13.2) directly
at arbitrary depth with the (a)-(c) toolkit rather than one $s$ at a time:
the carries in (a)/(b) only ever involve $\Psi_{<s}$ and the diagonal
$\mu_i(e_p,e_p)$, both controlled by the lower identities + primitivity.
Calibration probe: `scripts/s4probe.py` (session 10, chain-queued behind
`s3xy2gates.py` → `s4probe.log`; $\mathbb F_2[\epsilon]/\epsilon^4$, both
fibers).

**(e) The $s = 4$ assembly for the $t^4$ fiber, reduced to four scalars
(session 10, derived by hand; probe gates T1/T2/T5/T6).** Notation of
12.6.4; additionally $\Psi_2t = Pt + Qt^2 + Rt^3$ ($P = pB{+}qC$ by
Theorem K Step 6), $\mu_1(t,t^2) = qt + q_2t^2 + q_3t^3$,
$\sigma_2 := pp_2 + qp_3 + \mu_2(t,t)_t$,
$\sigma_3 := pq_2 + qq_3 + \mu_2(t,t^2)_t$. Layer-3 multiplicativity (a)
at $(t,t)$ and $(t,t^2)$ gives
$$\Psi_3(t^2) = p\,\Psi_2t + \sigma_2\,\Psi_1t + B^2u + aC^2t^3,\qquad
\Psi_3(t^3) = q\,\Psi_2t + \sigma_3\,\Psi_1t$$
(the $\mu_0$-cross terms cancel; $\mu_1(\Psi_1t,\Psi_1t) = B^2u +
C^2\,\mu_1(t^3,t^3) = B^2u + aC^2t^3$; for $(t,t^2)$ all product terms
land in $I^4 = 0$ since $\Psi_1t^2 = 0$, $\Psi_2t^2 = p\Psi_1t \in I^2$).
In particular $(\Psi_3t^2)_t = pP + aB^2$ [probe T1]. Then, with
$\Lambda := (\Psi_3t)_t + Qp + Rq + B\sigma_2 + C\sigma_3$:
$$D_4(t^2) = aB^2\,\Psi_1t,\qquad D_4(t^3) = 0\ \text{(both composites
$= qP\,\Psi_1t$)},$$
$$D_4(t) = aB^3\,t + (\Lambda B + bB^3)\,t^2 +
(\Lambda C + ac_1B^3 + aB^2C)\,t^3 .$$
So the $s = 4$ identity for the $t^4$ fiber is EQUIVALENT to the four
scalar identities
$$\boxed{aB^3 = 0,\qquad aB^2C = 0,\qquad \Lambda B = bB^3,\qquad
\Lambda C = 0}$$
over $k'[\epsilon]/\epsilon^N$, $N \ge 4$. CAUTION (Frobenius collapse):
over $k' = \mathbb F_2$ the probe cannot distinguish $aB^3 = 0$ from
$aB = 0$ ($B^3 = B$ for bits), so T3/T4's F₂ verdicts do NOT settle the
arbitrary-$k'$ shape of the obstruction — an
$\mathbb F_4[\epsilon]/\epsilon^4$ = `Ext(F2epsN(4))` run (256 elements,
expensive) or an M2 membership run distinguishes $aB$, $aB^2$, $aB^3$.
Note $aB = a\beta_{11}$ (since $ac_4 = 0$), so the cleanest possible
outcome is "$a\beta_{11} = 0$ under $\epsilon^4$-liftability", an order-3
carry identity in the spirit of B6/E7.

### 12.7 Validation record (golden rule 1)

`scripts/firstorder_gates.py`, log `firstorder_gates.log`: 24+ queries over
$\mathbb F_2[\epsilon]/\epsilon^2$ and
$\mathbb F_4[\epsilon]/\epsilon^2$, every lemma-level `unsat` claim
(P1/P1b/P2/P3/P4/P5/P6/P7) and every non-vacuity `sat` claim passing, plus
six pinned-fiber batteries (`PIN-a2a2`, `PIN-W2F`, `PIN-mu2mu2`,
`PIN-mu2a2`, `PIN-aF2`, `PIN-c4`) checking the case computations of 12.4.3
and 12.3.2 directly. Ring class $\mathbb F_4[\epsilon]/\epsilon^2 =$
`Ext(F2epsN(2))` added to `ringcheck.py` (rerun: `ringcheck_s8.log`).
The endpoint claim $\psi^2 = 0$ over $\mathbb F_2$ independently reproduces
the $\epsilon^2$ rows of `s2check.log` (Theorem 7.5.2). The $\mathbb F_4$
endpoint rows are new. `symbolsq.m2`, if it terminates, upgrades the $xy$
half to arbitrary coefficient rings (audit-only, see 12.5).

## 13. Audit of the second external handoff (divided-$[4]$; session 9)

The user supplied a second GPT theory handoff,
`order4_divided4_theory_handoff.md` (2026-07-09). Audit outcome, per the
golden-rule-4 discipline (its §9-10 job priorities predate Theorem I /
Corollary J and are stale — do not follow them; the mathematics audits as
follows).

**13.1 What it contains that we already had (independent convergence —
confirming, not new).** Its central reformulation — S′ over
$k[t]/t^{N+1}$ $\iff$ the divided-$[4]$ identity $D_t\varphi = 0$ where
$tD_t\varphi = \varphi^2$, $\iff$ the coefficient family
$\sum_{i+j=n}\psi_i\psi_j = 0$ ($2 \le n \le N{+}1$) — is exactly
Proposition 12.6.1 (its $\psi_i$ = our layer symbols $\Psi_i$; its
well-definedness argument for $D_t\varphi$ = Prop 7.5.1(ii)). Its
Koszul/syzygy-coset formulation for non-principal $\mathfrak m$ (§5) is the
encoding `s2check_np.py` already implements (design note, HANDOFF §0-4.2),
including the "no principal defect shortcut" caution (§5.2 there = our
session-5 design note). Its §4.2 warning that naive polarization is
insufficient at $s \ge 3$ (Massey corrections) is precisely what probe Q1
(`s3probe.py`, `sat`) had established. Two independent derivations landing
on the same reformulation is good evidence the reformulation is the right
coordinates for the problem.

**13.2 Genuinely new and banked.**

* **Proposition 13.2.1 (minimal-counterexample reduction; its §3).** If S′
  fails somewhere in the killed-by-2 local branch, then on a
  length-minimal counterexample $(R, A)$ one already has $[4]^\#_A =
  \eta\varepsilon$. *Proof.* Choose a socle line $M \subset
  \operatorname{Soc}(R)$; by minimality S′$(\bar A/\bar R)$ holds for
  $\bar R = R/M$, and $A$ is a socle-line lift of $\bar A$, so Theorem 7.1
  kills it by 4. $\square$
  Consequence: the S′-obstruction class $\omega_A(x) = [\varphi(x)] \in
  (K\cap\mathfrak mI)/\mathfrak mK$ on a minimal counterexample is a
  saturation failure INSIDE cycles ($\varphi^2 = 0$ forced) — a proof of
  universal S′ never needs to re-prove killedness at the minimal stage.
  Its accompanying module-theory counterexample ($d = t^2\,\mathrm{id}$
  over $k[t]/t^4$: $d^2 = 0$ but $d(M) \not\subseteq t\ker d$) shows the
  bialgebra axioms must enter; recorded alongside Remark 7.5.5.

* **The relative first-order lemma (its §8.3), adopted as the
  $s \ge 4$ induction target.** "If S′$(A/R)$ holds and $A'$ is a
  socle-line lift over $R'$, then the top-layer divided-$[4]$ defect of
  $A'$ vanishes." This is stronger than Theorem 7.1 (which gives only
  top-layer ordinary $[4]$-vanishing) and is exactly what a length
  induction proving S′ everywhere needs. The $s = 3$ theorem 12.6.4.1 is
  its first instance beyond Theorem I, and Steps 1-6 there (layer-$s$
  multiplicativity of $\varphi$; rigid shape of $w_{s-1}(t^2)$;
  degenerate diagonal identity; $\beta$-symmetry from order-$(s{-}1)$
  coassociativity; Hochschild values; assembly) are the template.

**13.3 Corrections to it (stale inputs — do not copy).** (i) Its §9.1/9.2
priorities (harvest `symbolsq`, `s2gen`) predate Theorem I: `symbolsq` is
audit-only (12.5), and the $t^4$ half of `s2gen` is now proved by hand
(12.6.4.3). (ii) Its §9.4 (mine `minassoc` certificates for a
human-readable $\psi^2 = 0$) is superseded — §12 IS the human-readable
proof. (iii) Its §1.2 calls `minassoc` "the strongest clue"; after Theorem
I the strongest clue is the §12.2 workhorse-identity mechanism, which its
string-diagram proposal (§8.2) approximates. (iv) Its Theorem X$_{\rm prin}$
coefficient range "$2 \le n \le N{+}1$" over $k[t]/t^{N+1}$ matches 12.6.1
after the index shift $N_{\rm theirs} = N_{\rm ours}-1$; no discrepancy,
but check indices before quoting either file.

## 14. Audit of the third external handoff (s = 4, t⁴ fiber; session 11)

The user supplied a third GPT note, `order4_further_push_s4_t4.md`
(2026-07-09, received just after the machine crash), claiming closure of
the $s = 4$ divided-$[4]$ identity for the $t^4$ fiber:
$D_4 := \Psi_1\Psi_3 + \Psi_2\Psi_2 + \Psi_3\Psi_1 = 0$ over
$k'[\epsilon]/\epsilon^N$ ($N \ge 4$), any characteristic-2 coefficient
ring $k'$, via three identities feeding the 12.6.6(e) four-scalar
reduction:

$$\text{(i) } aB = 0,\qquad \text{(ii) } \Lambda = bB^2,\qquad
\text{(iii) } BC = 0.$$

**14.1 Logical assembly: CORRECT.** Given (i)–(iii) and the 12.6.6(e)
assembly (session-10 hand derivation, gates T1/T5/T6), the four scalars
die: $aB^3 = (aB)B^2 = 0$; $aB^2C = (aB)(BC) = 0$; $\Lambda B = bB^3$
from (ii); $\Lambda C = bB^2C = bB\,(BC) = 0$. Checked by hand in-session;
no gap.

**14.2 DEPENDENCY ALERT (golden rule 4).** The note's proof of (i)
$aB = 0$ lives in its predecessor, `order4_sustained_attempt_note.md`,
which is **NOT in the project folder** — the identity is load-bearing
(all four scalars use it, and the §3.4 certificate residual $R$ needs
$a\beta_{11} = 0$) and its hand proof is currently unauditable. Ask the
user for that file. Machine status of (i) itself: `s4cert.py` gate G-aB
**unsat over $\mathbb F_2[\epsilon]/\epsilon^4$** (verified in-session),
independently reproduced by `s4probe.py` T3/T4 (the $aB \ne 0$ and
$aB^2 \ne 0$ realizability probes both came back unsat).

**14.3 Validation record.** `scripts/s4cert.py` → `s4cert.log`
(session 11) gates EVERY displayed identity of the note: the closed forms
$B = \beta_{11} + c_4b$, $C = \beta_{12}+\beta_{21}$; the first-order
facts $\Theta_{12} = \Theta_{21} = q_3 + ac_4 + bc_1$, $c_4C = 0$,
$\beta_{23} = \beta_{32}$, $\beta_{33} = \beta_{11}c_1^2$; Lemma 2.1
($aC = 0$); the three order-2 coassociativity extractions
$E_{112}, E_{211}, E_{121}$ and $\beta_{11}C = BC = 0$ (Lemma 2.2); the
§3.1 layer-3 diagonal at $(2,2)$ including the $\Gamma_1(Y,Y)_{22} = 0$
sub-claim; the three §3.2 associativity values; the §3.3 extractions
$E_V, E_U$; the main identity $\Lambda = bB^2$; the open scalars
$\Lambda B = bB^3$, $\Lambda C = 0$; and $D_4$ row-by-row.
**Over $\mathbb F_2[\epsilon]/\epsilon^4$: ALL 28 GATES PASSED**
(non-vacuity: $\Lambda \ne 0$ and $bB^2 \ne 0$ are realizable — (ii) is a
real cancellation). Still running at session-11 write-up: the same
battery over $(\mathbb F_2[u]/u^2)[\epsilon]/\epsilon^4$ (new coefficient
class `ExtD` — dual numbers break the Frobenius collapse that makes
$k' = \mathbb F_2$ blind to $aB$ vs $aB^3$; ring class self-gated R0,
deliberately NOT an Artin-local class, see the script docstring) and over
$\mathbb F_4[\epsilon]/\epsilon^4$. CHECK `s4cert.log` ends
`ALL S4CERT GATES PASSED` before citing beyond $\mathbb F_2$.

**14.4 Endpoint news beyond the note.** `s4probe.py` (relaunched after
the crash) finished in minutes on the idle box: **ALL GATES PASSED, BOTH
fibers**, in particular T2 and X2g = the FULL $s = 4$ endpoint
$D_4 = 0$ over $\mathbb F_2[\epsilon]/\epsilon^4$ for $t^4$ AND $xy$.
The note called the $xy$ endpoint "computationally expensive … not
closed"; at $k' = \mathbb F_2$ it is now closed. The $xy$ fiber at
arbitrary $k'$ remains the open frontier.

**14.5 The arbitrary-$k'$ upgrade (launched).** `scripts/s4gen.m2` →
`s4gen.log`: ideal-membership certificates over
$Q_2 = \mathbb F_2[\text{all structure-constant digits}]$ at
$\epsilon^4$, targets = the nine $D_4$ components (BOTH fibers) plus the
note's named scalars ($t^4$). Any target reducing to 0 against a partial
GB is a complete cofactor certificate valid over EVERY
$\mathbb F_2$-algebra $k'$ (partial logs = partial proofs). If all
targets land: **Theorem M** ($s = 4$, both fibers, arbitrary $k'$),
whence by 12.6.1 + Thm 7.1: S′-universality over $k'[\epsilon]/\epsilon^4$
and killed-by-4 over $k'[\epsilon]/\epsilon^5$, both fibers, arbitrary
$k'$ — subsuming `search_eps45`'s still-open $\epsilon^5$ stages (that
script stays retired) and closing the $s=4$ program without the missing
predecessor note. Banking discipline: the note's content is banked as
THEOREM only when either (a) `s4gen` certifies the $t^4$ targets, or
(b) the predecessor note arrives, audits cleanly, and the `s4cert`
dual-number + $\mathbb F_4$ batteries pass.

**14.6 Audit of the predecessor note (`order4_sustained_attempt_note.md`,
received later in session 11).** The missing dependency of §14.2 arrived.
It proves the Lemma: $aB = 0$ for every second-order lift — i.e. already
over $k'[\epsilon]/\epsilon^3$ — of a killed-by-2 $t^4$ fiber, via
$Y_{11} = \Theta_{11} = 0$ and the $(t,t)$-coefficient of the X2 identity
$w_0(v) = w_1(u) + Y^2$ at $t^2$, which reads
$0 = (w_1u)_{11} = a\beta_{11} + bY_{11} + ac_1\Theta_{11} = a\beta_{11}$.
Audit verdict: **statement and skeleton CORRECT; one justification gap,
repaired here.** Its degree argument for $Y_{11} = 0$ ("every product term
has positive degree in both tensor legs") overlooks the $\mu_1$-carry
terms of $(\Delta t)^2$ pairing a unit-legged monomial with a
$w_0t$-monomial: $(\mu_1{\otimes}\mu_0{+}\mu_0{\otimes}\mu_1)(1\tau1)$ on
$(t{\otimes}1)\otimes(c_1\,t^2{\otimes}t)$ produces
$c_1\,\mu_1(t,t^2)\otimes t \ni c_1q\,(t{\otimes}t)$, which is NOT killed
by degrees. It IS killed by symmetric-pair cancellation (the §12.2
workhorse: the $(X,Y)$ and $(Y,X)$ contributions coincide since every
$\mu_i$ is symmetric, so they cancel in char 2); the surviving diagonal
pairs $(X,X)$ have $\mu_0$-leg $\mu_0(e_k,e_k) \in \{t^2, 0\}$, never $t$,
so $Y_{11} = 0$ and likewise $\Theta_{11} = 0$. With the repair the Lemma
is proved for arbitrary $k'$. Micro-gates: `scripts/s4pred.py` →
`s4pred.log` ($Y_{11}$, $\Theta_{11}$, $a\beta_{11}$, $aB$ at
$\epsilon^3$, $\mathbb F_2$ AND $\mathbb F_4$; plus the note's contrast
$a\beta_{11} \ne 0$ realizable at $\epsilon^2$ — check the log ends
`ALL S4PRED GATES PASSED` before citing). The $\epsilon^2$-sat vs
$\epsilon^3$-unsat contrast is the cleanest known instance of the
relative first-order mechanism of §13.2: a nonzero first-order product
forced to die by the EXISTENCE of a one-step-higher lift. The chain of
custody for $s = 4$/$t^4$ is now complete on paper: $aB = 0$ (predecessor
note, audited + repaired) + $\Lambda = bB^2$, $BC = 0$ (third handoff,
§14.1–14.3) + the 12.6.6(e) assembly (session 10) $\Rightarrow D_4 = 0$.
Banking still follows the §14.5 rule.

**14.7 Forward program after $s = 4$/$t^4$ (the asks for the next
external push).** In priority order:

1. **Close $s = 4$ for the $xy$ fiber.** All structural inputs are in
   place: descent to the four split models of 12.4.1 (as in Theorems I
   and L); layer-3 multiplicativity 12.6.6(a) at $(x,x)$, $(y,y)$,
   $(x,y)$; the $\Gamma$-vanishing lemma 12.6.6(c) — freed from the
   symmetric-$W$ hypothesis — kills every $i = 0$ carry (machine gate
   X1g); the layer-3 X1-analogue
   $\Psi_2(\mu_1(a,a)) + \Psi_1(\mu_2(a,a)) + \mu_1(\Psi_1a,\Psi_1a) = 0$
   is gated (X3). Expect to need order-3 coassociativity extractions:
   the $s3xygates$ discovery GX9nc (`sat`) shows coassociativity is
   load-bearing for the $xy$ fiber at $s = 3$ (unlike $t^4$, G9nc
   `unsat`), and the Theorem L proof used the order-2 extraction triple;
   the $s = 4$ analogue is the $E_{112}/E_{211}/E_{121}$ pattern one
   layer up. The endpoint is TRUE at $k' = \mathbb F_2$ (s4probe X2g
   `unsat`), so a hand assembly exists to be found.
2. **The relative first-order lemma at arbitrary depth** (§13.2,
   12.6.6(d)): S′ of the truncation $A/\epsilon^s$ plus existence of a
   lift to level $s$ forces $\sum_{i+j=s}\Psi_i\Psi_j = 0$, uniformly in
   $s$. The $aB = 0$ mechanism (14.6) is its germ at $s = 4$ shifted
   down: first-order products die because a higher lift exists. Proving
   it once, for all $s$, closes curvilinear equal-char S′-universality
   in FULL (every $N$, both fibers, arbitrary $k'$) and retires the
   per-$s$ grind.
3. **Bigraded symbols for non-principal $\mathfrak m$**: formulate the
   12.6.1 layer calculus over $\mathbb F_2[x,y]/(x^2,y^2)$ (bidigits
   $\Psi_{(m,n)}$, S′ ⟺ a family of bidegree identities) and prove the
   first non-curvilinear S′ by hand. Machine data says it is true:
   s2check_np/np2 give S′ universally over BiDual (both fibers) and
   FatPoint3 ($t^4$; the $xy$ row is the one remaining `unknown`,
   np2 rerun in flight).
4. **Mixed-characteristic layers (stretch)**: a Witt-carry version of
   the symbol calculus over $\mathbb Z/2^N$ and
   $\mathbb Z[\pi]/(\pi^2{-}2,\pi^k)$. All exact-ring evidence is
   positive (Z/8..Z/32, both ramified rings, s2check probes); no hand
   framework exists yet.

## 14.8 Audit of the fourth external note (s = 4, xy fiber; session 12)

The user supplied a fourth GPT note, `order4_max_pass_xy_s4.md` (2026-07-09,
with bundle `order4_max_pass_xy_s4_bundle.zip` = two gate scripts + logs,
extracted to `scripts/xy_s4_bundle/`). It attacks exactly item 1 of the §14.7
forward program: the $s = 4$ identity $D_4 = \Psi_1\Psi_3 + \Psi_2^2 +
\Psi_3\Psi_1 = 0$ for the $xy$ fiber, reduced per split model (12.4.1). The
note is explicitly NOT claiming an arbitrary-$k'$ theorem — it provides the
proof-shaped decomposition and F₂ gates, and asks for coefficient extraction
or Gröbner membership. Writing $N = \Psi_1$, $M = \Psi_2$, $L = \Psi_3$:

* **Image-line cases $\alpha_2^2$, $\mu_2^2$** (where $N = \ell(\cdot)z$ for
  a functional $\ell$ with $\ell(z) = 0$; consistent with 12.4.3 cases
  (1)/(3), which give $\psi(I) \subseteq I^2 = k'z$): **Lemma A** — $M(z)
  \in k'z$ (for $\mu_2^2$ sharper: $M(z) = L(z) = 0$), plus for every basis
  element $g$: $(M^2g)_{x,y} + \ell(g)(Lz)_{x,y} = 0$ and $(M^2g)_z +
  \ell(g)(Lz)_z + \ell(Lg) = 0$. Since $NL(g) = \ell(Lg)z$ and $LN(g) =
  \ell(g)Lz$, these give $D_4 = 0$ by inspection.
* **Rank-one cases $W_2[F]$, $\mu_2{\times}\alpha_2$** (notation of the
  $W_2[F]$ case; the other is the $x{\leftrightarrow}y$ mirror): with
  $\lambda = \mu_1(x,x)_x$, $\nu = \mu_1(y,y)_x$, $m = \mu_1(x,y)_y$,
  $\alpha = (w_1x)_{11}$, $\delta = (w_1x)_{22}$, $\rho = \lambda\alpha +
  \nu\delta$, $\chi = (My)_z$: normal forms $Mx = \rho x$, $(My)_y = \rho$,
  $Mz = m\lambda x$, and four $L$-identities $\lambda(Lx)_y = \rho^2$,
  $\lambda(Lx)_z = \rho\chi$, $(Lz)_y = m\rho$, $\lambda((Ly)_y + (Lx)_x +
  m\chi) = 0$; then $D_4 = 0$ by 3×3 matrix multiplication.

**14.8.1 Assembly audit: CORRECT.** All four per-case matrix assemblies
were recomputed by hand in-session (including the $(My)_x$-coefficient
cancellation $a\rho + a\rho = 0$ in $M^2y$ that makes the free coefficient
$a$ harmless, and the $g = z$ row where $\ell(z) = 0$). The split-model
$\Delta_0$ pin tables in the bundle scripts were verified against
$\Delta(x)\Delta(y)$ expanded by hand in each model (e.g. for $\mu_2^2$:
$\Delta z = z{\otimes}1 + 1{\otimes}z + x{\otimes}y + y{\otimes}x +
x{\otimes}z + z{\otimes}x + y{\otimes}z + z{\otimes}y + z{\otimes}z$, nine
pins). Note's §3.1 has two LaTeX-mangled displays ("ig(" for "\big("); math
underneath is right.

**14.8.2 Gate audit.** The bundle scripts reuse the project's own validated
building blocks (`build_blocks` from s2check.py, `digit`/`KF2` from
s3gates.py, `F2epsN` from order4sat_beyond.py) with the fiber-$\Delta_0$
digit pinned per model — same encoding as the PIN batteries of 12.7. Both
logs reproduced verbatim in the bundle; all identity gates `unsat`, all Q0
rows `sat`, over $\mathbb F_2[\epsilon]/\epsilon^4$. CAVEAT the note itself
flags: F₂-only — the $\rho^2$-shaped identities are exactly the
Frobenius-collapsible kind (12.6.6(e) CAUTION), so these gates cannot
distinguish $\rho^2$ from $\rho$ or $\rho^4$. Addressed by s4xycert.py
below.

**14.8.3 The note's §5 audit notes check out.** (i) `s4probe.log` does
contain the X2g full-endpoint `unsat` (verified session 11). (ii) `s4gen.log`
in the v2 archive is indeed not a certificate — but the post-crash relaunch
has since produced PARTIAL certificates; see 14.8.6. (iii) The "malformed
--gaponly relaunch line" in `s2check_np2.log` is the first relaunch attempt's
zsh quoting bug (script name + flag passed as one filename, session 11); the
second relaunch is clean and running (gates + 3 cross-validation rows
reproduced `unsat`; FatPoint3/xy gap row in flight).

**14.8.4 Session-12 machine response, part 1: `scripts/s4xygen.m2`**
(→ `s4xygen.log`) — the targeted Gröbner job the note asks for, done
PER SPLIT MODEL rather than with free $\Delta_0$ (that free-$\Delta_0$
version is s4gen.m2's still-grinding xy stage): pin $\mu_0$ AND the
$\Delta_0$-digit to each split model over $Q_2 = \mathbb F_2[\text{all
structure-constant digits} \ge 1]$ at $\epsilon^4$ (135 vars vs s4gen's
162), targets = the note's displayed identities PLUS the nine $D_4$
components. Startup gates (both OK for all models): digit-0 part of every
axiom identically 0 (a wrong pin table would put $1 \in J$ and make every
"certificate" vacuous — this is the gate that catches it) and $\varphi_0 =
0$. Pinning collapsed the GB cost by ~50×: DegreeLimit 4 in 26–44 s per
model vs 2088 s for s4gen's t⁴ stage.

**RESULTS (COMPLETE, `DONE s4xygen`, log verified in-session): ALL FOUR
MODELS FULLY CERTIFIED** — $\alpha_2^2$: 27/27, $W_2[F]$: 29/29,
$\mu_2^2$: 31/31, $\mu_2{\times}\alpha_2$: 29/29 targets in $J$ (at
DegreeLimit 4, 4, 3, 4 respectively; total wall time under 3 minutes;
`1 in J? false` and both startup gates OK in every block). So EVERY
identity displayed in the fourth note AND the full $s = 4$ endpoint
$D_4 = 0$ are proved over EVERY $\mathbb F_2$-algebra $k'$, for each split
model. By the descent argument recorded in 14.8.7 this banks
**THEOREM M($xy$)**. The note's remaining-work items 1–2 (hand extraction
lemmas) are superseded at theorem level (still nice-to-have for a
self-contained paper write-up); its item 3 (targeted Gröbner job) is
exactly what landed.

**14.8.5 Session-12 machine response, part 2: `scripts/s4xycert.py`**
(chain-queued behind s4cert.py) — the coefficient-robust battery: every
note gate rerun over $\mathbb F_2[\epsilon]/\epsilon^4$ (port
cross-validation), $(\mathbb F_2[u]/u^2)[\epsilon]/\epsilon^4$ (dual
numbers, Frobenius-breaking, ring self-gated by s4cert.gateR0_extd) and
$\mathbb F_4[\epsilon]/\epsilon^4$ (endpoint off by default there, flag
`--f4endpoint`), plus non-vacuity probes ($\lambda \ne 0$, $\rho \ne 0$
realizable; `ell != 0 realizable` for the image-line cases — the latter
also settles empirically whether Remark 12.6.5.7's "$\psi(I) \subseteq
\operatorname{Prim}$" in case (3), where $\operatorname{Prim} = 0$, forces
$\ell = 0$, making the $\mu_2^2$ case triangularly trivial; the note
assumes only the weaker image-in-$k'z$, which is safe either way). Check
`s4xycert.log` ends `ALL S4XYCERT GATES PASSED`.

**14.8.6 $t^4$-side news from the same session (s4gen partials + ideal
algebra).** `s4gen.log` DegreeLimit 4 (2088 s): targets `aB`, `aC`, `BC`,
`aB2C` reduced to 0 — complete arbitrary-$k'$ cofactor certificates at
$\epsilon^4$ (golden rule: partial GB + zero remainder = proof). In
particular the predecessor note's load-bearing $aB = 0$ (14.6) is now
MACHINE-PROVED at arbitrary-$k'$ strength (and independently of its hand
proof), as is $BC = 0$ (third handoff Lemma 2.2). Ideal algebra then closes
two of the four 12.6.6(e) scalars for free — $aB^3 = B^2\,(aB) \in J$ and
$aB^2C = (aB)\,BC$-side products $\in J$ — even though the log lists them
"still open" (a DegreeLimit-truncated GB cannot see product memberships;
the log's list is about REDUCTION, not membership). The genuinely open
machine target for $s = 4$/$t^4$ is the single identity $\Lambda + bB^2
\in J$: both remaining scalars follow from it ($\Lambda B + bB^3 =
B(\Lambda + bB^2)$ and $\Lambda C = C(\Lambda + bB^2) + bB\,(BC)$).
DegreeLimit 5 grinding. Also: `s4pred.py` finished — log ends
`ALL S4PRED GATES PASSED` ($\mathbb F_2$ AND $\mathbb F_4$), completing the
predecessor-note validation of 14.6.

**14.8.7 Banking rule for Theorem M(xy) (mirror of §14.5).** Bank the
$s = 4$ identity for the $xy$ fiber (fibers defined over a perfect subfield,
via the 12.4.3 descent — a fiber-level isomorphism is $\epsilon$-degree-0,
so it transports layered deformations to layered deformations and conjugates
each $\Psi_n$; $D_4 = 0$ is conjugation-invariant) as THEOREM when either
(a) `s4xygen.m2` certifies the nine $D_4$ components for ALL FOUR split
models, or (b) hand proofs of the note's extraction lemmas are written and
the s4xycert dual-number + $\mathbb F_4$ batteries pass. Tower corollary is
automatic ($\Psi_1, \Psi_2, \Psi_3$ depend only on $A/\epsilon^4$, as in
12.6.5.4). Consequences once banked TOGETHER with the $t^4$ side (§14.5
rule): $s \le 4$ complete both fibers ⟹ by 12.6.1, S′-universality over
$k'[\epsilon]/\epsilon^4$, and killed-by-4 over $k'[\epsilon]/\epsilon^5$;
via Thm 7.1, killedness over every socle-line extension of
$k'[\epsilon]/\epsilon^4$.

**14.8.8 THEOREM M($xy$) (banked session 12, via 14.8.7 rule (a)).** *Let
$k'$ be any commutative $\mathbb F_2$-algebra and $N \ge 4$. For every free
rank-4 bialgebra $A$ over $k'[\epsilon]/\epsilon^N$ whose fiber is a
killed-by-2 $xy$-shaped bialgebra defined over a perfect subfield of $k'$,
the $s = 4$ divided-$[4]$ identity holds:*
$$\Psi_1\Psi_3 + \Psi_2\Psi_2 + \Psi_3\Psi_1 = 0.$$
*Proof.* $\Psi_1, \Psi_2, \Psi_3$ depend only on $A/\epsilon^4$, so assume
$N = 4$. Descend to a split model (12.4.1/12.4.3; fiber isomorphisms are
$\epsilon$-degree-0, so they transport layered structure constants to
layered structure constants and conjugate each $\Psi_n$; $D_4 = 0$ is
conjugation-invariant and faithfully-flat-descends). For each of the four
split models, the nine components of $D_4$ lie in the equation ideal $J$ of
the bialgebra axioms over the universal coefficient ring
$Q_2 = \mathbb F_2[\text{structure-constant digits}]$: cofactor
certificates `s4xygen.log` (`==> ALL s4xygen targets in J`, four blocks,
gates OK). $\blacksquare$

Combined with Theorem K towers (12.6.4.2), Theorem 12.6.5.1 towers
(12.6.5.4), and $s = 2$ (12.6.2): **all layer identities $2 \le s \le 4$
hold over $k'[\epsilon]/\epsilon^4$ for the $xy$ fiber** (perfect-subfield
proviso), i.e. S′ holds there once the $t^4$ side (§14.5) is banked too —
see 14.8.9.

**14.8.9 Session-12 machine response, part 3: `scripts/s4t4gen.m2`**
(→ `s4t4gen.log`) — the same pinning trick applied to the $t^4$ fiber to
complete banking rule §14.5(a) independently of the s4cert F₄ battery and
of s4gen's free-$\Delta_0$ grind. Soundness input is the BANKED Theorem-I
normal form (12.3): coassociativity + killed-by-2 pin
$w_0t = c_1\,t{\circ}t^2 + c_1^2\,t^2{\circ}t^3 + c_4\,t^2{\otimes}t^2$;
$\Delta_0$-multiplicativity then determines (hand computation, session 12;
char 2: every $w_0t$-monomial has a tensor leg of degree $\ge 2$, so all
squares die): $w_0(t^2) = 0$ and $w_0(t^3) = t{\circ}t^2 +
c_1\,t^2{\circ}t^3$. Substituting replaces the 27 free digit-0
comultiplication variables by the two parameters $(c_1, c_4)$ — the
solution variety is unchanged since the normal form holds for EVERY
killed-by-2 $t^4$ fiber. Gate: all digit-0 axiom parts must vanish
IDENTICALLY as polynomials in $c_1, c_4$ (this catches a wrong pin table,
including any error in the $w_0(t^2), w_0(t^3)$ derivation — abort on
failure). Targets: nine $D_4$ components + the s4gen scalar list (aB, aC,
BC, Lam+bB2, LamB+bB3, LamC, aB3, aB2C). ALL targets landing = **Theorem
M($t^4$)** at machine strength; then with 14.8.8, 12.6.1 and Thm 7.1:
S′-universality over $k'[\epsilon]/\epsilon^4$ and killed-by-4 over
$k'[\epsilon]/\epsilon^5$ AND over every socle-line extension of
$k'[\epsilon]/\epsilon^4$, both fibers, arbitrary $k'$ (perfect-subfield
proviso for $xy$). Check `s4t4gen.log` for `==> ALL s4t4gen targets in J`
and `DONE s4t4gen` before citing.

## 14.9 THEOREM M($t^4$) banked (session 13, hybrid rule (c))

**14.9.1 The certificate state (log lines verified in-session,
`s4t4gen.log`).** Both startup gates OK (`GATE digit-0 axioms of
(c1,c4)-pinned fiber identically 0: OK`, `GATE phi_0 = 0: OK`);
`1 in J? false` at every stage. Banked by degree: DegreeLimit 2 —
$aB$, $aB^3$, $aB^2C$ (the latter two DIRECTLY, not only via ideal
algebra); DegreeLimit 3 — $BC$; DegreeLimit 4 — $aC$, $D_4[3,1]$;
DegreeLimit 5 (2426 s) — $D_4[3,2]$, $\Lambda + bB^2$, $\Lambda C$.
Ideal algebra: $\Lambda B + bB^3 = B\,(\Lambda + bB^2) \in J$. Still
reducing at DegreeLimit 6: the six $D_4$ components in rows 1–2,
$D_4[3,3]$, and the (already settled) $\Lambda B + bB^3$.

**14.9.2 Banking rule (c) — machine scalars + audited hand assembly.**
§14.5 offered (a) full machine landing or (b) predecessor note + s4cert
DN/F₄ batteries. What has landed is stronger than (b) and does not need
to wait for (a): ALL scalar inputs of the audited hand chain — $aB$
(predecessor note, 14.6), $BC$, $\Lambda + bB^2$ (third handoff,
14.1–14.3), and the four 12.6.6(e) assembly scalars $aB^3$, $aB^2C$,
$\Lambda B + bB^3$, $\Lambda C$ — are cofactor certificates over
$Q_2 = \mathbb F_2[\text{structure-constant digits}]$ at $\epsilon^4$.
A Gröbner certificate over $Q_2$ is valid over EVERY $\mathbb F_2$-algebra
$k'$ and is immune to the Frobenius-collapse caveat that made the
DN/F₄ batteries necessary for rule (b) (an $\mathbb F_2$-point gate cannot
distinguish $\rho$ from $\rho^2$; an ideal membership can). The 12.6.6(e)
assembly itself (session 10, audited §14.1 "logical assembly CORRECT" and
14.6 "chain of custody complete on paper") is a purely axiomatic hand
computation, valid over arbitrary $k'$. Hence:

**14.9.3 THEOREM M($t^4$).** *Let $k'$ be any commutative
$\mathbb F_2$-algebra and $N \ge 4$. For every free rank-4 bialgebra $A$
over $k'[\epsilon]/\epsilon^N$ whose fiber is a killed-by-2 $t^4$-shaped
bialgebra (fully axiomatic — no classification or perfect-subfield input),
the $s = 4$ divided-$[4]$ identity holds:*
$$\Psi_1\Psi_3 + \Psi_2\Psi_2 + \Psi_3\Psi_1 = 0.$$
*Proof.* $\Psi_1, \Psi_2, \Psi_3$ depend only on $A/\epsilon^4$, so assume
$N = 4$. The Theorem-I normal form (12.3, axiomatic) puts the fiber
comultiplication in $(c_1, c_4)$-pinned form; the digit-0 gate certifies
the pin. The scalars $aB$, $aC$, $BC$, $\Lambda + bB^2$, $aB^3$, $aB^2C$,
$\Lambda C$ lie in the axiom ideal $J$ over $Q_2$ (`s4t4gen.log`,
14.9.1), and $\Lambda B + bB^3 = B(\Lambda + bB^2) \in J$. The 12.6.6(e)
assembly (audited, 14.1/14.6) derives all nine components of $D_4$ from
exactly these scalars. $\blacksquare$

**14.9.4 COROLLARY (the $\epsilon^4/\epsilon^5$ closure, BOTH fibers).**
With Theorem M($xy$) (14.8.8), Theorems I/K/L (s = 2, 3) and 12.6.1:
for every $\mathbb F_2$-algebra $k'$ (perfect-subfield proviso for the
$xy$ fiber only),
1. **S′-universality over $k'[\epsilon]/\epsilon^4$** — every free rank-4
   bialgebra with killed-by-2 local fiber satisfies S′;
2. by Thm 7.1, **killed-by-4 over $k'[\epsilon]/\epsilon^5$** and over
   **every socle-line extension of $k'[\epsilon]/\epsilon^4$** (including
   non-curvilinear ones);
3. the per-$s$ treadmill state is now: $s \le 4$ banked, $s = 5$ = the
   live frontier (see §15).

**14.9.5 Belt-and-braces.** `s4t4gen` continues at DegreeLimit 6+ toward
direct membership of the remaining seven $D_4$ components; full landing
would upgrade M($t^4$) to §14.5 rule (a) (pure machine, no hand assembly
in the chain). Not needed for banking; do not block on it. `s4gen.m2`
(free-$\Delta_0$) is now FULLY subsumed (t⁴ scalars by s4t4gen, xy by
s4xygen) — killed in session 13, deliberate (banner in its log).

## 15. Audit of the FIFTH external note (relative defect; session 13) + the cotangent reduction

Source: `order4_fifth_push_relative_defect.md` (2026-07-09, 10:49) with
bundle `order4_fifth_push_bundle.zip` → `scripts/fifth_push_bundle/`
(four Z3 probe scripts + logs). The note continues from the v3 archive.
Its v3-state audit (§0) is accurate on both counts it makes: `s4xygen`
complete, `s4t4gen` incomplete *in that archive* (superseded by §14.9:
banked in session 13 by rule (c)).

### 15.1 Setting and the top-defect map $\Omega$

Let $R' = k[\epsilon]/\epsilon^{N+1} \to R = k[\epsilon]/\epsilon^N$
($N \ge 1$), $A'$ a free rank-4 bialgebra over $R'$ with killed-by-2 local
fiber $H$, $A = A'/\epsilon^N A'$, and assume **S′($A/R$)**. By Theorem 7.1,
$\varphi'^2 = 0$ on $A'$ — this is used repeatedly below.

For $g \in I_H$, choose a lift $\tilde g \in I_{A'}$ and an
$\epsilon$-division $v_g \in I_{A'}$ of $\varphi'(\tilde g)$ (exists:
Lemma 1.3 gives $\varphi'(I') \subseteq \epsilon I'$ coordinatewise). Then:

* $\varphi'(v_g) \in \epsilon^N I'$. [The truncation $\bar v_g$ is an
  $\epsilon$-division of $\varphi_A(\bar{\tilde g})$ over $R$, so by
  Proposition 7.5.1(ii)+(iii) and S′($A/R$): $\varphi_A(\bar v_g) = 0$;
  hence $\varphi'(v_g) \equiv 0 \bmod \epsilon^N$, and it lies in $I'$
  since $\varphi'$ preserves $I'$.]
* Define $\Omega(g) := \big[\varphi'(v_g)/\epsilon^N\big]_0 \in I_H$
  (fiber digit). **Well-defined**, independent of all three choices:
  the division ($v_g \rightsquigarrow v_g + \epsilon^N u$, $u \in I'$:
  $\varphi'(\epsilon^N u) = \epsilon^N\varphi'(u) \in \epsilon^{N+1}I' = 0$);
  the lift ($\tilde g \rightsquigarrow \tilde g + \epsilon c$, $c \in I'$:
  changes $v_g$ by $\varphi'(c) + (\text{ann}(\epsilon)\text{-element})$, and
  $\varphi'(\varphi'(c)) = 0$ by killedness); $k$-linearity is clear. In
  fact $\epsilon^N\widetilde{\Omega(g)} = \delta'_g$, the Proposition-7.5.1
  defect of $A'/R'$ at $g$ — $\Omega$ is just the top digit of $\delta'$.

**Consequence (the bridge the note leaves implicit).** Combining with
7.5.1(iii): *given S′($A/R$),*
$$\text{S′}(A'/R') \iff \Omega(e_i) = 0 \text{ for a basis } e_i
\text{ of } I_H.$$

### 15.2 Lemma 1.1 of the note ($\Omega$ kills products): AUDIT = CORRECT

The note's proof is sound; recomputed in-session. Mechanics: for
$a, b \in I_H$, $\varphi'(\tilde a\tilde b) = \varphi'(\tilde a)
\varphi'(\tilde b) = \epsilon\cdot(\epsilon v_a v_b)$, so $\epsilon v_av_b$
is a valid division; $\varphi'(\epsilon v_av_b) =
\epsilon\,\varphi'(v_a)\varphi'(v_b) \in \epsilon\cdot\epsilon^N\cdot
\epsilon^N I' = 0$. The lift-discrepancy $\tilde a\tilde b =
\widetilde{ab} + \sum_r \epsilon^r m_r$ contributes
$\epsilon^{r-1}\varphi'^2(m_r) = 0$ per term. Hence $\Omega(ab) = 0$. ∎

Two supplements banked with the audit:

* **15.2.1 (characteristic-free).** The proof uses only: $\varphi$
  multiplicative and $I$-preserving, Lemma 1.3, Theorem 7.1, and principal
  $\mathfrak m$ arithmetic. All are characteristic-free. So Lemma 1.1 and
  the 15.1 bridge hold verbatim over every CURVILINEAR Artin local socle
  step, mixed characteristic included ($\mathbb Z/2^{N+1} \to \mathbb Z/2^N$,
  ramified towers, …). The note states it equal-char only.
* **15.2.2 (COTANGENT REDUCTION, the operative form).** Given S′ universally
  at level $N$: S′ at level $N+1$ reduces to $\Omega(\text{cotangent
  generators}) = 0$ — for $t^4$: the SINGLE value $\Omega(t)$; for $xy$:
  $\Omega(x), \Omega(y)$ (then $\Omega(z) = \Omega(xy) = 0$ free). In layer
  language (12.6.1, all lower identities in force): the product-class ROWS
  of $D_{N+1}$ vanish for formal reasons; the cotangent row is the entire
  remaining content of the depth program — at EVERY depth. This matches
  and explains the empirical shape of the $s = 3, 4$ proofs.

### 15.3 Lemma 2.1 of the note (pairwise nilpotence): AUDIT = CORRECT

Claim: any two first-order symbols $\psi, \chi$ of deformations of the SAME
fiber bialgebra $H$ compose to zero: $\psi\chi = \chi\psi = 0$.

* $t^4$: banked 12.3 gives $\chi(I) \subseteq I^2$ and banked 12.1.1 gives
  $\psi(I^2) = 0$ (that identity is universal: layer-1 multiplicativity
  $\psi(ab) = \varphi_0(\mu_1(a,b)) = 0$ since $\mu_1(a,b) \in I_H$ by the
  layer-1 counit and $\varphi_0|_{I_H} = 0$). Composite $= 0$. Any $k'$.
* $xy$, per split model (12.4.1, descent as in Theorem I; perfect-subfield
  proviso): cases (1)/(3) — $\psi(I) \subseteq I^2$, $\psi(I^2) = 0$, same
  argument. Case (2) $W_2[F]$ — banked 12.4.3 gives $\psi(x) = 0$ EXACTLY,
  $\psi(z) = 0$, $\psi(y) \in k''x + k''z$; so for two symbols,
  $\psi\chi(y) \in \psi(k''x + k''z) = 0$ and $\psi\chi(x) = \psi\chi(z) =
  0$. Case (4) is the mirror. Note: the composite-vanishing needs only the
  WEAKER banked forms (image in $kx + kz$), not the session-10 sharpenings
  $\psi(y) = \lambda x$ exactly — the note's "image in a fixed subspace
  annihilated by all symbols" phrasing implicitly uses the sharpened form,
  but the conclusion holds either way. ∎

Machine gates: `s5gates.py` battery A rows PW0 (non-vacuity, `sat`) and PW
(`unsat` = the lemma at $k = \mathbb F_2$) over the NEW ring class
$\mathbb F_2[u,v]/(u,v)^2$ (`FatPoint2`, added to `order4sat_beyond.py` +
`ringcheck.py` CASES this session — cite only after the ringcheck rerun's
ALL-PASSED line, per golden rule 1b).

### 15.4 THEOREM N (banked): S′ is universal over every equal-characteristic square-zero base, in every embedding dimension

*Let $(R,\mathfrak m)$ be an Artin local ring with $\mathfrak m^2 = 0$,
containing a coefficient field $k$ of characteristic 2 (automatic for the
finite residue fields of the §3 reduction, by Cohen), and let $A/R$ be a
free rank-4 bialgebra with killed-by-2 local fiber $H$ (for the $xy$ shape:
defined over a perfect subfield). Then S′($A/R$) holds.*

*Proof (note §3, audited).* Write $R = k \oplus \mathfrak m$, pick a
$k$-basis $(m_\alpha)$ of $\mathfrak m$. Since $\varphi(e_i) \in
\mathfrak mI$ (Lemma 1.3), $\varphi(e_i) = \sum_\alpha m_\alpha
k_{i,\alpha}$ with $k_{i,\alpha} \in I_H$ (coefficients in $k$ via the
basis splitting). Each $k_{i,\alpha} = \psi_\alpha(e_i)$ where $\psi_\alpha$
is the symbol of the restriction of $A$ along the ring surjection
$R \twoheadrightarrow R/(m_\beta : \beta \ne \alpha) \cong k[\epsilon]/
\epsilon^2$ (a ring map because $\mathfrak m^2 = 0$), a first-order
deformation of the same fiber $H$. Then $\varphi(k_{i,\alpha}) =
\sum_\beta m_\beta\,\widetilde{\psi_\beta\psi_\alpha(e_i)} = 0$ by pairwise
nilpotence (15.3), i.e. every $k_{i,\alpha} \in \ker\varphi\cap I$, i.e.
$\varphi(e_i) \in \mathfrak m(\ker\varphi\cap I)$. ∎

**Scope notes.** (i) Killedness-wise this adds nothing beyond Corollary J
(any $R$ reachable from a square-zero base by one socle line has
$\mathfrak m^3 = 0$); its content is the S′ form — the correct BASE CASE
for the non-principal socle induction, with no bound on embedding
dimension. It retires the "square-zero" part of §14.7 item 3.
(ii) Mixed-characteristic square-zero bases ($\mathbb Z/4$,
$\mathbb Z/4[y]/(y^2,2y)$, …) are NOT covered — no coefficient field; the
$\mathbb Z/4$ case is known by SAT (Theorem G) but the multi-parameter
mixed-char analogue of pairwise nilpotence is open (Witt-carry frontier).
(iii) Machine gate: `s5gates.py` battery A row S2 (`unsat`), both fibers,
over FatPoint2.

### 15.5 Bidual calculus (note §4): AUDIT = CORRECT, with one sharpening

Over $R = k[u,v]/(u^2,v^2)$, $\varphi = uP + vQ + uvT$: the truncation to
$R/(uv)$ (square-zero) satisfies S′ by Theorem N, and $P, Q$ are its
directional symbols with $P^2 = Q^2 = PQ = QP = 0$ (15.3). The general
division bookkeeping and both boxed lifting equations
$$TPg + Qr_g + Pa_g = 0, \qquad TQg + Qb_g + Ps_g = 0
\quad (b_g = Tg + a_g)$$
were recomputed in-session and are exactly right ($u^2 = v^2 = 0$ kills all
other carry terms; free parameters $r_g, a_g, s_g \in I_H$). So
S′($A/R$) $\iff$ solvability of these $k$-linear systems at $g = $ cotangent
generators only.

**Sharpening 15.5.1 (products are free over EVERY $\mathfrak m^3 = 0$ base,
unconditionally).** Let $(R,\mathfrak m)$ be Artin local with $\mathfrak m^3
= 0$ (any characteristic, any embedding dimension), $A/R$ free rank-4 with
killed-by-2 fiber, $a, b \in I_A$. Write $\varphi(a) = \sum_\alpha
u_\alpha A_\alpha$ ($u_\alpha$ generators of $\mathfrak m$, $A_\alpha \in I$;
Lemma 1.3). Then
$$\varphi(ab) = \varphi(a)\varphi(b) = \sum_\alpha u_\alpha\,
\big[A_\alpha\,\varphi(b)\big],$$
and each component $A_\alpha\varphi(b) \in I$ lies in $\ker\varphi$:
$\varphi(A_\alpha\varphi(b)) = \varphi(A_\alpha)\,\varphi^2(b)$ has
coefficients in $\mathfrak m\cdot\mathfrak m^2 = 0$ (any $A$-product of two
$I$-vectors has coefficients in the ideal generated by pairwise coefficient
products). So $\varphi(ab) \in \mathfrak m(\ker\varphi\cap I)$ with an
EXPLICIT division — no appeal to Lemma 1.1/Theorem 7.1, no S′ hypothesis.

**Basis-change point (the subtlety that makes this usable).** The argument
applies to the product OF LIFTS $e_1e_2 \in I_A$, not to a basis element
$e_3$ chosen independently; but $\{e_1, e_2, e_1e_2\}$ is again an $R$-basis
of $I$ (transition matrix $=$ identity $+$ $\mathfrak m$-entries, invertible
over Artin local $R$), and S′ is a submodule-membership condition, so it may
be checked on this basis. Consequence: **over every $\mathfrak m^3 = 0$
base, S′ $\iff$ the cotangent-generator memberships** ($e_1$ for $t^4$ —
$e_1^2$ and $e_1^3$ likewise free, the latter with $\varphi(e_1^3) =
\varphi(e_1)^3$ having coefficients in $\mathfrak m^3 = 0$; $e_1, e_2$ for
$xy$). Machine use: `s2check_np3.py` (session 13) attacks the FatPoint3/$xy$
gap with FAIL restricted to $i = 1, 2$ and SPLIT per-generator queries,
gated by `gateP` (the kernel certificate above on a symbolic structure).

The two boxed equations are the cleanest known formulation of the FIRST
non-principal induction step ($\mathbb F_2$ instance already known:
Theorem G′, s2check_np BiDual `unsat` ✓✓). The arbitrary-$k$ hand target:
show $TP g + P a_g \in \operatorname{im} Q$ and
$TQg + Q(Tg + a_g) \in \operatorname{im} P$ are simultaneously solvable in
$a_g$, using the 12.x shape theory of $P, Q$ ($P(I) \subseteq I^2$ for
$t^4$, etc.) and whatever pins $T$ (the $uv$-layer analogue of the
$\Psi_2$ identities — NOT yet worked out; this is the bigraded calculus of
§14.7 item 3).

### 15.6 The $D$-map decomposition of $\Omega$ (session-13 addition)

For computations and for the induction hunt, split $\Omega$ by choices:
pick $\bar v \in \ker\varphi_A \cap I_A$ with $\varphi_A(\bar t) =
\epsilon\bar v$ (exists by S′($A/R$), principal case), lift it to
$v \in I_{A'}$; then $\varphi'(\tilde t) = \epsilon v + \epsilon^N w$ for
some $w \in I'$ (coordinatewise), and
$$\Omega(t) = \big[\varphi'(v)/\epsilon^N\big]_0 + \psi_1(w_0),$$
where $\psi_1 = \Psi_1$ is the first-layer symbol and $w_0$ the fiber digit
of $w$. Neither term is separately well-defined — changing $\bar v$ by
$\epsilon^{N-1}\delta_0$ shifts BOTH terms by $\psi_1(\delta_0)$ (char 2:
the shifts cancel) — but the decomposition isolates the two mechanisms:
1. $[\varphi'(v)/\epsilon^N]_0$ = the **kernel-lift defect**: how far
   $\varphi'$ moves a lift of a kernel element (this is the $\beta$-map of
   Open Lemma 7.4 in coordinates);
2. $\psi_1(w_0)$ = first-order symbol applied to the **new digit** of
   $\varphi'(\tilde t)$.
The uniform relative lemma = these two contributions cancel for every
tower. At $N = 1$: $\bar v$ can be taken $0$, $w_0 = \psi_1(t)$, and
$\Omega(t) = \psi_1^2(t)$ — Theorem I. At $N = 2, 3$: Theorems K/L, M. The
$s \ge 5$ hunt should target this cancellation, not the full $D_s$ matrix
(15.2.2).

### 15.7 The note's s = 5 probes (bundle) + session-13 response

Bundle logs (verified in-session): over $\mathbb F_2[\epsilon]/\epsilon^5$,
$t^4$ fiber, $\Delta_0$ pinned (over $\mathbb F_2$ the $c_1$-vs-$c_1^2$ pin
difference is Frobenius-invisible — fine there, NOT fine for arbitrary-$k'$
runs), with banked $D_2$–$D_4$ as constraints: $D_5(1,1), D_5(1,2),
D_5(2,1), D_5(2,2)$ negations all `unsat`. No verdicts for $(2,3), (3,1),
(3,2), (3,3)$ (predicted by 15.2.2) or $(1,3)$ (THE open cotangent
component; their run skipped it).

Session-13 response, three jobs launched:
* `s5gates.py` battery B: the four missing Lemma-1.1 rows (cross-validation)
  + $D_5(1,3)$ with no timeout, LAST.
* `s5t4gen.m2`: arbitrary-$k'$ ideal membership at $\epsilon^5$, $(c_1,c_4)$
  pin with the CORRECT $c_1^2$, banked s ≤ 4 identities + 14.x scalars
  adjoined as generators ("banked boost" — soundness: they vanish at every
  $k'$-point of $V(J)$, so membership in $J_{\text{aug}}$ still certifies
  vanishing-on-solutions, which is the theorem content; record results as
  such, NOT as raw membership in $J$). Cotangent row = the content; product
  rows included as belt-and-braces.
* `s5xygen.m2`: same at $\epsilon^5$ for the four $xy$ split models
  (s4xygen pattern), cotangent rows $i = 1, 2$.
Full success ⟹ **s = 5 closed both fibers, arbitrary $k'$** ⟹
S′-universality over $k'[\epsilon]/\epsilon^5$, killedness over
$k'[\epsilon]/\epsilon^6$ + all socle-line extensions of $\epsilon^5$
(12.6.1 + 7.1 + 15.2.2).

### 15.8 The divided-squaring calculus (session-13 hand work): the uniform target as $\Phi^2 = 0$

Over $R' = k[\epsilon]/\epsilon^{N+1}$ with killed-by-2 fiber, Lemma 1.3
gives $\varphi(I') \subseteq \epsilon I'$ coordinatewise, so there is a
(non-unique, defined mod $\epsilon^N I'$) **divided squaring operator**
$$\Phi := \varphi/\epsilon : I' \to I',\qquad
\Phi = \Psi_1 + \epsilon\Psi_2 + \cdots + \epsilon^{N-1}\Psi_N
\ \ (\text{on constant-coefficient vectors}).$$

**15.8.1 The two axioms.** (i) $\Phi$ is $R'$-linear mod
$\operatorname{ann}(\epsilon)$; in particular $\Phi(\epsilon x) =
\epsilon\Phi(x)$. (ii) Divided multiplicativity:
$$\Phi(xy) = \epsilon\,\Phi(x)\Phi(y) \pmod{\epsilon^N I'}\qquad
(x, y \in I').$$
[Proof: $\epsilon\Phi(xy) = \varphi(xy) = \varphi(x)\varphi(y) =
\epsilon^2\Phi(x)\Phi(y)$, divide.] No commutativity of $A'$ is used.

**15.8.2 CONJECTURE $\Phi$ (equivalent to equal-char curvilinear
S′-universality, i.e. to the curvilinear half of Conjecture 7.5.4).** For
every tower and both fibers: $\Phi^2 = 0$ exactly (not just mod
$\epsilon^{N-1}$). Banked so far: the digits of $\Phi^2$ in
$\epsilon^0..\epsilon^2$ (= $D_2, D_3, D_4$; Theorems I/K/L/M) and — if
`s5t4gen`/`s5xygen` land — $\epsilon^3$ ($D_5$). Lemma 1.1 = $\Phi^2$ kills
$I'\cdot I'$ at the top digit; 15.5.1 = the same at ALL digits for
$\mathfrak m^3 = 0$.

**15.8.3 The recursion for the cotangent value (t⁴).** Write $v := \Phi(t)$,
$\Psi_1 t = B t^2 + C t^3$ ($B, C \in k$ — the s = 4 scalar names), and
$u := (v - \Psi_1t)/\epsilon$ (so $v = \Psi_1 t + \epsilon u$). Using
$t\cdot_{A'} t = t^2 + \sum_{n\ge1}\epsilon^n\mu_n(t,t)$ and the axioms:
$$\Phi(t^2) = \epsilon\,v^2 + \sum_{n\ge1}\epsilon^n\,\Phi(\mu_n(t,t)),
\qquad\text{(sim. } \Phi(t^3)\text{)},$$
$$\boxed{\ \Phi^2(t) = \Phi(v) = \epsilon B v^2
+ B\sum_{n\ge1}\epsilon^n\Phi(\mu_n(t,t))
+ C\,\Phi(t^3\text{-analogue}) + \epsilon\,\Phi(u).\ }$$
Every term carries an explicit $\epsilon$: the top digit of $\Phi^2(t)$ is
built from digit-$(N{-}2)$ data of $v^2$, $\Phi(u)$ and
digit-$(N{-}1{-}n)$ data of $\Phi(\mu_n(t,t))$. **Why induction does not
yet close:** the inductive hypothesis (lower-depth S′) controls
$\Phi^2$-values, but the recursion consumes $\Phi$-VALUES of the auxiliary
elements $u$, $\mu_n(t,t)$, $v^2$ — one derivative less. The missing
ingredient is a lemma controlling $\Phi$ on $\ker\varphi_A$-lifts (the
$D$-map of 15.6) in terms of $\Phi^2$-data of shallower towers. This is the
sharpest formulation to date of what the uniform lemma needs; suggested
next: (a) hunt for an identity expressing $[\Phi(u)]_{N-2}$ via the
layer-$(s{-}1)$ identities of the $\epsilon$-SHIFTED tower
$A'' := A'\otimes_{R'} k[\epsilon]/\epsilon^N$ twisted by one $\Psi$-index
(the shift $u = \Psi_2t + \epsilon\Psi_3t + \cdots$ is exactly the tower
symbol sequence with indices shifted by one — a "suspension"; if the
identity family were CLOSED under suspension, induction would close);
(b) machine-probe the suspension idea at small depth (does the shifted
sequence $(\Psi_2, \Psi_3, \ldots)$ of a valid tower again satisfy the
$D_s$ family? `s6probe.py` includes a discovery row for
$\Sigma_2 := \Psi_2\Psi_2 + \Psi_1\Psi_3 + \Psi_3\Psi_1$-analogues with
shifted indices).

**15.8.4 The edge/suspension split (session-13 hand work, exact).** Sorting
$D_{N+1} = \sum_{m+l=N+1}\Psi_m\Psi_l$ by whether an index equals 1:
$$\boxed{\ D_{N+1} \;=\; \{\Psi_1, \Psi_N\} \;+\; \Sigma^{\uparrow}_{N-1},
\qquad
\Sigma^{\uparrow}_{s} := \sum_{m+l=s,\ m,l\ge1} \Psi_{m+1}\Psi_{l+1}\ }$$
($\{\,,\}$ = anticommutator = sum in char 2; $\Sigma^{\uparrow}_s$ is the
index-suspension of $D_s$). Iterating: $D_s = \sum_j \{\Psi_j,
\Psi_{s-j}\}$ + middle square — trivially; the CONTENT is whether the
partial (suspended) sums vanish separately. Two-family strategy:

* **IF the suspension sums vanish** ($\Sigma^{\uparrow}_s = 0$ given the
  banked identities — exactly what `s6probe`'s discovery rows test at the
  first two instances; note $D_4 = 0$ makes the $s{=}2$ row equivalent to
  "$\{\Psi_1,\Psi_3\}$ can be nonzero alone"), **THEN the uniform lemma
  reduces to the EDGE family** $\{\Psi_1, \Psi_N\}(t) = 0$ for all $N$.
* **The edge family is scalar-shaped** ($t^4$): $\Psi_1$ kills $I^2$
  (12.1.1) and has image in $I^2$ (12.3), so
  $$\{\Psi_1,\Psi_N\}(t) = (\Psi_Nt)_t\,\big(Bt^2 + Ct^3\big)
  + B\,\Psi_N(t^2) + C\,\Psi_N(t^3),$$
  involving only the three values of $\Psi_N$ and the Theorem-I scalars
  $B, C$. Layer-$N$ multiplicativity (the generalization of Theorem K's
  step 1) rewrites $\Psi_N(t^2), \Psi_N(t^3)$ in lower-layer data — the
  same mechanism that closed $s = 3, 4$, now needed once, uniformly in $N$.
  Caveat from the s3probe discovery (session 8): individual anticommutators
  do NOT vanish separately in general ($\{\Psi_1,\Psi_2\} = 0$ only as a
  sum at $s = 3$)... but that concerned SMALL-index pairs; the suspension
  question is about the $m, l \ge 2$ tail, which is different. The probe
  decides.

**15.8.5 VERDICT (session 13, `s6probe.log`, `DONE s6probe`).** Both
suspension discovery rows returned `sat`: with $D_2$–$D_5$ enforced over
$\mathbb F_2[\epsilon]/\epsilon^6$, structures exist with
$\Psi_2\Psi_2 \ne 0$ (equivalently $\{\Psi_1,\Psi_3\} \ne 0$ alone) and
with $\{\Psi_2,\Psi_3\} \ne 0$. **The edge/suspension decoupling FAILS**:
the cancellation inside each $D_s$ is globally coupled across index pairs,
exactly as at $s = 3$. Route decision for Conjecture $\Phi$: the coupled
15.8.3 recursion / relative $D$-map lemma — NOT term-by-term splitting.
Bonus from the same run: **all nine $D_6$ components `unsat`** including
the full cotangent row — the first $s = 6$ data point ever (exact-$k =
\mathbb F_2$, $t^4$ fiber, pinned normal form + banked $s \le 5$): the
$s = 6$ identity has no $\mathbb F_2$ counterexample, i.e. the exact-F₂
content of S′ over $\mathbb F_2[\epsilon]/\epsilon^6$ ($t^4$ side) is
confirmed one depth beyond every previous probe.

### 15.9 State of the frontier after the fifth note

1. **Equal-char curvilinear, uniform in depth**: cotangent relative lemma
   ($\Omega(t) = 0$ / $\Omega(x) = \Omega(y) = 0$ given S′ below) — THE
   prize; now a 1-(resp. 2-)target problem per depth (15.2.2). Cleanest
   formulation: **Conjecture $\Phi$** (15.8.2, $\Phi^2 = 0$ exactly for the
   divided squaring operator); attack surfaces = the 15.6 decomposition and
   the 15.8.3 recursion + suspension question.
2. **Equal-char non-principal**: base case DONE (Theorem N); first
   induction step = the bidual boxed equations (15.5) at arbitrary $k$;
   general step = bigraded layer calculus (multi-variable analogue of
   12.6.1) — formulate S′ over $k[u_1..u_e]/(\text{monomials})$ as
   multidegree identities and find the analogues of Lemmas 1.1/2.1 (1.1's
   product-kill mechanism visibly survives: 15.5.1).
3. **Mixed char**: everything exact-ring so far (lengths ≤ 5–6); no hand
   framework. 15.2.1 at least transports the cotangent reduction to
   mixed-char curvilinear steps for free.

## 16. Audit of the SEVENTH external note (bidual $xy$ rank-one; session 14) + closure of the ENTIRE bidual step — THEOREM O

Source: `order4_seventh_push_bidual_xy_rank1.md` (2026-07-09, 13:45) with
bundle → `scripts/seventh_push_bundle/` (three Z3 gate scripts + logs;
rerun locally in-session with `PYTHONPATH` pointed at `scripts/` — their
hardcoded `/mnt/data/groth_v42/scripts` path does not exist here — all
four verdict lines reproduced exactly).

**Missing-predecessor alert (same pattern as the session-11 aB=0 note).**
The note opens "continues from `grothendieck_order4_handoff_v4(2).zip`"
and asserts "the bidual $t^4$ branch was closed in the previous pass" —
i.e. there exists a SIXTH push note, never delivered to this folder. No
§-numbered audit of a sixth note exists in this file. The dependency is
DISCHARGED by §16.2 below (independent in-session closure of the bidual
$t^4$ branch), but the sixth note should still be obtained from the user
for provenance and for any leaner mechanism it may contain.

### 16.1 What the note proves, and the audit verdicts

Setting = §15.5: $R = k[u,v]/(u^2,v^2)$, $\varphi = uP + vQ + uvT$,
S′($A/R$) $\iff$ the boxed systems (B1) $TPg + Qr_g + Pa_g = 0$,
(B2) $TQg + Q(Tg + a_g) + Ps_g = 0$ solvable at the cotangent generators
$g$ (15.5.1 kills the product classes; pairwise nilpotence 15.3 kills the
lower digits of $\varphi(k_i)$).

**(i) Rank-one split branches $W_2[F]$, $\mu_2{\times}\alpha_2$ (note
§§1–2): CORRECT.** Both two-line verifications recomputed by hand
in-session and they close exactly as displayed; no division by $\lambda,
\lambda'$ anywhere. Inputs the note uses without displayed derivations
(claimed "as in the $s=3$ proof", i.e. the Theorem-L Step-B machinery
polarized to the $uv$-layer):
  * (R1) $T(x) = \alpha x$ (resp. $T(y) = \alpha y$ in the mirror);
  * the polarized assembly formula $\rho = \lambda\alpha_Q + \nu\delta_Q +
    \lambda'\alpha_P + \nu'\delta_P$ for $\rho = (Ty)_y$;
  * the polarized diagonal $(2,2)$ identities $\lambda\delta_Q +
    \lambda'\delta_P = 0$, $\nu\delta_Q + \nu'\delta_P = 0$ (their
    conjunction turns the assembly formula into (R3) $\rho = \lambda
    \alpha_Q + \lambda'\alpha_P$).
All of these are now certified at arbitrary-$k'$ strength by
`bidualgen`/`bidualxy` (targets `R1[*]`, `rho`, `pol22a`, `pol22b` — in
$J$ for both rank-one models), and the note's explicit divisions
themselves are certified as the residual targets `B1res[*]`, `B2res[*]`
$\in J$. At $g = x$ (resp. $y$) the zero-witness solvability follows from
the shape + R1 targets by ideal algebra (every term of $TPx$, $TQx$,
$Q(Tx)$ carries a factor already in $J$ — the session-12 product-
membership reading rule applies).

**(ii) Koszul reduction of the image-line branches (note §3): CORRECT.**
Recomputed: with $P(g) = p_g z$, $Q(g) = q_g z$, $P(z) = Q(z) = 0$ and the
mixed-layer triangularity (I0) $T(z) = \tau z$, the substitution $a_g =
\tau g + h_g$ reduces (B1)–(B2) to $p(h_g) + q(r_g) = 0$ and
$q(\overline{Tg}) + q(h_g) + p(s_g) = 0$, and the displayed
$h_g, r_g, s_g$ solve these given a representation
$$\text{(I2)}\qquad q(\overline{Tg}) = p_xS_x + p_yS_y + q_x^2H_x +
q_xq_yH_{xy} + q_y^2H_y .$$
(The note's §5 also lists the $P/Q$-symmetric counterpart; by the audit
(I2) alone suffices — the symmetric form was certified anyway, below.)
Two typos, no mathematical effect: stray `\n` tokens in the polarized
$(2,2)$ display; "R2" is used both for the statement and its refined form
(R3).

**(iii) The note's fresh gates**: two dual-coefficient triangularity
probes ($T(x) \in kx$ for $W_2[F]$, $T(y) \in ky$ for $\mu_2\alpha_2$,
over $(\mathbb F_2[d]/d^2)[u,v]/(u^2,v^2)$, `unsat`) and the two
$\rho \in (\lambda_u,\lambda_v)$ rank-ideal gates over $\mathbb F_2$
(`unsat`). All four reproduced locally. These are exact-ring sanity
checks only; the arbitrary-$k'$ content is (i)–(ii) + `bidualgen`.

### 16.2 Session-14 closure of the bidual $t^4$ branch (sixth note not needed)

**Lemma 16.2.1 (polarized product-kill).** For $x, y \in I_H$ (constant
vectors): $P(\mu_0(x,y)) = Q(\mu_0(x,y)) = 0$.
*Proof.* $u$-digit (resp. $v$-digit) of $\varphi(x \cdot_A y) =
\varphi(x)\varphi(y)$: the right side has every term with at least two
$\mathfrak m$-factors, while the left side's $u$-digit is $P(\mu_0(x,y))$
(the $u\mu_P(x,y)$ term of $x\cdot_Ay$ contributes only to the $uv$-digit
after applying $\varphi$). $\square$

**Lemma 16.2.2 (polarized layer-2 multiplicativity).** For $x, y \in I_H$:
$$T(\mu_0(x,y)) = P(\mu_Q(x,y)) + Q(\mu_P(x,y)) + \mu_0(Px, Qy) +
\mu_0(Qx, Py).$$
*Proof.* $uv$-digit of the same equation; $u^2 = v^2 = 0$ kills the
diagonal carries $P\mu_P$, $\mu_0(P\cdot,P\cdot)$, etc. This is the
polarization of Theorem K's step (1) (layer-2 multiplicativity
$\Psi_2\mu_0 = \Psi_1\mu_1 + \mu_0(\Psi_1{\cdot},\Psi_1{\cdot})$): the
curvilinear diagonal terms split into the two cross terms. $\square$

**Theorem 16.2.3 (bidual S′, $t^4$ fiber, arbitrary $k'$).** Every free
rank-4 bialgebra over $R = k'[u,v]/(u^2,v^2)$ ($k'$ any
$\mathbb F_2$-algebra) with killed-by-2 $t^4$-shaped fiber satisfies
S′($A/R$).
*Proof.* Cotangent generator $g = t$ only (15.5.1; $t^2, t^3$ free). By
Lemma 16.2.1, $P(t^2) = P(t^3) = Q(t^2) = Q(t^3) = 0$ (machine: `kill*`
targets), and $Pt, Qt \in I^2$ (Theorem I per direction; machine: `PtI2`,
`QtI2`). Write $Pt = B_Pt^2 + C_Pt^3$, $Qt = B_Qt^2 + C_Qt^3$. By Lemma
16.2.2 at $(t,t)$ and $(t,t^2)$ — the $\mu_0(P\cdot,Q\cdot)$ terms die
because $I^2 \cdot I^2 = 0$ in $k'[t]/t^4$, and $P, Q$ kill the
$I^2$-parts of $\mu_Q, \mu_P$ by 16.2.1 —
$$T(t^2) = \mu_Q(t,t)_t\,Pt + \mu_P(t,t)_t\,Qt,\qquad
T(t^3) = \mu_Q(t,t^2)_t\,Pt + \mu_P(t,t^2)_t\,Qt.$$
Hence $TPt = A_sPt + R_sQt$ with $A_s = B_P\mu_Q(t,t)_t +
C_P\mu_Q(t,t^2)_t$, $R_s = B_P\mu_P(t,t)_t + C_P\mu_P(t,t^2)_t$, and (B1)
is solved by $a = A_st$, $r = R_st$. Likewise $TQt = \alpha_sPt +
\beta_sQt$ ($\alpha_s, \beta_s$ = the same scalars with $B_Q, C_Q$), and
(B2) with $s = \alpha_st$ reduces to $\kappa\,Qt = 0$ where
$$\kappa = (Tt)_t + A_s + \beta_s = (Tt)_t + B_P\mu_Q(t,t)_t +
C_P\mu_Q(t,t^2)_t + B_Q\mu_P(t,t)_t + C_Q\mu_P(t,t^2)_t.$$
$\kappa = 0$ is exactly the POLARIZATION of Theorem K's step (6)
($(\Psi_2t)_t = pB + qC$), and is certified in $J$ at arbitrary-$k'$
strength: target `Tscalar`, `bidualgen.log`, DegreeLimit 4, $(c_1,c_4)$-
pinned normal form (soundness of the pin as in §14.9); $1 \notin J$
checked. $\square$

(The direct module-membership row `Bsys` for $t^4$ — see 16.3 — is
belt-and-braces here and was still grinding at write-up; the theorem does
not depend on it.)

### 16.3 The machine layer: `bidualgen.m2` / `bidualxy.m2` (session 14)

New encoding ideas, reusable for every non-principal base:
1. **Bidual digits**: structure constants carry three layers $d \in \{u,
   v, uv\}$; the axiom ideal $J$ is generated by the $u$-, $v$-, $uv$-
   digits of associativity + $\Delta$-multiplicativity + coassociativity
   over the pinned digit-0 model (digit-0 parts and $\varphi_0$ gated to
   vanish identically — `GATE ... OK` for all five models, $1 \notin J$
   printed every round).
2. **Solvability as MODULE membership.** (B1)+(B2) at $g$ is the linear
   system $Mw = b_g$, $M = \begin{pmatrix} P & Q & 0\\ Q & 0 & P
   \end{pmatrix}$ (6×9 over the structure-constant ring), $b_g = (TPg;\,
   TQg + QTg)$. Membership $b_g \in \operatorname{im}M + J\cdot A^6$ —
   GB-checkable with DegreeLimit, partial reduction to 0 = complete
   certificate — yields POLYNOMIAL witnesses $w$, i.e. solvability at
   every $k'$-point of $V(J)$ uniformly. This encoding needs no
   structured lemmas at all; the structured targets remain valuable as
   the hand-proof skeleton and for transfer to deeper bases.
3. Per-model target batteries: pairwise-nilpotence rows (all basis
   vectors), first-order shapes per direction, and the note's structured
   identities ((R1)/rho/pol22 + explicit division residuals for the
   rank-one models; (I0) + BOTH (I2) memberships — $q$-side and the
   $P/Q$-symmetric $p$-side, each against $J + (p_x,p_y,q_x^2,q_xq_y,
   q_y^2)$ resp. its mirror — for the image-line models; `Tscalar` for
   $t^4$).

**VERDICTS (2026-07-09, `bidualgen.log` + `bidualxy.log`, `DONE
bidualxy` present; all read in-session).**
* $t^4$: all 51 ideal targets in $J$ by DegreeLimit 4 (44 at deg 2,
  `Tscalar` last). Module row still open at write-up (not needed).
* `a2a2`: all 52 ideal targets at deg 2; all 4 I2 targets + both module
  rows certified at deg 3–4. FULLY certified.
* `W2F`: all 63 ideal targets (shapes, R1, rho, pol22, B1res/B2res) at
  deg 2; both module rows by deg 4. FULLY certified.
* `mu2mu2`: as `a2a2`. FULLY certified.
* `mu2a2`: as `W2F` (deg 3). FULLY certified.

### 16.4 THEOREM O (banked, session 14): the bidual step at arbitrary $k'$

**Theorem O.** Let $k'$ be any $\mathbb F_2$-algebra, $R =
k'[u,v]/(u^2,v^2)$, and $A$ a free rank-4 bialgebra over $R$ whose fiber
is a killed-by-2 local-local Hopf algebra of either shape (for the $xy$
shape: defined over a perfect subfield, as in Theorems I/L/M).
Then **S′($A/R$) holds**, with witnesses polynomial in the structure
constants.
*Proof.* $t^4$: Theorem 16.2.3. $xy$: descent 12.4.3 to the four split
models (S′ is a submodule-membership condition, hence ff-descent-stable;
kernels commute with flat base change); per model, EITHER the direct
module rows `Bsys[1]`, `Bsys[2]` (all eight certified), OR the note's
assembly from the certified structured targets. $\square$

**Corollaries (via Thm 7.1 + Lemma 2.1 antipodes).** For every
$\mathbb F_2$-algebra $k'$:
* killed-by-4 over EVERY socle-line extension of $k'[u,v]/(u^2,v^2)$ —
  the first arbitrary-$k'$ killedness statements over embdim-2 bases of
  length 5 (monomial examples: $k'[u,v]/(u^2, uv^2, v^3)$,
  $k'[u,v]/(uv, u^3, v^3)$; plus all non-monomial socle-line extensions);
* Theorem G′'s BiDual rows (exact $\mathbb F_2$, s2check_np) are upgraded
  to arbitrary $k'$; the FatPoint3 rows are NOT (see §16.5);
* together with Theorem N (square-zero, any embdim) this completes the
  first TWO rungs of the non-principal induction of §15.9(2).

### 16.5 The bigraded division systems for the remaining $\mathfrak m^3 = 0$ embdim-2 bases (session-14 derivation)

The §15.5 digit-matching generalizes mechanically. Two new bases:

**(a) FatPoint3 $R = k'[u,v]/(u,v)^3$** (the np3 gap ring): $\varphi =
uP + vQ + u^2A + uvT + v^2B$. Writing $\varphi(g) = uk_1 + vk_2$ with
$k_1 = Pg + um_1 + vm_2$, $k_2 = Qg + un_1 + vn_2$ ($\mathfrak m^2$-
components of $k_i$ are irrelevant: they die in $uk_i$ and are
automatically in $\ker\varphi$), digit-matching FORCES $m_1 = Ag$,
$n_2 = Bg$, $m_2 + n_1 = Tg$, leaving ONE free vector $m_2 \in I_H$, and
$k_1, k_2 \in \ker\varphi$ becomes: pairwise nilpotence (4 rows) PLUS
* two PURE identities (no unknowns): $\{A,P\}g = 0$, $\{B,Q\}g = 0$
  (bigraded-anticommutator analogues of the $s = 3$ identity — the
  weight-$(3,0)$/$(0,3)$ pieces);
* one 12×3 module system: $Pm_2 = TPg + QAg$, $\ Qm_2 = BPg$,
  $\ Pm_2 = AQg + PTg$, $\ Qm_2 = TQg + QTg + PBg$.
S′ at $g$ $\iff$ pure identities hold and the module system is solvable.
Machine job: `fp3gen.m2` (session 14). Success settles the
FatPoint3/$xy$ S′ gap (np3's exact-$\mathbb F_2$ `unknown`) at FULL
arbitrary-$k'$ strength, subsuming np2/np3.
**UPDATE (later session 14): np3 itself closed the exact-$\mathbb F_2$
level first** — `[S2.1 FAIL_1] unsat`, `[S2.2 FAIL_2] unsat`,
`DONE s2check_np3` (Theorem G′ complete; REPORT §1). `fp3gen`'s
FatPoint3 runs now carry only the arbitrary-$k'$ upgrade.
**PARTIAL (session 15 harvest), FP3/$t^4$ model:** DegreeLimit 4
certified **38/42 ideal targets** (partial-GB reductions are complete
certificates), including the weight-(3,0)/(0,3) pure rows
$\{A,P\}t = \{B,Q\}t = 0$ (components [1,1], closed at deg 4 after
surviving deg 3). Still open: the [1,2], [1,3] components of the pure
rows (the restricted Theorem-K $D_3$ components — deg-5 tier, as
predicted) and the 12×3 module row `Msys` (deg-4 module GB grinding).
Four FP3 models remain after $t^4$; len5gen still chain-queued.

**(b) RingT $R = k'[u,v]/(u^2, uv, v^3)$**:
$\varphi = uP + vQ + v^2V$. Here $uv = 0$ makes $uk_1 = uPg$ exactly;
digit-matching forces $n_2 = Vg$ and leaves $m_2$ (the $v$-slot of $k_1$)
free. S′ at $g$ $\iff$ pairwise nilpotence + the pure identity
$\{Q,V\}g = 0$ + solvability of the single 3×3 system $Qm_2 = VPg$.
Also in `fp3gen.m2`. (Its $u \leftrightarrow v$ mirror is isomorphic as a
ring, so one run covers both.)
**VERDICT (in-session, `fp3gen.log`): RingT is DONE — all five models
(`t4`, `a2a2`, `W2F`, `mu2mu2`, `mu2a2`) print `ALL fp3gen targets
certified` (gates OK, $1 \notin J$, nilpotence + $\{Q,V\}$ rows in $J$,
module row certified). So S′ holds over $k'[u,v]/(u^2,uv,v^3)$ for every
$\mathbb F_2$-algebra $k'$, both fibers (perfect-subfield proviso for
$xy$) — the mixed weight-$(1,2)$ solvability $Qm_2 = VPg$ is a theorem.

**CORRECTION to the "last base" bookkeeping (caught in-session).** The
monomial $\mathfrak m^3 = 0$ embdim-2 bases are indexed by the SUBSET of
$\{u^2, uv, v^2\}$ surviving in the socle: $\emptyset$ = FatPoint2
(Thm N), $\{uv\}$ = BiDual (Thm O), $\{v^2\}$ ≅ $\{u^2\}$ = RingT,
$\{u^2,uv,v^2\}$ = FatPoint3, **plus three LENGTH-5 bases**:
$\{u^2, uv\}$ ≅ $\{uv, v^2\}$ = $R_Y := k'[u,v]/((u,v)^3 + (v^2))$ and
$\{u^2, v^2\}$ = $R_X := k'[u,v]/(uv, u^3, v^3)$. Their division systems
(same digit-matching, derived session 14):
* $R_X$ ($\varphi = uP + vQ + u^2U + v^2V$; $uv = 0$ decouples the two
  divisors): $m_1 = Ug$, $n_2 = Vg$ forced; conditions = nilpotence +
  pure $\{U,P\}g = \{V,Q\}g = 0$ (each is the $D_3$ anticommutator of a
  CURVILINEAR $k'[u]/u^3$ restriction — Theorem-K/L-type, banked) + two
  independent RingT-type 3×3 systems $Qm_2 = VPg$, $Pn_1 = UQg$.
* $R_Y$ ($\varphi = uP + vQ + u^2U + uvT$; $v^2 = 0$): $m_1 = Ug$ forced,
  $m_2 + n_1 = Tg$, $n_2$ free; conditions = nilpotence + pure
  $\{U,P\}g = 0$ + the 9×6 coupled system $Pm_2 = TPg + QUg$,
  $\ Pm_2 = UQg + PTg$, $\ Qm_2 + Pn_2 = TQg + QTg$.
Machine job: `len5gen.m2` (chain-queued after `fp3gen`). Landing all
three completes **S′ over EVERY monomial $\mathfrak m^3 = 0$ embdim-2
equal-char base at arbitrary $k'$** (non-monomial bases: future; they
need a presentation-independent formulation).

### 16.6 State of the frontier after Theorem O

1. Equal-char curvilinear uniform-in-depth: unchanged (Conjecture $\Phi$,
   §15.8; $s = 5$ jobs still grinding).
2. Equal-char non-principal: square-zero (N) + BiDual (O) banked at
   arbitrary $k'$; FatPoint3 + $(u^2,uv,v^3)$ reduced to explicit
   bigraded systems (16.5), machine job launched. After those: length-5
   embdim-2 bases by the same digit-matching, and embdim ≥ 3 (the first
   non-square-zero embdim-3 base $k'[u,v,w]/(u^2,v^2,w^2)$-type —
   trigraded analogue of 15.5).
3. Mixed char: unchanged.

### 16.7 Audit of the SIXTH external note (session 15; note arrived AFTER its dependency was discharged)

The missing sixth note `order4_sixth_push_bidual_t4.md` arrived on
2026-07-09 inside `order4_comprehensive_handoff_bundle.zip` (extracted to
`scripts/comprehensive_bundle/`; the bundle also contains the author's
own comprehensive record `order4_comprehensive_handoff_note.md` covering
pushes 1–7). Audit verdict: **CORRECT throughout, and — remarkably —
its bidual-$t^4$ closure is the SAME proof as §16.2, found
independently.** Term-by-term dictionary (their letters → ours):
$(p,q,r,s) = (\mu_P(t,t)_t,\ \mu_P(t,t^2)_t,\ \mu_Q(t,t)_t,\
\mu_Q(t,t^2)_t)$; their boxed $T(t^2), T(t^3)$ identities = the two
displays in the proof of Theorem 16.2.3; their (★) $(Tt)_t = pB_Q + qC_Q
+ rB_P + sC_P$ = our $\kappa = 0$ (`Tscalar`, certified in $J$ at
arbitrary-$k'$ strength, `bidualgen.log`); their divisions $(a, r_0, s_0)
= (A_Pt, A_Qt, A'_Pt)$ = our $(A_st, R_st, \alpha_st)$ exactly. Their §2
correctly cautions that (★) is NOT induced by a base map from BiDual to
$k'[\epsilon]/\epsilon^3$ — it is the literal polarization of the
Theorem-K step-6 extraction; our machine certificate discharges the
coefficient-level rigor gap they flag in their own §10.1(6).

**Machine layer rerun locally (golden rule 4).**
`bidual_t4_cross_gates.py`: all 22 negation rows `unsat` reproduced
(`scripts/bidual_t4_cross_gates_rerun.log`).
`s6_suspension_model_d6.py`: reproduced `susp 2 sat`, `susp 3 sat` with
the explicit countermodel (shift matrix $e_{12} \ne 0$, full $D_6 = 0$;
`scripts/s6_suspension_model_d6_rerun.log`).

**New content actually banked from the sixth note.**
1. **The suspension countermodel** (their §6) — an INDEPENDENT
   confirmation of s6probe's route decision (15.8.5): the shifted sums
   $\Sigma^{\uparrow}$ are `sat` even with $D_2 = \dots = D_5 = 0$
   pinned, while $D_6 = 0$ holds in the same model. Any uniform-depth
   lemma must prove EDGE–TAIL CANCELLATION, not separate suspension
   vanishing. Their explicit 3×3 model matrices (rerun log) are the
   cleanest witness we have.
2. Their §4 sketch (same divisions solve every equal-char
   $\mathfrak m^3 = 0$ base, $t^4$ branch) anticipates the §16.5
   digit-matching program; the caveat they flag (descent from a free
   two-step presentation to arbitrary quotients) is exactly our
   presentation-independence caveat in 16.5. No new gap.
3. Their §7 ($xy$ bidual pointers) is superseded by the seventh note +
   Theorem O.

**Comprehensive-note ledger corrections (their
`order4_comprehensive_handoff_note.md` §10–§13, written before our
sessions 12–14 landed).** For the next reader: (i) its "live frontier"
item 1 (bidual $xy$ image-line (I0)+(I2)) is CLOSED — Theorem O via
`bidualxy.m2`, which certified (I0), BOTH (I2) memberships, and the
direct module rows in all four split models; (ii) its §10.2 caution that
`s4t4gen` lacked a final banner is STALE — Theorem M($t^4$) banked
session 13 (§14.9); (iii) its §10.1(6)(7) "modulo polarized identities"
provisos are discharged by the `bidualgen`/`bidualxy` certificates.
Its remaining live item — uniform curvilinear edge–tail cancellation —
is our Conjecture $\Phi$ frontier, unchanged.

## 17. Audit of the 2026-07-10 handoff (block rigidity) — THEOREM BR, and the extension THEOREM BR′ (session 20)

### 17.1 Provenance

The handoff is `grothendieck_rank4_agent_handoff_20260710.zip` (top level
of the project folder, 2026-07-10 14:50). Its own claim ledger
(`NEW_RESULTS/CLAIM_LEDGER.md`) is honest: claims AM2–AM4 (below) are
banked, claim **G4 ("the full rank-four conjecture follows") is marked
NOT established**, and a correction paragraph retracts an earlier
overstatement. CAUTION: the top-level file `rank4_grothendieck_push.md`
in the project folder is byte-identical to
`PROVENANCE/earlier_rank4_grothendieck_push_uncorrected.md` — i.e. it is
the UNCORRECTED version, whose Scope paragraph and §6 assert that the
"only unresolved rank-four branch" was mixed-characteristic
$\alpha_2\times\mu_2$, so that the full theorem would follow. No
upstream document supports that case-exhaustion (verified against
`STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md` §8 item 5, which says the
opposite); the corrected `README_FIRST.md`/ledger inside the zip retract
it. **Cite only the corrected statements.**

### 17.2 THEOREM BR (audited CORRECT; = handoff AM2 + AM3)

**Theorem BR.** Let $(R,\mathfrak m,k)$ be Artin local with
$\operatorname{char} k = 2$ and let $G/R$ be finite locally free of
degree 4 with $G_k \simeq \alpha_2\times\mu_2$. Then $G$ is commutative
— hence (Deligne) $[4]_G = e$. Independent of length, ramification,
and any deformation ansatz.

**Proof mechanism** (all steps verified by hand this session):
$H = A^\vee$ with multiplication $= \Delta_A^\vee$ is an associative
(coassoc of $\Delta$) unital ($\varepsilon^\vee$) free rank-4
$R$-algebra; duality commutes with base change ($A$ finite projective);
$H_k = O((\alpha_2\times\mu_2)^D) = O(\alpha_2\times\underline{\mathbf
Z/2}) = k[u]/u^2 \times k[u]/u^2$ — two central blocks of dim 2. The
fiber block idempotent lifts along the nilpotent ideal $\mathfrak m H$;
the four Peirce pieces $eHe, eHf, fHe, fHf$ are images of commuting
idempotent $R$-linear endomorphisms, hence projective direct summands;
$(eHf)\otimes k = \bar e H_k \bar f = 0$, so Nakayama kills $eHf$ and
$fHe$; thus $e$ is central and $H = eHe \times fHf$ with both factors
free of rank 2; a unital rank-2 algebra over a local ring is
commutative (extend the unimodular unit to a basis $(1,x)$). So $H$ is
commutative $\Rightarrow$ $\Delta_A$ cocommutative ($A \otimes A
\hookrightarrow (H\otimes H)^\vee$ for $A$ finite projective)
$\Rightarrow$ $G$ commutative $\Rightarrow$ killed by 4 by Deligne
(the handoff includes a self-contained Ferrand-norm/norm-cycle proof;
this is the classical argument). $\square$

**Consistency + machine gate.** BR predicts that every faithfully
encoded noncocommutativity query on a pinned $\alpha_2\times\mu_2$ fiber
must return unsat over every Artin local base. Verified: (i) the
session-18 GPT docstring claim of an "N=5 SAT noncocommutative
$\alpha_2\times\mu_2$ deformation over $\mathbf Z_2[\pi]/(\pi^2-2,
\pi^5)$" was ALREADY RETRACTED upstream as a Z3 symbol-name pinning bug
(`EXPLICIT_RANK4_RAMIFIED_CONSTRUCTION_PASS_2026-07-09.md` §7: the ad
hoc pin constrained nonexistent symbols `c111__1_a` vs `c111_1_a`, so
the fiber was never pinned; corrected verdict UNSAT); the genuine
noncommutative lifts at those depths live on the $\alpha_2^2$ row —
which BR does NOT cover, consistently. (ii) Fresh rerun this session:
`scripts/bilinear_full_noncocomm_crosscheck_20260710.log` —
`explicit_bilinear_ramified_sat.py --full` at $N = 4,5,6$:
noncocommutative unsat, $[4]\ne e$ unsat, all axiom gates sat. (iii)
The stale docstring of `scripts/extract_sparse_alpha_mu_model.py` has
been corrected in place (session 20).

### 17.3 THEOREM BR′ (extension, session 20): every commutative fiber with nontrivial multiplicative part is rigidly commutative

**Lemma 17.3.1 (multi-block Peirce rigidity).** $(R,\mathfrak m)$ Artin
local, $B$ associative unital finite free $R$-algebra, $B_k = \prod_i
B_i$ a product of $\ge 2$ blocks. Then the complete orthogonal system of
central fiber idempotents lifts to a complete orthogonal system of
CENTRAL idempotents of $B$, and $B \cong \prod_i \tilde B_i$ with
$\tilde B_i$ free with $(\tilde B_i)_k = B_i$. (Lift idempotents
successively along the nilpotent ideal; kill every off-diagonal Peirce
summand by projectivity + Nakayama exactly as in BR. Ranks are
arbitrary.)

**Lemma 17.3.2 (rank $\le 2$ blocks).** A unital algebra free of rank
$\le 2$ over a commutative local ring is commutative. (Basis $(1,x)$.)

**Lemma 17.3.3 (unramified/Hensel blocks).** $B$ associative unital
free of rank $d$ over Artin local $(R,\mathfrak m,k)$ with $B_k = \ell$
a SEPARABLE field extension of $k$ of degree $d$. Then $B \cong
R[X]/(f)$ for a monic lift $f$ of the minimal polynomial of a primitive
element — in particular $B$ is commutative. *Proof.* Pick $\bar\theta$
primitive with separable minimal polynomial $\bar f$, lift to monic $f
\in R[X]$ and $\theta_0 \in B$. Newton-iterate $\theta_{n+1} = \theta_n
- f(\theta_n)f'(\theta_n)^{-1}$: $f'(\theta_0)$ is invertible in $B$
(unit modulo the nilpotent radical), its inverse commutes with
everything $f'(\theta_0)$ commutes with (conjugate $b^{-1}xb b^{-1}$),
so every iterate stays in a COMMUTATIVE subring and converges since
$\mathfrak m$ is nilpotent. Get $f(\theta) = 0$, giving $\psi: R[X]/(f)
\to B$ with $\psi \otimes k: k[X]/(\bar f) \xrightarrow{\ \sim\ } \ell$;
both sides free of rank $d$ and $\psi \otimes k$ iso $\Rightarrow$
$\psi$ surjective (Nakayama) $\Rightarrow$ iso. $\square$

**Theorem BR′.** $(R,\mathfrak m,k)$ Artin local, $\operatorname{char} k
= 2$, $G/R$ finite locally free of degree 4 whose special fiber $G_k$ is
COMMUTATIVE with NONTRIVIAL MULTIPLICATIVE PART. Then $G$ is commutative
and $[4]_G = e$.

*Proof.* $H_k = O(G_k^D)$; let $C$ be the identity component of
$G_k^D$. Multiplicative part of $G_k$ nontrivial $\iff$ étale quotient
$E = \pi_0(G_k^D)$ nontrivial $\iff$ $|C| \le 2$. If $|C| = 2$: $E$ is
an étale group scheme of order 2, hence CONSTANT $\mathbf Z/2$
($\operatorname{Aut}(\mathbf Z/2) = 1$, so no forms), so $G_k^D$ has two
components with residue field $k$, i.e. $H_k$ = two blocks of dim 2:
Lemmas 17.3.1 + 17.3.2. If $|C| = 1$: $G_k^D$ étale, $H_k$ = product of
separable field extensions of total degree 4: Lemmas 17.3.1 + 17.3.3
(+ 17.3.2). Either way $H$ is commutative $\Rightarrow$ $G$ commutative
$\Rightarrow$ Deligne. $\square$

**Remark 17.3.4 (fiber taxonomy closed by BR′).** Over the (finite,
hence perfect) residue fields relevant after Thm 3.1, the commutative
connected order-4 fibers with multiplicative part are: $\mu_2\times
\alpha_2$ (= BR), $\mu_2\times\mu_2$ AND ALL ITS RATIONAL FORMS (the
`mu2mu2_unipotent`, `mu2mu2_irreducible` twist classes of the six-orbit
classifications over $\mathbf F_2/\mathbf F_4/\mathbf F_8$ — their duals
are étale forms of $(\mathbf Z/2)^2$, blocks = separable field
extensions, e.g. $k \times k \times$ quadratic or $k \times$ cubic), and
$\mu_4$ and its forms (dual = forms of $\mathbf Z/4$). In particular
BR′ REPLACES the SGA3 multiplicative-type-rigidity citation in Cor C
step 3 ($\mu_4$ fiber) by an elementary self-contained argument.

**Remark 17.3.5 (what BR′ does NOT cover — and cannot).** (i) The
noncommutative fiber $\alpha_2\rtimes\mu_2$ (Schoof's case, not killed
by 2): its dual fiber algebra is INDECOMPOSABLE — explicitly, with
$O = k[x,s]/(x^2, s^2-1)$, $\Delta x = x\otimes 1 + s\otimes x$, dual
basis $(e_1, e_x, e_s, e_{xs})$: $1_H = e_1 + e_s$ is a decomposition
into NON-central orthogonal idempotents ($e_s e_x = e_x \ne 0 = e_x
e_s$), and no nontrivial central idempotent exists. So the Peirce
mechanism is silent and the Schoof-2001 dependency [FLAG G.2] stands.
(ii) LOCAL-LOCAL fibers ($H_k$ local, no blocks): $\alpha_2^2$, $W_2[F]$
(xy) and the four $t^4$ strata $(c_1,c_4)$. These genuinely admit
noncommutative deformations (e.g. the height-one group over $\mathbf
F_2[a,b]/(a^2,b^2)$ of `RANK4_NO_NORMAL_RANK2_FILTRATION_2026-07-10.md`,
and the $\alpha_2^2$ hand family over $\mathbf Z_2[\pi]/(\pi^2-2,\pi^N)$
of `EXPLICIT_..._PASS` §3), so no commutativity-forcing argument can
exist for them; they remain the computational/structural frontier.

**Remark 17.3.6 (arbitrary-$k'$ / non-local version for pinned split
$\mu$-models).** Commutativity of $H$ can be checked after localizing
the base at every prime, and Lemma 17.3.1's inputs (idempotent lifting
along the nilpotent ideal generated by the deformation parameters;
Nakayama for f.g. modules over a local ring) survive: for any base ring
of the form used by the M2 pipeline ($k'[\varepsilon]/\varepsilon^N$,
monomial bases, etc., $k'$ an ARBITRARY $\mathbf F_2$-algebra) with
$\Delta_0$ PINNED to a split $\mu_2\times\mu_2$ or $\mu_2\times\alpha_2$
normal form, every bialgebra solution is cocommutative identically.
Combined with Deligne over an arbitrary base and Prop 12.6.1, this gives
ALL layer identities $D_s = 0$, every $s$, every $k'$, for the two
$\mu$-split-models — the infinite tower, by pure theory.

### 17.4 Consequences for the frontier

1. **Master fiber reduction (new standing statement).** A rank-4
   counterexample must live over an Artin local ring with finite residue
   field of char 2, be noncommutative, and have special fiber that is
   either LOCAL-LOCAL (a form of $\alpha_2^2$, $W_2[F]$, or a $t^4$
   stratum) or the Schoof fiber $\alpha_2\rtimes\mu_2$ [FLAG G.2].
   Every $\mu$-containing commutative fiber is closed at every length,
   every ramification, both characteristics, by BR/BR′.
2. **Retired computational rows.** (a) The OOM'd principal length-6 row
   `e1_0000/xy/mu2mu2_unipotent/i2` and EVERY $\mu$-strata row of the
   length-7 program: no longer needed (their fibers force commutativity;
   an S′-failure below a counterexample has the counterexample's own
   local-local fiber). The stratified sweeps reduce from 10 residue-$\mathbf
   F_2$ strata to 6 (a2a2, W2F, four $t^4$). (b) The F₄ ramified
   66-task array: only its local-local rows retain content. (c) The
   depth-7 $\mu_2^2/\mu_2\alpha_2$ noncocommutativity `unknown`s of
   `EXPLICIT` §6: settled (unsat a priori). (d) The deep ramified
   $\alpha_2\times\mu_2$ family sweeps (`RANK4_SERIOUS` §4,
   $R_{N,L,\theta}$ through length 9): upgraded from "family exclusions"
   to instances of a theorem. (e) `s5xygen`'s still-running
   $\mu_2\times\alpha_2$ model and any future $s \ge 5$ xy work on
   $\mu$-models: redundant (Remark 17.3.6) — the xy tower reduces to
   $\alpha_2^2$ + $W_2[F]$ forever. (f) Torti's flagged-open
   mixed-characteristic $\alpha_2\times\mu_2$ locus: closed uniformly.
3. **NOT retired.** The two stretched-profile timeout rows
   (`s_f2/t4_11/i1`, `q00/t4_11/i1` — $t^4$ stratum, local-local), the
   principal $(1^6)$-quotient sweep (local-local rows), `s5t4gen`,
   FatPoint3 `Msys`, `len5gen`, Conjecture $\Phi$ / uniform depth, the
   tight-chain exclusion at arbitrary depth, mixed-char at
   arbitrary-coefficient strength, W(F₈) ramified, residue fields
   $\mathbf F_{2^r}$, $r \ge 2$ beyond banked rows.
4. **Convergence note (RT route).** The handoff's provisional
   universal-power-map program
   (`NEW_RESULTS/UNIVERSAL_POWER_MAP_REDUCTION_PROVISIONAL.md`) derives,
   conditional on three Hopf–Frobenius identities (HF1)–(HF3), the
   regular-translation identity $(T^2-I)(T^2-\delta I) = 0$, whence
   $D = [4]^\# - e$ is a square-zero 4-torsion augmentation derivation
   and $[16] = e$ UNIFORMLY at rank 4; and, on the locus where
   $(\delta-1)\wedge(\chi-4)$ is unimodular, $[4] = e$ — using
   additionally $\operatorname{Tr}([2]^\#) = 1$. That trace identity is
   ALREADY PROVED AND AUDITED upstream
   (`RELATIVE_TOP_DEFECT_TRACE_RANK_PASS_2026-07-10.md` Prop 3.1, audit
   GREEN) — the two lines converged without noticing each other. So the
   RT route's remaining obligations are exactly (HF1)–(HF3) (Larson–
   Sweedler/Pareigis-style integral theory, ring-level) plus a
   convention audit of its (4.1)–(4.4). Note the open-locus argument is
   VACUOUS on the local-local locus ($\delta \equiv 1$, $\chi \in
   \mathfrak m + I$ there), consistent with local-local being the hard
   locus in every approach. The derivation chain of the note was checked
   this session and is internally coherent; its smoke test passes
   (`FORMAL_IDENTITY_SMOKE_TEST.py`, rerun in-session).
