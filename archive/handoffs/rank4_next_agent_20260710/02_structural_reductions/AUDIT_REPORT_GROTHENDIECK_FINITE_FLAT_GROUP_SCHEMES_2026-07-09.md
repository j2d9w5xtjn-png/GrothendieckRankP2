# Grothendieck's killed-by-order question for finite locally free group schemes

## An audited report on the order-4 program and the higher-rank counterexample search

**Date:** 9 July 2026  
**Scope:** all mathematical notes, handoff archives, scripts, and logs in this directory, together with targeted reruns and a check against the current literature.  
**Verdict:** no complete proof and no genuine counterexample were found.

---

## 1. Executive conclusion

Grothendieck asked whether every finite locally free group scheme of order $n$ is killed by $n$. The accumulated work in this directory does not settle that question. It gives a substantial and coherent attack on order $4$, strong negative evidence at ranks $8$ and $16$, and several genuine theorems, but important infinite directions remain open.

For order $4$, the work successfully:

- reduces the global question to Artin local rings with finite residue field;
- isolates the difficult local residue-characteristic-$2$ branch;
- proves the conjecture in broad low-depth equal-characteristic regimes;
- establishes a strong sufficient invariant, denoted $S'$;
- proves $S'$ over all equal-characteristic square-zero bases and selected non-principal bases;
- proves the curvilinear divided-$[4]$ identities through layer $s=4$ at arbitrary-coefficient strength;
- verifies many deeper exact rings by SAT/SMT and Gröbner calculations.

It does **not** prove:

- a uniform all-depth curvilinear theorem;
- the general non-principal Artin case;
- a uniform mixed-characteristic theorem.

No full-axiom counterexample occurs in the files. The best apparent counterexample, a rank-16 quartic seed in the c44 family, is false. However, the directory's later explanation of that false positive is also false. The true cause is a quotient-linear-algebra bug in the scanner, not a failure of $\Psi_1$ to preserve $I^2$.

This audit found four consequential issues in the existing summaries:

1. First-order multiplicativity gives $\Psi_1(I^2)=0$, so the claimed “matrix-power trap” rationale is wrong.
2. The c44 scanner admitted impossible cotangent matrices because its row-reduction output was not a canonical quotient representative.
3. Cartier duality does not transfer the full noncommutative deformation problem between dual special fibers.
4. The divided operator $\Phi=[2]^\#/\epsilon$ is defined only modulo the top annihilator, so literal exact vanishing of $\Phi^2$ is not invariant.

One previously unsupported rank-8 cell was closed during the audit: a direct full-deformation run for the dual zigzag ZIG gave $TD_5\ne0$ **UNSAT** over exact $\mathbb F_2$. This repairs that cell directly, without using the invalid Cartier-duality transfer. It is still only an exact-$\mathbb F_2$, finite-layer result.

The evidence favors the conjecture, but the gaps are real. The strongest proof target is an invariant treatment of the order-4 socle obstruction, ideally combined with a universal rank-4 Hopf-structure ideal-membership computation. The most credible counterexample locus remains a deep mixed-characteristic deformation of the order-4 special fiber $\alpha_2\times\mu_2$.

---

## 2. Statement and Hopf-algebra formulation

Let $G\to S$ be a finite locally free group scheme of constant rank $n$. The pointwise power map is

\[
[n]:G\longrightarrow G,\qquad g\longmapsto g^n.
\]

For noncommutative $G$, this is generally not a group homomorphism, but it is a morphism of schemes. If

\[
G=\operatorname{Spec}A
\]

and $\varepsilon:A\to R$ is the counit, with augmentation ideal

\[
I=\ker\varepsilon,
\]

then the coordinate map is

\[
[n]^\#=\mu^{(n)}\circ\Delta^{(n)}:A\longrightarrow A.
\]

The assertion that $G$ is killed by $n$ is

\[
[n]^\#=\eta\varepsilon,
\]

equivalently

\[
[n]^\#(I)=0.
\]

For order $4$, put

\[
\varphi=[2]^\#=\mu\Delta.
\]

Since $(g^2)^2=g^4$ even in a noncommutative group,

\[
[4]^\#=\varphi\circ\varphi.
\]

The basic setup is recorded in [THEORY_order4.md](THEORY_order4.md), lines 45–60.

One convention is crucial: $A=\mathcal O(G)$ is always a **commutative algebra**. Noncommutativity of the group scheme is encoded by failure of cocommutativity of $\Delta$.

---

## 3. Current literature baseline

The following cases are known.

- Over a field, finite group schemes are killed by their order.
- Hence the result holds over reduced bases.
- Deligne proved it for commutative finite locally free group schemes over arbitrary bases.
- Schoof proved that, over a local Artin ring $(R,\mathfrak m)$ with residue characteristic $p$, every finite flat group scheme is killed by its rank when

\[
\mathfrak m^p=p\mathfrak m=0.
\]

In particular, square-zero maximal ideals are safe.

- Torti proves the conjecture for deformations of a specified family of noncommutative special fibers, but presents this as a new special case of Grothendieck's still-open question.

Primary references:

- R. Schoof, [Finite Flat Group Schemes over Local Artin Rings](https://www.cambridge.org/core/journals/compositio-mathematica/article/finite-flat-group-schemes-over-local-artin-rings/EF8E7E798A1AB12E4BC8B831DE47FDA9), *Compositio Mathematica* 128 (2001), 1–15.
- R. Schoof, [Is a finite locally free group scheme killed by its order?](https://www.mat.uniroma2.it/~schoof/schoof_oortAAG.pdf), survey.
- E. Torti, [Lagrange's theorem for a family of finite flat group schemes over local Artin rings](https://arxiv.org/abs/2411.12129), arXiv:2411.12129.

Torti's paper supports clearing the standing local flag in [THEORY_order4.md](THEORY_order4.md) concerning the Schoof theorem for deformations of the noncommutative $G_1$ fiber. It does not close the mixed-characteristic $\alpha_p\times\mu_{p^m}$ branch.

---

## 4. Evidence standards

The directory combines several logically different kinds of evidence. They must be kept separate.

| Evidence type | Logical strength |
|---|---|
| Complete hand proof | A theorem under its stated hypotheses |
| Polynomial ideal-membership certificate | A universal identity over the stated coefficient ring and presentation |
| Exact finite-ring UNSAT | A theorem for that exact encoded ring |
| Full-axiom layer UNSAT | Excludes that fiber, coefficient field, and deformation layer |
| SAT non-vacuity query | Shows only that the deformation space is nonempty |
| SAT after dropping an axiom | Produces a diagnostic pseudo-bialgebra, not a group scheme |
| Timeout, unknown, killed process, or missing DONE | No mathematical verdict |

This distinction matters here. Some report headlines are stronger than their logs, while several low-layer Gröbner reductions really are theorem-strength arbitrary-coefficient identities.

---

## 5. Sound general reductions

### 5.1 Arbitrary bases reduce to Artin local bases with finite residue field

[THEORY_order4.md](THEORY_order4.md), Theorem 3.1, lines 150–190, proves a useful reduction for every fixed $n$.

Work locally where $A$ is free. The finitely many structure constants for multiplication, comultiplication, counit, unit, and antipode descend to a finitely generated $\mathbb Z$-subalgebra. If a coefficient of

\[
[n]^\#-\eta\varepsilon
\]

were nonzero, one could choose a maximal ideal that detects it. The residue field is finite, and Krull intersection preserves the nonzero coefficient in some Artin local quotient.

Therefore, for fixed $n$, it suffices to treat Artin local bases with finite residue field.

### 5.2 Prime-to-$n$ residue characteristic is harmless

[THEORY_order4.md](THEORY_order4.md), Proposition 3.2, lines 177–191, shows that if the residue characteristic does not divide $n$, the group scheme is étale. After a faithfully flat strict henselian extension it becomes constant, so ordinary Lagrange theory applies.

For order $4$, only residue characteristic $2$ remains.

### 5.3 The hard order-4 special fiber

The connected–étale sequence and the extension argument remove mixed connected–étale cases. The Schoof branch handles the relevant local fibers not killed by $2$. In the remaining branch the special fiber is local and killed by $2$.

Because the residue field can be taken finite, hence perfect, its coordinate algebra has one of the two shapes

\[
k[t]/(t^4)
\]

or

\[
k[x,y]/(x^2,y^2).
\]

Nearly all order-4 calculations in the directory address these two shapes.

### 5.4 Automatic antipodes

[THEORY_order4.md](THEORY_order4.md), Lemma 2.1, lines 118–146, proves:

1. on a killed-by-$2$ special fiber, $S=\mathrm{id}$ is an antipode;
2. convolution units lift through nilpotent ideals, so the antipode lifts over an Artin local thickening.

Thus the bialgebra searches in the hard order-4 branch are genuinely searches over group schemes. Omitting an antipode variable there does not enlarge the class.

---

## 6. Elementary constraints on the doubling map

For $g\in I$, counitality gives

\[
\Delta(g)=g\otimes1+1\otimes g+w,
\qquad
w\in I\otimes I.
\]

It follows that

\[
[n]^\#(g)\equiv ng\pmod{I^2}.
\]

In equal characteristic $2$,

\[
\varphi(I)\subseteq I^2.
\]

If the special fiber is killed by $2$, base change gives

\[
\varphi(I)\subseteq\mathfrak m I.
\]

These are Lemmas 1.2 and 1.3 of [THEORY_order4.md](THEORY_order4.md), lines 63–105.

If $\mathfrak m^2=0$, then

\[
\varphi^2(I)=0.
\]

More generally, Proposition 1.4 proves in every rank: a lift of a fiber killed by $m$ over a square-zero maximal ideal is killed by $m^2$.

---

## 7. The order-4 proof architecture

### 7.1 The strengthened invariant $S'$

For a free rank-4 bialgebra $A/R$ with killed-by-$2$ special fiber, define

\[
S'(A/R):
\qquad
\varphi(I)\subseteq
\mathfrak m(\ker\varphi\cap I).
\]

This is introduced in [THEORY_order4.md](THEORY_order4.md), lines 531–539.

The condition has two decisive properties.

First,

\[
S'(A/R)\Longrightarrow\varphi^2(I)=0,
\]

so $S'$ implies killedness by $4$.

Second, Theorem 7.1 proves a socle-lifting statement. If

\[
0\longrightarrow M\longrightarrow R'\longrightarrow R\longrightarrow0,
\qquad
\mathfrak m'M=0,
\]

and the reduction satisfies $S'$, then every lift over $R'$ is killed by $4$.

Universal $S'$ over all Artin local residue-characteristic-$2$ rings would therefore prove the order-4 conjecture after the general reductions.

But $S'$ is stronger than killedness. A failure of $S'$ would **not** by itself be a counterexample to Grothendieck's question. The abstract filtered-module example in [THEORY_order4.md](THEORY_order4.md), lines 702–713, also shows that $S'$ cannot follow from square-zero endomorphism theory alone; a proof must use the bialgebra axioms.

### 7.2 Principal-base defect

When $\mathfrak m=(t)$ and the special fiber is killed by $2$, choose $v_i\in I$ with

\[
t v_i=\varphi(e_i).
\]

The value

\[
\delta_i=\varphi(v_i)
\]

is independent of the choice of division. Proposition 7.5.1 proves

\[
S'(A/R)
\quad\Longleftrightarrow\quad
\delta_i=0
\quad\text{for every basis vector }e_i.
\]

This turns the curvilinear problem into a polynomial defect calculation.

### 7.3 Relative top defect and cotangent reduction

For the socle step

\[
k[\epsilon]/(\epsilon^{N+1})
\longrightarrow
k[\epsilon]/(\epsilon^N),
\]

assuming $S'$ below, the new top defect is a map

\[
\Omega:I_H\longrightarrow I_H.
\]

The audited relative-defect lemma proves

\[
\Omega(I_H^2)=0.
\]

Hence the entire new obstruction at every depth lives on the cotangent space:

- one value $\Omega(t)$ for $k[t]/t^4$;
- two values $\Omega(x)$ and $\Omega(y)$ for $k[x,y]/(x^2,y^2)$.

This is the most important conceptual compression in the order-4 program. See [THEORY_order4.md](THEORY_order4.md), §§15.1–15.2, especially lines 2294–2352.

---

## 8. Curvilinear layer calculus

Over $k[\epsilon]/(\epsilon^{N+1})$, write

\[
\varphi=[2]^\#
=
\epsilon\Psi_1+\epsilon^2\Psi_2+\cdots+\epsilon^N\Psi_N.
\]

The divided-$[4]$ layers are

\[
D_s=
\sum_{i+j=s}\Psi_i\Psi_j.
\]

The first three are

\[
D_2=\Psi_1^2,
\]

\[
D_3=\Psi_1\Psi_2+\Psi_2\Psi_1,
\]

and

\[
D_4=\Psi_1\Psi_3+\Psi_2^2+\Psi_3\Psi_1.
\]

The directory proves $D_2=D_3=D_4=0$ for both order-4 fiber shapes at arbitrary-coefficient strength, using a combination of hand arguments, descent, machine gates, and polynomial ideal-membership certificates.

### Correction to the divided operator

The directory defines

\[
\Phi=\varphi/\epsilon
\]

over

\[
R'=k[\epsilon]/(\epsilon^{N+1})
\]

and then asks for literal “$\Phi^2=0$ exactly.” This formulation is not invariant.

Division by $\epsilon$ determines $\Phi$ only modulo

\[
\operatorname{ann}(\epsilon)I'
=
\epsilon^N I'.
\]

Changing the division can change the top coefficient of $\Phi^2$. The choice-independent assertion corresponding to the $S'$ defect is

\[
\Phi^2\equiv0\pmod{\epsilon^N I'},
\]

equivalently

\[
\epsilon\Phi^2=0.
\]

In basis-wise language, this is exactly the choice-independent condition

\[
\varphi(v_i)=0
\]

for an $\epsilon$-division $v_i$ of $\varphi(e_i)$.

This correction does not invalidate the banked $D_s$ identities. It corrects the all-depth formulation in [THEORY_order4.md](THEORY_order4.md), §15.8.

---

## 9. What is actually proved at order 4

### 9.1 Theorem-strength results

| Regime | Result | Evidence |
|---|---|---|
| Arbitrary square-zero maximal ideal | A lift of an $m$-killed fiber is killed by $m^2$ | Hand proof |
| Equal characteristic, $\mathfrak m^3=0$, arbitrary embedding dimension | Killed-by-$4$ in the hard branch | Hand proof and polarization |
| Equal-characteristic square-zero base, arbitrary embedding dimension | Universal $S'$ | Hand proof, Theorem N |
| Curvilinear equal characteristic, $s=2$ | $\Psi_1^2=0$ | Hand proof, machine-gated |
| Curvilinear equal characteristic, $s=3$ | $D_3=0$ for both fibers | Hand proofs, machine-gated |
| Curvilinear equal characteristic, $s=4$ | $D_4=0$ for both fibers | Hand proof plus arbitrary-coefficient certificates |
| $k'[u,v]/(u^2,v^2)$, arbitrary $k'$ | Universal $S'$ in the hard branch | Hand reduction plus certificates, Theorem O |
| $k'[u,v]/(u^2,uv,v^3)$, arbitrary $k'$ | The displayed bigraded systems close | Ideal and module certificates |

The first-order theorem, layer theorems, and bidual theorem are assembled in [THEORY_order4.md](THEORY_order4.md) and summarized in [REPORT_order4.md](REPORT_order4.md).

The phrase “arbitrary $k'$” is important: these are polynomial identities in universal coefficient rings, not merely checks of $\mathbb F_2$-points.

### 9.2 Exact-ring evidence

The solver suite finds no counterexample over many named rings, including:

- $\mathbb F_2[\epsilon]/\epsilon^N$ at several depths;
- $\mathbb Z/4$, $\mathbb Z/8$, $\mathbb Z/16$, and $\mathbb Z/32$;
- selected ramified Artin rings;
- bidual and FatPoint-type non-principal rings;
- selected unramified residue-field extensions in mixed characteristic.

The detailed ledger is in [REPORT_order4.md](REPORT_order4.md), especially lines 654–789, and in the corresponding logs under **scripts/**.

These exact-ring results are genuine theorems for the encoded rings. They are not arbitrary-coefficient theorems unless a separate ideal-membership argument is supplied.

### 9.3 Deeper exact-$\mathbb F_2$ evidence

- [scripts/s5gates.log](scripts/s5gates.log) reports every tested $D_5$ component **UNSAT** for the pinned exact-$\mathbb F_2$ order-4 model.
- [scripts/s6probe.log](scripts/s6probe.log) reports all nine $D_6$ components **UNSAT** for the pinned $t^4$ model over exact $\mathbb F_2$.
- The same $s=6$ probe gives **SAT** suspension rows. These are not counterexamples. They disprove the attempted proof strategy of killing the shifted tail separately from the edge terms.

### 9.4 Unfinished arbitrary-coefficient calculations

The logs do not prove arbitrary-coefficient $s=5$.

- [scripts/s5t4gen.log](scripts/s5t4gen.log) reaches the start of DegreeLimit 5 with no certified target and no completion banner.
- [scripts/s5xygen.log](scripts/s5xygen.log) certifies all nine $D_5$ targets only for the $\alpha_2^2$ split model. The $W_2[F]$ block stops at the start of DegreeLimit 5; later split models are absent.
- [scripts/fp3gen.log](scripts/fp3gen.log) certifies all 42 scalar/ideal targets for the FatPoint3 $t^4$ model, but the essential module row remains open at the displayed DegreeLimit 5 stage.
- The ramified $W(\mathbb F_4)[\pi]$ $S'$ computation has no final verdict.

The full order-4 problem therefore remains open in three independent directions:

1. arbitrary depth, even curvilinear and equal characteristic;
2. arbitrary non-principal bases, especially embedding dimension at least $3$;
3. uniform mixed-characteristic theory.

---

## 10. Rank-8 evidence

For a rank-$2^d$ special fiber killed by $2$, write

\[
\varphi=\epsilon\Psi_1+\epsilon^2\Psi_2+\cdots.
\]

Then

\[
[2^d]^\#=\varphi^d.
\]

Its coefficient layers are noncommutative words in the $\Psi_i$. A leading counterexample would require $\Psi_1^d\ne0$; deeper layers contain mixed Massey-type words involving $\Psi_2,\Psi_3,\ldots$.

### 10.1 First-order results

[THEORY_rank8.md](THEORY_rank8.md), Theorem R8-1, lines 153–175, proves for fourteen listed rank-8 fibers, over any $\mathbb F_2$-algebra $k$,

\[
\Psi_1(I^2)=0,
\qquad
L^2=0\text{ on }I/I^2,
\qquad
\Psi_1^3=0.
\]

This excludes leading first-order counterexamples for those fibers.

### 10.2 The $TD_4$ layer

The exact-$\mathbb F_2$ full-deformation scripts establish $TD_4=0$ for fourteen listed exterior, product, and truncated-monomial fibers.

This is a finite-family result. The file does not supply a classification proving that these are every rank-8 killed-by-$2$ fiber.

### 10.3 U3/Heisenberg

For the non-killed-by-$2$ U3 fiber, the completed exact-$\mathbb F_2$ full-deformation calculations give the displayed vanishing through $D_3$. No comparable mixed-characteristic theorem is present.

### 10.4 Zigzag fibers and the duality issue

For

\[
Z1:
\quad
\mathbb F_2[t,x]/(t^4,x^2),
\qquad
\Delta x=x\otimes1+1\otimes x+t^2\otimes t^2,
\]

the local scripts give exact-$\mathbb F_2$ full-deformation **UNSAT** for both $TD_4\ne0$ and $TD_5\ne0$.

The directory then transfers these results to the Cartier-dual special fiber. That transfer is invalid for the **full noncommutative deformation problem**.

For a noncommutative group scheme, coordinate multiplication is commutative but $\Delta$ is generally noncocommutative. Linear duality therefore produces a generally noncommutative multiplication, outside the category of affine group-scheme coordinate algebras. Killedness of an individual commutative group scheme is compatible with Cartier duality; the two full deformation functors searched here are not thereby identified.

The archived direct ZIG computation independently repairs $TD_4$. During this audit, the archived **full-deformation** ZIG $TD_5$ script was rerun directly and completed:

~~~text
S0 axioms only:             sat
Psi1^3 != 0:               unsat
Psi1 != 0:                 sat
Psi2 != 0:                 sat
Psi3 != 0:                 sat
TD4 != 0 regression:       unsat
MAIN TD5 != 0:             unsat   (130.2 s)
total:                              212.9 s
~~~

This supplies an exact-$\mathbb F_2$, full-deformation result for ZIG directly. It does not validate the general duality argument and cannot be used to transfer arbitrary layers or arbitrary-coefficient statements.

### 10.5 Incomplete exterior $TD_5$ sweep

The claim that all exterior rank-8 $TD_5$ rows are **UNSAT** is not supported by [scripts/rank8_td5.log](scripts/rank8_td5.log).

The log completes only:

\[
W_3[F],\qquad
\text{mask }6,\qquad
\text{mask }3,\qquad
\text{mask }5.
\]

It stops during mask1, before the main query, and has no DONE line.

A fresh audit run reached the mask1 main query, but after 498.2 seconds it was interrupted and returned **unknown**. That is no verdict. The mask7 row is formally zero under the stated $\Psi_1=0$ result, but the remaining general rows are not closed by the current log.

---

## 11. Rank-16 audit and the false c44 seed

### 11.1 Universal first-order product-kill

Let

\[
\Phi_\epsilon=[2]^\#
=
\epsilon\Psi_1
\pmod{\epsilon^2}
\]

be a first-order deformation of a special fiber killed by $2$.

For $a,b\in I_H$, multiplicativity gives

\[
\Phi_\epsilon(a\cdot_\epsilon b)
=
\Phi_\epsilon(a)\Phi_\epsilon(b).
\]

The right side is zero modulo $\epsilon^2$. On the left, the first-order multiplication correction is killed by

\[
\Phi_0|_{I_H}=0.
\]

Therefore

\[
\boxed{\Psi_1(I_H^2)=0.}
\]

This identity is already correctly recorded in [THEORY_rank8.md](THEORY_rank8.md), lines 67–70 and 153–170.

Consequently $\Psi_1$ induces

\[
L:I/I^2\longrightarrow I/I^2,
\]

and

\[
L^r=\Psi_1^r\pmod{I^2}.
\]

Thus the later explanation that cotangent matrix powers are meaningless because $\Psi_1$ does not preserve $I^2$ is mathematically false.

### 11.2 The actual scanner bug

The positive c44 seed came from

[scripts/rank16_push_bundle/scripts/hopf_firstorder_scanner.py](scripts/rank16_push_bundle/scripts/hopf_firstorder_scanner.py).

Its **RowBasis.reduce** routine returns as soon as it encounters the first nonpivot coordinate. This suffices for a zero or rowspace-membership test, but it does not produce a canonical linear representative of the quotient. The scanner then treats these noncanonical outputs as a linear family and computes relations among them.

For c44_ca1_cb1, the buggy computation reports a two-dimensional cotangent image generated by bitmasks $5$ and $10$, which appear idempotent. Directly solving the scanner's own linear equations with the entry values pinned gives the actual image

\[
\left\{
0,
15
\right\},
\qquad
15\longleftrightarrow
\begin{pmatrix}
1&1\\
1&1
\end{pmatrix}.
\]

The true relation masks include

\[
3,5,6,9,10,12,15,
\]

forcing all four entries to agree. In characteristic $2$,

\[
\begin{pmatrix}
1&1\\
1&1
\end{pmatrix}^2=0.
\]

After correcting quotient reduction in memory and rerunning all 64 c44 fibers, every cotangent product span is already zero in degree $2$. Thus

\[
L^2=0,
\qquad
\Psi_1^2(I)\subseteq I^2,
\qquad
\Psi_1^3=0,
\qquad
\Psi_1^4=0.
\]

The apparent c44 quartic seed is therefore decisively false. The exact-$\mathbb F_2$ honest-composition Z3 sweep independently agrees.

The same defective reduction pattern appears in **rank16_altzigzag_firstorder.py**. Its negative results may remain conservative, but any claimed image dimension or positive matrix signal needs a corrected rerun. Corrected reruns during this audit preserve the negative W3F, W4F, and 64 square-zero-Z1-extension rows.

### 11.3 Scope of the surviving rank-16 computation

[scripts/rank16_leading_z3.log](scripts/rank16_leading_z3.log) establishes exact-$\mathbb F_2$ first-order vanishing for the **listed** rank-16 fibers. It does not classify every rank-16 killed-by-$2$ fiber.

The safe conclusions are:

- the listed fibers have no leading exact-$\mathbb F_2$ quartic seed;
- the entire 64-member c44 family has no leading seed, with the corrected linear argument valid over arbitrary $\mathbb F_2$-algebras;
- unlisted fibers, deeper layers, and mixed characteristic remain open.

The stronger phrases “no leading rank-16 seed” and “the rank-uniform theorem at rank 16” are not justified by the available classification evidence.

### 11.4 Attempted deeper rank-16 layer

During this audit a first direct c44 rank-16 $TD_5$ build was attempted with full multiplication and comultiplication deformed through the two-jet.

It built

~~~text
292320 axiom equations in 895.90 seconds
~~~

and then the process disappeared while constructing the $\Psi/TD_5$ target, before any solver query.

This run is **untested**. It is neither SAT nor UNSAT evidence.

---

## 12. Why no SAT signal is a counterexample

A genuine counterexample requires a finite locally free Hopf algebra satisfying every axiom and an element of the augmentation ideal on which $[n]^\#$ is nonzero. None of the positive rows in the directory meets that standard.

- **S0 sat** shows only that the axiom system is nonempty.
- **Psi_i != 0 sat** shows only that a deformation layer is nontrivial.
- A nonzero suspension sum may cancel inside the complete $D_s$ identity.
- A model after dropping associativity, $\Delta$-multiplicativity, coassociativity, counit, or antipode is not the required group scheme.
- A first- or second-order seed must lift through all higher deformation equations to a ring where the obstruction survives.
- Failure of the stronger property $S'$ would not imply $[4]^\#\ne e$.
- A timeout, unknown result, or killed process has no polarity.

No full-axiom model with

\[
[n]^\#(I)\ne0
\]

appears anywhere in the audited material.

---

## 13. Structural restrictions on a counterexample

The reductions and extension argument force a possible counterexample into a narrow regime.

1. **The base must be nonreduced.** Reduced bases are known.
2. **The group scheme must be noncommutative.** Deligne handles commutative group schemes.
3. **The residue characteristic must divide the order.** Otherwise the group scheme is étale.
4. **Square-zero maximal ideals are excluded.**
5. **A flat normal filtration by safe factors is excluded.**

For the last point, suppose $N\triangleleft G$ is finite flat of order $a$, $G/N$ has order $b$, and both are killed by their orders. For every point $g$,

\[
g^b\in N,
\]

hence

\[
g^{ab}=1.
\]

Thus products, ordinary semidirect products, and many triangular matrix constructions are poor counterexample candidates.

6. **Leading Jordan-chain mechanisms are heavily constrained.** Coassociativity forces the carry elements that support such chains to be primitive. In many tested fibers this collapses the cotangent image to a star-shaped square-zero space.

A counterexample, if one exists, is therefore likely to be genuinely deformation-theoretic: a higher Massey layer over a deep Artin base, with no persistent flat normal subgroup and no visible product decomposition.

---

## 14. Best remaining counterexample regimes

### 14.1 Order 4 in mixed characteristic

This is the smallest and most credible regime.

The special fiber

\[
\alpha_2\times\mu_2
\]

admits mixed-characteristic deformations, and the recent literature leaves the analogous $\lambda=0$ branch outside the proved noncommutative family. The directory has strong negative evidence for several exact mixed-characteristic rings but no uniform Witt-carry theorem.

A serious search must allow both multiplication and comultiplication to deform, impose every Hopf axiom, and query $[4]^\#$ directly. Fixed-algebra or comultiplication-only searches are too restrictive.

### 14.2 Order 4 at arbitrary equal-characteristic depth

The arbitrary-coefficient identities through $s=4$ and exact-$\mathbb F_2$ evidence at $s=5,6$ make a shallow counterexample unlikely.

However, a coefficient polynomial can vanish at every $\mathbb F_2$-point without belonging to the universal axiom ideal. It may then fail over a nonreduced coefficient algebra. This is why the unfinished arbitrary-coefficient $D_5$ computations remain genuine counterexample searches.

### 14.3 Non-principal order-4 bases

The square-zero and bidual cases are closed, but higher embedding dimension creates multigraded compatibility systems. A counterexample could exploit a syzygy class invisible on every curvilinear quotient.

### 14.4 Rank 8 and rank 16

The higher-rank programs remain useful but are currently less compelling than the unresolved order-4 mixed-characteristic case.

- Rank $8$: several $TD_5$ rows, variable-special-fiber searches, arbitrary-coefficient upgrades, and mixed characteristic remain open.
- Rank $16$: only selected leading first-order families have been excluded. $TD_5$ and higher, unclassified fibers, and mixed characteristic are essentially untouched.

---

## 15. Best remaining proof strategies

### 15.1 Invariant relative-defect induction

The proof should target the choice-independent defect

\[
\varphi\!\left(\frac{\varphi(e_i)}{\epsilon}\right)
\]

rather than a literal globally chosen $\Phi^2$.

The product-killing lemma reduces every curvilinear step to one cotangent target for $t^4$ and two for $xy$. The missing result is an identity that expresses the top kernel-lift defect in terms of lower-depth bialgebra data while allowing the edge and tail terms to cancel together.

The suspension probes show that separate tail vanishing is false. Any successful recursion must preserve the coupled $D_s$ sum.

### 15.2 Antipode and convolution

Let

\[
x=\mathrm{id}_A
\]

in the convolution algebra $\operatorname{End}_R(A)$, let

\[
e=\eta\varepsilon,
\qquad
S=x^{-1},
\]

and in characteristic $2$ put

\[
D=S-x.
\]

Because the coordinate algebra is commutative, $S^2=\mathrm{id}$ under ordinary composition, so

\[
D\circ D=0.
\]

Under convolution,

\[
D*D=x^{-2}+x^2,
\]

and hence

\[
x^2*(D*D)=e+x^4=[4]^\#-e.
\]

Since $x^2$ is convolution-invertible,

\[
[4]^\#=e
\quad\Longleftrightarrow\quad
D*D=0.
\]

This packages the order-4 obstruction as the convolution square of the deviation of inversion from the identity.

It is not an automatic proof: composition-square-zero does not imply convolution-square-zero. At a socle step, however, $D*D$ represents the same top obstruction and may be a lower-degree or more symmetric target for a universal calculation.

### 15.3 Universal rank-4 Hopf ideal

For fixed order $4$, the problem admits a finite universal algebraic formulation.

Choose a basis

\[
1,e_1,e_2,e_3
\]

and introduce polynomial variables over $\mathbb Z$ for:

- commutative multiplication constants;
- comultiplication constants;
- counit and unit data;
- antipode constants.

Let $P$ be the polynomial ring and let $J\subset P$ be the ideal generated by associativity, coassociativity, counit, $\Delta$-multiplicativity, and antipode identities.

The universal module

\[
A_{\mathrm{univ}}=(P/J)^4
\]

is finite free of rank $4$ with its universal based Hopf structure.

Compute every coefficient $f_{ij}$ of

\[
[4]^\#-\eta\varepsilon.
\]

Then:

- if every $f_{ij}\in J$, the order-4 conjecture follows on every based-free local chart and hence for every finite locally free rank-4 group scheme;
- if some $f_{ij}\notin J$, its nonzero class in $P/J$ makes the universal object itself a counterexample over $\operatorname{Spec}(P/J)$.

Thus fixed order $4$ is, in principle, an exact ideal-membership decision problem. The obstruction is computational size, not logical infinitude.

The existing fiber normal forms, gradings, low-layer identities, and arbitrary-coefficient certificates should be used to stratify this calculation. The convolution target $D*D$ may be cheaper than expanding $[4]^\#$ directly.

### 15.4 Mixed-characteristic first-order shape theorem

In equal characteristic, the first symbol is square-zero or pairwise nilpotent in the hard order-4 branch.

In mixed characteristic, the divided doubling map has an initial form schematically like

\[
\tau\,\mathrm{id}+\psi,
\]

where $\tau$ records the initial form of $2$. The desired theorem is not separate vanishing of the two terms but cancellation in their composite. A uniform Witt-carry theorem of this kind would address the strongest remaining literature gap.

---

## 16. Recommended work plan

### Priority A: repair the evidence base

1. Replace the defective quotient projection in **hopf_firstorder_scanner.py** with canonical Gaussian elimination.
2. Rerun every scanner that used the same **RowBasis.reduce** pattern.
3. Keep the negative c44 result but replace the false “$\Psi_1$ does not preserve $I^2$” explanation.
4. Remove full-deformation claims transferred solely by Cartier duality.
5. Restate the $\Phi$ conjecture in invariant top-defect form.
6. Mark every log without a terminal verdict as open.

### Priority B: exact order-4 decision

1. Build the universal based rank-4 Hopf ideal over $\mathbb Z$.
2. Gate it on constant groups and the standard $\alpha_2^2$, $\alpha_2\times\mu_2$, $W_2[F]$, and $\mu_2^2$ fibers.
3. Test both $D*D$ and $[4]^\#-e$ by staged Gröbner bases.
4. If the global system is too large, split it by residue characteristic and the two local algebra shapes.
5. Add already-proved identities only when their ideal-membership justification is explicit.

### Priority C: focused counterexample search

1. Start with mixed-characteristic deformations of $\alpha_2\times\mu_2$.
2. Deform both multiplication and comultiplication.
3. Search successive universal Witt or ramified jets while retaining lift data.
4. Treat SAT only as a seed until a full Hopf structure with $[4]^\#\ne e$ is explicitly verified.

### Priority D: higher rank

Only after the order-4 universal and mixed-characteristic routes:

- finish the missing rank-8 $TD_5$ rows;
- make the non-exterior special-fiber coproduct variable;
- attempt arbitrary-coefficient $TD_4/TD_5$ certificates;
- revisit rank-16 $TD_5$ with a sparse expression builder and checkpointed resource limits.

---

## 17. Final assessment

The accumulated work is mathematically meaningful. It supplies:

- a strong global-to-local reduction;
- an effective order-4 obstruction theory;
- several broad arbitrary-coefficient theorems;
- extensive exact-ring negative evidence;
- a useful cotangent reduction of the relative defect;
- strong obstructions to naive higher-rank counterexamples.

It does not resolve Grothendieck's question.

The evidence presently favors the conjecture:

- no full-axiom counterexample appears;
- all completed exact order-4 searches are negative;
- arbitrary-coefficient layer identities hold through the first nontrivial depths;
- the apparent rank-16 leading seed was a scanner artifact;
- completed deeper-layer tests continue to return UNSAT.

But uniform depth, general non-principal bases, and mixed characteristic each require new mathematics.

> **The mathematically justified conclusion is: no proof and no counterexample. Order $4$ is the closest target; a universal Hopf-ideal calculation or a uniform mixed-characteristic socle-obstruction theorem offers the clearest route to a genuine resolution.**

---

## Appendix A. Key local sources

- [THEORY_order4.md](THEORY_order4.md): reductions, $S'$, first-order theory, layer calculus, bidual theorem, and the order-4 frontier.
- [REPORT_order4.md](REPORT_order4.md): theorem and computation ledger; several headlines require the corrections in this report.
- [HANDOFF_NEXT.md](HANDOFF_NEXT.md): chronological record and validation warnings.
- [THEORY_rank8.md](THEORY_rank8.md): rank-8/16 layer bookkeeping; §§8 and 10 contain the duality and scanner overclaims corrected here.
- [RESPONSE_TO_rank16_push.md](RESPONSE_TO_rank16_push.md): honest Z3 refutation of the c44 seed, but an incorrect explanation of the initial false positive.
- [scripts/rank16_push_bundle/scripts/hopf_firstorder_scanner.py](scripts/rank16_push_bundle/scripts/hopf_firstorder_scanner.py): source of the quotient-reduction bug.
- [scripts/rank16_c44_full_sweep.log](scripts/rank16_c44_full_sweep.log): complete exact-$\mathbb F_2$ honest-composition sweep, 64/64 with zero leading seeds.
- [scripts/rank16_leading_z3.log](scripts/rank16_leading_z3.log): selected exact-$\mathbb F_2$ rank-16 leading-layer results.
- [scripts/rank8_td5.log](scripts/rank8_td5.log): incomplete exterior rank-8 $TD_5$ sweep.
- [higher_rank_push_artifacts.zip](higher_rank_push_artifacts.zip): archived direct zigzag scripts used for the audit rerun.
- [scripts/s5t4gen.log](scripts/s5t4gen.log), [scripts/s5xygen.log](scripts/s5xygen.log), and [scripts/fp3gen.log](scripts/fp3gen.log): principal unfinished arbitrary-coefficient order-4 computations.

## Appendix B. Targeted audit runs

### B.1 Direct full-deformation ZIG $TD_5$

The full-deformation script extracted from **higher_rank_push_artifacts.zip** completed with:

~~~text
[MAIN TD5 != 0] -> unsat   (130.2s)
===== fiber ZIG done (212.9s total) =====
DONE rank8_zigzag_td5
~~~

### B.2 Exterior rank-8 mask1 $TD_5$

The rerun reached the main query but was interrupted after 498.2 seconds:

~~~text
[MAIN TD5 != 0] -> unknown   (498.2s)
~~~

This is recorded as open.

### B.3 Rank-16 c44 $TD_5$ prototype

The prototype built:

~~~text
292320 equations in 895.90s
~~~

It then terminated before a solver verdict. This is recorded as untested.

