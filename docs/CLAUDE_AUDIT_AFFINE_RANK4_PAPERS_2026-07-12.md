# Claude independent audit: the affine-group rank-4 counterexample papers (2026-07-12)

**Auditor:** Claude (Fable 5), independent session, 2026-07-12 ~13:00.
**Verdict up front: BOTH PAPERS ARE CORRECT.** Every displayed identity, lemma,
and theorem item was re-derived by hand and re-verified by a third, fully
independent machine implementation (58/58 checks pass), and both companion M2
scripts pass end-to-end. I found **no mathematical errors**. The one "failure"
produced during the audit was a bug in *my own* first-draft check, not in the
papers (details in §4). Minor expository/provenance nits and suggested
simplifications are in §5–§6.

---

## 1. What was audited

Most recent work products (all dated 2026-07-12) on the rank-4 counterexample
to Grothendieck's power question:

1. `notes/A_RANK_FOUR_COUNTEREXAMPLE_TO_GROTHENDIECKS_POWER_QUESTION_2026-07-12.tex`
   (the short article; PDF compiled 12:53/12:57) — read line by line.
2. `notes/A_HUMAN_SCALE_RANK_FOUR_COUNTEREXAMPLE_FROM_THE_AFFINE_GROUP_2026-07-12.tex`
   (the long pedagogical companion; PDF 12:02) — read line by line.
3. `m2/verify_rank4_affine_article_20260712.m2` — read line by line and rerun.
4. `m2/verify_human_scale_affine_rank4_counterexample_20260712.m2` — rerun.

The claimed theorem (identical in both papers):

- R = **Z[a,b]/(a³, b³, a²b+2)** is Artin local, complete intersection,
  length 9, residue field F₂, characteristic 4, Soc(R) = F₂·(2b).
- A = **R[U,V]/(U² − abU + b²V, V² − a²V)** is free of rank 4 on 1, U, V, W=UV.
- With λ = (1+aU)(1+bV), the formulas Δ(U) = U⊗1 + λ⊗U, Δ(V) = V⊗λ + 1⊗V,
  ε(U) = ε(V) = 0 make A a Hopf algebra; G = Spec A is a finite locally free
  group scheme of rank 4.
- **[4]#(U) = 2bW ≠ 0**, [4]#(V) = 0, **[8] = e**. So G is *not killed by 4*.
- Special fiber α₂×α₂ (commutative); G itself noncommutative.

---

## 2. Hand verification (complete list)

Every one of the following was re-derived from scratch on paper during this
audit; all agree with the papers.

**Base ring (Lemma 2.1 / §7 of the long paper).**
Cokernel of (2 + mult-by-a²b) on Z⁹: two 2×2 blocks [[2,0],[1,2]] (Smith form
(1,4), giving Z/4·{1} and Z/4·{b}) plus five 1×1 blocks (2), giving
R_add ≅ (Z/4){1,b} ⊕ (Z/2){a,a²,ab,b²,ab²}; |R| = 512, length 9. Consequences
4 = 0 (= a⁴b²), 2a = −a³b = 0, 2b = −a²b² ≠ 0, q := b² with q² = bq = 2q = 0,
a²q = −2b. Regular sequence: a³, b³ obviously regular; a²b+2 injective on R₀
since the block matrix has det 2⁹. gr_m R ≅ F₂[A,B]/(A³,B³), Hilbert
(1,2,3,2,1), socle = (2b) = m⁴. All correct.

**Rank-two cancellation (eq. 3.1).** T² = cT, g = 1+dT, T\* = T₁+g₁T₂ gives
T\*² − cT\* = (2 + 3cd + (cd)²)T₁T₂ = g₁(2+cd)T₁T₂; with cd = a²b = −2 both
P (c=ab, d=a) and K (c=a², d=b) close, g² = 1, [2]#T = (2+cd)T = 0. Correct.

**The one-curvature Lemma (3.2 / Appendix A).** I verified every auxiliary
identity in A_t (t ∈ Q = (b²)): M² = 1; λ² = 1 − a²tV; a²(λ−1) = −2V;
t(λ−1) = atU; t(λ²−1) = 0; and 2λU + ab(λ²−λ) = −aqV (both summands recomputed:
2U+2bUV and 2U−aqV+2bUV). Then: V-quadric defect = V₁λ₂(a²(λ₂−1)+2V₂) = 0;
U-quadric defect = a(q−t)V₁U₂ (expansion re-done term by term); graph defect
= L₁M₂·E(2+A′+B′+E) with A′=aU₂, B′=bV₁, E=A′B′ (factorization re-derived:
the bracket equals (L₂−1)(M₁−1)(1+M₁L₂)), and 2E = EA′ = EB′ = E² = 0 using
(A′)² = −a²tV₂, (B′)² = −2B′, bt = 0. λ is a unit since λ² = 1 − a²tV and
(a²tV)² = 0. **All correct.**

**Hopf inheritance logic.** O(H) → A (z ↦ λ, a unit) is surjective, so G ↪ H_R
is a closed immersion; Lemma 3.2 at t=q says the image is closed under
multiplication; unit (0,0,1) ∈ G; hence G is a closed submonoid and
associativity/coassociativity/counit and the Δ-formulas are inherited. Since
[8] = e is proved by the power computation (which uses only the monoid
structure — no circularity), [7] is a two-sided inverse word, so G is a group
scheme and the antipode exists. Sound.

**Power computation (§4).** (u,v,z)ⁿ = (N_n(z)u, vN_n(z), zⁿ) verified by
induction; M² = 1, L² = 1+2bV, λ² = 1+2bV, θ² = λ²−2λ+1 = 0, 2θ = 2bV,
N₄(λ) = 4 + 6θ = 2θ = 2bV, λ⁴ = 1, N₈(λ) = N₄(λ)(1+λ⁴) = 0. Hence
[4]#(U) = 2bVU = 2bW ≠ 0 (2b ≠ 0, W a basis element), [4]#(V) = 2bV² = −4V = 0,
[8]# = ηε (U,V ↦ 0 and they generate). Correct.

**Noncommutativity and fiber.** Coefficient of V⊗U in Δ(U) − τΔ(U) is b ≠ 0
(free basis of A⊗A); mod m both quadrics collapse and both coordinates are
primitive, so G_{F₂} ≅ α₂×α₂. Correct.

**Deformation interpretation (§5 / long paper §8).** Regular-sequence conormal
frame; κ_naive(Φ̄) = aqV₁U₂; coboundary −q(V\*−V₁−V₂) = −qV₁(λ₂−1) = −aqV₁U₂;
exactness because Q² = 0; nonsplitting (b+x)² = q for all x ∈ Q; ω₄ is an
ηε-relative derivation with ω₄(U) = 2bUV = −a²qUV = −a·diag\*(κ_naive(Φ̄));
torsor of corrections {t : a(q−t) = 0} = {q, q+2b}. All correct.

**Long-paper extras.** (i) Extension no-go Lemma 4.1 (killedness multiplies
through exact sequences) — correct, functorial-points proof sound. (ii) The
universal five-relation Lemma 5.1/Prop 5.2 over
B_br = Z[α,β,γ,r,s]/(αr+2, γs+2, γr, βs, βr+αs): I re-derived the scalar
consequences 4 = 2α = 2β = 2γ = 2r = 0, r²β = 2s, 2s² = 0 and the full closure
computation at universal-coefficient strength — correct. (iii) The
"three relations are forced" specialization table — correct. (iv) The
monoid-lifts-group lemma (8.2: finite locally free monoid over a nilpotent
thickening of a group is a group, via translation determinants) — correct.
(v) Chain-ring exclusion (§9): the five relations plus 2s ≠ 0 force 2 ∈ m² and
are unsatisfiable in an Artin chain ring — correct (the displayed valuation
chain implicitly assumes αs ≠ 0, but the αs = 0 case yields the contradiction
even faster; conclusion unaffected). (vi) The three toy deformations — correct.

---

## 3. Machine verification — three independent layers

**Layer 1 (mine, new): `scripts/claude_indep_audit_affine_rank4_20260712.py`**
(log: `scripts/claude_indep_audit_affine_rank4_20260712.log`). A *third
implementation* sharing nothing with the papers' proofs or the M2 scripts: no
Gröbner bases. R is modeled as an explicit finite ring of order 512 by normal
forms whose reduction rules are derived only from the three relations; the
model is *proved* isomorphic to R inside the script (ring axioms checked
exhaustively on basis triples + a spanning/cardinality argument, documented in
the header). A_t and its tensor powers are handled by monic normal-form
reduction. Checks include: all base-ring facts (incl. socle = {0,2b} by
512-element enumeration, |m^k| = 512,256,64,8,2,1); associativity of A_t
(⇒ freeness); **the full defect vector (a(q−t)V₁U₂, 0, 0) for all eight
t ∈ Q**; the torsor {q, q+2b}; the coboundary identity; gauge rigidity;
θ/λ/N₄/N₈ identities; Δ well-definedness; coassociativity on U, V, W in A^⊗3;
counit both sides; noncocommutativity with V⊗U-coefficient exactly b;
antipode relations + both convolution identities on the whole basis; power
words [2]–[8] via convolution powers of the identity, with the cross-checks
[4]# = [2]#∘[2]#, [4]#(U) = N₄(λ)U, and [2]# multiplicative on basis pairs;
**[4]#(U) = 2bW ≠ 0, [4]#(V) = [4]#(W) = 0, [4]# ≠ ηε, [8]# = ηε**; and the
α₂×α₂ fiber. **Result: `ALL CLAUDE INDEPENDENT AFFINE-RANK4 AUDIT CHECKS
PASSED` (58/58).** Runtime ~1 s, memory negligible.

**Layer 2: the article's own script** `m2/verify_rank4_affine_article_20260712.m2`
rerun locally (M2 1.25.11 at /opt/homebrew/bin/M2, the version the script
states it was tested with): all twelve
claim-blocks PASS, terminal banner
`ALL CLAIM-BY-CLAIM RANK-FOUR AFFINE-GROUP AUDITS PASSED`. I also audited the
script itself: the tensor-square/triple rings are the correct presentations of
A⊗A and A⊗A⊗A; nonmembership conclusions use completed strong Gröbner bases
over Z (sound); the antipode convolution identities are checked on generators
only *after* verifying S is an algebra endomorphism, which is exactly what
makes generator-checking sufficient (S\*id and id\*S are then comorphisms of
scheme maps, i.e., algebra maps); `doubleMap` iteration is justified by
[2ⁿ] = [2]∘[2ⁿ⁻¹] for powers of a single point. Block 9 verifies the
universal five-relation lemma; block 10 the exact curvature vector with t a
formal square-zero parameter; block 11 the conormal regular sequence by colon
ideals. Well-designed; no gaps found.

**Layer 3:** `m2/verify_human_scale_affine_rank4_counterexample_20260712.m2`
rerun: `ALL HUMAN-SCALE AFFINE-GROUP AUDITS PASSED` (includes the three toys,
the universal lemma, the weight-(1,−1) presentation closure, and the
coboundary/word-defect links).

Agreement across: papers' hand proofs = my hand re-derivation = finite-ring
model (no GB) = two Z-Gröbner scripts. The compute cost was trivial and the
box stayed at load ≈ 6–7/18 throughout (other agents' jobs untouched).

---

## 4. The one audit "failure" (mine, not theirs) — for transparency

My first-draft Layer-1 script checked `λ·(1−θ) = 1` for **all** t ∈ Q. That is
false for t ≠ q (there θ² = −(a²t+2b)V ≠ 0, so λ⁻¹ = 1 − θ + θ² instead), and
the check correctly failed. The papers never claim it: Lemma 3.2 claims only
that λ is a *unit* in A_t (proof: λ² = 1 − a²tV, square-zero correction), and
the identity λ⁻¹ = 1 − θ is asserted only at t = q, where it is true. I fixed
my check to the papers' actual claim (explicit inverse λ(1+a²tV)) and it
passes for all eight t ∈ Q. This is worth recording because it is exactly the
kind of overreach an auditor can misattribute to the source.

---

## 5. Correctness verdict, item by item (Theorem 1.1 of the short paper)

| Item | Claim | Verdict |
|---|---|---|
| (1) | R Artin local CI, length 9, residue F₂, char 4 | **Correct** (hand + both machine layers; CI via colon ideals and det = 2⁹) |
| (2) | A free rank 4 on 1,U,V,W | **Correct** (successive monic quadrics; independently by normal-form model + GB staircase) |
| (3) | Hopf structure with the displayed Δ | **Correct** (closure lemma + inheritance + [8]=e ⇒ [7] is the inverse; antipode −λ⁻¹U, −Vλ⁻¹ double-checked) |
| (4) | [4]#(U) = 2bW ≠ 0, [4]#(V) = 0, [8] = e | **Correct** (three independent computations of the power words) |
| (5) | Fiber α₂×α₂, G noncommutative | **Correct** |

The headline conclusion stands: **G is a finite locally free group scheme of
rank 4, over an Artin local ring of length 9, with [4] ≠ e and [8] = e.**
Grothendieck's power question has a rank-four counterexample, now with a
fully human-checkable proof.

Consistency with the program's banked exclusions was also spot-checked: G₀ =
G mod (b²) lives over a length-6 base and is killed by 4 (machine-verified
"[4]=e downstairs"), consistent with the exhaustive residue-F₂ length ≤ 6
UNSAT sweeps; the defect 2b·W is socle-valued, as minimality theory predicts;
the base has m² ≠ 0 and 2m ≠ 0, outside Schoof's theorem, and the fiber is
commutative, outside the Schoof–Torti deformation families.

---

## 6. Notable simplifications and observations

1. **The base ring is the same length-9 ring as the 2026-07-11 example, not a
   new one.** The Jul-11 audit ring Z[x,y]/(x³, y³, xy²−2) maps isomorphically
   to today's R via x ↦ −b, y ↦ a (char 4 makes ±2 interchangeable). What is
   genuinely new today is the *presentation and proof mechanism* (ambient
   affine group + one curvature coefficient), which eliminates the
   coefficient-by-coefficient Hopf verification entirely. This should be said
   explicitly in the short paper (the long paper's §9 alludes to the
   "optimized paper" ring Z[r,s]/(r³+2, s³+2, rs²), which is yet another
   presentation of the same family; today's tex never states the relation to
   the earlier writeups). Recommended: one remark with the explicit
   isomorphism, so referees don't think three counterexamples are in play.
2. **The five-relation universal lemma deserves theorem status.** The long
   paper proves (Prop 5.2): over *any* commutative ring B with
   αr = γs = −2, γr = βs = 0, βr + αs = 0, the algebra
   B[U,V]/(U²−αU−βV, V²−γV) is a rank-4 Hopf algebra with
   [4]#(U) = 2sUV and [8] = e; it is a counterexample exactly when 2s ≠ 0.
   That is a portable, machine-free statement — the counterexample is a
   *family* with initial base B_br, and R is just a convenient Artinian point
   of it. Packaging it as the main theorem (with R as Example) would make the
   short paper both stronger and shorter.
3. **[4]# = [2]#∘[2]# gives the shortest possible verification path.** Since
   [2]#(U) = (1+λ)U, [2]#(V) = V(1+λ), and [2ⁿ] = [2]∘[2ⁿ⁻¹] on points, a
   referee can verify item (4) with two substitutions in a rank-4 free module.
   The M2 script uses this; the papers use N_n(λ), which is equivalent but
   could mention the two-substitution shortcut.
4. **A flat rank-2 subgroup survives.** The V = 0 locus P = Spec R[U]/(U²−abU)
   is still a flat closed rank-2 subgroup of G (the bridge term b²V vanishes
   on it, S(U) = −λ⁻¹U preserves it), whereas the U = 0 locus is *not* flat
   over R (U = 0 forces b²V = 0). By the long paper's extension no-go lemma,
   P therefore cannot be normal with flat rank-2 quotient. Stating this would
   sharpen the "the bridge destroys the extension structure" sentence into a
   precise assertion.
5. **Minimality status (worth one remark in the paper).** Length 9 is an upper
   bound for the minimal base length of a rank-4 counterexample; the program's
   exact-ring sweeps closed all residue-F₂ bases of length ≤ 6 (and most
   length-7 strata), so the true minimum lies in {7, 8, 9}. Neither paper
   claims minimality — correctly — but a one-line remark recording the known
   window would preempt the obvious referee question. (The long paper's §9
   chain-ring exclusion and 2 ∈ m² observation support, but do not prove,
   optimality of the two-variable design.)
6. **Expository nits (no mathematical effect).**
   - Long paper §9, chain-ring argument: the displayed equation
     v(β)+v(r) = v(α)+v(s) silently assumes αs ≠ 0; adding "(if αs = 0 the
     third relation already gives the contradiction)" would make it airtight.
   - Short paper §3: "Both subgroup assertions are the same one-line rank-two
     calculation" — the displayed identity (3.1) is per-factor; the *pair*
     also needs g² = 1, which is stated two lines later. Fine, but the
     ordering could be tightened.
   - History §1: the sentence attributing to Schoof the no-length-bound
     killedness for deformations of α_p⋊μ_{p^m} matches this project's
     literature notes (via Torti's introduction), but the project's
     long-standing flag that Schoof 2001 Thm 1.2's exact scope was never
     verified against the printed paper still applies; likewise the claim
     about notes (38)–(39) of the annotated SGA3 Exp. VIII was not re-verified
     in this audit. These affect only the history paragraph, not the theorem.
7. **What the papers deliberately do not claim (and correctly so):** no
   minimality, no classification, no statement about which power words other
   than [4], [8] vanish ([4]#(W) = 0 as well — all of [4]#−ηε is carried by U,
   machine-checked), and no claim that the construction is unique: the torsor
   check shows exactly two bridges t ∈ {q, q+2b} work, and both give
   counterexamples (same [4]# defect −a²t·UV = 2bUV for both, since
   a²·2b = 0 — verified in passing by the defect formula).

---

## 7. Reproduction

```
python3 scripts/claude_indep_audit_affine_rank4_20260712.py   # ~1 s, 58 checks
M2 --script m2/verify_rank4_affine_article_20260712.m2         # ~20 s
M2 --script m2/verify_human_scale_affine_rank4_counterexample_20260712.m2
```

Files written by this audit (nothing pre-existing was modified):
- `scripts/claude_indep_audit_affine_rank4_20260712.py` (+ `.log`)
- this report.
