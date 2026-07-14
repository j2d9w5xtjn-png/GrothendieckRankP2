# Theory push handoff: Grothendieck order-kills question, order 4

**Date:** 2026-07-08  
**Prepared by:** GPT-5.5 Pro  
**Scope:** finite locally free group schemes of order `4`; emphasis on the remaining local Artin, residue-characteristic-`2`, special-fiber-killed-by-`2` branch.

This handoff is meant to be appended after the latest `HANDOFF_NEXT.md` / `THEORY_order4.md` session.  I did not run the CLI jobs; this is a theory push.  I also did **not** audit the actual `REPORT_order4.md` logs or Macaulay2 certificates.  Any statement below that uses a previously banked theorem must be checked against the logs before being promoted to a theorem in the report.

---

## 0. Executive conclusion

I did **not** prove the full order-four theorem over all Artinian bases.  However, I think there is a real strengthening of the current theory state:

> **New useful theorem, conditional only on already-banked Theorem A / `THEORY_order4.md` Theorem 6.2 as stated in the latest handoff.**  
> Let `R` be an equal-characteristic-`2` Artin local ring with maximal ideal `m` and `m^3 = 0`.  Let `A = O(G)` be a rank-four commutative Hopf algebra over `R`, with local special fiber killed by `2`.  Then `[4]^#(I) = 0`, where `I = ker(epsilon)`.  
> In particular, if the usual connected-etale / non-`2`-killed fiber reductions are valid, this closes the equal-characteristic `m^3 = 0` branch for **all embedding dimensions**, not merely embdim `<= 2`.

This suggests that the running `len3gen.m2` job is not logically necessary for the theorem if the earlier dual-number theorem and the graded formula are truly proven as stated.  It remains useful as an independent audit and as certificate material.

The next conceptual target is no longer merely `psi^2 = 0`; it is the following **homogeneous-symbol lemma**:

> For an arbitrary equal-characteristic Artin local base, every homogeneous degree-`r` symbol of the squaring map `phi = [2]^#` belongs to the same square-zero, pairwise-anticommuting symbol space detected at first order.

If this lemma is proved, then the equal-characteristic order-four theorem follows by associated-graded induction.  Mixed characteristic still needs a separate version including the initial form of `2`.

---

## 1. Setup and notation

Throughout this handoff:

```text
R        = Artin local ring, usually characteristic 2 here
m        = maximal ideal of R
k        = R/m
A        = O(G), finite free rank 4 over R
I        = ker(epsilon: A -> R)
phi      = [2]^# = mu_A o Delta_A : A -> A
K        = ker(phi) cap I
```

The remaining branch after the standard reductions is:

```text
R local Artin, residue characteristic 2;
G local and possibly noncommutative;
G_k killed by 2;
phi(I) subset m I;
show phi^2(I) = [4]^#(I) = 0.
```

The latest handoff records that `THEORY_order4.md` proves:

1. reduction to Artin local rings with finite residue field;
2. a rigidity theorem across socle-line extensions;
3. a graded formula for `m'^3 = 0`:

```text
d = [4]^# - eta epsilon
  = sum_{alpha,beta} (t_alpha t_beta) tensor psi_beta psi_alpha;
```

4. an `S'` induction theorem except for Open Lemma 7.4, where

```text
S'(A/R):     phi(I) subset m (ker(phi) cap I);
```

5. automatic antipodes in the killed-by-`2` special-fiber branch.

The latest handoff also says the ablation computations identify `{Delta-multiplicativity, associativity}` as the common minimal axiom set in the first nontrivial layer, and that coassociativity is not load-bearing for the length-three `[4]` vanishing tests.

---

## 2. New theorem: equal-characteristic `m^3 = 0` is already closed

### Theorem 2.1

Assume:

1. `R` is an equal-characteristic-`2` Artin local ring with `m^3 = 0`;
2. `A/R` is a rank-four commutative Hopf algebra whose special fiber is local and killed by `2`;
3. the dual-number theorem holds as stated in the current project, namely: for every first-order deformation over `k[e]/e^2` of either local killed-by-`2` fiber, the associated divided squaring operator `psi` satisfies

```text
psi^2 = 0;
```

4. the length-three graded obstruction formula of `THEORY_order4.md` holds:

```text
[4]^# - eta epsilon
  = sum_{alpha,beta} t_alpha t_beta tensor psi_beta psi_alpha.
```

Then

```text
[4]^#(I) = 0.
```

### Proof

Choose elements `t_alpha in m` whose images form a `k`-basis of `m/m^2`.  Since `m^3 = 0`, every obstruction to `[4]^# = eta epsilon` lies in `m^2`.

Because the special fiber is killed by `2`,

```text
phi(I) subset m I.
```

Modulo `m^2`, write the first-order part of `phi` as

```text
phi(x~) = sum_alpha t_alpha psi_alpha(x_0)   mod m^2 I,
```

where `x_0` is the image of `x~` in the special fiber.

For any scalar tuple `lambda = (lambda_alpha)` over any extension algebra of `k`, quotienting `R` by `m^2` and by the linear equations orthogonal to `lambda` produces a first-order deformation over `k[e]/e^2` whose divided squaring operator is

```text
psi_lambda = sum_alpha lambda_alpha psi_alpha.
```

The dual-number theorem gives

```text
psi_lambda^2 = 0
```

for every `lambda`.  Since the theorem is over arbitrary coefficient algebras, this is a polynomial identity, not merely a finite-field pointwise statement.  Therefore the coefficients of the quadratic polynomial in the `lambda_alpha` vanish:

```text
psi_alpha^2 = 0,
psi_alpha psi_beta + psi_beta psi_alpha = 0       for all alpha,beta.
```

Now apply the graded formula:

```text
[4]^# - eta epsilon
  = sum_{alpha,beta} t_alpha t_beta psi_beta psi_alpha.
```

The diagonal terms vanish because `psi_alpha^2 = 0`.  The off-diagonal terms cancel in pairs because `t_alpha t_beta = t_beta t_alpha` and

```text
psi_beta psi_alpha + psi_alpha psi_beta = 0.
```

Thus the obstruction is zero.  Hence `[4]^#(I) = 0`.

### Important audit note

This proof is only as strong as the two cited project inputs:

```text
(1) the dual-number theorem over arbitrary coefficient algebras;
(2) the length-three graded obstruction formula.
```

The latest handoff says these are proved in `THEORY_order4.md`, but the next agent should open that file and verify exact hypotheses before moving this theorem into `REPORT_order4.md`.

### Consequence if the audit passes

The running universal embdim-2 computation over

```text
k[s,t]/(s,t)^3
```

is no longer needed to prove equal-characteristic `m^3 = 0`; it becomes an independent validation and source of explicit certificates.  In particular, an embdim-3 analogue of `len3gen.m2` is lower priority unless the audit of Theorem 2.1 fails.

---

## 3. Why this does not yet prove all equal-characteristic Artin bases

For an arbitrary equal-characteristic Artin local ring, write the associated graded pieces

```text
gr^r_m R = m^r / m^{r+1}.
```

Because `phi(I) subset mI`, `phi` has homogeneous symbols

```text
theta_r : I_0 -> I_0 tensor_k gr^r_m R,
qquad r >= 1.
```

The degree-`n` part of `phi^2` is formally

```text
sum_{r+s=n} theta_s theta_r.
```

The `m^3 = 0` theorem only uses `theta_1`.  For larger nilpotence depth, one must control `theta_r` for `r >= 2`.

The natural conjecture is:

> **Homogeneous-symbol lemma.**  Every `theta_r` lies in the same first-order symbol space as the `psi_alpha` from the dual-number theorem; hence all `theta_r` square to zero and pairwise anticommute.

If true, then for every `n`,

```text
sum_{r+s=n} theta_s theta_r = 0,
```

and therefore `phi^2 = 0` on `I`.

This would prove the equal-characteristic order-four theorem.

The point that is not yet proved is that a higher symbol `theta_r` is genuinely a tangent vector of the same first-order moduli problem.  One cannot simply quotient by `m^{r+1}` and ignore lower symbols; the lower-degree pieces of `phi` may contribute nonlinearly to the degree-`r` equations.  This is exactly where Open Lemma 7.4 / `S'` propagation lives.

---

## 4. Reformulation of Open Lemma 7.4

The latest handoff phrases the remaining gap as propagation of

```text
S'(A/R): phi(I) subset m (ker(phi) cap I).
```

Here is the sharper form I recommend attacking.

### Proposed replacement for Open Lemma 7.4

Let `R' -> R` be a socle extension with kernel `M`, so

```text
M^2 = 0,
m' M = 0.
```

Let `A'/R'` be a rank-four bialgebra/Hopf algebra in the remaining branch, and set

```text
A      = A'/M A',
phi'   = [2]^#_{A'},
phi    = [2]^#_A.
```

Assume `A/R` satisfies `S'`.  Let `theta_M` denote the homogeneous `M`-symbol of `phi'`, i.e. the `M`-component of `phi'` after subtracting the lift of `phi`.

The required statement is equivalent to:

```text
theta_M belongs to the same square-zero, pairwise-anticommuting symbol space
as first-order divided squaring operators of the special fiber.
```

This is stronger and more structural than the module saturation statement

```text
ker(phi') cap m'I' = m' (ker(phi') cap I'),
```

and it is probably the right object to prove using `Delta`-multiplicativity and associativity.

---

## 5. Why purely formal `S'` propagation cannot work

A formal module argument cannot prove Open Lemma 7.4.

Indeed, take

```text
R' = k[e]/e^3,
R  = R'/(e^2),
I' = R' e_1 + R' e_2.
```

Define an `R'`-linear endomorphism

```text
Phi'(e_1) = e e_2,
Phi'(e_2) = e^2 e_1.
```

Then `Phi'^2 = 0`.  Downstairs, the induced `Phi` satisfies the analogue of `S'`, but upstairs

```text
Phi'(e_1) = e e_2
```

is not in

```text
m' (ker Phi' cap I').
```

Thus `S'` propagation is false for arbitrary square-zero endomorphisms.  Any proof must use the fact that `phi` is the squaring map of a rank-four bialgebra, and the ablation results correctly point to the load-bearing identities:

```text
A is associative;
Delta is multiplicative.
```

Coassociativity may be unnecessary for the key length-three identity, according to the latest ablation logs.

---

## 6. Concrete algebraic target for Macaulay2 / hand proof

The next best computation is **not** another finite-ring Z3 search.  It is a linear-algebra computation of the first-order symbol space.

For each of the two local killed-by-`2` fibers:

```text
A_0 = k[x,y]/(x^2,y^2),
A_0 = k[t]/t^4,
```

perform the following.

### Step 1. Linearize only the minimal axioms

Work over `k[e]/e^2` and write

```text
mu    = mu_0 + e mu_1,
Delta = Delta_0 + e Delta_1.
```

Impose only:

```text
mu associative and commutative;
Delta counital;
Delta multiplicative with respect to mu.
```

Do **not** impose coassociativity at first.  The ablation logs suggest it is not needed for the symbol identity.

### Step 2. Construct the divided squaring symbol

In characteristic `2`, define

```text
psi = mu_0 o Delta_1 + mu_1 o Delta_0.
```

This is the coefficient of `e` in

```text
phi = mu o Delta.
```

### Step 3. Compute the vector space `T` of all possible `psi`

The linearized axioms are linear in the coefficients of `mu_1, Delta_1`.  Eliminate the deformation variables or parameterize the solution space.  The image in `End_k(I_0)` is a finite-dimensional `k`-vector space `T`.

### Step 4. Prove `T` is totally square-zero

Show, by linear algebra, that for all `u,v in T`,

```text
u^2 = 0,
uv + vu = 0.
```

Equivalent computational tests:

1. choose a basis `q_1,...,q_N` of `T`;
2. verify

```text
q_i^2 = 0,
q_i q_j + q_j q_i = 0
```

for all `i,j`.

This is much smaller than the existing nonlinear Groebner searches.  It should produce a human-readable proof of the `psi^2 = 0` mechanism.

### Step 5. Higher-symbol test

Once `T` is explicit, try to prove that every homogeneous symbol `theta_r` of a higher-depth deformation lies in `T`.  This is the actual Open Lemma 7.4 replacement.

One possible route: use the Rees algebra / associated graded of `R` and `A`, then show that the degree-`r` part of `Delta`-multiplicativity linearizes to the same equations that define `T`, because all lower-degree contributions have already been killed by the pairwise-anticommuting identities.

If this induction works, it proves the equal-characteristic theorem for arbitrary depth.

---

## 7. Mixed characteristic: separate initial-form problem

The equal-characteristic argument does not automatically handle mixed characteristic.  In mixed characteristic, Schoof's estimate gives

```text
phi(I) subset 2I + I^2,
```

and even when the special fiber is killed by `2`, the initial form of `2` contributes to the leading symbol of `phi`.

The basic model is `mu_4` over `Z/8`, where

```text
phi(t) = 2t + t^2,
[4]^#(t) = 0.
```

So the mixed-characteristic symbol space must include a distinguished scalar operator coming from the initial form of `2`, not only the deformation symbol `psi`.

Suggested mixed-characteristic analogue:

```text
theta = tau * id + psi,
```

where `tau = in_m(2)` in `gr_m R` when `2` has the relevant degree.  The target identity becomes

```text
theta^2 = 0
```

and pairwise anticommutation for multiple homogeneous pieces.

This is why `z8search.m2` and the ramified `Z[pi]/(pi^2-2, pi^3)` analogues are still genuinely important.

---

## 8. Current status after this theory push

### What I would mark as new progress

1. **Equal-characteristic `m^3=0` should be considered theoretically closed**, assuming the previous handoff accurately states Theorem A and the graded formula.
2. The embdim-2 `len3gen` computation is no longer the main route to that theorem; it is now an audit/certificate source.
3. The real equal-characteristic problem is to prove the **homogeneous-symbol lemma**, not to enumerate more length-three finite rings.
4. The mixed-characteristic problem requires a separate symbol calculus including the initial form of `2`.

### What remains unproved

1. The full order-four theorem over arbitrary Artin local rings.
2. Open Lemma 7.4 / `S'` propagation.
3. The homogeneous-symbol lemma for higher-depth equal-characteristic bases.
4. The mixed-characteristic analogue with the `2`-symbol.

---

## 9. Recommended next actions

### First: audit before promoting

Open `THEORY_order4.md` and verify the exact hypotheses of:

```text
Theorem 6.2: length-three graded obstruction formula;
Theorem A / length-two theorem: psi^2 = 0 for every first-order deformation over arbitrary coefficient algebras.
```

If both match the hypotheses used in Theorem 2.1 above, update `REPORT_order4.md`:

```text
Equal-characteristic m^3 = 0 branch is closed for all embedding dimensions.
```

Mark `len3gen.m2` as validation/certificate, not as load-bearing.

### Second: build `symbolspace.m2`

Create a new Macaulay2 script that performs the linear computation in §6.  It should output:

```text
dim T for xy fiber;
dim T for t^4 fiber;
a basis for T;
verification that all basis elements square to zero and anticommute pairwise.
```

Run it first with the three validation gates from the latest handoff.

### Third: prove the higher-symbol lemma

Try to prove by induction on `r` that the degree-`r` homogeneous symbol of `phi` lies in `T`.  The induction hypothesis should be exactly the pairwise anticommutation of lower symbols.

This is the likely path to a full equal-characteristic proof.

### Fourth: keep mixed characteristic separate

Do not try to force the equal-characteristic proof onto `Z/8`.  Instead define the mixed symbol space containing `tau * id + psi`, validate it on `mu_4`, and then revisit `z8search` / ramified searches.

---

## 10. Suggested update to the project memory

```text
Session 4 theory push: no full proof yet.  New conditional theorem: if Theorem A
(dual-number psi^2=0 over arbitrary coefficient algebras) and THEORY_order4 Thm 6.2
(length-three graded formula) are as stated, then equal-characteristic Artin local
bases with m^3=0 are fully closed for all embedding dimensions.  Proof uses
polarization: psi_lambda^2=0 for all lambda gives psi_i^2=0 and psi_i psi_j +
psi_j psi_i=0, killing d = sum t_i t_j psi_j psi_i.  This makes len3gen an audit,
not a load-bearing computation.  New main target: prove homogeneous-symbol lemma
for higher-depth equal-char bases; i.e. every degree-r symbol of phi=[2]^# lies in
the same totally square-zero symbol space T detected at first order.  Proposed new
script: symbolspace.m2, a linearized assoc + Delta-mult computation for the two
local killed-by-2 fibers.  Mixed characteristic remains separate because the initial
form of 2 contributes, as in mu_4 over Z/8 with phi(t)=2t+t^2.
```

---

## 11. Caution flags

1. Do not promote Theorem 2.1 until the exact statements in `THEORY_order4.md` are audited.
2. Do not claim a full Artin-depth theorem from first-order `psi^2 = 0`; higher symbols are the missing issue.
3. Do not merge equal-characteristic and mixed-characteristic symbol calculi.
4. Do not treat Z3 `UNSAT` over finite rings as universal over all residue fields; keep the three evidence strengths separate.
5. Do not skip `ringcheck.py` for new finite-ring classes.

