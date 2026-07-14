# Comprehensive handoff note for the order-4 Grothendieck project

Date: 2026-07-09  
Author of this continuation sequence: GPT-5.5 Pro in this chat  
Scope: account of the mathematical work, proof reductions, Z3 probes, logs, and generated notes/scripts produced during the sequence of sustained pushes following the supplied handoff archives.

---

## 0. Executive status

This sequence did **not** prove the full order-4 Grothendieck conjecture.  The conjecture under discussion is the assertion, in order 4, that every finite locally free group scheme of order 4 is killed by 4, equivalently that the relevant `[4]` morphism is zero.  The project has been working in the hard noncommutative/local killed-by-2 branch, after the standard reductions in the supplied handoffs.

The main progress made in these passes is as follows.

1. **Curvilinear `t^4`, layer `s=4`, hand closure.**  The previous handoff reduced the `s=4` divided-[4] endpoint for the `t^4` fiber to four scalar obstructions.  I first proved `aB=0`, then in a further push proved `aC=0`, `BC=0`, and `Lambda=bB^2`.  These identities close the `t^4` `s=4` branch at the hand-proof level, modulo the normal-form reductions already in the handoff.

2. **Curvilinear `xy`, layer `s=4`, proof-shaped case reduction.**  Before the Macaulay2 banking appeared in later handoffs, I decomposed the `xy` `s=4` endpoint into four split-model linear algebra packages.  For the image-line cases `alpha_2^2` and `mu_2^2`, the endpoint reduces to operator identities involving `N=Psi_1`, `M=Psi_2`, `L=Psi_3`, and a rank-one functional `ell`.  For the rank-one cases `W_2[F]` and `mu_2 x alpha_2`, the endpoint reduces to a short list of scalar identities.  Fresh F2 gates confirmed every displayed reduction.  In the later v3/v4 archive, the `xy`, `s=4` branch was then banked at arbitrary-`k'` strength by Macaulay2 (`s4xygen.log`).

3. **Relative top-defect lemma.**  I proved a formal lemma for curvilinear socle lifts: if the truncation satisfies S′ and `[2]^#` squares to zero on the lift, then the new top S′ defect kills products.  In symbols, the defect `Omega` satisfies
   
   ```text
   Omega(I_H^2)=0.
   ```
   Thus the all-depth relative first-order lemma is a cotangent-level problem: one generator `t` for `t^4`, and two generators `x,y` for `xy`.

4. **Pairwise nilpotence of first-order symbols.**  I strengthened the first-order theorem from `psi^2=0` to pairwise nilpotence: for any two first-order symbols `psi, chi` in the killed-by-2 order-4 local branch,
   
   ```text
   psi chi = chi psi = 0.
   ```
   This gives S′ over every equal-characteristic square-zero base `k + m`, `m^2=0`, in arbitrary embedding dimension.

5. **Bidual calculus for the first non-principal base.**  For
   
   ```text
   R = k[u,v]/(u^2,v^2),     phi=[2]^# = uP + vQ + uvT,
   ```
   I derived the exact finite-dimensional S′ obstruction equations.  For a cotangent generator `g`, the remaining S′ problem is to find `a_g,r_g,s_g in I_H` such that
   
   ```text
   TPg + Q r_g + P a_g = 0,
   TQg + Q(Tg + a_g) + P s_g = 0.
   ```
   Product classes are already free by the product-killing lemma.

6. **Bidual `t^4` branch hand closure.**  I proved a hand-level solution of the bidual S′ equations for the `t^4` fiber.  The key polarized identities are
   
   ```text
   T(t^2) = p Q(t) + r P(t),
   T(t^3) = q Q(t) + s P(t),
   (Tt)_t = p B_Q + q C_Q + r B_P + s C_P.
   ```
   These give explicit no-division choices of `a,r_0,s_0` solving the bidual equations.

7. **Bidual `xy` rank-one branches hand closure.**  I closed the bidual S′ equations for the two rank-one split `xy` fibers, `W_2[F]` and `mu_2 x alpha_2`, again with explicit no-division S′ divisions.  The two image-line split fibers, `alpha_2^2` and `mu_2^2`, remain as the live bidual frontier.

8. **Negative result for a tempting suspension shortcut.**  I tested the conjectural shifted-tail vanishing route at `s=6` in the `t^4` fiber.  The shifted sums can be nonzero even when the full next `D_6` matrix vanishes.  Hence the uniform curvilinear proof cannot separately kill shifted sums; it must prove an edge-tail cancellation.

The live frontier after these passes is therefore concentrated in two places:

- **Bidual `xy` image-line branches:** `alpha_2^2` and `mu_2^2`.  The current target is the mixed-layer divisibility/Koszul lemma described in §8.3 below.
- **Uniform curvilinear induction beyond the banked depths:** after `s<=4`, the top-defect lemma says only the cotangent row remains, but a general all-depth edge-tail cancellation lemma is still missing.

---

## 1. File/artifact ledger

### 1.1 Notes generated during these passes

The following Markdown notes were generated in this conversation and are the primary mathematical record.

| File | Role |
|---|---|
| `order4_sustained_attempt_note.md` | First continuation.  Proves `aB=0` at the `t^4`, `s=4` frontier and records Z3 calibration. |
| `order4_further_push_s4_t4.md` | Closes the `t^4`, `s=4` endpoint by proving `aC=0`, `BC=0`, and `Lambda=bB^2`. |
| `order4_max_pass_xy_s4.md` | Decomposes the `xy`, `s=4` endpoint into split-model operator/scalar identities and records F2 gates. |
| `order4_fifth_push_relative_defect.md` | Proves the relative top-defect product-killing lemma, pairwise nilpotence of first-order symbols, square-zero-base S′, and derives the bidual calculus. |
| `order4_sixth_push_bidual_t4.md` | Closes the bidual S′ step for the `t^4` fiber and records the suspension counterexample. |
| `order4_seventh_push_bidual_xy_rank1.md` | Closes the bidual S′ step for the two rank-one `xy` split fibers and reduces the remaining image-line cases to a Koszul divisibility lemma. |
| `order4_comprehensive_handoff_note.md` | This comprehensive handoff. |

### 1.2 Bundles generated during these passes

| File | Contents |
|---|---|
| `order4_max_pass_xy_s4_bundle.zip` | `order4_max_pass_xy_s4.md`, `s4xy_case_reduction_gates.py/.log`, and `s4xy_rank1_gates.py/.log`. |
| `order4_fifth_push_bundle.zip` | `order4_fifth_push_relative_defect.md` plus `s5_t4_partial_probe.py/.log` and component probes for `D5(1,2)`, `D5(2,1)`, `D5(2,2)`. |
| `order4_sixth_push_bundle.zip` | `order4_sixth_push_bidual_t4.md`, `bidual_t4_cross_gates.py/.log`, `s6_suspension_timeout.py/.log`, `s6_suspension_model_d6.py/.log`. |
| `order4_seventh_push_bundle.zip` | `order4_seventh_push_bidual_xy_rank1.md`, rank-one bidual dual-coefficient probes, and reduced-field rho gates. |
| `order4_comprehensive_handoff_bundle.zip` | A newly created bundle containing this note, the prior notes, the generated scripts/logs available in `/mnt/data`, and copies of the supplied handoff archives for context. |

### 1.3 Standalone scripts/logs visible in `/mnt/data`

| File | Purpose |
|---|---|
| `s4xy_case_reduction_gates.py` | Z3/F2 gates for the four split `xy`, `s=4` case reductions. |
| `s4xy_case_reduction_gates.log` | Output showing the split-model reductions and raw endpoint negations are `unsat` over `F2[eps]/eps^4`. |
| `bidual_t4_cross_gates.py` | Z3/F2 gates over `F2[u,v]/(u^2,v^2)` for the bidual `t^4` cross identities. |
| `bidual_t4_cross_gates.log` | Output showing `P,Q` first-order shape, `T(t^2)`, `T(t^3)`, and `(Tt)_t` cross formula negations are `unsat`. |
| `s6_suspension_model_d6.log` | Log exhibiting a model where a shifted suspended sum is nonzero while the full `D6` matrix is zero. |

Some scripts are inside the bundle zips rather than root `/mnt/data`, notably `s4xy_rank1_gates.py`, `s5_t4_partial_probe.py`, `s6_suspension_model_d6.py`, `probe_w2f_Tx_dual.py`, `probe_mu2a2_Ty_dual.py`, and `bidual_xy_rank1_f2_rho_gates.py`.

---

## 2. Mathematical setup and notation used throughout

The project works after the handoff reductions.  We are in characteristic 2, in the local killed-by-2 special fiber branch of rank/order 4.  The two local algebra shapes are:

```text
H = k[t]/t^4                  (the t^4 fiber),
H = k[x,y]/(x^2,y^2), z=xy    (the xy fiber).
```

Let

```text
phi = [2]^# = mu Delta
```

be the coordinate map associated to multiplication-by-2.  In a curvilinear equal-characteristic family over `k[epsilon]/epsilon^N`, write

```text
phi = sum_{r>=1} epsilon^r Psi_r.
```

The strengthened S′ condition is equivalent to the divided-[4] layer identities

```text
D_s := sum_{i+j=s} Psi_i Psi_j = 0,      2 <= s <= N.
```

The handoff had already proved/banked the low layers and reduced `s=4` to concrete targets.  The continuation work below focuses on:

- `D_4` for `t^4` and `xy`;
- the relative defect in the passage `N -> N+1`;
- the first non-principal base `k[u,v]/(u^2,v^2)`.

For the bidual base, the notation is

```text
R = k[u,v]/(u^2,v^2),
phi = uP + vQ + uvT.
```

Here `P` and `Q` are first-order symbols and `T` is the mixed second-order symbol.

---

## 3. First push: `t^4`, `s=4`, proof of `aB=0`

### 3.1 Frontier inherited from the handoff

For the `t^4` fiber, use the normal form from the handoff:

```text
w_0(t) = c_1(t o t^2) + c_1^2(t^2 o t^3) + c_4(t^2 tensor t^2),
w_0(t^2)=0,
w_0(t^3)=t o t^2 + c_1(t^2 o t^3),
```

where `o` denotes the symmetric tensor sum.  At `s=4`, the handoff reduced

```text
D_4 = Psi_1 Psi_3 + Psi_2^2 + Psi_3 Psi_1
```

to four scalar identities:

```text
a B^3 = 0,
a B^2 C = 0,
Lambda B = b B^3,
Lambda C = 0.
```

The first continuation proved the stronger identity

```text
aB = 0.
```

This kills the first two scalar obstructions immediately.

### 3.2 Notation

Let

```text
u := mu_1(t^2,t^2) = a t + b t^2 + a c_1 t^3,
ac_4 = 0,
beta := w_1(t),
Psi_1(t) = B t^2 + C t^3,
B = beta_11 + c_4 b.
```

Let

```text
Y := w_1(t^2),
Theta := w_1(t^3).
```

### 3.3 Proof sketch of `aB=0`

It suffices to show `a beta_11=0`, because `B=beta_11+c_4 b` and `ac_4=0`.

The `epsilon`-coefficient of

```text
Delta(t*t) = Delta(t)^2
```

gives `Y`.  Its `(t,t)` coefficient vanishes by degree considerations: no `w_0(t^i)` has a `t tensor t` coefficient, and product terms with positive degree in both tensor legs cannot produce `t tensor t`.  Hence

```text
Y_11 = 0.
```

Similarly, the `epsilon`-coefficient of

```text
Delta(t*t^2) = Delta(t) Delta(t^2)
```

gives

```text
Theta_11 = 0.
```

Now take the `epsilon^2` coefficient of

```text
Delta(t^2 *_A t^2) = (Delta t^2)^2.
```

Writing `v=mu_2(t^2,t^2)`, the reduced nonunit part is

```text
w_0(v) = w_1(u) + Y^2.
```

Taking the `(t,t)` coefficient gives zero on the left and zero from `Y^2`, so

```text
0 = (w_1(u))_11 = a beta_11 + b Y_11 + a c_1 Theta_11 = a beta_11.
```

Therefore

```text
aB=0.
```

### 3.4 Machine calibration from this stage

The following Z3/F2 checks were run in the first continuation stage.

- `s4probe.py` over `F2[epsilon]/epsilon^4`, `t^4` branch:
  - `Q0` satisfiable sanity check: `sat`.
  - `T1`: `(Psi3 t^2)_t = pP + aB^2`: negation `unsat`.
  - `T2`: full `s=4` endpoint `D4=0`: negation `unsat`.
- Tail probe over `F2[epsilon]/epsilon^4`:
  - `aB != 0`: `unsat`.
  - `aB^2 != 0`: `unsat`.
  - `aB^3 != 0`: `unsat`.
  - `aB^2 C != 0`: `unsat`.
- Contrast check:
  - over `F2[epsilon]/epsilon^2`, `a beta_11 != 0`: `sat`;
  - over `F2[epsilon]/epsilon^3`, `a beta_11 != 0`: `unsat`.

The contrast is conceptually useful: `a beta_11` is a real first-order possibility, but it is killed by existence of the second-order lift.

---

## 4. Second push: `t^4`, `s=4`, closure by `Lambda=bB^2` and `BC=0`

The second continuation closed the two remaining `t^4`, `s=4` scalar obstructions.

### 4.1 Additional notation

Use

```text
beta = w_1(t),
Y = w_1(t^2),
Theta = w_1(t^3),
gamma = w_2(t),
V = w_2(t^2),
U = w_2(t^3).
```

Write

```text
mu_1(t,t)   = p t + p_2 t^2 + p_3 t^3,
mu_1(t,t^2) = q t + q_2 t^2 + q_3 t^3,
u = mu_1(t^2,t^2) = a t + b t^2 + a c_1 t^3,
B = beta_11 + c_4 b,
C = beta_12 + beta_21.
```

### 4.2 New vanishing: `aC=0`

The first-order digit of

```text
Delta(t*t^2)=Delta(t)Delta(t^2)
```

at `(1,2)` and `(2,1)` gives

```text
Theta_12 = q_3 + a c_4 + b c_1 = Theta_21.
```

The second-order diagonal identity for `t^2*t^2` is

```text
w_0(v)=w_1(u)+Y^2.
```

Take the sum of the `(1,2)` and `(2,1)` coefficients.  The `w_0(v)` contribution cancels because the relevant `w_0` terms are symmetric.  The `Y^2` contribution cancels in the symmetric sum.  The middle term gives

```text
a(beta_12+beta_21) + b(Y_12+Y_21) + a c_1(Theta_12+Theta_21).
```

Since `Y_12=Y_21` and `Theta_12=Theta_21`, characteristic 2 leaves

```text
aC=0.
```

### 4.3 New vanishing: `BC=0`

First-order coassociativity gives

```text
c_4 C = 0.
```

Hence

```text
BC = (beta_11+c_4 b)C = beta_11 C.
```

Order-2 coassociativity of `Delta(t)` at triple coefficients `(1,1,2)`, `(2,1,1)`, and `(1,2,1)` gives three equations.  Adding them cancels everything except

```text
beta_11 C + (Theta_12+Theta_21)(beta_13+beta_31)=0.
```

Since `Theta_12=Theta_21`, this yields

```text
beta_11 C=0,
```

hence

```text
BC=0.
```

### 4.4 Main scalar identity: `Lambda=bB^2`

Let

```text
Psi_2(t) = P t + Q t^2 + R t^3,
P = pB + qC,
```

and, as in the handoff,

```text
sigma_2 = p p_2 + q p_3 + mu_2(t,t)_t,
sigma_3 = p q_2 + q q_3 + mu_2(t,t^2)_t,
Lambda = (Psi_3 t)_t + Qp + Rq + B sigma_2 + C sigma_3.
```

The coefficient certificate obtained in the second continuation is:

```text
Lambda + bB^2
 = b E_V + a E_C + a c_1 E_U
   + a beta_13 E_T^12 + a beta_31 E_T^21 + Remainder,
```

where the `E` terms are coefficient equations already forced by associativity, multiplicativity of `Delta`, and coassociativity.  After first-order coassociativity consequences

```text
beta_13 = beta_31,
beta_23 = beta_32,
beta_33 = beta_11 c_1^2,
```

the residual is

```text
Remainder =
  aC(p_3+c_1p+c_1q_2+a c_1^2)
  + ab beta_11 c_1^2
  + a c_1 c_4 sigma_3.
```

Each term vanishes using

```text
aC=0,
a beta_11=0,
ac_4=0.
```

Thus

```text
Lambda=bB^2.
```

### 4.5 Assembly of `D_4=0` in the `t^4` branch

The handoff assembly formula was

```text
D_4(t^2)=aB^2 Psi_1(t),
D_4(t^3)=0,
```

and

```text
D_4(t)=
  aB^3 t
  + (Lambda B+bB^3)t^2
  + (Lambda C+a c_1 B^3+aB^2C)t^3.
```

With

```text
aB=0,
BC=0,
Lambda=bB^2,
```

all terms vanish.  This gives the hand-level closure:

```text
D_4=0 for the t^4 fiber.
```

### 4.6 Machine checks from this stage

Fresh checks over `F2[epsilon]/epsilon^4`, `t^4` fiber, returned negation `unsat` for:

```text
Lambda=bB^2,
Lambda B=bB^3,
Lambda C=0,
aB=0,
D_4=0.
```

A dual-number coefficient probe over `(F2[d]/d^2)[epsilon]/epsilon^4` returned negation `unsat` for:

```text
aB=0,
BC=0,
bBC=0,
bB^2C=0.
```

---

## 5. Third push: `xy`, `s=4`, case-by-case decomposition

This push targeted the `xy` fiber at

```text
D_4 = Psi_1 Psi_3 + Psi_2^2 + Psi_3 Psi_1 = 0.
```

Set

```text
N := Psi_1,
M := Psi_2,
L := Psi_3.
```

The lower banked identities are

```text
N^2=0,
NM+MN=0.
```

The split `xy` fiber models are

```text
alpha_2^2,
W_2[F],
mu_2^2,
mu_2 x alpha_2.
```

### 5.1 Image-line cases: `alpha_2^2` and `mu_2^2`

In the image-line cases,

```text
N(x)=c_x z,
N(y)=c_y z,
N(z)=0.
```

Let

```text
ell(a x + b y + c z) = a c_x + b c_y,
```

so `N(v)=ell(v)z`.

The new operator package is:

```text
(M^2 g)_{x,y} + ell(g)(Lz)_{x,y} = 0,
(M^2 g)_z + ell(g)(Lz)_z + ell(Lg) = 0,
```

for `g=x,y,z`.  These identities imply `D_4(g)=0` because

```text
NL(g)=ell(Lg) z,
LN(g)=ell(g) Lz.
```

Additional model-specific checks:

- For `alpha_2^2`, `M(z) in k z`.
- For `mu_2^2`, `M(z)=0` and `L(z)=0`.

### 5.2 Rank-one case `W_2[F]`

The split model is

```text
w_0 x = 0,
w_0 y = x tensor x,
w_0 z = x o y.
```

The first-order shape is

```text
N(x)=0,
N(y)=lambda x,
N(z)=0.
```

Define

```text
nu    := mu_1(y,y)_x,
alpha := (w_1 x)_11,
delta := (w_1 x)_22,
rho   := lambda alpha + nu delta,
m     := mu_1(x,y)_y,
chi   := (M y)_z.
```

The normal form and scalar identities are:

```text
M(x)=rho x,
(My)_y=rho,
M(z)=m lambda x,
lambda(Lx)_y = rho^2,
lambda(Lx)_z = rho chi,
(Lz)_y = m rho,
lambda((Ly)_y+(Lx)_x+m chi)=0.
```

These imply `D_4=0` by direct matrix multiplication.

### 5.3 Rank-one mirror `mu_2 x alpha_2`

The mirror first-order shape is

```text
N(x)=lambda y,
N(y)=0,
N(z)=0.
```

Define

```text
nu    := mu_1(y,y)_y,
alpha := (w_1 y)_11,
delta := (w_1 y)_22,
rho   := lambda alpha + nu delta,
m     := mu_1(x,y)_x,
chi   := (M x)_z.
```

The normal form and scalar identities are:

```text
M(y)=rho y,
(Mx)_x=rho,
M(z)=m lambda y,
lambda(Ly)_x = rho^2,
lambda(Ly)_z = rho chi,
(Lz)_x = m rho,
lambda((Lx)_x+(Ly)_y+m chi)=0.
```

Again these imply `D_4=0` by direct matrix multiplication.

### 5.4 Script: `s4xy_case_reduction_gates.py`

This script is an exploratory Z3 verifier over `F2[epsilon]/epsilon^4`.  It imports the handoff infrastructure:

```python
from order4sat_beyond import F2epsN
from s2check import build_blocks
from s3gates import KF2, digit
```

It pins each of the four split fibers, extracts

```text
P[1]=Psi_1, P[2]=Psi_2, P[3]=Psi_3,
```

and checks negations of the reduction identities above.  It is not an arbitrary-`k'` Groebner certificate; it is a proof map and sanity check.

The log reports, for each split case:

```text
[Q0 axioms sat] -> sat
[reduction identity negations] -> unsat
[endpoint D4=0] -> unsat
```

Representative log lines:

```text
===== W2F over F2[eps]/eps^4 =====
[Psi1: x->0, y->lambda x, z->0] -> unsat
[Psi2(x)=rho x] -> unsat
[(Psi2 y)_y=rho] -> unsat
[Psi2(z)=m lambda x] -> unsat
[lambda (Psi3 x)_y=rho^2] -> unsat
[lambda (Psi3 x)_z=rho (Psi2 y)_z] -> unsat
[(Psi3 z)_y=m rho] -> unsat
[lambda((Psi3 y)_y+(Psi3 x)_x+m(Psi2 y)_z)=0] -> unsat
[endpoint D4=0] -> unsat
```

### 5.5 Later audit status

In the later v3/v4 handoff, the `xy`, `s=4` branch is banked by Macaulay2 at arbitrary-`k'` strength: the log `s4xygen.log` ends successfully and reports all four split models closed.  Therefore this decomposition is no longer the only evidence for `xy`, `s=4`, but it remains useful as a human-readable proof skeleton.

---

## 6. Fourth/fifth push: relative top defects, square-zero bases, and bidual calculus

### 6.1 The relative top-defect map

Let

```text
R' = k[epsilon]/epsilon^(N+1),
R  = k[epsilon]/epsilon^N,
```

and let `A'` be a free rank-4 bialgebra over `R'` with killed-by-2 local fiber `H`.  Let

```text
phi=[2]^#=mu Delta.
```

Assume the truncation `A=A'/epsilon^N A'` satisfies S′.  By the project's killedness theorem, the lift is killed by 4, so

```text
phi^2=0 on A'.
```

For `x in I_H`, choose `v_x` with

```text
epsilon v_x = phi(tilde x).
```

Then `phi(v_x)` lies in the top socle `epsilon^N I`, so write

```text
phi(v_x) = epsilon^N Omega(x).
```

The desired relative first-order lemma is `Omega=0`.

### 6.2 Product-killing lemma

For all `a,b in I_H`,

```text
Omega(ab)=0.
```

Proof: since `phi` is an algebra endomorphism,

```text
phi(tilde a tilde b)=phi(tilde a) phi(tilde b)=epsilon^2 v_a v_b.
```

A valid division by `epsilon` is `epsilon v_a v_b`.  Applying `phi` gives

```text
phi(epsilon v_a v_b)=epsilon phi(v_a) phi(v_b)=0,
```

because both `phi(v_a)` and `phi(v_b)` are already top-socle.  Corrections from replacing `tilde a tilde b` by a chosen lift of `ab` contribute terms of the form `epsilon^{r-1} phi^2(...)`, hence vanish.

Therefore `Omega` factors through

```text
I_H/I_H^2.
```

Consequences:

```text
t^4 fiber: only Omega(t) remains.
xy fiber: only Omega(x), Omega(y) remain.
```

### 6.3 Pairwise nilpotence of first-order symbols

If `psi` and `chi` are first-order symbols of the same killed-by-2 order-4 local fiber, then

```text
psi chi = chi psi = 0.
```

Reason by split cases:

```text
t^4:        psi(I) subset I^2 and psi(I^2)=0.
alpha_2^2:  image in I^2 and kills I^2.
W_2[F]:     image in kx and kills kx.
mu_2^2:     image in I^2 and kills I^2.
mu_2*a_2:   image in ky and kills ky.
```

Descent gives the assertion before splitting.

### 6.4 S′ over all square-zero equal-characteristic bases

Let

```text
R = k + m,    m^2=0.
```

Write

```text
phi(e_i)=sum_alpha m_alpha psi_alpha(e_i).
```

Taking the S′ divisions `k_{i,alpha}=psi_alpha(e_i)`, pairwise nilpotence gives

```text
phi(k_{i,alpha})=sum_beta m_beta psi_beta psi_alpha(e_i)=0.
```

Therefore S′ holds over every equal-characteristic square-zero base in the killed-by-2 local branch, in arbitrary embedding dimension.

### 6.5 Bidual obstruction equations

For

```text
R = k[u,v]/(u^2,v^2),
phi = uP + vQ + uvT,
```

the square-zero quotient gives

```text
P^2=Q^2=PQ=QP=0.
```

For a basis element `g`, a general division of `phi(g)` by `(u,v)` may be written

```text
A_g = P g + u r_g + v a_g + uv r'_g,
B_g = Q g + u b_g + v s_g + uv s'_g,
a_g + b_g = Tg.
```

The conditions `A_g,B_g in ker(phi)` reduce exactly to

```text
TPg + Q r_g + P a_g = 0,                         (B1)
TQg + Q b_g + P s_g = 0.                         (B2 raw)
```

Substituting `b_g=Tg+a_g`, this becomes

```text
TPg + Q r_g + P a_g = 0,                         (B1)
TQg + Q(Tg+a_g) + P s_g = 0.                    (B2)
```

This is the main non-principal S′ reduction used in the subsequent bidual passes.

### 6.6 Partial `s=5` curvilinear probes

A next-layer probe for the `t^4` fiber over `F2[epsilon]/epsilon^5` imposed the already-banked `D2=D3=D4=0` identities and tested pieces of `D5=0`.  The full endpoint did not finish, but the following component negations returned `unsat`:

```text
D5(1,1), D5(1,2), D5(2,1), D5(2,2).
```

These are consistent with the product-killing lemma.  The hard cotangent component, including `D5(1,3)`, was not closed in that pass.

---

## 7. Sixth push: bidual `t^4` hand closure

### 7.1 Setup

For the `t^4` fiber over the bidual base,

```text
phi = uP + vQ + uvT.
```

The first-order shape theorem gives

```text
P(t)=B_P t^2 + C_P t^3,
Q(t)=B_Q t^2 + C_Q t^3,
P(I^2)=Q(I^2)=0.
```

Write the product deformation as

```text
mu = mu_0 + u mu_u + v mu_v + uv mu_uv,
```

and define

```text
p = (mu_u(t,t))_t,
q = (mu_u(t,t^2))_t,
r = (mu_v(t,t))_t,
s = (mu_v(t,t^2))_t.
```

### 7.2 Polarized `t^4` layer-2 identities

The required identities are

```text
T(t^2) = p Q(t) + r P(t),
T(t^3) = q Q(t) + s P(t),
(Tt)_t = p B_Q + q C_Q + r B_P + s C_P.      (*).
```

The first two follow directly from the `uv` coefficient of multiplicativity of `phi`:

```text
phi(a *_A b)=phi(a) phi(b).
```

At `(a,b)=(t,t)` and `(t,t^2)`, the right side vanishes because `P(t),Q(t) in I^2` and `I^4=0`, while `P,Q` kill `I^2`.

The third identity `(*)` is the literal bilinear/polarized version of the banked one-variable `s=3`, `t^4` Step-6 assembly

```text
(Psi_2 t)_t = pB+qC.
```

It is not obtained from a simple base map; rather, it repeats the coefficient extraction and keeps the mixed `uv` terms.

### 7.3 Explicit solution of the bidual equations

Define

```text
A_Q  = B_P p + C_P q,
A_P  = B_P r + C_P s,
A'_Q = B_Q p + C_Q q,
A'_P = B_Q r + C_Q s.
```

Then

```text
T(Pt)=A_Q Q(t)+A_P P(t),
T(Qt)=A'_Q Q(t)+A'_P P(t),
(Tt)_t=A'_Q+A_P.
```

The bidual equations at `g=t` are

```text
TPt + Q r_0 + P a = 0,
TQt + Q(Tt+a) + P s_0 = 0.
```

Choose

```text
a   = A_P t,
r_0 = A_Q t,
s_0 = A'_P t.
```

Then

```text
TPt + Qr_0 + Pa
 = (A_Q Q + A_P P) + A_Q Q + A_P P = 0.
```

Also

```text
Q(Tt+a)=((Tt)_t + A_P)Q(t)=A'_Q Q(t),
```

so

```text
TQt + Q(Tt+a) + Ps_0
 = (A'_Q Q + A'_P P) + A'_Q Q + A'_P P = 0.
```

Thus S′ holds over `k[u,v]/(u^2,v^2)` for the killed-by-2 `t^4` fiber, over arbitrary characteristic-2 coefficient rings, assuming the banked first-order shape and polarized Step-6 identity.

### 7.4 Script: `bidual_t4_cross_gates.py`

This script works over the exact ring `F2[u,v]/(u^2,v^2)` using the handoff's `BiDual` infrastructure.  It extracts

```text
P = [u] phi,
Q = [v] phi,
T = [uv] phi,
```

and checks:

```text
P,Q kill rows t^2,t^3,
P(t),Q(t) have no t component,
T(t^2)=pQ(t)+rP(t),
T(t^3)=qQ(t)+sP(t),
(Tt)_t=pB_Q+qC_Q+rB_P+sC_P.
```

The log reports negation `unsat` for every tested identity.

### 7.5 Negative suspension result

A proposed uniform curvilinear shortcut was that shifted sums

```text
Sigma_s^up = sum_{i+j=s} Psi_{i+1} Psi_{j+1}
```

might vanish once lower `D` identities are banked.  I tested this over `F2[epsilon]/epsilon^6`, `t^4` fiber, imposing `D2=D3=D4=D5=0`.

The shifted-sum tests were `sat`: shifted tails can be nonzero.  One extracted model has nonzero shifted matrix

```text
[0, 1, 0]
[0, 0, 0]
[0, 0, 0]
```

while the full `D6` matrix in the same model is zero.  Therefore the separate suspension-vanishing approach is false; the desired all-depth proof must prove edge-tail cancellation.

---

## 8. Seventh push: bidual `xy` rank-one closure and image-line reduction

### 8.1 Common bidual setup for `xy`

Let

```text
H=k[x,y]/(x^2,y^2), z=xy,
R=k[u,v]/(u^2,v^2),
phi=uP+vQ+uvT.
```

The bidual obstruction equations at a cotangent generator `g` are again

```text
TPg + Q r_g + P a_g = 0,                         (B1)
TQg + Q(Tg+a_g) + P s_g = 0.                    (B2)
```

The product generator `z` is free by `Omega(I^2)=0`, so only `x,y` matter.

### 8.2 Rank-one split models: closed

#### `W_2[F]`

The split model is

```text
w_0 x=0,
w_0 y=x tensor x,
w_0 z=x o y.
```

First-order shape:

```text
P(x)=Q(x)=P(z)=Q(z)=0,
P(y)=lambda x,
Q(y)=lambda' x.
```

The mixed `uv` coefficient of the Step-B calculations gives

```text
T(x)=alpha x,
(Ty)_y = rho in (lambda,lambda').
```

More explicitly, with directional notation,

```text
rho = lambda alpha_Q + nu delta_Q + lambda' alpha_P + nu' delta_P.
```

The polarized diagonal relations are

```text
lambda delta_Q + lambda' delta_P = 0,
nu delta_Q + nu' delta_P = 0.
```

Hence

```text
rho = lambda A + lambda' A',     A=alpha_Q, A'=alpha_P.
```

Explicit S′ divisions:

```text
for g=x:   a_x=r_x=s_x=0,
for g=y:   a_y=(alpha+lambda' A') y,
           r_y=lambda A' y,
           s_y=lambda' A y.
```

A direct substitution gives `(B1)` and `(B2)` without dividing by `lambda` or `lambda'`.

#### `mu_2 x alpha_2`

The mirror model has

```text
P(y)=Q(y)=P(z)=Q(z)=0,
P(x)=lambda y,
Q(x)=lambda' y.
```

The mixed calculation gives

```text
T(y)=alpha y,
(Tx)_x = rho = lambda A + lambda' A'.
```

Mirror divisions:

```text
for g=y:   a_y=r_y=s_y=0,
for g=x:   a_x=(alpha+lambda' A') x,
           r_x=lambda A' x,
           s_x=lambda' A x.
```

This closes the two rank-one split `xy` bidual branches.

### 8.3 Remaining image-line split models

The open split models are

```text
alpha_2^2,
mu_2^2.
```

Here

```text
P(g)=p_g z,
Q(g)=q_g z,        g=x,y,
P(z)=Q(z)=0.
```

Let

```text
p=(p_x,p_y),
q=(q_x,q_y),
```

and let `overline{Tg}` denote the cotangent projection of `Tg` to `<x,y>`.

The expected mixed triangularity is

```text
T(z)=tau z.                                     (I0)
```

Assume `(I0)` and write

```text
a_g = tau g + h_g.
```

Then the bidual equations reduce to

```text
p(h_g) + q(r_g) = 0,
q(overline{Tg}) + q(h_g) + p(s_g) = 0.          (I1)
```

It is enough to prove the Koszul divisibility condition

```text
q(overline{Tg}) in (p_x,p_y) + (q_x,q_y)^2,     g=x,y.       (I2)
```

Indeed, if

```text
q(overline{Tg})
 = p_x S_x + p_y S_y
   + q_x^2 H_x + q_x q_y H_xy + q_y^2 H_y,
```

then set

```text
h_g = (q_x H_x + q_y H_xy)x + q_y H_y y,
r_g = p_x H_x x + (p_x H_xy+p_y H_y)y,
s_g = S_x x + S_y y.
```

This solves `(I1)`.  Therefore the live bidual `xy` image-line problem is no longer the full S′ system; it is the mixed-layer coefficient lemma `(I0)+(I2)`, plus the symmetric version with `P` and `Q` interchanged if one wants a fully symmetric formulation.

### 8.4 Scripts from this pass

Inside `order4_seventh_push_bundle.zip`:

- `probe_w2f_Tx_dual.py` checks, over `(F2[d]/d^2)[u,v]/(u^2,v^2)`, that in the `W_2[F]` rank-one case the mixed term satisfies `T(x) in kx`.  Log: `W2F T(x) not in kx over dual coeff unsat`.
- `probe_mu2a2_Ty_dual.py` checks the mirror triangularity `T(y) in ky`.  Log: `mu2a2 T(y) not in ky over dual coeff unsat`.
- `bidual_xy_rank1_f2_rho_gates.py` checks, over reduced `F2[u,v]/(u^2,v^2)`, that the rank-one rho obstruction is in the ideal generated by the two first-order lambda directions.  Logs:
  
  ```text
  W2F rho not in (lambda_u,lambda_v) over F2: unsat
  mu2a2 rho not in (lambda_u,lambda_v) over F2: unsat
  ```

These scripts are sanity checks for the hand proof, not arbitrary-`k` certificates.

---

## 9. Detailed script and log guide

This section describes all scripts/logs generated by my passes, including those stored inside bundles.

### 9.1 `s4xy_case_reduction_gates.py`

Purpose: refine the one-line `xy`, `s=4` endpoint into human-readable split-model reductions.  It checks each proposed reduction by adding the negation to the bialgebra axioms and verifying `unsat` over `F2[epsilon]/epsilon^4`.

Important internal conventions:

```python
R=F2epsN(4)
A,Mb,C,F,phi,c,Mtab=build_blocks(R,XY)
P[n][(i,r)] = digit(phi[i][r], n)   # n=1,2,3
```

Case pins:

```python
'a2a2':    {(3,1,2),(3,2,1)}
'W2F':     {(2,1,1),(3,1,2),(3,2,1)}
'mu2mu2':  {(1,1,1),(2,2,2),(3,1,2),(3,2,1),...}
'mu2a2':   {(1,1,1),(3,1,2),(3,2,1),(3,1,3),(3,3,1)}
```

Outputs: all reduction negations and endpoint negations are `unsat`.

Dependency caveat: as written in the original generated file, the script has a hard-coded path such as `/mnt/data/groth_handoff_v2/scripts`.  To rerun it elsewhere, extract the appropriate handoff archive and adjust `sys.path` to the extracted `scripts` directory.

### 9.2 `s4xy_rank1_gates.py`

Location: inside `order4_max_pass_xy_s4_bundle.zip`.

Purpose: earlier/smaller rank-one-specific Z3 gates used before the consolidated `s4xy_case_reduction_gates.py`.  It checks the `W_2[F]` and `mu_2 x alpha_2` scalar identities separately.

Status: superseded by the consolidated script, but useful for debugging because it isolates rank-one cases.

### 9.3 `s5_t4_partial_probe.py` and component probes

Location: inside `order4_fifth_push_bundle.zip`.

Purpose: probe `D5=0` for `t^4` over `F2[epsilon]/epsilon^5`, imposing lower `D2=D3=D4=0` constraints.  The full endpoint did not finish.  Component probes closed selected entries:

```text
D5(1,1): unsat
D5(1,2): unsat
D5(2,1): unsat
D5(2,2): unsat
```

These checks support the product-killing picture but do not prove the hard cotangent row.

### 9.4 `bidual_t4_cross_gates.py`

Purpose: exact `F2[u,v]/(u^2,v^2)` gates for the bidual `t^4` cross identities.  It uses the handoff `BiDual` ring and extracts coefficient maps:

```python
P={(i,j):dig(phi[i][j],1)}   # u coefficient
Q={(i,j):dig(phi[i][j],2)}   # v coefficient
T={(i,j):dig(phi[i][j],3)}   # uv coefficient
```

It verifies:

```text
P,Q kill I^2,
P(t),Q(t) have no t component,
T(t^2)=pQ(t)+rP(t),
T(t^3)=qQ(t)+sP(t),
(Tt)_t=pB_Q+qC_Q+rB_P+sC_P.
```

Log summary:

```text
BiDual t4 cross gates
[P kills row 2,1] -> unsat
...
[Tt_t cross formula] -> unsat
[trace equation] -> unsat
```

Dependency caveat: imports from the extracted handoff infrastructure; adjust `PYTHONPATH`/`sys.path` when rerunning.

### 9.5 `s6_suspension_timeout.py` and `s6_suspension_model_d6.py`

Location: inside `order4_sixth_push_bundle.zip`; `s6_suspension_model_d6.log` is also visible at root.

Purpose: test the proposed shifted-sum/suspension route.  The key result is a countermodel to separate shifted-tail vanishing.  The log records a nonzero shifted matrix but zero full `D6` matrix.

Interpretation: do not attempt to prove all shifted sums vanish separately.  The correct uniform induction, if it exists, must capture cancellation between shifted tails and edge terms.

### 9.6 `probe_w2f_Tx_dual.py`

Location: inside `order4_seventh_push_bundle.zip`.

Purpose: tests over `(F2[d]/d^2)[u,v]/(u^2,v^2)` with `d` a coefficient nilpotent.  It checks that, in the `W_2[F]` rank-one branch, after imposing first-order rank shape, the mixed symbol satisfies

```text
T(x) in kx.
```

Log:

```text
W2F T(x) not in kx over dual coeff unsat
```

### 9.7 `probe_mu2a2_Ty_dual.py`

Location: inside `order4_seventh_push_bundle.zip`.

Purpose: mirror of the previous script.  It checks

```text
T(y) in ky
```

for the `mu_2 x alpha_2` split branch.

Log:

```text
mu2a2 T(y) not in ky over dual coeff unsat
```

### 9.8 `bidual_xy_rank1_f2_rho_gates.py`

Location: inside `order4_seventh_push_bundle.zip`.

Purpose: reduced `F2` specialization checking the ideal membership that `rho` lies in the ideal generated by the two first-order lambda directions.

Logs:

```text
W2F rho not in (lambda_u,lambda_v) over F2: unsat
mu2a2 rho not in (lambda_u,lambda_v) over F2: unsat
```

This supports the hand formula `rho=lambda A+lambda' A'`, but is not an arbitrary-coefficient proof by itself.

---

## 10. Audit notes and caveats

### 10.1 What should be considered hand-proved in this sequence

The following items are hand-proof level, modulo the reductions and notation in the supplied handoff:

1. `t^4`, `s=4`: `aB=0`, `aC=0`, `BC=0`, `Lambda=bB^2`, hence `D_4=0`.
2. Relative top-defect product-killing: `Omega(I^2)=0`.
3. Pairwise nilpotence of first-order symbols in killed-by-2 local order-4 fibers.
4. S′ over equal-characteristic square-zero bases.
5. Bidual calculus equations `(B1),(B2)`.
6. Bidual `t^4` S′ solution, assuming the polarized Step-6 coefficient identity.  This identity is proof-shaped and Z3-checked; for publication-level rigor, one should either write the full coefficient extraction explicitly or produce a Groebner certificate.
7. Bidual `xy` rank-one S′ solution, assuming the polarized Step-B rank-one mixed identities.  Again, the proof is written at coefficient-extraction level but could use a formal Macaulay2 certificate for the mixed identities.

### 10.2 What is computationally banked by later handoffs

From my audit of the v3/v4 archives:

- `xy`, `s=4` is banked by Macaulay2 in `s4xygen.log`.
- `s<=4` curvilinear layer identities are treated as banked in v4.
- The specific `s4t4gen.log` visible in one archive did not show a full final banking banner in my earlier audit, so the `t^4`, `s=4` proof should be cited primarily through the hand proof unless a later archive supplies a completed `s4t4gen` certificate.

### 10.3 What is only Z3 sanity-checked

The following are **not** arbitrary-`k` proofs by themselves:

- `s4xy_case_reduction_gates.py`: finite `F2[epsilon]/epsilon^4` gates.
- dual-number coefficient probes for `aB`, `BC`, rank-one bidual triangularity.
- reduced-field rho ideal membership gates.
- `s5` partial probes.
- suspension countermodel search, except as a valid finite-model disproof of the separate shifted-tail vanishing shortcut.

### 10.4 Known issue in generated text

In `order4_seventh_push_bidual_xy_rank1.md`, a displayed line contains a typo with extra `\n` characters:

```text
\n\nu delta_Q + \n\nu' delta_P = 0
```

It should read

```text
nu delta_Q + nu' delta_P = 0.
```

This typo is corrected in the account above.

---

## 11. Suggested next tasks

### 11.1 Best immediate target: bidual `xy` image-line branches

The remaining bidual split models are

```text
alpha_2^2,
mu_2^2.
```

The target is to prove, over arbitrary characteristic-2 coefficient rings, the mixed triangularity

```text
T(z)=tau z                                           (I0)
```

and the Koszul divisibility condition

```text
q(overline{Tg}) in (p_x,p_y)+(q_x,q_y)^2,     g=x,y.     (I2)
```

Here

```text
P(g)=p_g z,
Q(g)=q_g z,
P(z)=Q(z)=0,
q(overline{Tg}) = q_x (Tg)_x + q_y (Tg)_y.
```

Proving `(I0)+(I2)` gives explicit S′ divisions via the formula in §8.3.  This would close the bidual `xy` step and, combined with the previous bidual `t^4` result, would finish the first non-principal base `k[u,v]/(u^2,v^2)` for killed-by-2 local fibers.

Recommended proof strategy:

1. Work first in `alpha_2^2`, where the fiber coproduct is sparse.
2. Extract the `uv` coefficient of `Delta(z)=Delta(xy)=Delta(x)Delta(y)` and coassociativity on `z` to prove `T(z) in kz`.
3. Write `T(x)_x,T(x)_y,T(y)_x,T(y)_y` in terms of first-order product/coproduct coefficients.
4. Try to form `q_x T(g)_x+q_y T(g)_y` and reduce it modulo `(p_x,p_y)+(q_x,q_y)^2` using the polarized first-order diagonal relations.
5. Mirror to `mu_2^2`, or use Cartier duality if the handoff's duality conventions support it cleanly.

A Macaulay2 membership certificate for these two identities would be especially valuable and much smaller than a raw S′ syzygy computation.

### 11.2 Uniform curvilinear induction beyond `s<=4`

The top-defect lemma shows that the relative defect kills `I^2`, so the all-depth problem reduces to cotangent generators.  The failed suspension shortcut shows the next lemma must be edge-tail cancellation, not separate shifted-tail vanishing.

The target should be stated as follows.  Suppose `D_2,...,D_s` are banked and consider the next defect `D_{s+1}`.  Product rows/inputs vanish formally.  For the remaining cotangent generators, prove that the edge terms involving `Psi_1,Psi_s` cancel the shifted suspended tail

```text
sum_{i+j=s-1} Psi_{i+1} Psi_{j+1}.
```

The `s=6` model in `s6_suspension_model_d6.log` should be used as a warning/test case: any proposed lemma that separately kills the shifted tail is false.

### 11.3 Publication-level cleanup

For a rigorous final proof package, the following coefficient proofs should be expanded or certified:

1. The `Lambda=bB^2` certificate in the `t^4`, `s=4` branch.  The note gives a coefficient-certificate outline; a final writeup should list the exact `E_V,E_C,E_U,E_T^12,E_T^21` equations and their source coefficients.
2. The polarized `t^4` Step-6 identity `(Tt)_t=pB_Q+qC_Q+rB_P+sC_P` in the bidual branch.
3. The rank-one `xy` polarized Step-B identities, especially `rho=lambda A+lambda'A'` over arbitrary coefficient rings.
4. The image-line bidual Koszul divisibility `(I2)`.

---

## 12. Recommended directory layout for the next agent

After extracting `order4_comprehensive_handoff_bundle.zip`, use this layout:

```text
order4_comprehensive_handoff/
  README-ish primary note:
    order4_comprehensive_handoff_note.md

  prior_notes/
    order4_sustained_attempt_note.md
    order4_further_push_s4_t4.md
    order4_max_pass_xy_s4.md
    order4_fifth_push_relative_defect.md
    order4_sixth_push_bidual_t4.md
    order4_seventh_push_bidual_xy_rank1.md

  generated_scripts_and_logs/
    s4xy_case_reduction_gates.py
    s4xy_case_reduction_gates.log
    bidual_t4_cross_gates.py
    bidual_t4_cross_gates.log
    s6_suspension_model_d6.log
    extracted_from_bundles/
      ...

  source_handoff_archives/
    grothendieck_order4_handoff*.zip
```

The generated Python scripts rely on infrastructure from the corresponding handoff archive's `scripts/` directory.  To rerun them, extract the relevant handoff archive and edit the hard-coded `sys.path` line near the top of each script.

---

## 13. Minimal theorem ledger

This ledger separates conclusions by confidence/proof status.

### Closed by hand in these passes

```text
[t^4, curvilinear, s=4]
D_4=0.
```

```text
[Relative curvilinear]
Omega(I^2)=0.
```

```text
[First-order symbols]
psi chi = chi psi = 0 for any two first-order symbols.
```

```text
[Square-zero equal-characteristic bases]
S′ holds for killed-by-2 local order-4 fibers over k+m, m^2=0.
```

```text
[Bidual t^4]
S′ holds over k[u,v]/(u^2,v^2) for the t^4 fiber, modulo the explicit polarized Step-6 coefficient identity.
```

```text
[Bidual xy rank-one]
S′ holds over k[u,v]/(u^2,v^2) for W_2[F] and mu_2 x alpha_2 split fibers, modulo the explicit polarized Step-B coefficient identities.
```

### Computationally banked upstream or sanity-checked

```text
[xy, curvilinear, s=4]
Banked by v3/v4 Macaulay2 s4xygen.log.
```

```text
[t^4, bidual cross identities]
Z3/F2 gates unsat in bidual_t4_cross_gates.log.
```

```text
[xy, s=4 case reductions]
Z3/F2 gates unsat in s4xy_case_reduction_gates.log.
```

```text
[rank-one bidual triangularity]
Dual-coefficient Z3 gates unsat in order4_seventh_push_bundle logs.
```

### Still open/frontier

```text
[Bidual xy image-line]
alpha_2^2 and mu_2^2: prove T(z)=tau z and q(overline{Tg}) in (p)+(q)^2.
```

```text
[Uniform curvilinear induction]
Prove cotangent edge-tail cancellation at all depths.
```

```text
[General non-principal equal-characteristic bases]
Extend beyond square-zero and bidual bases, probably via socle induction once the relative cotangent lemma is proved.
```

---

## 14. One-page next-agent summary

The project has moved past the raw `s=4` endpoint.  The useful reductions from these passes are:

1. `t^4`, `s=4` is closed by the hand identities `aB=0`, `BC=0`, `Lambda=bB^2`.
2. `xy`, `s=4` has both a proof-shaped split-model decomposition and a later Macaulay2 bank.
3. Any relative top defect kills `I^2`; only cotangent generators matter.
4. First-order symbols are pairwise nilpotent, giving all square-zero bases.
5. The bidual base reduces to two linear equations `(B1),(B2)`.
6. Those bidual equations are solved for `t^4` and for the rank-one `xy` split fibers.
7. The remaining bidual `xy` image-line cases reduce to a clean Koszul divisibility lemma.
8. Do not pursue separate shifted-tail vanishing in curvilinear induction; a finite model shows it is false.

The next serious attack should be on the image-line bidual lemma:

```text
T(z)=tau z,
q(overline{Tg}) in (p_x,p_y)+(q_x,q_y)^2,    g=x,y,
```

for `alpha_2^2` and `mu_2^2`.  This is the smallest known live obstruction and should be much cheaper than the original S′ syzygy search.
