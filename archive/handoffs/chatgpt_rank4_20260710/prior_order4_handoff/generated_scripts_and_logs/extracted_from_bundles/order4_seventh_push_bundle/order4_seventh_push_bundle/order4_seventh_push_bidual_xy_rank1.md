# Seventh push on Grothendieck order 4: bidual `xy` rank-one branches

Date: 2026-07-09

This note continues from `grothendieck_order4_handoff_v4(2).zip`.  I did **not** close the full order-4 conjecture.  The new contribution is a hand-level closure of the first non-principal **bidual S′ equations** for the two rank-one split `xy` fibers, plus a Koszul reduction of the remaining image-line split fibers.

Throughout

\[
R=k[u,v]/(u^2,v^2),\qquad \mathfrak m=(u,v),\qquad \mathfrak m^2=(uv),
\]

and

\[
\varphi=[2]^\#=uP+vQ+uvT.
\]

The v4 handoff's bidual calculus says that, after the square-zero quotient has supplied S′, the remaining S′ problem at a cotangent generator `g` is equivalent to finding

\[
a_g,r_g,s_g\in I_H
\]

such that

\[
TPg+Qr_g+Pa_g=0,\tag{B1}
\]

\[
TQg+Q(Tg+a_g)+Ps_g=0.\tag{B2}
\]

The product class `z=xy` is already free by the product-kill lemma, so only `x,y` matter.

---

## 1. Rank-one case `W_2[F]`

Use the split model

\[
w_0x=0,\qquad w_0y=x\otimes x,\qquad w_0z=x\circ y.
\]

The first-order shape theorem gives

\[
P(x)=Q(x)=P(z)=Q(z)=0,
\]

\[
P(y)=\lambda x,\qquad Q(y)=\lambda' x.
\]

The mixed `uv` coefficient of the same Step-B coassociativity/multiplicativity calculations used in the `s=3` proof gives two facts:

\[
T(x)=\alpha x,\tag{R1}
\]

and

\[
(Ty)_y=\rho\in(\lambda,\lambda').\tag{R2}
\]

More explicitly, with directional notation

\[
\mu_P(x,x)=\lambda x,
\quad \mu_P(y,y)=\nu x,
\quad
\alpha_P=(w_Px)_{11},
\quad \delta_P=(w_Px)_{22},
\]

and similarly for `Q`, the polarized assembly formula is

\[
\rho=
\lambda\alpha_Q+
\nu\delta_Q+
\lambda'\alpha_P+
\nu'\delta_P.
\]

The `uv` coefficient of the two diagonal `(2,2)` identities polarizes the old one-variable relations

\[
\lambda\delta=0,\qquad \nu\delta=0
\]

into

\[
\lambda\delta_Q+
\lambda'\delta_P=0,
\qquad
\n\nu\delta_Q+
\n\nu'\delta_P=0.
\]

Therefore

\[
\rho=\lambda\alpha_Q+
\lambda'\alpha_P.
\]

So (R2) holds with

\[
A=\alpha_Q,\qquad A'=\alpha_P,
\qquad \rho=\lambda A+
\lambda'A'.\tag{R3}
\]

### Explicit S′ divisions

For `g=x`, both `Pg` and `Qg` vanish and (B1), (B2) are solved by

\[
a_x=r_x=s_x=0.
\]

For `g=y`, choose

\[
a_y=(\alpha+\lambda' A')y,
\qquad
r_y=\lambda A' y,
\qquad
s_y=\lambda' A y.
\]

Then (B1) is

\[
TPy+Qr_y+Pa_y
=
\lambda\alpha x+
\lambda'\lambda A'x+
\lambda(\alpha+
\lambda'A')x=0.
\]

For (B2), only the `y`-component of `Ty+a_y` is seen by `Q`, so

\[
\begin{aligned}
TQy+Q(Ty+a_y)+Ps_y
&=\lambda'\alpha x+
\lambda'(\rho+
\alpha+
\lambda'A')x+
\lambda\lambda'Ax \\
&=\bigl(\lambda'\rho+
\lambda'^2A'+
\lambda\lambda'A\bigr)x=0
\end{aligned}
\]

because \(\rho=\lambda A+\lambda'A'\).  No division by \(\lambda\) or \(\lambda'\) is used.

Thus the bidual S′ equations close in the `W_2[F]` split case.

---

## 2. Rank-one mirror `mu_2 x alpha_2`

The mirror split model has

\[
w_0x=x\otimes x,
\qquad w_0y=0,
\qquad w_0z=x\circ y+x\circ z.
\]

The first-order shape theorem gives

\[
P(y)=Q(y)=P(z)=Q(z)=0,
\]

\[
P(x)=\lambda y,
\qquad
Q(x)=\lambda' y.
\]

The same polarized calculation with `x` and `y` interchanged gives

\[
T(y)=\alpha y,
\qquad
(Tx)_x=\rho=\lambda A+
\lambda'A'.\tag{M1}
\]

The S′ divisions are the mirror of the previous case:

\[
a_y=r_y=s_y=0,
\]

and for `g=x`,

\[
a_x=(\alpha+\lambda'A')x,
\qquad
r_x=\lambda A'x,
\qquad
s_x=\lambda'Ax.
\]

The same two-line verification proves (B1), (B2).  Hence the bidual S′ equations also close in the `mu_2 x alpha_2` split case.

---

## 3. Remaining image-line cases: a Koszul reduction

The two remaining split models are the image-line cases

\[
\alpha_2\times\alpha_2,
\qquad
\mu_2\times\mu_2.
\]

Here

\[
P(g)=p_g z,
\qquad
Q(g)=q_g z
\qquad(g=x,y),
\]

and

\[
P(z)=Q(z)=0.
\]

The mixed-layer triangular fact expected from the gates is

\[
T(z)=\tau z.\tag{I0}
\]

Let

\[
p=(p_x,p_y),\qquad q=(q_x,q_y),
\]

and let \(\overline{Tg}\) denote the cotangent part of `Tg`, i.e. its projection to

\[
I_H/I_H^2=\langle x,y\rangle.
\]

For each cotangent generator `g`, the bidual equations reduce to the following linear system.  Write

\[
a_g=\tau g+h_g.
\]

Then (B1), (B2) become

\[
p(h_g)+q(r_g)=0,
\]

\[
q(\overline{Tg})+q(h_g)+p(s_g)=0.\tag{I1}
\]

So it is enough to prove the divisibility condition

\[
\boxed{
q(\overline{Tg})\in(p_x,p_y)+(q_x,q_y)^2
}
\tag{I2}
\]

for `g=x,y`.  Indeed, if

\[
q(\overline{Tg})
=p_xS_x+p_yS_y+q_x^2H_x+q_xq_yH_{xy}+q_y^2H_y,
\]

then set

\[
h_g=(q_xH_x+q_yH_{xy})x+q_yH_y y,
\]

\[
r_g=p_xH_xx+(p_xH_{xy}+p_yH_y)y,
\]

\[
s_g=S_xx+S_yy.
\]

A direct calculation gives

\[
p(h_g)+q(r_g)=0,
\]

and

\[
q(h_g)+p(s_g)=q(\overline{Tg}).
\]

Thus (I1) is solved.

So the image-line bidual branch is now reduced to the concrete mixed-layer coefficient lemma (I2), plus the already-observed triangularity (I0).  This is much smaller than the original S′ problem: it is a two-functional Koszul divisibility statement on the cotangent quotient.

---

## 4. Fresh executable checks from this pass

I ran new Z3 gates in this environment.  Macaulay2 is not installed here, so these are exact finite-ring checks rather than arbitrary-`k` Gröbner certificates.

Over the dual-coefficient test ring

\[
(\mathbb F_2[d]/d^2)[u,v]/(u^2,v^2),
\]

with `d` treated as a coefficient nilpotent rather than as a base maximal-ideal direction, I checked the rank-one mixed triangularities:

```text
W2F T(x) not in kx over dual coeff: unsat
mu2a2 T(y) not in ky over dual coeff: unsat
```

Over the exact base

\[
\mathbb F_2[u,v]/(u^2,v^2),
\]

I checked the rank-one ideal condition in the reduced-field specialization:

```text
W2F rho not in (lambda_u,lambda_v) over F2: unsat
mu2a2 rho not in (lambda_u,lambda_v) over F2: unsat
```

These checks are sanity checks for the hand proof above.  They are not being used as arbitrary-`k` certificates.

---

## 5. Current state after this push

The bidual `t^4` branch was closed in the previous pass.  This pass closes the two rank-one `xy` split branches:

\[
W_2[F],
\qquad
\mu_2\times\alpha_2.
\]

The remaining bidual `xy` work is now concentrated in the two image-line branches:

\[
\alpha_2\times\alpha_2,
\qquad
\mu_2\times\mu_2.
\]

For those, the target is no longer the full S′ system.  It is the mixed-layer divisibility

\[
q(\overline{Tg})\in(p_x,p_y)+(q_x,q_y)^2,
\qquad g=x,y,
\]

and its `P/Q` symmetric counterpart, together with `T(z) in kz`.

Proving that coefficient lemma would close the first non-principal bidual S′ step for the whole `xy` fiber.
