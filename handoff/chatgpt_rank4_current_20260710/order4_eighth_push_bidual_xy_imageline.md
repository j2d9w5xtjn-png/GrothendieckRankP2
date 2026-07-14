# Eighth sustained push on Grothendieck order 4: bidual `xy` image-line frontier

Date: 2026-07-09

This note responds to `grothendieck_order4_handoff_v4(4).zip`.  I treated that archive as the current machine/handoff state, but also used the two later bidual notes already produced in this conversation:

* `order4_sixth_push_bidual_t4.md`: bidual `t^4` S′ equations closed by a polarized Step-6 formula.
* `order4_seventh_push_bidual_xy_rank1.md`: bidual `xy` S′ equations closed for the two rank-one split fibers, and the remaining image-line cases reduced to a Koszul containment.

I did **not** prove the full order-4 conjecture in this pass.  The new progress is at the remaining bidual `xy` image-line front:


a) I rederived and sharpened the image-line bidual reduction.

b) I found a clean explanation for why the naive stronger containment fails in the `alpha_2^2` image-line case.

c) I obtained fresh exact finite-ring evidence, including a dual-coefficient check, for the exact weaker containment that is sufficient for S′.

d) I isolated a stronger `mu_2^2` sub-branch: the probes indicate that the whole divided `[2]` image of the cotangent generators lies in the deformed product line `R·(x*y)`, which would close the `mu_2^2` bidual branch by a very short hand argument once promoted from gate to coefficient proof.

The upshot is that, after the previous `t^4` and rank-one closures, the first non-principal bidual S′ step is now concentrated almost entirely in one explicit coefficient lemma for the `alpha_2^2` image-line split fiber.

---

## 1. Bidual setup

Let

\[
R=k[u,v]/(u^2,v^2),\qquad \mathfrak m=(u,v),\qquad \mathfrak m^2=(uv),
\]

where `k` is a commutative `F_2`-algebra, and let

\[
\varphi=[2]^\#=uP+vQ+uvT.
\]

The v4 handoff's bidual calculus says that, after the square-zero quotient has supplied S′, S′ at a cotangent generator `g` is equivalent to solving

\[
TPg+Qr_g+Pa_g=0,\tag{B1}
\]

\[
TQg+Q(Tg+a_g)+Ps_g=0,\tag{B2}
\]

with

\[
a_g,r_g,s_g\in I_H.
\]

The product class `z=xy` is already free by the product-killing lemma, so in the `xy` fiber one only has to solve these equations for `g=x,y`.

The previous two bidual passes already closed:

* `t^4`, all bidual cases;
* `xy`, rank-one split cases `W_2[F]` and `mu_2 × alpha_2`.

The remaining split fibers are the image-line cases

\[
\alpha_2\times\alpha_2,
\qquad
\mu_2\times\mu_2.
\]

---

## 2. Image-line notation

In both image-line cases the first-order symbols have the common form

\[
P(x)=p_x z,
\qquad
P(y)=p_y z,
\qquad
P(z)=0,
\]

\[
Q(x)=q_x z,
\qquad
Q(y)=q_y z,
\qquad
Q(z)=0.
\]

Let

\[
p=(p_x,p_y),\qquad q=(q_x,q_y).
\]

For an element

\[
w=A x+B y+Cz,
\]

write

\[
p(w)=p_xA+p_yB,
\qquad
q(w)=q_xA+q_yB.
\]

The mixed triangularity target is

\[
T(z)=\tau z.\tag{T0}
\]

Fresh gates below show `(T0)` again in both image-line cases, over both `F_2` and the dual-coefficient test ring.

---

## 3. The Koszul reduction, in its useful form

Assume `(T0)`.  Let `g` be `x` or `y`, and write the cotangent projection of `Tg` as

\[
\overline{Tg}=A_gx+B_gy\in I_H/I_H^2.
\]

Set

\[
a_g=\tau g+h_g.
\]

Then `(B1)` becomes

\[
p(h_g)+q(r_g)=0,\tag{K1}
\]

and `(B2)` becomes

\[
q(\overline{Tg})+q(h_g)+p(s_g)=0.\tag{K2}
\]

Thus it is enough to prove the containment

\[
\boxed{
q(\overline{Tg})\in(p_x,p_y)+(q_x,q_y)^2.
}
\tag{Cq}
\]

Indeed, if

\[
q(\overline{Tg})
=p_xS_x+p_yS_y+q_x^2H_x+q_xq_yH_{xy}+q_y^2H_y,
\]

then choose

\[
h_g=(q_xH_x+q_yH_{xy})x+q_yH_yy,
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

So `(K1)` and `(K2)` are solved.

There is also the symmetric variant

\[
\boxed{
 p(\overline{Tg})\in(q_x,q_y)+(p_x,p_y)^2,
}
\tag{Cp}
\]

which is what one obtains by interchanging `P` and `Q`.  The probes below checked both forms.

---

## 4. New important finding: the stronger containment is false for `alpha_2^2`

One might hope for the stronger relation

\[
q(\overline{Tg})\in(p_x,p_y).
\tag{too strong}
\]

This is **false** already over `F_2[u,v]/(u^2,v^2)` and remains false over the dual-coefficient test ring

\[
(\mathbb F_2[d]/d^2)[u,v]/(u^2,v^2).
\]

The SAT models found by the gate have

\[
p=(0,0),
\]

but nonzero `q` and nonzero `q(\overline{Tg})`.  Therefore the quadratic `q^2` allowance in `(Cq)` is not cosmetic; it is exactly the missing room needed by the `alpha_2^2` mixed layer.

This is a useful correction to the hand strategy.  Any proof that tries to force the linear ideal `(p_x,p_y)` alone must fail.  The right target is the Koszul containment `(Cq)`.

---

## 5. Fresh exact gates

I added the script

* `bidual_xy_imageline_probe.py`

It uses the v4 `s2check.build_blocks` bialgebra encoder and pins the two image-line split fibers.  It then extracts the `u`, `v`, and `uv` coefficients of `[2]^#` as `P`, `Q`, and `T`.

### 5.1 Over `F_2[u,v]/(u^2,v^2)`

For `alpha_2^2`:

```text
P image kz and kills z fails: unsat
Q image kz and kills z fails: unsat
T(z) in kz fails: unsat
q(Tbar 1) not in (p)+q^2: unsat
q(Tbar 1) not in (p) stronger: sat
p(Tbar 1) not in (q)+p^2 sym: unsat
q(Tbar 2) not in (p)+q^2: unsat
q(Tbar 2) not in (p) stronger: sat
p(Tbar 2) not in (q)+p^2 sym: unsat
```

For `mu_2^2`:

```text
P image kz and kills z fails: unsat
Q image kz and kills z fails: unsat
T(z) in kz fails: unsat
q(Tbar 1) not in (p)+q^2: unsat
q(Tbar 1) not in (p) stronger: unsat
p(Tbar 1) not in (q)+p^2 sym: unsat
q(Tbar 2) not in (p)+q^2: unsat
q(Tbar 2) not in (p) stronger: unsat
p(Tbar 2) not in (q)+p^2 sym: unsat
```

So over the reduced coefficient field, `(Cq)` and `(Cp)` hold in both image-line branches; moreover the stronger linear containment holds in the `mu_2^2` branch but not the `alpha_2^2` branch.

### 5.2 Over the dual-coefficient ring

To avoid relying only on Boolean-idempotent coefficients, I ran the same gates over

\[
(\mathbb F_2[d]/d^2)[u,v]/(u^2,v^2),
\]

with `d` treated as a coefficient nilpotent and the split fiber pinned over `F_2[d]/d^2`.

For `alpha_2^2`:

```text
P image kz and kills z fails: unsat
Q image kz and kills z fails: unsat
T(z) in kz fails: unsat
q(Tbar 1) not in (p)+q^2: unsat
q(Tbar 1) not in (p) stronger: sat
p(Tbar 1) not in (q)+p^2 sym: unsat
q(Tbar 2) not in (p)+q^2: unsat
q(Tbar 2) not in (p) stronger: sat
p(Tbar 2) not in (q)+p^2 sym: unsat
```

For `mu_2^2`:

```text
P image kz and kills z fails: unsat
Q image kz and kills z fails: unsat
T(z) in kz fails: unsat
q(Tbar 1) not in (p)+q^2: unsat
q(Tbar 1) not in (p) stronger: unsat
p(Tbar 1) not in (q)+p^2 sym: unsat
q(Tbar 2) not in (p)+q^2: unsat
q(Tbar 2) not in (p) stronger: unsat
p(Tbar 2) not in (q)+p^2 sym: unsat
```

This is not a Macaulay2 arbitrary-`k` certificate, but it is a stronger sanity check than the original `F_2` gate.  It sees coefficient nilpotents and confirms that the quadratic ideal `(q_x,q_y)^2` is the correct replacement for the false linear containment.

---

## 6. A stronger possible route for the `mu_2^2` branch

I also added the script

* `bidual_xy_phi_in_I2_probe.py`

It tests whether

\[
\varphi(g)\in R\cdot z_A,
\qquad
z_A:=x\cdot_A y,
\]

for cotangent generators `g=x,y`.

For `mu_2^2`, the result is very strong:

```text
==== mu2mu2 F2[u,v]/(u^2,v^2) sat sat
  phi(1) not in R*zA: unsat
  phi(2) not in R*zA: unsat
  phi(3) not in R*zA: unsat
```

Over the dual-coefficient ring, the two cotangent rows also returned `unsat`:

```text
==== mu2mu2 (F2[d]/d^2)[u,v]/(u^2,v^2) sat sat
  phi(1) not in R*zA: unsat
  phi(2) not in R*zA: unsat
```

This suggests the following clean `mu_2^2` theorem.

> **Candidate lemma (`mu_2^2` line lemma).** In the bidual `mu_2^2` image-line branch,
> \[
> \varphi(x),\varphi(y)\in R\cdot (x\cdot_A y).
> \]

If this line lemma is promoted to an arbitrary-`k` coefficient proof, then the `mu_2^2` bidual S′ branch closes immediately: write

\[
\varphi(g)=a_g z_A,
\qquad a_g\in\mathfrak m.
\]

Since

\[
\varphi(z_A)=\varphi(x\cdot_A y)=\varphi(x)\varphi(y)=a_xa_yz_A^2=0
\]

over the bidual base, because `a_xa_y∈m^2` and `z_A^2∈mI`, hence the product lies in `m^3I=0`, all the evident divisions of `a_g z_A` are already in `ker phi`.

This is a much shorter route for `mu_2^2` than the general Koszul containment.

For `alpha_2^2`, the analogous line statement is false:

```text
==== a2a2 F2[u,v]/(u^2,v^2) sat sat
  phi(1) not in R*zA: sat
  phi(2) not in R*zA: sat
  phi(3) not in R*zA: unsat
```

So `alpha_2^2` genuinely needs the Koszul correction mechanism.

---

## 7. Current proof state after this pass

Combining the previous bidual work with this pass, the first non-principal bidual S′ step now stands as follows.

### Closed by hand in previous passes

* `t^4` fiber: closed, assuming the polarized Step-6 scalar identity from the sixth note.
* `xy` rank-one fibers:
  \[
  W_2[F],\qquad \mu_2\times\alpha_2,
  \]
  closed by explicit no-division S′ corrections.

### Newly sharpened in this pass

* `xy`, `mu_2^2`: a very strong line-containment route is now isolated and finite-ring checked.  The likely hand proof is to show directly from the mixed `uv` coefficient of `Delta`-multiplicativity and the `mu_2^2` pins that `phi(x),phi(y)` are multiples of `x*y` in the deformed algebra.

* `xy`, `alpha_2^2`: the exact remaining coefficient target is
  \[
  T(z)\in kz,
  \]
  and, for `g=x,y`,
  \[
  q(\overline{Tg})\in(p_x,p_y)+(q_x,q_y)^2,
  \]
  together with the symmetric `P/Q` version.  The stronger linear containment is false, so this target is sharp.

If the `alpha_2^2` containment is promoted from the finite-ring gates to an arbitrary-`k` coefficient proof, then the bidual `xy` branch closes.  Together with the previous `t^4` and rank-one closures, that would close the first non-principal bidual S′ induction step for all killed-by-2 order-4 local fibers in equal characteristic.

---

## 8. Suggested next exact Macaulay2 target

The best Macaulay2 job is now much smaller than the original bidual S′ query.  Pin the `alpha_2^2` fiber and work over the universal coefficient ring for the bidual base.  Add the bialgebra axiom ideal and the first-order image-line identities.  Then certify the following five target families:

\[
T(z)_x,
\qquad
T(z)_y,
\]

and, for `g=x,y`,

\[
q_xT(g)_x+q_yT(g)_y
\in
(p_x,p_y)+(q_x^2,q_xq_y,q_y^2),
\]

\[
p_xT(g)_x+p_yT(g)_y
\in
(q_x,q_y)+(p_x^2,p_xp_y,p_y^2).
\]

Because the right side is an ideal-containment assertion rather than a single polynomial vanishing, the clean M2 implementation should introduce temporary cofactor variables or directly reduce after adjoining the ideal generators.  This is far smaller than quantifying over the original S′ syzygy cosets.

