# Grothendieck order-4 project: another sustained pass

Date: 2026-07-09  
Target: the open hand target in `grothendieck_order4_handoff_v2.zip`, namely the `xy`-fiber at the `s=4` divided-[4] layer.

## 0. Status after auditing the v2 handoff

The handoff has absorbed and audited the previous two notes.  The `t^4` branch at `s=4` is now on paper modulo the handoff's reductions: the prior `aB=0` mechanism plus the later `Lambda=bB^2` and `BC=0` package close the four scalar obstructions in THEORY §12.6.6(e).

The remaining natural hand target is therefore the `xy` fiber at

\[
D_4 := \Psi_1\Psi_3+\Psi_2^2+\Psi_3\Psi_1=0.
\]

The v2 archive reports a Z3 endpoint gate `X2g` over `F2[eps]/eps^4`, so the identity is true at that finite coefficient ring.  What was missing is a proof-shaped decomposition that can be transported to arbitrary coefficient algebras.

This pass produced such a decomposition.  I do **not** claim it is already a complete arbitrary-`k'` proof, because the final coefficient-extraction lemmas below still need to be written out or replaced by a Groebner membership certificate.  But the endpoint is now reduced, case by case, to small matrix identities, and I verified every displayed identity by fresh F2 gates.

New artifacts:

* `s4xy_case_reduction_gates.py`
* `s4xy_case_reduction_gates.log`
* `s4xy_rank1_gates.py`
* `s4xy_rank1_gates.log`

## 1. Universal notation for the `xy` branch

Let

\[
H=k'[x,y]/(x^2,y^2),\qquad z=xy,
\]

with basis `x,y,z` of the augmentation ideal.  Write

\[
N:=\Psi_1,
\qquad M:=\Psi_2,
\qquad L:=\Psi_3.
\]

The target is the endomorphism identity

\[
D_4=NL+M^2+LN=0.
\]

The lower identities already banked in the handoff are

\[
N^2=0,
\qquad NM+MN=0.
\]

The four split fiber models are those of THEORY §12.4.1:

\[
\alpha_2^2,
\quad W_2[F],
\quad \mu_2^2,
\quad \mu_2\times\alpha_2.
\]

## 2. Cases with `N(I) \subseteq k'z`: `alpha_2^2` and `mu_2^2`

In the two cases

\[
\alpha_2\times\alpha_2,
\qquad \mu_2\times\mu_2,
\]

one has

\[
N(x)=c_xz,
\qquad N(y)=c_yz,
\qquad N(z)=0.
\]

Equivalently, for the linear functional

\[
\ell(ax+by+cz)=ac_x+bc_y,
\]

we have

\[
N(v)=\ell(v)z.
\]

The fresh reduction is the following operator package.

### Lemma A: image-line operator package

For `alpha_2^2`,

\[
M(z)\in k'z.
\]

For `mu_2^2`, the stronger identities hold:

\[
M(z)=0,
\qquad L(z)=0.
\]

For both cases, for every basis element `g in {x,y,z}` and for the `x,y` components,

\[
(M^2g)_{x,y}+\ell(g)(Lz)_{x,y}=0.
\]

For the `z` component,

\[
(M^2g)_z+\\ell(g)(Lz)_z+
\ell(Lg)=0.
\]

These identities immediately imply `D4=0`, since

\[
NL(g)=\ell(Lg)z,
\qquad LN(g)=\ell(g)Lz.
\]

### Fresh gates for Lemma A

For `alpha_2^2` over `F2[eps]/eps^4`:

```text
[Q0 axioms sat] -> sat
[N has image in kz and N(z)=0] -> unsat
[M(z) in kz] -> unsat
[M^2(g)_{x,y} + N(g)*L(z)_{x,y}=0] -> unsat, for g=x,y,z
[z-component identity for input g] -> unsat, for g=x,y,z
[endpoint D4=0] -> unsat
```

For `mu_2^2` over `F2[eps]/eps^4`:

```text
[Q0 axioms sat] -> sat
[N has image in kz and N(z)=0] -> unsat
[M(z)=0] -> unsat
[L(z)=0] -> unsat
[M^2(g)_{x,y} + N(g)*L(z)_{x,y}=0] -> unsat, for g=x,y,z
[z-component identity for input g] -> unsat, for g=x,y,z
[endpoint D4=0] -> unsat
```

So the two “image in `kz`” cases are no longer a black-box endpoint: they are reduced to one clean operator lemma.

## 3. The rank-one cases: `W_2[F]` and `mu_2 x alpha_2`

These are the cases where coassociativity was already load-bearing at `s=3`.  The new decomposition makes the `s=4` cancellation transparent.

### 3.1 The `W_2[F]` case

Here

\[
w_0x=0,
\qquad w_0y=x\otimes x,
\qquad w_0z=x\circ y.
\]

The lower-layer proof gives

\[
N(x)=0,
\qquad N(y)=\lambda x,
\qquad N(z)=0,
\]

where

\[
\lambda=\mu_1(x,x)_x.
\]

Write

\[
\nu:=\mu_1(y,y)_x,
\qquad
\alpha:=(w_1x)_{11},
\qquad
\delta:=(w_1x)_{22},
\]

and

\[
\rho:=\lambda\alpha+\nu\delta.
\]

Let

\[
m:=\mu_1(x,y)_y,
\qquad
\chi:=(M y)_z.
\]

The new normal form is:

\[
M(x)=\rho x,
\qquad
(M y)_y=\rho,
\qquad
M(z)=m\lambda x.
\]

The new `s=4` coefficient identities are:

\[
\lambda(Lx)_y=\rho^2,
\]

\[
\lambda(Lx)_z=\rho\chi,
\]

\[
(Lz)_y=m\rho,
\]

\[
\lambda\big((Ly)_y+(Lx)_x+m\chi\big)=0.
\]

These imply `D4=0` by direct matrix multiplication.

Indeed, for `x`,

\[
D_4(x)=N(Lx)+M^2x=ig(\lambda(Lx)_y+\rho^2\big)x=0.
\]

For `z`,

\[
D_4(z)=N(Lz)+M^2z=ig(\lambda(Lz)_y+m\lambda\rho\big)x=0.
\]

For `y`, write

\[
M(y)=a x+\rho y+\chi z.
\]

Then

\[
M^2y=m\lambda\chi x+\rho^2 y+\rho\chi z,
\]

and

\[
L(Ny)=\lambda Lx,
\qquad N(Ly)=\lambda(Ly)_y x.
\]

Thus the `y`, `z`, and `x` components of `D4(y)` are respectively

\[
\rho^2+\lambda(Lx)_y,
\]

\[
\rho\chi+\lambda(Lx)_z,
\]

and

\[
\lambda\big((Ly)_y+(Lx)_x+m\chi\big),
\]

all zero by the displayed identities.

#### Where the identities come from

The first three normal-form identities are layer-2 refinements of the `s=3` proof:

* `M(x)=rho x` is the old `B6` assembly sharpened.
* `(M y)_y=rho` follows by combining `X2` at `x` and `y`: if
  `mu2(x,x)_y=d2`, then `d2=lambda alpha`; the apparent extra term
  `nu delta` is killed by the `X2`-at-`y` entry `nu delta=0`.
* `M(z)=m lambda x` is the multiplicativity formula at `z=xy`.

The first `L` identity can also be read directly from the layer-3 diagonal identity at `x` plus the layer-2 diagonal identities:

\[
(Lx)_y=(\mu_2(w_1x))_y
      =\alpha\mu_2(x,x)_y+
        \delta\mu_2(y,y)_y
      =\lambda\alpha^2,
\]

because the terms containing `delta` are killed by `lambda delta=nu delta=0`; hence

\[
\lambda(Lx)_y=\lambda^2\alpha^2=\rho^2.
\]

The remaining two identities are the expected order-3 coassociativity extractions, i.e. the `E_{112}/E_{211}/E_{121}` pattern one layer above the `s=3` proof.  The F2 gates below identify exactly what needs to be written out by hand.

### Fresh gates for `W_2[F]`

```text
[Q0 axioms sat] -> sat
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

### 3.2 The `mu_2 x alpha_2` case

This is the `x/y`-dual rank-one case.  Here

\[
w_0x=x\otimes x,
\qquad w_0y=0,
\qquad w_0z=x\circ y+x\circ z.
\]

The lower-layer proof gives

\[
N(x)=\lambda y,
\qquad N(y)=0,
\qquad N(z)=0,
\]

where

\[
\lambda=\mu_1(x,x)_y.
\]

Write

\[
\nu:=\mu_1(y,y)_y,
\qquad
\alpha:=(w_1y)_{11},
\qquad
\delta:=(w_1y)_{22},
\qquad
\rho:=\lambda\alpha+\nu\delta,
\]

and

\[
m:=\mu_1(x,y)_x,
\qquad
\chi:=(M x)_z.
\]

The normal form is:

\[
M(y)=\rho y,
\qquad
(Mx)_x=\rho,
\qquad
M(z)=m\lambda y.
\]

The `s=4` identities are:

\[
\lambda(Ly)_x=\rho^2,
\]

\[
\lambda(Ly)_z=\rho\chi,
\]

\[
(Lz)_x=m\rho,
\]

\[
\lambda\big((Lx)_x+(Ly)_y+m\chi\big)=0.
\]

The same matrix multiplication as above, with `x` and `y` interchanged, gives `D4=0`.

### Fresh gates for `mu_2 x alpha_2`

```text
[Q0 axioms sat] -> sat
[Psi1: x->lambda y, y->0, z->0] -> unsat
[Psi2(y)=rho y] -> unsat
[(Psi2 x)_x=rho] -> unsat
[Psi2(z)=m lambda y] -> unsat
[lambda (Psi3 y)_x=rho^2] -> unsat
[lambda (Psi3 y)_z=rho (Psi2 x)_z] -> unsat
[(Psi3 z)_x=m rho] -> unsat
[lambda((Psi3 x)_x+(Psi3 y)_y+m(Psi2 x)_z)=0] -> unsat
[endpoint D4=0] -> unsat
```

## 4. What this pass actually proves, and what remains

This pass proves the **linear algebra assembly** of the `xy`, `s=4` endpoint in all four split cases.  It also identifies the small coefficient-extraction package that must be promoted from F2 gates to arbitrary-`k'` hand proof or ideal membership.

What remains before I would bank the arbitrary-coefficient theorem:

1. Write out Lemma A for the two image-line cases from the layer-3 multiplicativity/diagonal equations and order-3 coassociativity.
2. Write out the two coassociativity extractions in the rank-one cases:

\[
\lambda(Lx)_z=\rho(M y)_z,
\qquad
\lambda((Ly)_y+(Lx)_x+m(M y)_z)=0
\]

for `W_2[F]`, and the `x/y`-dual pair for `mu_2 x alpha_2`.

3. Preferably run a Groebner membership job over the polynomial coefficient ring for exactly the displayed identities, not the full endpoint.  This should be much lighter than the crashed/partial `s4gen.m2` endpoint job, because the new targets are scalar-normal-form identities rather than all nine raw components.

If those coefficient extractions are completed, then the `xy` branch at `s=4` joins the already-closed `t^4` branch, yielding S' over `k'[eps]/eps^4` and killed-by-4 over `k'[eps]/eps^5` for equal-characteristic curvilinear bases with killed-by-2 local fiber.

## 5. Audit notes

* `s4probe.log` really does contain the full `xy` endpoint gate `X2g: s=4 endpoint D4=0 -> unsat` over `F2[eps]/eps^4`.
* `s4gen.log` is **not** a successful arbitrary-`k'` certificate in the archive: it first crashed, then relaunched, and its visible log stops during `DegreeLimit 4` after all targets remained open at `DegreeLimit 3`.
* `s2check_np2.log` contains good initial non-principal rows, but the post-crash `--gaponly` relaunch line is malformed in the captured log.  The FatPoint3/xy gap row should not be cited as closed from this archive alone.

