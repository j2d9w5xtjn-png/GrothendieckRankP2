# Fifth sustained push: relative top defects and the next induction target

Date: 2026-07-09

This note continues from `grothendieck_order4_handoff_v3.zip`.  I did not
prove the full order-4 conjecture in this pass.  I did get two proof-level
reductions that are independent of the per-`s` computations, and they sharpen
what remains for both the curvilinear and first non-principal equal-characteristic
cases.

## 0. Audit of the v3 state

The v3 archive changes the frontier.

* The `xy`, `s=4` branch is banked at arbitrary-`k'` strength: `s4xygen.log`
  ends `DONE s4xygen`, and all four split models have every target in the
  Gröbner ideal.
* The uploaded `s4t4gen.log` is not complete: it stops at `DegreeLimit 5`.
  Thus the `t^4`, `s=4` result is complete on paper from the previous hand
  notes and the v3 audit, but the specific `s4t4gen` machine-banking banner is
  not present in this archive.
* Therefore the live mathematical prize is the **relative first-order lemma**:
  if the truncation satisfies S′ and a one-socle-step lift exists, then the
  new top S′ defect also vanishes.

## 1. A formal top-defect lemma: the defect kills products

Let

\[
R'=k[\epsilon]/\epsilon^{N+1},\qquad R=k[\epsilon]/\epsilon^N,
\]

and let `A'` be a free rank-4 bialgebra over `R'` with killed-by-2 local
fiber `H`.  Let

\[
\varphi=[2]^\#=\mu\Delta.
\]

Assume S′ holds for the truncation `A=A'/\epsilon^N A'`.  By Theorem 7.1 of
the project, `A'` is killed by 4, i.e.

\[
\varphi^2=0\quad\text{on }A'.
\]

For `x in I_H`, choose a lift `\tilde x` and a division `v_x` with

\[
\epsilon v_x=\varphi(\tilde x).
\]

Then `\varphi(v_x)` is killed by `\epsilon`, hence lies in
`\epsilon^N I_{A'}`.  Write

\[
\varphi(v_x)=\epsilon^N\,\widetilde{\Omega(x)}.
\]

The relative first-order lemma is exactly the assertion

\[
\Omega=0.
\]

### Lemma 1.1

For all `a,b in I_H`,

\[
\boxed{\Omega(ab)=0.}
\]

Equivalently, the top S′ defect factors through the cotangent quotient

\[
I_H/I_H^2.
\]

### Proof

Choose lifts `\tilde a,\tilde b`.  Since `\varphi` is an algebra endomorphism,

\[
\varphi(\tilde a\tilde b)=\varphi(\tilde a)\varphi(\tilde b)
=\epsilon^2 v_a v_b.
\]

So one valid division of `\varphi(\tilde a\tilde b)` by `\epsilon` is

\[
\epsilon v_a v_b.
\]

Applying `\varphi` gives

\[
\varphi(\epsilon v_a v_b)=
\epsilon\,\varphi(v_a)\varphi(v_b)=0,
\]

because each `\varphi(v_a),\varphi(v_b)` lies in `\epsilon^N I_{A'}`.

Now

\[
\tilde a\tilde b=\widetilde{ab}+\sum_{r\ge1}\epsilon^r m_r.
\]

The contribution of each `\epsilon^r m_r` to the divided defect is zero: after
one division by `\epsilon`, applying `\varphi` gives

\[
\epsilon^{r-1}\varphi^2(m_r)=0.
\]

Therefore the divided defect of `\tilde a\tilde b` is the same as the divided
defect of `\widetilde{ab}`.  Hence `\Omega(ab)=0`.  ∎

### Consequences

For the `t^4` fiber, `I^2=(t^2,t^3)`, so the relative lemma at **every depth**
now reduces to the single generator `t`.

For the `xy` fiber, `I^2=(z)`, so the relative lemma at **every depth** reduces
to the two cotangent generators `x,y`.

This explains the repeated empirical pattern in the `s=3` and `s=4` proofs:
large blocks of the endpoint on product classes vanish for formal reasons, and
the hard work is always concentrated on the cotangent quotient.

## 2. A stronger first-order lemma: pairwise nilpotence, not just squares

Theorem I in the handoff proves that each first-order symbol `psi` satisfies
`psi^2=0`.  For square-zero multi-parameter bases one needs a stronger
statement: **two different first-order symbols compose to zero individually**.

### Lemma 2.1

Let `H` be a killed-by-2 local order-4 fiber of type `t^4` or `xy` under the
same hypotheses as Theorem I.  If `psi` and `chi` are any two first-order
symbols arising from first-order deformations of the same fiber, then

\[
\boxed{\psi\chi=\chi\psi=0.}
\]

### Proof

For the `t^4` fiber, Theorem I is stronger than `psi^2=0`: every first-order
symbol satisfies

\[
\psi(I)\subseteq I^2,
\qquad
\psi(I^2)=0.
\]

Thus any composite of two such symbols is zero.

For the `xy` fiber, pass faithfully flatly to the split height-one models, as
in the proof of Theorem I.  The four cases have a common annihilator shape:

* `alpha_2^2`: `psi(I) subset I^2`, and `psi(I^2)=0`.
* `W_2[F]`: `psi(x)=0`, `psi(y) in k x`, `psi(z)=0`; hence every symbol has
  image in `kx` and kills `kx`.
* `mu_2^2`: `psi(I) subset I^2`, and `psi(I^2)=0`.
* `mu_2 x alpha_2`: `psi(x) in k y`, `psi(y)=0`, `psi(z)=0`; hence every
  symbol has image in `ky` and kills `ky`.

In each split case, all first-order symbols have image in a fixed subspace
annihilated by all first-order symbols.  Therefore all pairwise composites
vanish.  Descent preserves the assertion. ∎

## 3. Corollary: S′ over every square-zero equal-characteristic base

Let

\[
R=k\oplus \mathfrak m,
\qquad \mathfrak m^2=0,
\]

and let `A/R` be a free rank-4 bialgebra with killed-by-2 local fiber.
Write

\[
\varphi(e_i)=\sum_\alpha m_\alpha\,\psi_\alpha(e_i),
\]

where `m_alpha` is a `k`-basis of `m`.  Choose the S′ division

\[
k_{i,\alpha}:=\psi_\alpha(e_i).
\]

Then

\[
\varphi(k_{i,\alpha})=
\sum_\beta m_\beta\,\psi_\beta\psi_\alpha(e_i)=0
\]

by Lemma 2.1.  Hence

\[
\varphi(e_i)\in \mathfrak m(\ker\varphi\cap I),
\]

for each basis element `e_i`, and therefore S′ holds.

So S′ is universal for all equal-characteristic square-zero bases, in arbitrary
embedding dimension, in the killed-by-2 local branch.

This is not the full induction, but it supplies the correct non-principal base
case for the socle strategy.

## 4. Exact bidual calculus: `k[u,v]/(u^2,v^2)`

The first genuinely non-principal socle lift is

\[
R=k[u,v]/(u^2,v^2),\qquad \mathfrak m=(u,v),\qquad \operatorname{Soc}(R)=(uv).
\]

Write the symbol expansion

\[
\varphi=uP+vQ+uvT.
\]

Modulo the socle `(uv)`, the base has square-zero maximal ideal.  By the
previous section, the truncation satisfies S′, and the first-order symbols
satisfy

\[
P^2=Q^2=PQ=QP=0.
\]

For a basis element `g`, a general division of `\varphi(g)` by `(u,v)` may be
written

\[
A_g=P g+u r_g+v a_g+uv r'_g,
\]

\[
B_g=Q g+u b_g+v s_g+uv s'_g,
\]

with

\[
a_g+b_g=Tg.
\]

The condition that both divisions lie in `ker(phi)` reduces, using pairwise
nilpotence of `P,Q`, to the two equations

\[
\boxed{TPg+Qr_g+Pa_g=0,}
\]

\[
\boxed{TQg+Qb_g+Ps_g=0.}
\]

Equivalently, after setting `b_g=Tg+a_g`, the obstruction is the solvability of

\[
TPg+Pa_g\in\operatorname{im}Q,
\]

\[
TQg+Q(Tg+a_g)\in\operatorname{im}P.
\]

This is an exact, finite-dimensional replacement for the large syzygy-coset
S′ search over the bidual base.  Lemma 1.1 further says the obstruction
vanishes automatically on `I^2`, so only cotangent generators remain:

* `t^4`: only `g=t`.
* `xy`: only `g=x,y`.

This is the cleanest next hand target I found in this pass.  It converts the
non-principal S′ problem from a raw quantified syzygy problem into a small
linear-algebra lifting problem controlled by `P,Q,T`.

## 5. Fresh computational probe toward the next curvilinear layer

I also started probing the next unbanked curvilinear identity, `s=5`, for the
`t^4` fiber over `F2[eps]/eps^5`, with `Delta_0` pinned to the `(c1,c4)` normal
form and the already-banked `D2=D3=D4=0` identities added as constraints.

The full `D5=0` endpoint did not finish in this environment.  Selected
components did close:

```text
D5(1,1) negation: unsat
D5(1,2) negation: unsat
D5(2,1) negation: unsat
D5(2,2) negation: unsat
```

The components involving product classes are predicted by Lemma 1.1; the
cotangent row is the genuinely hard part.  The hard components I did not close
in this pass include `D5(1,3)` and the remaining unharvested product-row tail.

Relevant files from this pass:

* `s5_t4_partial_probe.py`
* `s5_t4_partial_probe.log`
* `s5_t4_component_12.py/.log`
* `s5_t4_component_21.py/.log`
* `s5_t4_component_22.py/.log` if present from the local run

## 6. What remains after this pass

The full order-4 conjecture is not proved here.  The strongest new structural
reduction is:

> In any curvilinear socle lift whose truncation satisfies S′, the new top
> defect kills `I^2`.  Thus the relative first-order lemma is a cotangent-level
> problem.

For the next proof attempt, I would not attack full `D_s` matrices.  The right
objects are:

1. the single cotangent scalar/vector for `t^4`;
2. the two cotangent vectors for `xy`;
3. in the bidual case, the linear lifting equations
   `TPg+Qr_g+Pa_g=0` and `TQg+Qb_g+Ps_g=0` above.

Those are the minimal targets that can still contain the obstruction.
