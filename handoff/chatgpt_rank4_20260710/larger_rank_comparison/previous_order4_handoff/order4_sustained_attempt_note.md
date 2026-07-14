# Order-4 Grothendieck question: continuation note

This note records a continuation attempt from the supplied handoff archive.
It does not claim a complete proof of the order-4 case.  It records one new
hand lemma for the `t^4` fiber at the `s = 4` frontier and the accompanying
Z3 calibration runs I was able to complete in this environment.

## Frontier after reading the handoff

The attached handoff has already reduced the order-4 killed-by-2 local branch
to the `S'` / divided-[4] identities.  In equal characteristic over
`k[epsilon]/epsilon^N`, writing

\[
\varphi=[2]^\#=\sum_{n\ge 1}\epsilon^n\Psi_n,
\]

`S'` is equivalent to

\[
\sum_{i+j=s}\Psi_i\Psi_j=0\qquad (2\leq s\leq N).
\]

The handoff proves `s = 2` and `s = 3` by hand for both local killed-by-2
fiber shapes.  The next target is

\[
D_4:=\Psi_1\Psi_3+\Psi_2^2+\Psi_3\Psi_1=0.
\]

For the `t^4` fiber, the handoff reduces `D_4=0` to four scalars:

\[
aB^3=0,
\quad aB^2C=0,
\quad \Lambda B=bB^3,
\quad \Lambda C=0.
\]

## New hand lemma: the first two scalar obstructions vanish

Use the notation of `THEORY_order4.md` §12.6.4--12.6.6.  Thus

\[
w_0t=c_1(t\circ t^2)+c_1^2(t^2\circ t^3)+c_4(t^2\otimes t^2),
\]

\[
u:=\mu_1(t^2,t^2)=a t+b t^2+a c_1t^3,
\qquad ac_4=0,
\]

\[
\beta=w_1t,
\qquad
\Psi_1t=Bt^2+Ct^3,
\qquad B=\beta_{11}+c_4b.
\]

### Lemma

For every second-order lift over `k[epsilon]/epsilon^3` of a killed-by-2
`t^4` fiber,

\[
aB=0.
\]

### Proof

It is enough to prove `a beta_11 = 0`, because `ac_4 = 0` and
`B = beta_11 + c_4 b`.

Let

\[
Y=w_1(t^2),\qquad \Theta=w_1(t^3).
\]

The epsilon-digit of `Delta(t*t)=Delta(t)^2` gives `Y`.  Its `(t,t)` entry
is zero: every term in the first-order expansion either is a `w_0` of an
element of the span of `t,t^2,t^3`, and no `w_0(t^i)` has a `t tensor t`
coefficient, or is a product term with positive degree in both tensor legs,
which cannot produce `t tensor t`.  Hence

\[
Y_{11}=0.
\]

Similarly, the epsilon-digit of `Delta(t*t^2)=Delta(t)Delta(t^2)` gives
`Theta`; the same degree check gives

\[
\Theta_{11}=0.
\]

Now take the epsilon-squared digit of

\[
\Delta(t^2\cdot_A t^2)=(\Delta t^2)^2.
\]

Writing `v = mu_2(t^2,t^2)`, the reduced non-unit part is, up to the harmless
char-2 sign convention used in the handoff,

\[
w_0(v)=w_1(u)+Y^2.
\]

Taking the `(t,t)` coefficient: the left side is zero, because `w_0` of any
linear combination of `t,t^2,t^3` has no `t tensor t` entry.  The `(t,t)`
coefficient of `Y^2` is also zero, again by degree.  Therefore

\[
0=(w_1(u))_{11}=a\beta_{11}+bY_{11}+ac_1\Theta_{11}=a\beta_{11}.
\]

Thus `aB = a beta_11 + a c_4 b = 0`.

### Consequence

The handoff's formula

\[
D_4(t^2)=aB^2\Psi_1t,
\qquad D_4(t^3)=0
\]

now gives

\[
D_4(t^2)=D_4(t^3)=0
\]

universally for the `t^4` branch.  This reduces the remaining `s = 4`,
`t^4` proof to the two scalar identities

\[
\Lambda B=bB^3,
\qquad \Lambda C=0.
\]

## Machine calibration completed here

I installed and used `z3-solver` locally in this container, then ran the
project scripts from the handoff archive.

Completed outputs:

* `s4probe.py` over `F2[epsilon]/epsilon^4`, `t^4` branch:
  * `Q0` satisfiable sanity check: `sat`.
  * `T1`: `(Psi3 t^2)_t = pP + aB^2`: `unsat`.
  * `T2`: full `s = 4` endpoint `D4 = 0`: `unsat`.
  * The script then timed out on discovery probes, so I ran a smaller tail probe.
* Tail probe over `F2[epsilon]/epsilon^4`, `t^4` branch:
  * `aB != 0`: `unsat`.
  * `aB^2 != 0`: `unsat`.
  * `aB^3 != 0`: `unsat`.
  * `aB^2C != 0`: `unsat`.
* First-order contrast:
  * over `F2[epsilon]/epsilon^2`, `a beta_11 != 0`: `sat`;
  * over `F2[epsilon]/epsilon^3`, `a beta_11 != 0`: `unsat`.

The last contrast is the useful conceptual signal: the dangerous product
`a beta_11` is a genuine first-order possibility, but it is killed by the
existence of a second-order lift.  This is exactly the kind of relative
first-order mechanism the remaining proof needs.

Further calibration over `F2[epsilon]/epsilon^4` found

\[
\Lambda=bB^2
\]

in the exact-F2 model (`Lambda + bB^2 != 0` was `unsat`), and also
`Lambda B + bB^3 = 0`, `Lambda C = 0`.  I did not prove these universally;
they are now the most natural next hand lemmas for the `t^4`, `s = 4` case.

## Remaining target

A clean next theorem would be:

\[
\Lambda=bB^2,
\qquad \Lambda C=0
\]

for arbitrary coefficient rings, in the notation above.  Together with
`aB = 0`, this would close `s = 4` for the `t^4` branch.  The analogous `xy`
branch still needs the layer-3 `X1` endpoint; I was able to confirm the
Gamma-vanishing gate over `F2[epsilon]/epsilon^4`, but the full endpoint did
not finish in this session.
