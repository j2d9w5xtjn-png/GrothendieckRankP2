# Further push on Grothendieck order 4: closing the `s = 4`, `t^4` fiber branch

This note continues from `order4_sustained_attempt_note.md` and the supplied handoff.
It does **not** claim the full order-4 theorem.  It does claim a new closed
piece: under the handoff's reductions and notation, the `t^4` fiber satisfies
the full `s = 4` divided-[4] identity.

## 1. Setup and target

Work over a commutative characteristic-2 coefficient ring.  Let

\[
H=k[t]/t^4,
\]

with killed-by-2 fiber comultiplication in the normal form used in
`THEORY_order4.md` §12.6.4:

\[
w_0t=c_1(t\circ t^2)+c_1^2(t^2\circ t^3)+c_4(t^2\otimes t^2),
\quad
w_0t^2=0,
\]

\[
w_0t^3=t\circ t^2+c_1(t^2\circ t^3).
\]

Write

\[
\varphi=[2]^\#=\sum_{n\ge1}\epsilon^n\Psi_n,
\qquad
D_4=\Psi_1\Psi_3+\Psi_2^2+\Psi_3\Psi_1.
\]

The handoff reduces the `s = 4`, `t^4` endpoint to four scalar identities:

\[
aB^3=0,
\qquad
 aB^2C=0,
\qquad
 \Lambda B=bB^3,
\qquad
 \Lambda C=0.
\]

My previous continuation proved the stronger identity

\[
\boxed{aB=0.}
\]

The remaining obstruction was therefore

\[
\Lambda B=bB^3,
\qquad
\Lambda C=0.
\]

The new result below proves the stronger formula

\[
\boxed{\Lambda=bB^2}
\]

and also proves

\[
\boxed{BC=0.}
\]

Together with `aB = 0`, this closes the `s = 4`, `t^4` branch.

## 2. New auxiliary vanishings

Use the notation

\[
\beta=w_1t,
\quad
Y=w_1t^2,
\quad
\Theta=w_1t^3,
\quad
\gamma=w_2t,
\quad
V=w_2t^2,
\quad
U=w_2t^3.
\]

Write

\[
\mu_1(t,t)=pt+p_2t^2+p_3t^3,
\qquad
\mu_1(t,t^2)=qt+q_2t^2+q_3t^3,
\]

\[
u:=\mu_1(t^2,t^2)=at+bt^2+ac_1t^3,
\qquad
ac_4=0.
\]

The handoff gives

\[
B=\beta_{11}+c_4b,
\qquad
C=\beta_{12}+\beta_{21}.
\]

### Lemma 2.1: `aC = 0`

The first-order digit of

\[
\Delta(t\cdot t^2)=\Delta t\,\Delta t^2
\]

at the `(1,2)` and `(2,1)` tensor coefficients gives

\[
\Theta_{12}=q_3+ac_4+bc_1=\Theta_{21}.
\]

Now use the second-order diagonal identity for `t^2*t^2`:

\[
w_0(v)=w_1(u)+Y^2,
\qquad
v:=\mu_2(t^2,t^2).
\]

Take the sum of the `(1,2)` and `(2,1)` coefficients.  The left side cancels
because both `w_0t` and `w_0t^3` contribute symmetrically.  The `Y^2` side
also cancels in the same symmetric sum.  The middle term is

\[
\bigl(w_1(u)\bigr)_{12}+\bigl(w_1(u)\bigr)_{21}
= a(\beta_{12}+\beta_{21})
+b(Y_{12}+Y_{21})
+ac_1(\Theta_{12}+\Theta_{21}).
\]

Since `Y_{12}=Y_{21}` and `Theta_{12}=Theta_{21}`, characteristic 2 leaves

\[
\boxed{aC=0.}
\]

### Lemma 2.2: `BC = 0`

First-order coassociativity gives

\[
c_4(\beta_{12}+\beta_{21})=c_4C=0.
\]

So

\[
BC=(\beta_{11}+c_4b)C=\beta_{11}C.
\]

Now use order-2 coassociativity of `Delta(t)`.  Let

\[
\lambda=p c_1+p_3+a c_1^2.
\]

The coefficients `(1,1,2)`, `(2,1,1)`, and `(1,2,1)` give respectively

\[
E_{112}=\gamma_{13}+\Theta_{12}\beta_{13}
+c_4V_{11}+c_1V_{12}+c_1^2U_{11}+\beta_{12}\lambda=0,
\]

\[
E_{211}=\gamma_{31}+\Theta_{21}\beta_{31}
+c_4V_{11}+c_1V_{21}+c_1^2U_{11}+\beta_{21}\lambda=0,
\]

\[
E_{121}=\gamma_{13}+\gamma_{31}
+\Theta_{12}\beta_{31}+\Theta_{21}\beta_{13}
+c_1(V_{12}+V_{21})+\beta_{11}C+C\lambda=0.
\]

Adding these three equations cancels every term except

\[
\beta_{11}C+(\Theta_{12}+\Theta_{21})(\beta_{13}+\beta_{31})=0.
\]

Because `Theta_{12}=Theta_{21}`, this gives `beta_11 C = 0`.  Hence

\[
\boxed{BC=0.}
\]

## 3. Main new identity: `Lambda = bB^2`

Let

\[
\Psi_2t=Pt+Qt^2+Rt^3,
\qquad
P=pB+qC,
\]

and, as in the handoff,

\[
\sigma_2=pp_2+qp_3+\mu_2(t,t)_t,
\qquad
\sigma_3=pq_2+qq_3+\mu_2(t,t^2)_t,
\]

\[
\Lambda=(\Psi_3t)_t+Qp+Rq+B\sigma_2+C\sigma_3.
\]

The proof is a coefficient certificate.  The following displayed equations
are all direct coefficient extractions from associativity, multiplicativity of
`Delta`, and coassociativity, after the normal forms above.

### 3.1. The layer-3 diagonal substitution

Let

\[
z:=\mu_3(t^2,t^2),
\qquad
v:=\mu_2(t^2,t^2)=v_1t+v_2t^2+v_3t^3.
\]

The layer-3 diagonal identity for `t^2*t^2`, at coefficient `(2,2)`, gives

\[
c_4z_t
= v_1\beta_{22}+v_2pc_4+v_3qc_4
+a\gamma_{22}+bV_{22}+ac_1U_{22}.
\]

The possible `Gamma_1(Y,Y)` contribution is zero at `(2,2)` because of the
known shape of `Y`.

### 3.2. Associativity values for the `mu_2` t-components

The second-order associativity equations at `(t,t,t^2)`, `(t,t^2,t^2)`, and
`(t,t^2,t^3)` give

\[
\mu_2(t,t^3)_t
= v_1+ap_2+qq_2+aq_3,
\]

\[
\mu_2(t^2,t^3)_t
= ap+bq+a^2c_1+q^2+aq_2,
\]

\[
\mu_2(t^3,t^3)_t
= ab+aq.
\]

### 3.3. Multiplicativity equations used in the certificate

The coefficient `(2,2)` of the layer-2 equation
`Delta(t*t)=Delta(t)^2` gives

\[
E_V:=V_{22}+\beta_{11}^2+p\beta_{22}
+c_4\mu_2(t,t)_t+c_4pp_2+c_4p_3q+b^2c_4^2=0.
\]

The coefficient `(2,2)` of the layer-2 equation
`Delta(t*t^2)=Delta(t)Delta(t^2)` gives

\[
E_U:=U_{22}+V_{12}+V_{21}+a(\beta_{23}+\beta_{32})
+q_2(\beta_{12}+\beta_{21})+q\beta_{22}
+c_4\mu_2(t,t^2)_t+c_4pq_2+c_4qq_3=0.
\]

Also, from the first-order coefficients `(1,2)` and `(2,1)` of the same
`Delta(t*t^2)` equation,

\[
E_T^{12}:=\Theta_{12}+q_3+ac_4+bc_1=0,
\qquad
E_T^{21}:=\Theta_{21}+q_3+ac_4+bc_1=0.
\]

Finally, let

\[
E_C:=E_{112}+E_{211}=0
\]

with `E_{112}` and `E_{211}` as in Lemma 2.2.

### 3.4. Certificate identity

Expanding `(Psi_3t)_t`, substituting the diagonal identity of §3.1 and the
associativity values of §3.2, one obtains the following polynomial identity
over `F_2` in the coefficient ring variables:

\[
\Lambda+bB^2
= bE_V+aE_C+ac_1E_U+a\beta_{13}E_T^{12}+a\beta_{31}E_T^{21}+R,
\]

where, after the first-order coassociativity consequences

\[
\beta_{13}=\beta_{31},
\qquad
\beta_{23}=\beta_{32},
\qquad
\beta_{33}=\beta_{11}c_1^2,
\]

the residual is

\[
R=aC(p_3+c_1p+c_1q_2+ac_1^2)
+ab\beta_{11}c_1^2
+ac_1c_4\sigma_3.
\]

Each term in `R` is zero:

\[
aC=0,
\qquad
ac_4=0,
\qquad
 a\beta_{11}=0.
\]

The last identity follows from the previous continuation's `aB=0` together
with `B=beta_11+c_4b` and `ac_4=0`.

Therefore

\[
\boxed{\Lambda=bB^2.}
\]

## 4. Consequence for `D_4`

The handoff's `s = 4` assembly says

\[
D_4(t^2)=aB^2\Psi_1t,
\qquad
D_4(t^3)=0,
\]

and

\[
D_4(t)=aB^3t+(\Lambda B+bB^3)t^2
+(\Lambda C+ac_1B^3+aB^2C)t^3.
\]

Now:

\[
aB=0 \implies aB^3=0,\quad aB^2C=0;
\]

\[
\Lambda=bB^2 \implies \Lambda B=bB^3;
\]

\[
\Lambda C=bB^2C=bB(BC)=0.
\]

Hence

\[
\boxed{D_4=0}
\]

for the `t^4` fiber branch, universally over arbitrary characteristic-2
coefficient rings, subject to the handoff's reductions and notation.

Equivalently, the `t^4` branch has now been pushed one layer beyond the
handoff: the `s = 4` divided-[4] identity is closed.

## 5. Machine checks run during this push

Fresh checks in the supplied Z3 encoding:

- Over `F2[epsilon]/epsilon^4`, `t^4` fiber:
  - negation of `Lambda=bB^2`: `unsat`;
  - negation of `Lambda B=bB^3`: `unsat`;
  - negation of `Lambda C=0`: `unsat`;
  - negation of `aB=0`: `unsat`;
  - negation of full `D4=0`: `unsat`.
- Over `(F2[u]/u^2)[epsilon]/epsilon^4`, implemented as a fresh dual-number
  coefficient probe:
  - negation of `aB=0`: `unsat`;
  - negation of `BC=0`: `unsat`;
  - negation of `bBC=0`: `unsat`;
  - negation of `bB^2C=0`: `unsat`.
- For the `xy` fiber over `F2[epsilon]/epsilon^4`:
  - the `Gamma`-vanishing gate `X1g`: `unsat`;
  - the layer-3 `X1` analogue `X3`: `unsat`;
  - the full `D4` endpoint remains computationally expensive in the current
    encoding and was not closed in this push.

## 6. Remaining frontier

This closes the `s = 4` endpoint for the `t^4` fiber, but not the whole
order-4 problem.  The next unresolved piece is the `xy` fiber at `s = 4`,
where the two main structural gates already pass but the full endpoint still
needs either a hand assembly or a sharper computational certificate.
