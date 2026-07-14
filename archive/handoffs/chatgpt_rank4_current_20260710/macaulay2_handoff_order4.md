# Handoff for CLI/Macaulay2 Agent: Order-four finite flat group-scheme search

## 0. Goal

We are investigating the claim:

\[
\text{If }G/R\text{ is a finite locally free group scheme of order }n,\text{ then }G\text{ is killed by }n.
\]

For noncommutative group schemes, “killed by \(n\)” means the \(n\)-th power map

\[
[n]\colon G\to G,\qquad g\mapsto g^n
\]

is the constant identity section. On the Hopf algebra side, if

\[
G=\operatorname{Spec}A,
\qquad
I=\ker(\varepsilon\colon A\to R),
\]

then \(G\) is killed by \(n\) iff

\[
[n]^\#(I)=0,
\]

where

\[
[n]^\#=\mu^{(n)}\circ \Delta^{(n)}\colon A\to A.
\]

For \(n=4\), the task is to search computationally for a counterexample, or to produce evidence/certificates that plausible branches contain none.

The first target is:

\[
R=\mathbb F_2[\epsilon]/(\epsilon^3),
\qquad
A=R[x,y]/(x^2,y^2).
\]

This gives a finite locally free rank-four coordinate algebra over \(R\). The group scheme is noncommutative exactly when the comultiplication \(\Delta\) is noncocommutative.

---

## 1. Mathematical background and reductions

The theoretical reductions suggest that any order-four counterexample, if one exists, should occur over a local Artinian base with perfect residue field of characteristic \(2\).

Known cases eliminate many easy possibilities:

1. If \(G\) is commutative, Deligne’s theorem implies \(G\) is killed by its order.

2. If the base is reduced, the claim is known.

3. If the residue characteristic is not \(2\), order \(4\) group schemes behave tamely.

4. If \(R\) has square-zero maximal ideal in residue characteristic \(2\), existing Schoof-type results rule out counterexamples.

Therefore, for \(n=4\), the first genuinely interesting rings are:

\[
R=\mathbb F_2[\epsilon]/(\epsilon^3)
\]

and later

\[
R=\mathbb Z/8\mathbb Z.
\]

The search should first use equal characteristic:

\[
R=\mathbb F_2[\epsilon]/(\epsilon^3).
\]

The desired branch is:

\[
G/R\text{ finite locally free of order }4,
\]

\[
G\text{ local},
\]

\[
G\text{ noncommutative},
\]

\[
G_k\text{ killed by }2,
\]

but

\[
G\text{ not killed by }4.
\]

In Hopf-algebra terms:

\[
[2]^\#(I)\subset \epsilon I
\]

but

\[
[4]^\#(I)\neq 0.
\]

---

## 2. First fixed-algebra search

Start with the fixed commutative \(R\)-algebra

\[
A=R[x,y]/(x^2,y^2).
\]

Use basis

\[
1,\quad x,\quad y,\quad xy.
\]

The augmentation is

\[
\varepsilon(x)=\varepsilon(y)=0.
\]

Thus the augmentation ideal is

\[
I=(x,y,xy).
\]

The comultiplication should satisfy

\[
\Delta(x),\Delta(y)\in A\otimes_R A,
\]

with counit normalization

\[
\Delta(x)=x\otimes 1+1\otimes x+\text{higher augmentation terms},
\]

\[
\Delta(y)=y\otimes 1+1\otimes y+\text{higher augmentation terms}.
\]

Use the ansatz

\[
\Delta(x)
=
x\otimes 1+1\otimes x+
\sum_{u,v\in\{x,y,xy\}}c^x_{u,v}\,u\otimes v,
\]

\[
\Delta(y)
=
y\otimes 1+1\otimes y+
\sum_{u,v\in\{x,y,xy\}}c^y_{u,v}\,u\otimes v.
\]

Each coefficient lies in

\[
R=\mathbb F_2[\epsilon]/(\epsilon^3),
\]

so write

\[
c^g_{u,v}=c^g_{u,v,0}+\epsilon c^g_{u,v,1}+\epsilon^2 c^g_{u,v,2},
\]

where

\[
g\in\{x,y\}.
\]

The coefficient variables

\[
c^g_{u,v,r}
\]

are variables over \(\mathbb F_2\).

Do **not** impose Boolean equations

\[
z^2-z=0
\]

unless intentionally doing an \(\mathbb F_2\)-rational brute-force search. For geometric nonexistence, leave the coefficient variables as ordinary polynomial variables over \(\mathbb F_2\). If the final ideal is the unit ideal, the branch has no solutions over \(\overline{\mathbb F}_2\).

---

## 3. Hopf equations

### 3.1 Counit

The ansatz already enforces the counit identities:

\[
(\varepsilon\otimes \operatorname{id})\Delta
=
\operatorname{id}
=
(\operatorname{id}\otimes\varepsilon)\Delta.
\]

No additional counit equations are required.

### 3.2 Algebra compatibility

Because

\[
A=R[x,y]/(x^2,y^2),
\]

we need \(\Delta\) to respect the relations:

\[
\Delta(x)^2=0,
\]

\[
\Delta(y)^2=0
\]

inside

\[
A\otimes_R A.
\]

Since \(x\) and \(y\) commute in \(A\), and \(A\otimes_R A\) is commutative, no additional commutativity equations are needed.

### 3.3 Coassociativity

Impose

\[
(\Delta\otimes \operatorname{id})\Delta(x)
=
(\operatorname{id}\otimes \Delta)\Delta(x),
\]

\[
(\Delta\otimes \operatorname{id})\Delta(y)
=
(\operatorname{id}\otimes \Delta)\Delta(y)
\]

inside

\[
A\otimes_R A\otimes_R A.
\]

Because the characteristic is \(2\), equality of two expressions is imposed by setting their sum to zero.

### 3.4 Antipode

Introduce unknowns

\[
S(x),S(y)\in I.
\]

Write

\[
S(x)
=
s^x_xx+s^x_yy+s^x_{xy}xy,
\]

\[
S(y)
=
s^y_xx+s^y_yy+s^y_{xy}xy,
\]

with

\[
s=s_0+\epsilon s_1+\epsilon^2s_2.
\]

Impose

\[
S(x)^2=0,
\qquad
S(y)^2=0.
\]

Then impose the antipode identities on generators:

\[
m(S\otimes \operatorname{id})\Delta(x)=0,
\]

\[
m(\operatorname{id}\otimes S)\Delta(x)=0,
\]

\[
m(S\otimes \operatorname{id})\Delta(y)=0,
\]

\[
m(\operatorname{id}\otimes S)\Delta(y)=0.
\]

Because the coordinate algebra is commutative, \(S\) is an algebra endomorphism once it respects the defining relations.

---

## 4. Branch conditions for a counterexample

After imposing the Hopf equations, add the following conditions.

### 4.1 Special fiber killed by \(2\)

The square map is

\[
[2]^\#=\mu\circ\Delta.
\]

Compute

\[
P_2(x)=[2]^\#(x),
\qquad
P_2(y)=[2]^\#(y).
\]

The special fiber is killed by \(2\) iff

\[
P_2(x)\equiv 0\pmod{\epsilon},
\qquad
P_2(y)\equiv 0\pmod{\epsilon}.
\]

So extract the \(\epsilon^0\)-coefficients of \(P_2(x)\) and \(P_2(y)\) in the basis

\[
1,x,y,xy,
\]

and set all of them equal to zero.

### 4.2 Noncommutativity of \(G\)

The group scheme is noncommutative iff \(\Delta\) is not cocommutative.

Compute

\[
\Delta(x)-\tau\Delta(x),
\qquad
\Delta(y)-\tau\Delta(y).
\]

In characteristic \(2\), this is

\[
\Delta(x)+\tau\Delta(x),
\qquad
\Delta(y)+\tau\Delta(y).
\]

The asymmetry coefficients are of the form

\[
c^g_{u,v}+c^g_{v,u}.
\]

Collect all asymmetry coefficients:

\[
a_1,\dots,a_N.
\]

Instead of branching into cases, introduce witness variables

\[
\lambda_1,\dots,\lambda_N
\]

and impose

\[
\lambda_1a_1+\cdots+\lambda_Na_N=1.
\]

This forces at least one asymmetry coefficient to be nonzero.

### 4.3 Not killed by \(4\)

Compute

\[
[4]^\#=[2]^\#\circ [2]^\#.
\]

Equivalently,

\[
P_4(x)=[4]^\#(x)=P_2(P_2(x)),
\]

\[
P_4(y)=[4]^\#(y)=P_2(P_2(y)).
\]

We want

\[
P_4(x)\neq 0
\quad\text{or}\quad
P_4(y)\neq 0.
\]

Extract all coefficients of \(P_4(x)\) and \(P_4(y)\) in the basis

\[
1,x,y,xy
\]

and in \(\epsilon\)-digits

\[
1,\epsilon,\epsilon^2.
\]

Let these coefficients be

\[
b_1,\dots,b_M.
\]

Introduce witness variables

\[
\mu_1,\dots,\mu_M
\]

and impose

\[
\mu_1b_1+\cdots+\mu_Mb_M=1.
\]

This forces

\[
[4]^\#(I)\neq 0.
\]

---

## 5. Macaulay2 implementation plan

Use one polynomial ring over \(\mathbb F_2\) with variables:

- \(\epsilon\),
- tensor variables \(x_1,y_1,x_2,y_2,x_3,y_3\),
- structure-constant variables for \(\Delta(x),\Delta(y)\),
- antipode variables,
- witness variables.

Use quotient relations

\[
\epsilon^3=0,
\]

\[
x_i^2=0,
\qquad
y_i^2=0.
\]

For two tensor factors:

\[
\epsilon^3=x_1^2=y_1^2=x_2^2=y_2^2=0.
\]

For three tensor factors:

\[
\epsilon^3=x_1^2=y_1^2=x_2^2=y_2^2=x_3^2=y_3^2=0.
\]

Expressions should be reduced to normal form after each major operation.

A good helper is:

```macaulay2
NF = (f, rels) -> f % (gb rels)
```

---

## 6. Pseudocode skeleton for the first branch

This is close to Macaulay2 syntax, but the CLI agent should adjust variable-generation syntax as needed.

```macaulay2
restart

kk = GF(2)

-- Indices:
-- g = 0 for x, 1 for y
-- u,v = 0,1,2 corresponding to x,y,xy
-- r = 0,1,2 epsilon digit

deltaVars =
    flatten apply(0..1, g ->
    flatten apply(0..2, u ->
    flatten apply(0..2, v ->
        apply(0..2, r -> c_(g,u,v,r)))))

sVars =
    flatten apply(0..1, g ->
    flatten apply(0..2, u ->
        apply(0..2, r -> s_(g,u,r))))

-- Allocate more witness variables than needed;
-- later use only the first N or M.
asymWitnessVars = apply(0..50, i -> la_i)
powWitnessVars  = apply(0..50, i -> mu_i)

P = kk[
    eps,
    x1,y1,x2,y2,x3,y3,
    deltaVars,
    sVars,
    asymWitnessVars,
    powWitnessVars,
    MonomialOrder => GRevLex
]

rels1 = ideal(eps^3, x1^2, y1^2)
rels2 = ideal(eps^3, x1^2, y1^2, x2^2, y2^2)
rels3 = ideal(eps^3, x1^2, y1^2, x2^2, y2^2, x3^2, y3^2)

NF = (f, rels) -> f % (gb rels)

ibasis = slot -> (
    if slot == 1 then {x1, y1, x1*y1}
    else if slot == 2 then {x2, y2, x2*y2}
    else {x3, y3, x3*y3}
)

gen = (g, slot) -> (
    if g == 0 then (
        if slot == 1 then x1 else if slot == 2 then x2 else x3
    ) else (
        if slot == 1 then y1 else if slot == 2 then y2 else y3
    )
)

coefC = (g,u,v) ->
    c_(g,u,v,0) + eps*c_(g,u,v,1) + eps^2*c_(g,u,v,2)

Delta = (g,a,b) -> (
    local Ba;
    local Bb;
    Ba = ibasis a;
    Bb = ibasis b;

    NF(
        gen(g,a) + gen(g,b)
        + sum(0..2, u -> sum(0..2, v -> coefC(g,u,v)*Ba#u*Bb#v)),
        rels3
    )
)

Dx12 = Delta(0,1,2)
Dy12 = Delta(1,1,2)

Dx23 = Delta(0,2,3)
Dy23 = Delta(1,2,3)
```

The agent should verify whether using `rels3` inside `Delta` is safe even when producing two-factor expressions. It usually is, because the unused variables do not appear.

---

## 7. Coassociativity code

```macaulay2
DeltaTensorId = f -> NF(
    sub(f, {x1 => Dx12, y1 => Dy12, x2 => x3, y2 => y3}),
    rels3
)

IdTensorDelta = f -> NF(
    sub(f, {x1 => x1, y1 => y1, x2 => Dx23, y2 => Dy23}),
    rels3
)

coassocX = NF(DeltaTensorId(Dx12) + IdTensorDelta(Dx12), rels3)
coassocY = NF(DeltaTensorId(Dy12) + IdTensorDelta(Dy12), rels3)
```

Because the field is characteristic \(2\), subtraction equals addition.

---

## 8. Algebra-compatibility code

```macaulay2
algX = NF(Dx12^2, rels2)
algY = NF(Dy12^2, rels2)
```

These encode

\[
\Delta(x)^2=0,
\qquad
\Delta(y)^2=0.
\]

---

## 9. Antipode code

```macaulay2
coefS = (g,u) ->
    s_(g,u,0) + eps*s_(g,u,1) + eps^2*s_(g,u,2)

Sgen = g -> (
    local B;
    B = ibasis 1;
    NF(sum(0..2, u -> coefS(g,u)*B#u), rels1)
)

Sx = Sgen 0
Sy = Sgen 1

SrelX = NF(Sx^2, rels1)
SrelY = NF(Sy^2, rels1)

antiL = f -> NF(
    sub(f, {x1 => Sx, y1 => Sy, x2 => x1, y2 => y1}),
    rels1
)

antiR = f -> NF(
    sub(f, {x1 => x1, y1 => y1, x2 => Sx, y2 => Sy}),
    rels1
)

antiLX = antiL Dx12
antiRX = antiR Dx12
antiLY = antiL Dy12
antiRY = antiR Dy12
```

The equations are all coefficients of:

```macaulay2
SrelX, SrelY, antiLX, antiRX, antiLY, antiRY
```

---

## 10. Power-map code

The multiplication map

\[
A\otimes_R A\to A
\]

is implemented by identifying the two tensor slots:

\[
x_1,x_2\mapsto x_1,
\qquad
y_1,y_2\mapsto y_1.
\]

```macaulay2
mult12 = f -> NF(
    sub(f, {x1 => x1, y1 => y1, x2 => x1, y2 => y1}),
    rels1
)

P2x = mult12 Dx12
P2y = mult12 Dy12

P4x = NF(sub(P2x, {x1 => P2x, y1 => P2y}), rels1)
P4y = NF(sub(P2y, {x1 => P2x, y1 => P2y}), rels1)
```

Important: verify that Macaulay2’s `sub` performs simultaneous substitution here. If there is any doubt, use an explicit ring map or temporary variables to avoid sequential substitution artifacts.

---

## 11. Extracting coefficients

The agent needs a function that, given a normal-form expression, extracts coefficients in the monomial basis.

For \(A\), the basis is:

\[
\epsilon^r x_1^a y_1^b,
\qquad
0\le r\le 2,\quad a,b\in\{0,1\}.
\]

For \(A\otimes A\), the basis is:

\[
\epsilon^r x_1^{a_1}y_1^{b_1}x_2^{a_2}y_2^{b_2},
\qquad
0\le r\le 2,
\qquad
a_i,b_i\in\{0,1\}.
\]

For \(A^{\otimes 3}\), the basis is:

\[
\epsilon^r
x_1^{a_1}y_1^{b_1}
x_2^{a_2}y_2^{b_2}
x_3^{a_3}y_3^{b_3}.
\]

In Macaulay2, one can use `coefficient(monomial, expression)` or collect terms manually after normal reduction.

The Hopf ideal should include all coefficients of:

```macaulay2
algX, algY,
coassocX, coassocY,
SrelX, SrelY,
antiLX, antiRX, antiLY, antiRY
```

Then add the branch equations.

---

## 12. Special fiber killed by \(2\)

From

```macaulay2
P2x
P2y
```

extract the coefficients of monomials

\[
x_1^a y_1^b
\]

with no \(\epsilon\)-factor, i.e. \(\epsilon^0\)-coefficients.

Set all these coefficients to zero.

This imposes

\[
P_2(x)\equiv 0\pmod{\epsilon},
\]

\[
P_2(y)\equiv 0\pmod{\epsilon}.
\]

---

## 13. Noncocommutativity witness

Define the flip map

\[
\tau\colon A\otimes A\to A\otimes A
\]

by

\[
x_1\leftrightarrow x_2,
\qquad
y_1\leftrightarrow y_2.
\]

Compute:

```macaulay2
flip12 = f -> NF(
    sub(f, {x1 => x2, y1 => y2, x2 => x1, y2 => y1}),
    rels2
)

asymX = NF(Dx12 + flip12(Dx12), rels2)
asymY = NF(Dy12 + flip12(Dy12), rels2)
```

Again, addition is subtraction in characteristic \(2\).

Extract all coefficients of `asymX` and `asymY`. Let them be:

```macaulay2
asymCoeffs = {...}
```

Introduce witness variables:

```macaulay2
la_0, ..., la_(N-1)
```

and add:

```macaulay2
sum(i -> la_i * asymCoeffs#i) + 1
```

or, equivalently in characteristic \(2\),

\[
\sum_i\lambda_i a_i -1=0
\]

which is the same as

\[
\sum_i\lambda_i a_i+1=0.
\]

This forces at least one asymmetry coefficient to be nonzero.

---

## 14. Not-killed-by-four witness

Extract all coefficients of

```macaulay2
P4x
P4y
```

in the basis

\[
\epsilon^r x_1^a y_1^b,
\qquad
0\le r\le 2,
\qquad
a,b\in\{0,1\}.
\]

Let them be:

```macaulay2
powCoeffs = {...}
```

Introduce witness variables:

```macaulay2
mu_0, ..., mu_(M-1)
```

and add:

```macaulay2
sum(i -> mu_i * powCoeffs#i) + 1
```

This forces

\[
P_4(x)\neq 0
\quad\text{or}\quad
P_4(y)\neq 0.
\]

---

## 15. Final ideal

The final ideal is

\[
J
=
J_{\mathrm{Hopf}}
+
J_{\overline G\text{ killed by }2}
+
J_{\mathrm{noncocomm}}
+
J_{[4]\neq 0}.
\]

In Macaulay2 terms:

```macaulay2
J = ideal(
    hopfCoeffs
    | specialFiberKilledBy2Coeffs
    | {noncocommWitnessEquation}
    | {notKilledBy4WitnessEquation}
)

gbJ = gb J
```

Check whether

```macaulay2
ideal(1) == ideal gbJ
```

or use the appropriate Macaulay2 method for testing whether \(1\in J\).

If

\[
J=(1),
\]

then this fixed-algebra branch contains no counterexample, even after extending the residue field.

---

## 16. Sanity checks

Before running the full search, test the machinery on known examples.

### 16.1 Noncommutative example \(\alpha_2\rtimes\mu_2\)

Over a field \(k\) of characteristic \(2\), consider

\[
A=k[x,t]/(x^2,t^2).
\]

Set

\[
\Delta(t)=t\otimes 1+1\otimes t+t\otimes t,
\]

\[
\Delta(x)=x\otimes 1+1\otimes x+t\otimes x.
\]

This is the semidirect product

\[
\alpha_2\rtimes\mu_2.
\]

The code should verify:

\[
\Delta\neq \tau\Delta,
\]

\[
[2]^\#(t)=0,
\]

\[
[2]^\#(x)=tx,
\]

and

\[
[4]^\#(t)=[4]^\#(x)=0.
\]

So this group scheme is not killed by \(2\), but it is killed by \(4\). It is **not** a counterexample, but it is an important test case because it is noncommutative of order \(4\).

### 16.2 Noncocommutative deformation killed by \(4\)

Over

\[
R=\mathbb F_2[\epsilon]/(\epsilon^3),
\]

take

\[
A=R[x,y]/(x^2,y^2)
\]

and set

\[
a=\epsilon^2.
\]

Define

\[
\Delta(y)=y\otimes 1+1\otimes y,
\]

\[
\Delta(x)=x\otimes 1+1\otimes x+a\,y\otimes x.
\]

The code should verify:

\[
\Delta\neq \tau\Delta
\]

provided \(a\neq 0\),

\[
G_k\simeq \alpha_2\times\alpha_2,
\]

\[
[2]^\#(x)=a\,xy,
\]

\[
[2]^\#(y)=0,
\]

and

\[
[4]^\#=0.
\]

This verifies that the code can detect noncocommutativity in the remaining branch while not falsely reporting a counterexample.

---

## 17. Second fixed-algebra branch: \(A=R[t]/(t^4)\)

After completing the branch

\[
A=R[x,y]/(x^2,y^2),
\]

repeat the search with

\[
A=R[t]/(t^4).
\]

Use basis

\[
1,t,t^2,t^3.
\]

The augmentation ideal is

\[
I=(t,t^2,t^3).
\]

Use the ansatz

\[
\Delta(t)
=
t\otimes 1+1\otimes t
+
\sum_{i,j=1}^3c_{i,j}t^i\otimes t^j,
\]

where

\[
c_{i,j}=c_{i,j,0}+\epsilon c_{i,j,1}+\epsilon^2c_{i,j,2}.
\]

Because \(A\) is generated by \(t\), algebra compatibility is:

\[
\Delta(t)^4=0.
\]

Then impose:

\[
(\Delta\otimes \operatorname{id})\Delta(t)
=
(\operatorname{id}\otimes \Delta)\Delta(t),
\]

the antipode equations,

special fiber killed by \(2\),

noncocommutativity,

and

\[
[4]^\#(t)\neq 0.
\]

This branch captures deformations whose special fiber resembles

\[
\alpha_4.
\]

---

## 18. General structure-constants search

If both fixed-algebra branches are empty, move to a more general search.

Let

\[
A=R\cdot 1\oplus Re_1\oplus Re_2\oplus Re_3,
\]

with augmentation

\[
\varepsilon(e_i)=0.
\]

Write the multiplication as

\[
e_ie_j=\sum_{r=1}^3m_{ij}^r e_r.
\]

Since \(A\) is the coordinate algebra of a group scheme, \(A\) is commutative:

\[
m_{ij}^r=m_{ji}^r.
\]

There is no constant term because the augmentation is multiplicative.

Write

\[
m_{ij}^r
=
m_{ij,0}^r+\epsilon m_{ij,1}^r+\epsilon^2m_{ij,2}^r.
\]

Use a comultiplication ansatz

\[
\Delta(e_i)
=
e_i\otimes 1+1\otimes e_i
+
\sum_{j,k=1}^3c_{i,j,k}e_j\otimes e_k,
\]

with

\[
c_{i,j,k}
=
c_{i,j,k,0}
+\epsilon c_{i,j,k,1}
+\epsilon^2c_{i,j,k,2}.
\]

Then impose:

1. Associativity of multiplication:

   \[
   (e_ie_j)e_k=e_i(e_je_k).
   \]

2. Commutativity of multiplication:

   \[
   e_ie_j=e_je_i.
   \]

3. Algebra compatibility:

   \[
   \Delta(e_ie_j)=\Delta(e_i)\Delta(e_j).
   \]

4. Coassociativity:

   \[
   (\Delta\otimes \operatorname{id})\Delta(e_i)
   =
   (\operatorname{id}\otimes \Delta)\Delta(e_i).
   \]

5. Antipode identities.

6. Special fiber killed by \(2\).

7. Noncocommutativity.

8. Not killed by \(4\).

For this general branch, a vector-space implementation may be better than quotient rings. Represent elements of \(A\) as length-four vectors in the basis

\[
1,e_1,e_2,e_3.
\]

Represent elements of \(A\otimes A\) as length-sixteen vectors

\[
e_i\otimes e_j,
\qquad
0\le i,j\le 3.
\]

Represent elements of \(A^{\otimes 3}\) as length-sixty-four vectors.

Define multiplication from the structure constants and then define tensor multiplication componentwise. This avoids dynamically constructing quotient rings with unknown multiplication laws.

---

## 19. Suggested special-fiber branches for general search

To keep the general search tractable, split according to the special fiber algebra.

### 19.1 Special fiber \(k[x,y]/(x^2,y^2)\)

Use basis

\[
e_1=x,
\qquad
e_2=y,
\qquad
e_3=xy.
\]

Modulo \(\epsilon\), impose:

\[
e_1^2=0,
\]

\[
e_2^2=0,
\]

\[
e_1e_2=e_3,
\]

\[
e_1e_3=0,
\]

\[
e_2e_3=0,
\]

\[
e_3^2=0.
\]

Allow only \(\epsilon\)- and \(\epsilon^2\)-corrections to these products.

### 19.2 Special fiber \(k[t]/(t^4)\)

Use basis

\[
e_1=t,
\qquad
e_2=t^2,
\qquad
e_3=t^3.
\]

Modulo \(\epsilon\), impose:

\[
e_1^2=e_2,
\]

\[
e_1e_2=e_3,
\]

\[
e_1e_3=0,
\]

\[
e_2^2=0,
\]

\[
e_2e_3=0,
\]

\[
e_3^2=0.
\]

Again, allow only \(\epsilon\)- and \(\epsilon^2\)-corrections.

---

## 20. Mixed-characteristic branch: \(R=\mathbb Z/8\mathbb Z\)

Only attempt this after the equal-characteristic search.

Do not rely naïvely on Groebner bases over \(\mathbb Z/8\mathbb Z\), because \(\mathbb Z/8\mathbb Z\) has zero divisors.

Instead digitize coefficients:

\[
a=a_0+2a_1+4a_2,
\qquad
a_i\in\mathbb F_2.
\]

For multiplication modulo \(8\):

\[
(a_0+2a_1+4a_2)(b_0+2b_1+4b_2)
\]

equals

\[
a_0b_0
+
2(a_0b_1+a_1b_0)
+
4(a_0b_2+a_1b_1+a_2b_0)
\pmod 8.
\]

The digit arithmetic must include carries correctly.

In this branch, the same Hopf equations and branch conditions apply.

If the special fiber is killed by \(2\), one expects

\[
[2]^\#(I)\subset 2I,
\]

and therefore

\[
[4]^\#(I)\subset 4I.
\]

So a counterexample over \(\mathbb Z/8\mathbb Z\) would have genuinely nonzero \(4\)-coefficient in \([4]^\#(I)\).

---

## 21. Interpretation of results

### Case A: Final ideal is the unit ideal

If

\[
J=(1),
\]

then the corresponding branch contains no counterexample, even over algebraic residue-field extensions.

The agent should save:

1. the full Macaulay2 script;
2. the final list of equations;
3. the Groebner-basis output;
4. a certificate or log showing \(1\in J\).

### Case B: Final ideal is nonunit

Do not immediately claim a counterexample.

First check whether the nonunit ideal is caused by missing equations, degenerate coordinate algebras, or witness-variable artifacts.

Verify explicitly:

\[
\Delta\text{ is an algebra map},
\]

\[
\Delta\text{ is coassociative},
\]

\[
\varepsilon\text{ satisfies both counit identities},
\]

\[
S\text{ satisfies both antipode identities},
\]

\[
A\text{ is finite free of rank }4,
\]

\[
\Delta\neq \tau\Delta,
\]

\[
G_k\text{ is killed by }2,
\]

and

\[
[4]^\#(I)\neq 0.
\]

Then try to extract an actual solution over either

\[
\mathbb F_2
\]

or a finite extension

\[
\mathbb F_{2^r}.
\]

The final counterexample should be written explicitly as:

\[
R=\mathbb F_{2^r}[\epsilon]/(\epsilon^3),
\]

\[
A=R[x,y]/(x^2,y^2)
\]

or another explicit rank-four \(R\)-algebra, with explicit formulas for:

\[
\Delta(x),\Delta(y),S(x),S(y),
\]

and explicit computations of:

\[
[2]^\#(x),\quad [2]^\#(y),
\]

\[
[4]^\#(x),\quad [4]^\#(y).
\]

One of the two \([4]\)-values must be nonzero.

---

## 22. Common false positives

Be careful about these points.

First, \(A\) is commutative. Noncommutativity of the group scheme means **noncocommutativity** of \(\Delta\), not noncommutativity of \(A\).

Second,

\[
[4]^\#
\]

is induced by the fourth-power map

\[
g\mapsto g^4.
\]

In the noncommutative setting, this map is not generally a group homomorphism. Do not confuse it with multiplication-by-four in an abelian group object.

Third, absence of \(\mathbb F_2\)-rational points is not enough. To rule out a branch geometrically, prove the ideal is the unit ideal over \(\mathbb F_2\), without adding Boolean equations.

Fourth, Boolean equations

\[
z^2-z=0
\]

should only be used for finite \(\mathbb F_2\)-rational searches. They should not be used for the main geometric search.

Fifth, when working over \(\mathbb Z/8\mathbb Z\), avoid direct Groebner computations over a ring with zero divisors unless the agent is very careful. Prefer \(2\)-adic digit arithmetic over \(\mathbb F_2\).

---

## 23. Optional theoretical subtask

If the computational branches keep returning no counterexamples, try to prove the following statement:

> Every local finite flat group scheme of order \(4\) over a local Artinian ring with perfect residue field of characteristic \(2\), whose special fiber is killed by \(2\), admits a normal finite locally free subgroup scheme of order \(2\).

If this is true, it would settle the \(n=4\) case.

Indeed, suppose

\[
1\to H\to G\to Q\to 1
\]

with

\[
|H|=|Q|=2.
\]

Every order-two finite locally free group scheme is commutative and killed by \(2\). Then for any \(g\in G\), the image of \(g^2\) in \(Q\) is trivial, so

\[
g^2\in H.
\]

Since \(H\) is killed by \(2\),

\[
g^4=(g^2)^2=e.
\]

Therefore \(G\) is killed by \(4\).

Computationally, this can be attacked by searching for Hopf ideals

\[
J\subset A
\]

such that

\[
A/J
\]

is finite free of rank \(2\) over \(R\). Normality can then be checked via the appropriate Hopf/coideal invariance conditions.

---

## 24. Recommended deliverables

The CLI/Macaulay2 agent should return:

1. The exact Macaulay2 scripts used.

2. For each branch, whether the final ideal is the unit ideal.

3. If the ideal is unit, a Groebner-basis certificate or log showing \(1\in J\).

4. If the ideal is nonunit, an explicit solution point or a clear explanation of why extraction failed.

5. Explicit formulas for \([2]^\#\) and \([4]^\#\).

6. A clear distinction between:

   \[
   \mathbb F_2\text{-rational search}
   \]

   and

   \[
   \overline{\mathbb F}_2\text{-geometric search}.
   \]

7. If a possible counterexample is found, an explicit Hopf algebra presentation:

   \[
   R,\quad A,\quad \Delta,\quad \varepsilon,\quad S,
   \]

   and explicit verification that

   \[
   [4]^\#(I)\neq 0.
   \]

The recommended search order is:

\[
R=\mathbb F_2[\epsilon]/(\epsilon^3),
\qquad
A=R[x,y]/(x^2,y^2);
\]

then

\[
R=\mathbb F_2[\epsilon]/(\epsilon^3),
\qquad
A=R[t]/(t^4);
\]

then the general structure-constants search over

\[
R=\mathbb F_2[\epsilon]/(\epsilon^3);
\]

and only afterwards the mixed-characteristic branch

\[
R=\mathbb Z/8\mathbb Z.
\]
