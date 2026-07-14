# Authoritative handoff: the length-ten rank-four counterexample

**Date:** 2026-07-11  
**Workspace:** /Users/akhilmathew/Library/CloudStorage/Dropbox/FiniteFlatGroupSchemes  
**Audience:** the next Codex agent or mathematically capable collaborator  
**Status:** authoritative for the length-ten construction. It supersedes the
mathematical status in older top-level handoffs which say that no rank-four
counterexample had been found.

## 0. Executive state

There is an explicit, independently audited finite locally free group scheme
\(G\) of rank \(4\) over a characteristic-\(4\), length-\(10\) local
Gorenstein ring \(R\) such that

\[
[4]\ne e,\qquad [8]=e.
\]

Equivalently, the fourth-power word on \(G\) is nontrivial even though the
rank is four. This is the counterexample sought in this workspace.

The clean paper-level account is:

- **TeX:** notes/RANK4_LENGTH10_COUNTEREXAMPLE_AND_CONCEPTUAL_EXPLANATION_2026-07-10.tex
- **PDF:** notes/RANK4_LENGTH10_COUNTEREXAMPLE_AND_CONCEPTUAL_EXPLANATION_2026-07-10.pdf

The PDF is currently 23 pages. It includes the base and Hopf tables, the
power computation, inverse-system origin, conditional chart-minimality,
complete-intersection and functor-of-points descriptions, the dual measure
algebra, a minimal embedding in \(\mathrm{GL}_3\), all rank-two subgroups
over \(R\), and the deformation tower.

The fastest exact verification is:

    python3 scripts/verify_rank4_length10_counterexample_20260710.py
    python3 scripts/audit_rank4_descriptions_20260710.py
    python3 scripts/audit_rank4_subgroups_deformations_20260711.py

These are self-contained, dependency-free, bounded Python computations. The
largest base enumeration has \(1024\) elements. They finish in seconds with
modest memory.

## 1. Nonnegotiable workspace and compute rules

Read **AGENTS.md** before doing anything.

1. This directory is not presently a Git worktree. Do not assume that Git
   status, commits, or history are available.
2. Preserve unrelated user files.
3. Use apply_patch for textual source edits.
4. Substantive Macaulay2 calculations must go through Slurm and the prescribed
   Apptainer image. Do not run substantive M2 directly on a login node.
5. Local Python checks are allowed, but keep searches bounded and memory-safe.
6. A timeout, OOM, crash, malformed log, absent footer, or nonzero exit is
   inconclusive. None is negative mathematical evidence.
7. Do not modify a source associated with a running job.
8. Old logs record some short M2 runs performed before the current RCC policy
   was installed. Reproduction now must follow **AGENTS.md**.

Begin with the three small Python auditors above. This handoff does not
authorize launching broad searches.

## 2. Five-minute recovery procedure

From the workspace root:

    python3 scripts/verify_rank4_length10_counterexample_20260710.py

Expected headline output:

    BASE PASS: local characteristic 4; |R|=2^10; length 10
    HOPF PASS: algebra, counit, multiplicativity, coassociativity
    POWER IDENTITY PASS: psi^2=2psi for psi=[2]^#-unit*epsilon
    [4]^#(e1)=(s)e3
    [4]^#(e2)=0
    [4]^#(e3)=0
    [8]^#=unit*epsilon PASS
    NONCOMMUTATIVE PASS: Delta(e1) is not cocommutative

Then run:

    python3 scripts/audit_rank4_descriptions_20260710.py
    python3 scripts/audit_rank4_subgroups_deformations_20260711.py

Expected additional headlines:

    GL3 PASS: quotient matrix invertible; e1,e2,e3 recovered exactly
    DUAL HOPF PASS: all displayed products and coproducts
    SUBGROUP CLASSIFICATION PASS: exactly 16 normalized Hopf quotients
    ADJOINT PASS: H_x normal exactly after killing d
    DEFORMATION PASS: lengths 6 -> 8 -> 10 with square-zero steps
    COMMUTATIVE QUOTIENT PASS: kill d and y+z (length 4)

Compile the paper with:

    cd notes
    latexmk -pdf -interaction=nonstopmode -halt-on-error \
      RANK4_LENGTH10_COUNTEREXAMPLE_AND_CONCEPTUAL_EXPLANATION_2026-07-10.tex

There should be no undefined references, overfull boxes, or fatal errors.
Some installations may report harmless underfull boxes in the audit
longtable.

## 3. The exact base ring

Define

\[
R=(\mathbf Z/4)[x,y,z,d]/J
\]

with

\[
J=(2x,2y,2d,x^2-2,z^2-2,y^2,yz,zd,d^2-xd,
yd-xz-xy).
\]

Use

\[
\xi=xz,\qquad \eta=xd,\qquad \omega=xy,\qquad
\sigma=2z,\qquad q=x(y+z)=\xi+\omega.
\]

Important exact consequences are

\[
x^2=z^2=2,\qquad yd=q,\qquad d^2=\eta,\qquad
qx=dq=\omega d=\sigma.
\]

Every element has a unique additive normal form

\[
a+bz+\alpha x+\beta y+\gamma d+\lambda\xi+\mu\eta+\nu\omega
\]

with \(a,b\in\mathbf Z/4\) and all Greek coefficients in \(\mathbf F_2\).
Thus

\[
R_{\mathrm{add}}\simeq(\mathbf Z/4)^2\oplus(\mathbf Z/2)^6,
\qquad |R|=2^{10}.
\]

The maximal ideal and its powers are

\[
\mathfrak m=(x,y,z,d),\qquad
\mathfrak m^2=\mathbf F_2\{2,\xi,\eta,\omega,\sigma\},
\]

\[
\mathfrak m^3=\mathbf F_2\sigma,\qquad \mathfrak m^4=0.
\]

The socle is exactly \(\mathbf F_2\sigma\). Hence \(R\) is local
Gorenstein, has Hilbert function \((1,4,4,1)\), length \(10\), cardinality
\(1024\), and characteristic exactly \(4\).

The inverse-system description uses

\[
\mathcal G=X^{[2]}Z+XYD+YD^{[2]}+Z^{[3]}.
\]

Its first catalecticant has rank four. The mixed-characteristic
identifications are \(Z^\vee=2\) and \(s=2Z\). This explains the ring
multiplication and Hilbert function.

## 4. The rank-four Hopf algebra

Let

\[
A=R\{1,e_1,e_2,e_3\}
\]

with \(\epsilon(e_i)=0\). Multiplication is

\[
\begin{aligned}
e_1^2&=xe_1+ye_2,& e_1e_2&=e_3,& e_1e_3&=xe_3,\\
e_2^2&=ze_2,& e_2e_3&=ze_3,& e_3^2&=\xi e_3.
\end{aligned}
\]

The coproduct is

\[
\Delta(e_1)=e_1\otimes1+1\otimes e_1
+xe_1\otimes e_1+(y+z)e_2\otimes e_1+q e_3\otimes e_1,
\]

\[
\Delta(e_2)=e_2\otimes1+1\otimes e_2
+d e_2\otimes e_1+(y+z)e_2\otimes e_2+q e_2\otimes e_3,
\]

\[
\begin{aligned}
\Delta(e_3)={}&e_3\otimes1+1\otimes e_3
+e_1\otimes e_2+e_2\otimes e_1+x e_1\otimes e_3\\
&+(2+\eta)e_2\otimes e_1+q e_2\otimes e_2
+\sigma e_2\otimes e_3\\
&+(x+d)e_3\otimes e_1+(y+z+\sigma)e_3\otimes e_2
+q e_3\otimes e_3.
\end{aligned}
\]

Do not omit the initial \(e_2\otimes e_1\) term in the last formula.
Together with the correction \((2+\eta)e_2\otimes e_1\), its total
coefficient is \(3+\eta\).

The antipode is

\[
\begin{aligned}
S(e_1)&=e_1+\omega e_2+(y+z)e_3,\\
S(e_2)&=e_2+d e_3,\\
S(e_3)&=(3+\eta)e_3.
\end{aligned}
\]

Associativity, counitality, multiplicativity of \(\Delta\),
coassociativity, and both convolution antipode equations have been checked
coefficient by coefficient.

The special fiber is

\[
A/\mathfrak mA\simeq
\mathbf F_2[e_1,e_2]/(e_1^2,e_2^2),\qquad e_3=e_1e_2,
\]

with the usual coproduct of \(\alpha_2^2\).

## 5. The decisive power calculation

Let

\[
\phi=m_A\circ\Delta=[2]^\#,\qquad
P=\iota\epsilon,\qquad \psi=\phi-P.
\]

Here \([n]\) is the \(n\)-th power **word map** on a possibly
noncommutative group scheme. It need not be a group homomorphism.
\([n]^\#\) is its contravariant map on coordinate rings.

Direct contraction gives

\[
\begin{aligned}
\phi(e_1)&=\omega e_2+(y+z+\sigma)e_3,\\
\phi(e_2)&=d e_3,\\
\phi(e_3)&=0.
\end{aligned}
\]

Therefore

\[
[4]^\#(e_1)=\omega d\,e_3=xyd\,e_3=\sigma e_3\ne0,
\]

\[
[4]^\#(e_2)=[4]^\#(e_3)=0.
\]

The equality \(\sigma\ne0\) is exact: it is the nonzero socle generator in
the explicit 1024-element ring.

The identity

\[
\psi^2=2\psi
\]

holds in the small example and on the audited universal cubic base. Since
\(\psi^3=4\psi=0\) and \(P\psi=\psi P=0\),

\[
[8]^\#=P.
\]

Noncommutativity is immediate because the coefficient of
\(e_2\otimes e_1\) in \(\Delta(e_1)\) is \(y+z\ne0\), while that of
\(e_1\otimes e_2\) is zero.

## 6. Equivalent and conceptual descriptions

### 6.1 Relative complete intersection and points

\[
A\simeq R[U,V]/(U^2-xU-yV,\;V^2-zV),
\]

with \(e_1=U\), \(e_2=V\), \(e_3=UV\). Thus \(A\) is an iterated pair of
monic quadratic covers and a relative Gorenstein complete intersection.

For every \(R\)-algebra \(T\),

\[
G(T)=\{(u,v)\in T^2:u^2=xu+yv,\ v^2=zv\}.
\]

Put \(w=uv\). The first two product coordinates are

\[
\begin{aligned}
u''&=u+u'+u'(xu+(y+z)v+quv),\\
v''&=v+v'+v(du'+(y+z)v'+qu'v').
\end{aligned}
\]

The inverse is

\[
(u,v)^{-1}=(u+\omega v+(y+z)uv,\;v+duv).
\]

### 6.2 Dual measure algebra

The finite dual \(D=A^\vee\) is a cocommutative coalgebra but a
noncommutative algebra. With \(E_i\) dual to \(e_i\),

\[
E_1E_2=E_3,\qquad
E_2E_1=(y+z)E_1+dE_2+(3+\eta)E_3.
\]

The full product, coproduct, and antipode tables are in the main TeX,
Section “The dual measure Hopf algebra,” and are independently verified by
**scripts/audit_rank4_descriptions_20260710.py**.

Do not call \(\operatorname{Spec}(D)\) the Cartier dual: \(D\) is not
commutative.

### 6.3 Minimal faithful linear representation

Right translation descends from \(A\) to

\[
Q=A/R1=R\{\bar e_1,\bar e_2,\bar e_3\}.
\]

For \(g=(u,v,w)\), put

\[
\begin{aligned}
K&=1+du+(y+z)v+qw,\\
L&=(3+\eta)u+qv+\sigma w,\\
M&=1+(x+d)u+(y+z+\sigma)v+qw.
\end{aligned}
\]

Then

\[
\rho(g)=
\begin{pmatrix}
1+xu&0&v+xw\\
(y+z)u&K&L\\
qu&0&M
\end{pmatrix}.
\]

This is a closed immersion \(G\hookrightarrow\mathrm{GL}_{3,R}\). Direct
recovery uses

\[
\mathcal U=e_2+xe_3,\qquad
\mathcal V=(3+\eta)e_1+qe_2+\sigma e_3.
\]

Since \(qx=\sigma\) and \((3+\eta)^2=1\),

\[
e_1=(3+\eta)(\mathcal V-q\mathcal U).
\]

If \(t=xe_1\), then \(t^4=0\), so

\[
e_2=(1-t+t^2-t^3)\mathcal U,\qquad e_3=e_1e_2.
\]

Hence the matrix coefficients generate \(A\).

Dimension three is minimal. A hypothetical \(\mathrm{GL}_2\) immersion
would specialize to \(\alpha_2^2\hookrightarrow
\mathrm{GL}_{2,\mathbf F_2}\), producing two independent commuting
square-zero \(2\times2\) matrices. Every square-zero matrix commuting with a
fixed nonzero one is its scalar multiple.

The representation has invariant line \(R\bar e_2\). On the special fiber
the line is trivial; the two-dimensional quotient sees only \(v\), while
the extension entry \(L\bmod\mathfrak m=u\) records the other direction.
This is a module filtration, not a subgroup filtration.

## 7. Rank-two subgroups and absence of a normal filtration

The simplest subgroup \(H_x\subset G\) is

\[
A\longrightarrow B_x=R[T]/(T^2-xT),\qquad
e_1\mapsto T,\quad e_2,e_3\mapsto0,
\]

\[
\Delta(T)=T\otimes1+1\otimes T+xT\otimes T,\qquad S(T)=T.
\]

It is the self-dual Oort–Tate group with parameter pair \((x,x)\) in the
normalization used here. It is killed by two:

\[
[2]^\#(T)=(2+x^2)T=0.
\]

The left coset scheme is

\[
H_x\backslash G\simeq\operatorname{Spec}R[V]/(V^2-zV).
\]

The projection \(G\to H_x\backslash G\) is a left \(H_x\)-torsor.  The
coset scheme itself is not a quotient group over \(R\), because \(H_x\) is
not normal.

There are exactly sixteen rank-two finite locally free closed subgroups
over \(R\). For
\((\epsilon,\alpha,\beta,\gamma)\in\mathbf F_2^4\), put

\[
\begin{aligned}
r&=\epsilon d+\alpha\eta+\beta q+\gamma\sigma,\\
t&=x+\epsilon q+\alpha\sigma,\\
s&=\epsilon\eta+(\epsilon+\beta)\sigma.
\end{aligned}
\]

The Hopf quotient sends

\[
e_1\mapsto f,\qquad e_2\mapsto rf,\qquad e_3\mapsto sf
\]

into

\[
B_t=R[f]/(f^2-tf),\qquad
\Delta(f)=f\otimes1+1\otimes f+t f\otimes f.
\]

All sixteen are abstractly isomorphic to \(H_x\), have distinct embeddings,
and reduce to the same \(\alpha_2\)-line. The special fiber itself has more
subgroups; the count is over \(R\), not after arbitrary non-faithfully-flat
base change.

None is normal. A uniform certificate is

\[
(q_r\otimes\mathrm{id})\operatorname{Ad}^*(e_3-se_1)
=f\otimes(\eta+\epsilon\sigma)e_2\ne0.
\]

Structurally, every rank-two finite locally free group is killed by two. If
\(H\triangleleft G\) had rank two, \(G/H\) would have rank two, so \(g^2\)
would land in \(H\), forcing \(g^4=1\). This contradicts
\([4]^\#(e_1)=\sigma e_3\ne0\).

Therefore \(G\) has rank-two subgroup chains but no rank-two quotient group,
no normal/composition filtration, and no normal rank-two subgroup after
faithfully flat base change.

## 8. Deformation-theoretic explanation

### 8.1 The maximal-ideal filtration

Modulo \(\mathfrak m\), \(G=\alpha_2^2\). Modulo \(\mathfrak m^2\), the
first reduced doubling/skew symbol is

\[
N(\bar e_1)=(\bar y+\bar z)e_3,\qquad
N(\bar e_2)=\bar d\,e_3.
\]

The coefficients are independent, so no nonzero tangent line can be a
cocommutative rank-two quotient direction. Normal filtrability already
fails to first order.

The fourth-power class first appears in
\(\mathfrak m^3=\mathbf F_2\sigma\):

\[
\operatorname{in}_3(\psi^2)=\operatorname{in}_2(2)\,N.
\]

Killing \(\sigma\) gives a length-nine base over which \([4]=e\). The final
square-zero socle lift creates the defect. “Bockstein-type carry” describes
multiplication by the mixed-characteristic class of \(2\); no formal
connecting morphism is claimed.

Killing both first skew directions gives

\[
R/(d,y+z)\simeq\mathbf F_2[x,z]/(x^2,z^2),
\]

over which the coproduct is cocommutative.

### 8.2 The length \(6\to8\to10\) tower

Let

\[
I=(d)=\mathbf F_2\{d,\eta,q,\sigma\},\qquad
I^2=\mathbf F_2\{\eta,\sigma\},\qquad I^3=0.
\]

Set

\[
R_{10}=R,\qquad R_8=R/I^2,\qquad R_6=R/I.
\]

Both successive kernels are square-zero.

Over \(R_6\), \(q=\eta=\sigma=0\) and \(R_6\{1,e_2\}\) is a rank-two Hopf
subalgebra. There is an exact sequence

\[
1\to(H_x)_{R_6}\to G_{R_6}\to K_6\to1
\]

of rank-two Oort–Tate factors, so \(G_{R_6}\) is killed by four.

The lift to \(R_8\) turns on \(d\) and \(q=yd\). The terms

\[
d e_2\otimes e_1+q e_2\otimes e_3
\]

destroy normality, but \(\sigma=0\), so \([4]\) remains trivial.

The final lift turns on

\[
\eta=d^2,\qquad \sigma=dq=\omega d.
\]

The power map contains

\[
e_1\xmapsto{\omega}e_2\xmapsto{d}e_3,
\]

with coefficient \(\omega d=\sigma\). Thus normality breaks one
infinitesimal layer before the fourth-power relation.

## 9. Verification ledger

### 9.1 Direct small-model audit

**scripts/verify_rank4_length10_counterexample_20260710.py** constructs the
1024-element ring and verifies ring laws, base invariants, all Hopf
identities, the antipode, \(\psi^2=2\psi\), the power maps, and
noncommutativity. This is the first truth source.

### 9.2 Independent coordinate model

**scripts/independent_verify_rank4_length10_counterexample_20260710.py** uses
a different additive model and can evaluate the raw universal equations:

    EXPORT=results/m2_rank4_export_audit_JOBID.txt
    python3 scripts/independent_verify_rank4_length10_counterexample_20260710.py \
      "$EXPORT"

Here and below, replace **JOBID** by the number returned by the bounded
Slurm export job in Section 9.4.  The historical temporary export was
ephemeral; a regenerated export belongs under **results/**. Its expected
SHA-256 is

    686c35c91b74af2a414dd119024411266fb0056865dd1d19676c20485f93b6b7

A missing temporary file is not a mathematical failure.

### 9.3 Structural and subgroup audits

**scripts/audit_rank4_descriptions_20260710.py** checks both regular
matrices and inverses, coordinate recovery, the dual Hopf table, and the
basic subgroup.

**scripts/audit_rank4_subgroups_deformations_20260711.py** exhausts all
1024 normalized quotient parameters and checks exactly sixteen solutions,
their isomorphisms and adjoint certificates, both ideal filtrations, both
square-zero lifts, and the commutative quotient.

### 9.4 Universal source audit

Principal files:

- m2/universal_local_rank4.m2
- scripts/compare_universal_rank4_m2_export_20260710.py
- scripts/independent_audit_mixed_a2a2_export.py
- m2/verify_mixed_a2a2_dual_direct.m2
- notes/RANK4_GROTHENDIECK_COUNTEREXAMPLE_AUDIT_2026-07-10.tex
- logs/rank4_counterexample_audit_20260710.txt

The historical export command was

    env RANK4_BRANCH=0 RANK4_INTEGRAL=1 RANK4_EXPORT_POLYS=1 \
      M2 --script m2/universal_local_rank4.m2 \
      > /tmp/m2_rank4_export_audit_20260710.txt

Under current policy this is substantive M2 and must be wrapped in Slurm
with the prescribed Apptainer image. Do not run that historical command
directly on a login node. A bounded wrapper is now provided:

    sbatch slurm/export_rank4_length10_source_audit.sbatch

It requests one CPU, 2 GiB, and ten minutes, and writes a unique file
**results/m2_rank4_export_audit_JOBID.txt**. Record the job ID, inspect
both Slurm streams, and use **sacct** before classifying the result.

Given the export, exact Python comparisons are:

    EXPORT=results/m2_rank4_export_audit_JOBID.txt

    python3 scripts/compare_universal_rank4_m2_export_20260710.py \
      "$EXPORT"

    python3 scripts/independent_audit_mixed_a2a2_export.py \
      "$EXPORT"

    python3 scripts/audit_rank4_length10_specialization_20260710.py \
      "$EXPORT"

The native M2 dual verifier checks all \(45{,}414\) cubic candidates and is
substantive, so it also belongs on Slurm.  A one-CPU, 2-GiB, ten-minute
wrapper is provided.  Submit it only after the export job has completed
successfully, again replacing **JOBID** by the export job number:

    sbatch --export=ALL,RANK4_EXPORT_FILE=results/m2_rank4_export_audit_JOBID.txt \
      slurm/verify_rank4_cubic_dual.sbatch

Inspect the resulting **logs/rank4_dual_JOBID.out** and
**logs/rank4_dual_JOBID.err**, and record the new verifier job's Slurm state,
elapsed time, maximum RSS, and exit code with **sacct**.  Do not run the raw
M2 command on a login node.

### 9.5 Universal quasi-idempotence

Run

    python3 scripts/audit_rank4_psi_quasi_idempotent_20260710.py

It proves by exact filtered reduction that all coordinates of
\(\psi^2-2\psi\) vanish on the universal cubic base.

### 9.6 Catalecticant minimum

Run

    python3 scripts/audit_rank4_catalecticant_minimum_20260710.py

This requires **z3-solver**. The audited environment used Z3 4.16.0 in
/tmp/rank4_z3; the script checks there if ordinary import fails.

Audited result:

- rank-\(4\) witness;
- complete rank-\(\le3\) factorization instance UNSAT;
- about 19 seconds;
- \(1024\) MiB memory cap;
- assertion hash
  7f20f68bb134f26bbbe943089f0a92fcec206a0ebb48da48db528f3f76a4f1df.

The result is conditional on the solver verdict because no separately
checked proof object is archived.

## 10. Claim ledger

### Unconditional and audited

1. \(R\) has the stated invariants.
2. \(A,\Delta,\epsilon,S\) form a rank-four Hopf algebra.
3. \(G\) is noncommutative.
4. \([4]^\#(e_1)=\sigma e_3\ne0\).
5. \([8]^\#=P\).
6. The complete-intersection, point, measure-algebra, and
   \(\mathrm{GL}_3\) descriptions are exact.
7. Three is the minimum faithful representation dimension.
8. Exactly sixteen rank-two subgroups are defined over \(R\); all are
   isomorphic and nonnormal.
9. No finite-flat normal/composition filtration exists, even fppf-locally.
10. The deformation tower is exact.
11. Every proper quotient of this particular Gorenstein base kills the
    displayed socle defect.

### Conditional or scoped

1. Conditional on the recorded Z3 UNSAT verdict, length \(10\) is minimal
   among Artin quotients of the audited universal cubic base retaining
   either fourth-power target.
2. Older broad length-\(\le6\) exclusions rely on a larger exact-search
   corpus and were not re-audited in the length-ten structural pass.

### Not proved

1. Global minimality of length \(10\) among all possible constructions is
   not proved.
2. Unrelated constructions over bases of lengths \(7,8,9\) are not excluded
   by cubic MinRank.
3. No sharp general exponent theorem for every rank-four group is proved
   here.
4. No cohomological Bockstein connecting map is constructed.
5. The note is not submission-ready until historical attribution,
   literature, and bibliography are checked by a human expert.

## 11. Superseded and dangerous artifacts

Many older files predate the counterexample and retain a stale open-problem
state.

- **HANDOFF_NEXT_AGENT_2026-07-10.md** has a warning but then a long stale
  narrative.
- Most of **HANDOFF_NEXT.md** is a historical session diary.
- **RANK4_NO_NORMAL_RANK2_FILTRATION_2026-07-10.md** treats a different
  height-one example. Do not transfer its formulas.
- **logs/rank4_length10_counterexample_audit_20260710.txt** predates the
  later \(\mathrm{GL}_3\), subgroup, and deformation expansions. Its old
  12-page count and TeX/PDF hashes are stale, though its mathematical
  command output remains valid.
- /tmp/m2_rank4_export_audit_20260710.txt is temporary.

Use the current main TeX/PDF and three self-contained Python auditors as the
primary truth sources.

## 12. Search chronology and methodological lessons

The successful route was not a blind search over small rings.

1. A universal mixed-characteristic chart around \(\alpha_2^2\) produced a
   large local base with Hilbert function \((1,15,107,509)\), length \(632\).
2. Two fourth-power targets survived in the cubic/top filtered layer.
   Independent dual nonmembership certificates established this exactly.
3. Instead of deleting presentation generators ad hoc, the search was
   dualized: choose a cubic functional nonzero on a target and annihilating
   all cubic ideal relations.
4. The first sparse certificate had catalecticant rank \(7\), giving Hilbert
   function \((1,7,7,1)\), length \(16\).
5. Varying the functional in the full admissible dual space and minimizing
   catalecticant rank produced rank \(4\), represented by
   \(X^{[2]}Z+XYD+YD^{[2]}+Z^{[3]}\).
6. The apolar multiplication plus \(Z^\vee=2\), \(s=2Z\) produced the
   length-ten base.
7. All 189 universal equations were checked after exact specialization.
8. A direct tuple model and a second independent coordinate model replaced
   the large universal computation as the proof of the headline theorem.
9. Complete-intersection, representation, subgroup, and deformation
   descriptions were derived only after the example was secure.

Key lessons:

- optimize an invariant such as catalecticant rank, not the superficial
  number of presentation variables;
- associated-graded discovery must be lifted to exact inhomogeneous
  equations;
- add integral terms before taking mixed-characteristic initial forms:
  \(f+f=2f\), not zero;
- exact finite tuple arithmetic is preferable once a small quotient is
  known;
- use independent implementations and different coordinate models;
- never interpret timeout/OOM as negative evidence;
- separate solver-dependent minimality from unconditional existence;
- deformation ablation can explain which phenomenon appears at which order.

A paper-appropriate version of this chronology is now included in the main
TeX discovery section.

## 13. Prioritized next work

### A. Turn the note into a paper

1. State the precise historical conjecture and hypotheses.
2. Verify attribution using primary literature.
3. Add citations for finite flat quotients, Oort–Tate groups, rank-two
   killedness, inverse systems, and the historical question.
4. Decide whether the universal chart and MinRank belong in the main text
   or a computational supplement.
5. Keep conditional chart-minimality visibly separate from the theorem.
6. Have a human check left/right coset and Oort–Tate sign conventions.
7. Package the direct auditors and exact output.

### B. Seek a globally smaller base

The honest frontier is lengths \(7,8,9\), subject to the scope of older
length-\(\le6\) exclusions.

1. Search different special fibers or charts, not only quotients of this
   cubic chart.
2. Permit greater Loewy depth.
3. Classify possible Hilbert functions and skew symbols at lengths \(7,8,9\).
4. Use the deformation insight to seek a base where normality and power
   failure require fewer independent directions.
5. Keep searches bounded and classify resource failure honestly.

### C. Conceptual deformation theory

1. Locate the skew symbol \(N\) in the deformation complex of
   \(\alpha_2^2\).
2. Make the Bockstein-type carry precise if possible.
3. Interpret \(R_6\to R_8\to R_{10}\) as successive obstruction classes.
4. Determine the automorphism orbit of the cubic \(\mathcal G\).

### D. Strengthen minimality

1. Produce an independently checkable proof certificate for rank-\(\le3\)
   UNSAT.
2. Alternatively prove rank \(\ge4\) by hand.
3. Do not remove the conditional qualifier without one of these.

### E. Additional structure

1. Compute \(\operatorname{Aut}(G)\) and its action on the sixteen subgroups.
2. Uniformly describe left and right coset schemes.
3. Study the determinant character of the \(\mathrm{GL}_3\) representation.
4. Seek a conceptual, non-enumerative explanation of the sixteen embeddings.

## 14. Paper-writing skeleton

1. Theorem and scope.
2. Base ring normal form, length, Gorenstein property, and socle.
3. Complete-intersection coordinate algebra.
4. Coproduct and antipode with exact verification.
5. Hand computation of \([2]\), \([4]\), and \([8]\).
6. Mixed-characteristic carry times skew symbol.
7. \(\mathrm{GL}_3\), subgroup, and deformation structure.
8. Inverse-system construction and universal specialization.
9. Clearly marked solver-dependent relative minimality.
10. Global lengths \(7,8,9\) question.

Do not lead with failed searches. The explicit construction and short power
calculation are the mathematical core.

## 15. Continuation checklist

- [ ] Read **AGENTS.md**.
- [ ] Run the three self-contained Python auditors.
- [ ] Read the current main TeX/PDF.
- [ ] Scope every claim as unconditional or solver-dependent.
- [ ] Distinguish subgroup chains from normal filtrations.
- [ ] Distinguish the power word from a group homomorphism.
- [ ] Remember that the sixteen subgroups are counted over \(R\).
- [ ] Do not call \(A^\vee\) a coordinate algebra.
- [ ] Do not over-formalize the Bockstein-type language.
- [ ] Put substantive M2 work through Slurm.
- [ ] Diagnose every failed computation before interpreting it.
- [ ] Recompile the TeX and inspect warnings after edits.
- [ ] Add a dated supersession note if the state changes.

The construction itself is secure. The highest-value continuation is
conceptualization, publication-quality exposition, and the genuinely global
length-\(7,8,9\) search.
