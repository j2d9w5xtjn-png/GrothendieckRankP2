# Explicit rank-four ramified construction pass

**Date:** 2026-07-09  
**Purpose:** try to build, rather than merely search abstractly for, a rank-four
counterexample to Grothendieck's killed-by-the-order conjecture over a highly
ramified Artin local base.

## 1. Outcome

No counterexample was found.  This pass nevertheless rules out two natural and
fairly large explicit construction mechanisms.

1. A two-sided matched Oort--Tate construction on
   \(R[x,y]/(x^2-ax,y^2-cy)\), with every cross-term bilinear in \(x,y\), is
   killed by four over **every** local base satisfying the stated Oort--Tate and
   special-fiber hypotheses.  This is a hand proof, not merely a finite search.
2. Let
   \[
   R_N=\mathbf Z[\pi]/(\pi^2-2,\pi^N),\qquad
   A_N=R_N[x,y]/(x^2-\pi x,\ y^2+2y).
   \]
   On this fixed tensor Oort--Tate algebra, allow **all eighteen** possible
   \(I\otimes I\) corrections to \(\Delta x,\Delta y\), impose relation
   preservation and coassociativity, and query \([4]\) directly.  Exact Z3
   searches for every \(4\le N\le20\) are UNSAT for \([4]\ne e\).  In fact they
   are UNSAT already for noncocommutativity, although nontrivial \([2]\) maps do
   occur.  Thus a counterexample in this ramified tower must deform the
   multiplication as well as the coproduct.

Full 45-parameter bialgebra searches, with both multiplication and coproduct
free, were also split according to the four classified \(xy\)-fiber Hopf
structures.  For \(N=4,5,6\), the only split fiber admitting a noncommutative
lift is \(\alpha_2^2\); direct \([4]\ne e\) queries are UNSAT in all four
fibers.  The mixed fiber \(\mu_2\times\alpha_2\), the most plausible literature
frontier, admits no noncommutative lift in these exact instances.

These are exclusions inside explicit families and exact finite rings, not a
proof of the conjecture.

## 2. The rank-two extension obstruction

Suppose there is an exact sequence of finite flat group schemes
\[
1\longrightarrow N\longrightarrow G\overset q\longrightarrow Q
\longrightarrow1
\]
with \(N\) and \(Q\) of rank two.  Every rank-two finite flat group scheme is
killed by two.  Since
\[
q\circ[2]_G=[2]_Q\circ q=e,
\]
the scheme map \([2]_G\) factors through \(N\).  Its restriction to \(N\) is
\([2]_N=e\), and hence
\[
[4]_G=[2]_G\circ[2]_G=e.
\]
This argument does not require \([2]_G\) to be a group homomorphism.  It rules
out products, semidirect products, nonsplit extensions by a flat rank-two
normal subgroup, and triangular Hopf formulas that preserve such an extension.
A counterexample must lose every such flat normal filtration.

## 3. A noncommutative family that illustrates the obstruction

Noncommutativity by itself is easy to manufacture at arbitrary ramification
depth.  On
\[
A=R_N[x,y]/(x^2-\pi x,y^2-\pi y)
\]
take \(h\in\operatorname{Ann}(\pi)\) with \(h^2=0\), for example
\(h=\pi^{N-1}\), and set
\[
\begin{aligned}
\Delta y&=y\otimes1+1\otimes y-\pi y\otimes y,\\
\Delta x&=x\otimes1+1\otimes x-\pi x\otimes x+h,y\otimes x.
\end{aligned}
\]
The relation and coassociativity defects are multiples of
\(\pi h,h^2,2h\), hence vanish.  The law is noncocommutative when \(h\ne0\),
but
\[
[2]^\#(x)=hxy,\qquad [2]^\#(y)=0,
\]
so \([4]^\#=0\).  Moreover \(R_N[y]\) remains a Hopf subalgebra: this is a
rank-two-by-rank-two extension and is killed by the preceding argument.  This
family explains the persistent `noncomm=sat`, `[4]!=e=unsat` row for the
\(\alpha_2^2\) fiber.

## 4. The two-sided matched Oort--Tate ansatz

Let \(R\) be local and put
\[
A=R[x,y]/(x^2-ax,y^2-cy),\qquad ab=cd=2.
\]
For the \(\alpha_2\times\mu_2\) specialization, \(a,b,c\in\mathfrak m\)
and \(d\) is a unit.  Consider the most general cross-coproduct involving only
the degree-one generators in each tensor factor:
\[
\begin{aligned}
\Delta x={}&x_1+x_2-bx_1x_2
 +p,y_1x_2+r,x_1y_2+u,y_1y_2,\\
\Delta y={}&y_1+y_2-dy_1y_2
 +q,x_1y_2+s,y_1x_2+v,x_1x_2,
\end{aligned}
\]
where \(p,q,r,s,u,v\in\mathfrak m\).  Both cross-directions are present, so
this is not assumed triangular and need not exhibit a rank-two normal factor.

### 4.1 Equations forced by the Hopf axioms

Preservation of \(x^2=ax\) contains
\[
ap(1+cp)=0,\qquad ar(1+cr)=0.
\]
Since \(cp,cr\in\mathfrak m\), the parenthesized elements are units, and
therefore
\[
ap=ar=0.
\]
Similarly, preservation of \(y^2=cy\) gives
\[
cq=cs=0.
\]
The coassociativity defects include
\[
uv-qr=0,
\]
as well as \(uv-ps=0\) and further equations not needed below.  The complete
coefficient list is printed by `scripts/explicit_bicross_rank4.py`.

### 4.2 Direct computation of the fourth power

Write \(z=xy\), \(P=p+r\), and \(Q=q+s\).  Since \(ab=cd=2\), multiplication
of the coproduct gives
\[
\varphi(x):=[2]^\#(x)=cu\,y+Pz,
\qquad
\varphi(y)=av\,x+Qz.
\]
The equations above say \(aP=cQ=0\).  Using
\(xz=az\), \(yz=cz\), and \(z^2=acz\), one obtains
\[
\varphi(z)=\varphi(x)\varphi(y)=acuv\,z
\]
and consequently
\[
\varphi^2(x)=acuv\,x,\qquad
\varphi^2(y)=acuv\,y.
\]
But \(uv=qr\), so
\[
acuv=acqr=0
\]
because \(cq=0\).  Hence \([4]^\#=\varphi^2=e\) throughout this family,
at arbitrary depth and without assuming the law is commutative.

The smaller oriented-cross ansatz
\(\Delta x=\Delta_{OT}x+p,y_1x_2\),
\(\Delta y=\Delta_{OT}y+q,x_1y_2\) is a specialization.  Its apparent target
\(acp^2qz\) is already killed by the relation equation \(ap=0\).

## 5. Exact fixed-algebra search through depth twenty

The script `scripts/explicit_bilinear_ramified_sat.py --full` uses the exact
presentation
\[
R_N=\{A+B\pi:A\bmod 2^{\lceil N/2\rceil},\;
B\bmod2^{\lfloor N/2\rfloor}\}
\]
with \(\pi^2=2\).  It fixes
\[
A_N=R_N[x,y]/(x^2-\pi x,y^2+2y)
\]
but writes
\[
\Delta g=\Delta_{OT}g+
\sum_{e_i,e_j\in\{x,y,xy\}}c^g_{ij}e_i\otimes e_j,
\qquad c^g_{ij}\in(\pi),quad g=x,y.
\]
This is every counital coproduct on the fixed algebra reducing to the chosen
\(\alpha_2\times\mu_2\) product law.  The script imposes:

- preservation of both defining algebra relations;
- all coefficients of coassociativity for \(x,y\);
- the special-fiber pin through \(c^g_{ij}\in(\pi)\);
- and the literal nonvanishing of \([4]^\#\), not failure of \(S'\).

For every \(N=4,\dots,20\):

| query | exact verdict |
|---|---|
| bialgebra gate | SAT |
| \([2]\ne e\) | SAT |
| noncocommutative coproduct | UNSAT |
| \([4]\ne e\) | UNSAT |

The noncocommutativity result is especially informative: on this natural
Oort--Tate tensor algebra, the Hopf equations rigidify the group law back to a
commutative one.  Therefore a counterexample must change the underlying
rank-four algebra, not merely add increasingly deep coproduct terms.

As a higher-ramification check, the same fixed-algebra experiment was rerun
over \(\mathbf Z[\pi]/(\pi^e-2,\pi^N)\) for \(e=3\), both Oort--Tate splits,
and \(5\le N\le12\), and for \(e=4\), splits \((1,3)\) and \((2,2)\), and
\(6\le N\le12\).  The ring arithmetic was independently checked for
associativity at representative deepest instances \((e,N)=(3,8),(4,12)\), in
addition to the defining coefficient formula.  Every row again had gate SAT and \([2]\ne e\)
SAT, but noncocommutativity UNSAT and \([4]\ne e\) UNSAT.  These remain
fixed-algebra exclusions; they do not cover simultaneous multiplication
deformations.

## 6. Full multiplication-and-coproduct search, split by special fiber

The script `scripts/pin_split_fibers_ramified.py` calls the existing full
45-parameter bialgebra encoder.  Its pin is symbol-independent: the ring's
`var("cijk")` method itself returns the prescribed residue coefficient plus
\(\pi\) times a fresh lift.  The four residue coproducts are the classified
split models `a2a2`, `W2F`, `mu2mu2`, and `mu2a2`.

Completed exact results are:

| depth | fiber | bialgebra gate | noncommutative | \([4]\ne e\) |
|---:|---|---|---|---|
| 4 | \(\alpha_2^2\) | SAT | SAT | UNSAT |
| 4 | \(W_2[F]\) | SAT | UNSAT | UNSAT |
| 4 | \(\mu_2^2\) | SAT | UNSAT | UNSAT |
| 4 | \(\mu_2\times\alpha_2\) | SAT | UNSAT | UNSAT |
| 5 | \(\alpha_2^2\) | SAT | SAT | UNSAT |
| 5 | \(W_2[F]\) | SAT | UNSAT | UNSAT |
| 5 | \(\mu_2^2\) | SAT | UNSAT | UNSAT |
| 5 | \(\mu_2\times\alpha_2\) | SAT | UNSAT | UNSAT |
| 6 | \(\alpha_2^2\) | SAT | SAT | UNSAT |
| 6 | \(W_2[F]\) | SAT | UNSAT | UNSAT |
| 6 | \(\mu_2^2\) | SAT | UNSAT | UNSAT |
| 6 | \(\mu_2\times\alpha_2\) | SAT | UNSAT | UNSAT |
| 7 | \(\alpha_2^2\) | SAT | SAT | UNSAT |
| 7 | \(W_2[F]\) | SAT | UNSAT | UNSAT |
| 7 | \(\mu_2^2\) | SAT | UNKNOWN (timeout) | UNSAT |
| 7 | \(\mu_2\times\alpha_2\) | SAT | UNKNOWN (timeout) | UNSAT |

At depth 7, the two noncommutativity-only UNKNOWN rows are failures to decide
whether a noncommutative lift exists; they are not counterexample signals.  The
stronger point relevant to Grothendieck's question was decided independently:
the direct \([4]\ne e\) query is UNSAT for all four fibers.

Because the special fiber is killed by two, every bialgebra in these searches
has an antipode automatically.  No extra antipode assumption is missing.

## 7. Audit note: a corrected variable-pinning error

An initial ad hoc \(N=5\) pin addressed names of the form `c111__1_a`, copied
from the older ring class.  The new generic ramified class generates
`c111_1_a` with one underscore.  Those ad hoc constraints therefore created
unrelated Z3 symbols and did **not** pin the fiber.  The resulting generic SAT
noncommutative row was incorrectly described, briefly, as an
\(\alpha_2\times\mu_2\) row.

This was caught by minimizing against the tensor Oort--Tate point: the solver
purported to satisfy `noncomm` at an exactly cocommutative table.  The pin was
rewritten inside the ring representation, eliminating all dependence on symbol
names.  Corrected verdict: at \(N=5\), the generic noncommutative lift belongs
to the \(\alpha_2^2\) row; the \(\mu_2\times\alpha_2\) noncommutative query is
UNSAT.

## 8. A rejected base-ring candidate

The proposed presentation
\[
\mathbf Z/4[x,y]/(2x,2y,xy,x^2-y^2,x^3-2)
\]
does not define the claimed mixed-characteristic length-five ring: multiplying
\(x^2=y^2\) by \(x\) and using \(xy=0\) gives \(x^3=0\), hence \(2=0\).
The associated claimed multiplication table also violates associativity.

A valid nearby ring is
\[
\mathbf Z/4[x,y]/(2x,2y,xy,y^2-2,x^3-2),
\]
but its socle quotient is the already-treated RingT algebra after swapping
generators.  The existing socle-lift theorem therefore kills every rank-four
lift over it.  It is a useful consistency gate, not a new frontier.

## 9. What a surviving explicit construction must do

The calculations sharpen the necessary features of any counterexample.

1. It cannot have a finite flat rank-two normal subgroup and rank-two quotient.
2. It cannot be an ordinary semidirect product or a nonsplit extension of two
   Oort--Tate groups.
3. Even a two-sided bilinear matched product fails universally.
4. In the quadratic ramified tower through length twenty, keeping the natural
   Oort--Tate tensor algebra forces every lifted coproduct to be cocommutative.
5. Through lengths four to six, the \(\mu_2\times\alpha_2\) fiber does not even
   support a noncommutative full deformation in the exact search.

Thus a credible example must simultaneously deform multiplication and
comultiplication, destroy every flat rank-two filtration, and use either a more
complicated base (probably nonprincipal or with a different ramification
pattern) or a deformation layer not present in these exact towers.  This is
substantially narrower than the original instruction "try a very ramified
base," but it is not empty and does not amount to a proof.

## 10. Reproduction

The new scripts are:

- `scripts/explicit_bicross_rank4.py` -- dependency-free symbolic coefficient
  expansion for the six-parameter and general bilinear matched ansatz;
- `scripts/explicit_bilinear_ramified_sat.py` -- exact \(R_N\) arithmetic and
  the fixed-algebra 18-correction search;
- `scripts/pin_split_fibers_ramified.py` -- full bialgebra search with robust
  split-fiber pins;
- `scripts/extract_sparse_alpha_mu_model.py` -- sparse-model diagnostic that
  exposed the obsolete symbol-name pin and now serves as a regression test.

Representative commands:

```sh
python3 scripts/explicit_bicross_rank4.py
$HOME/.venvs/z3env/bin/python scripts/explicit_bilinear_ramified_sat.py \
  --full --min-n 4 --max-n 20 --timeout-ms 300000
$HOME/.venvs/z3env/bin/python scripts/pin_split_fibers_ramified.py \
  --n 6 --case all --timeout-ms 300000
```

The exact SAT scripts require the workspace Z3 environment documented in
`scripts/JOBS.md`; bare `python3` does not contain Z3.
