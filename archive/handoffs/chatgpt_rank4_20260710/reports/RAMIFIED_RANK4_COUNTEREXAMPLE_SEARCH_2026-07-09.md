# Sustained ramified rank-four counterexample search

> **Later same-day update.** The depth-five frontier in §6 was subsequently
> closed on all principal rings and on two nonprincipal rings after splitting
> into all **six** rational \(xy\) fibers and four \(t^4\) normal forms.  The
> final state, including the correction from four geometric to six rational
> \(xy\) classes, is recorded in
> `RANK4_SERIOUS_RAMIFIED_COUNTEREXAMPLE_PASS_2026-07-09.md`.  Use that report
> for the current frontier; the completed length-\(\le5\) theorem here remains
> valid.

## Executive verdict

No rank-four counterexample was found.  The search instead produced a
stronger finite-length exclusion:

> Subject to the structural classification and reductions in
> `STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md`, every rank-four finite
> locally free group scheme over an Artin local base with residue field
> \(\mathbf F_2\) and base length at most five is killed by four.

The essential new computation is not a collection of isolated
\([4]^\#=0\) checks.  It proves the stronger invariant

\[
 S'(A/R):\qquad
 \phi(I)\subseteq \mathfrak m(\ker\phi\cap I),\qquad \phi=[2]^\#,
\]

over six exact ramified length-four quotient rings, for both local
rank-four special-fiber algebra shapes.  The socle-extension theorem then
handles every length-five lift of those quotients.

This is not a proof of Grothendieck's conjecture in rank four.  A
residue-\(\mathbf F_2\) counterexample can first occur at length six, where
its length-five socle quotient must fail \(S'\).  Mixed-characteristic
length-three bases with larger residue fields also remain open when one
minimizes length rather than cardinality.

## 1. Exact search scope

The ring-generic builder in `scripts/order4sat.py` was used without fixing a
coproduct.  For a free augmented rank-four algebra

\[
 A=R\cdot1\oplus R e_1\oplus R e_2\oplus R e_3,
\]

it makes all multiplication deformations and all reduced coproduct
coefficients variable and imposes:

1. commutative unital associativity;
2. counital normalized coproduct form;
3. multiplicativity of \(\Delta\);
4. coassociativity;
5. the condition that the special fiber is killed by two.

It then computes \(\phi=[2]^\#=\mu\Delta\) and
\([4]^\#=\phi^2\) exactly in the finite base ring.  Both possible local
special-fiber algebra shapes are searched:

\[
 \mathbf F_2[x,y]/(x^2,y^2),\qquad \mathbf F_2[t]/(t^4).
\]

The coproduct is not required to be cocommutative, so the noncommutative
group-scheme branch is included.  A full-bialgebra UNSAT verdict after adding
\([4]^\#\ne0\) is stronger than needed: every Hopf algebra is a bialgebra, so
no separate antipode computation is required in an UNSAT row.  Had the
bialgebra row been SAT, the driver would have imposed both antipode
convolution identities before calling it a candidate counterexample.

Every new finite ring class was gated by exhaustive concrete checks of its
ring axioms, presentation relations, maximal ideal, ideal filtration, and
socle before its Hopf verdict was accepted.  The general Eisenstein-tower
class was additionally cross-checked against both legacy \(e=2\) classes at
lengths three and four.

## 2. Previously omitted small ramified rings

The earlier statement that all residue-\(\mathbf F_2\) curvilinear rings of
length at most four had been tested omitted two chain rings:

\[
 C_{34}=\mathbf Z/4[p]/(p^3-2,p^4),\qquad
 C_{2\mathrm{tw}}=\mathbf Z/4[p]/(p^2-2p-2).
\]

The second relation records the unit twist \(2=p^2+p^3\).  Exact full
bialgebra searches excluded \([4]^\#\ne0\) on both rings and both fibers.
More importantly, the later \(S'\)-FAIL queries were UNSAT, so all their
one-socle lifts are killed as well.

The three mixed-characteristic, nonprincipal Gorenstein rings of length four
lying over

\[
 B_0=\mathbf Z/4[y]/(2y,y^2)
\]

were also searched directly:

\[
 R_0=\mathbf Z/4[y]/(y^2),\quad
 R_1=\mathbf Z/4[y]/(y^2-2y),\quad
 R_u=\mathbf Z/8[y]/(2y,y^2-4).
\]

For every ring and both fiber shapes, the full bialgebra space was SAT while
adding \([4]^\#\ne0\) was UNSAT.  The complete banked transcript is
`scripts/order4sat_ramified_gorenstein_len4_20260709.log`.

## 3. Direct full-bialgebra exclusions

The following exact-ring runs all passed non-vacuity and exhaustive ring
gates.  "H1 UNSAT" means all bialgebra axioms, killed-by-two special fiber,
and \([4]^\#\ne0\) are jointly inconsistent.

| Base | Length | Key filtration | \(xy\) fiber | \(t^4\) fiber |
|---|---:|---|---|---|
| \(C_{34}\) | 4 | \(|(p^i)|=8,4,2,1\) | H1 UNSAT | H1 UNSAT |
| \(C_{2\mathrm{tw}}\) | 4 | \(|(p^i)|=8,4,2,1\) | H1 UNSAT | H1 UNSAT |
| \(R_0\) | 4 | \(\mathfrak m^2=(2y),\ \mathfrak m^3=0\) | H1 UNSAT | H1 UNSAT |
| \(R_1\) | 4 | \(\mathfrak m^2=(2y),\ \mathfrak m^3=0\) | H1 UNSAT | H1 UNSAT |
| \(R_u\) | 4 | \(\mathfrak m^2=(4),\ \mathfrak m^3=0\) | H1 UNSAT | H1 UNSAT |
| \(R_5=\mathbf Z/4[p,y]/(p^2-2,2y,py-2p,y^2-2p)\) | 5 | \(|\mathfrak m^i|=16,4,2,1\) | H1 UNSAT | H1 UNSAT |
| \(\mathbf Z/4[x,y]/(2x,2y,xy,y^2-2,x^3-2)\) | 5 | \(|\mathfrak m^i|=16,4,2,1\) | H1 UNSAT | H1 UNSAT |

The last two length-five rows are now subsumed by the stronger six-quotient
\(S'\) result below.  Their value is as independent exact cross-checks of
the structural route.

## 4. The six decisive length-four \(S'\) queries

The structural classification reduces every residue-\(\mathbf F_2\)
Gorenstein base of length five to a socle lift of one of six length-four
rings not already covered by earlier \(S'\) theorems:

\[
\begin{aligned}
 C_{34}&=\mathbf Z/4[p]/(p^3-2,p^4),\\
 C_{2\mathrm{tw}}&=\mathbf Z/4[p]/(p^2-2p-2),\\
 B_{00}&=\mathbf Z/4[x,y]/(2x,2y,(x,y)^2),\\
 B_1&=\mathbf Z/4[x,y]/(2x,2y,x^2-2,xy,y^2),\\
 C_4&=\mathbf Z/4[y]/(2y,y^3),\\
 C_8&=\mathbf Z/8[y]/(2y,y^2).
\end{aligned}
\]

For the two principal rings, Proposition 7.5.1's finite
\(\operatorname{ann}(p)\)-coset encoding was reused.  Every ring gate had
\(|R|=16\), \(|\mathfrak m|=8\), and \(|\operatorname{ann}(p)|=2\).

For a nonprincipal ring, a naive exact failure formula has a universal
quantifier over every generator division of \(\phi(e_i)\).  This was first
implemented and independently audited, but it is unnecessarily expensive.
The following exact reduction removes the quantifier.

Let \(S=\operatorname{Soc}(R)=\operatorname{Ann}(\mathfrak m)\).  The
fiber-killed-by-two constraints put every coefficient of
\(P=\phi|_I\) in \(\mathfrak m\).  Therefore, for \(s\in S^3\),

\[
 P(s)=0,
 \qquad g s=0\quad(g\in\mathfrak m).
\]

Adding socle elements to division coefficients changes neither their
division equation nor whether they lie in \(\ker P\).  It is enough to work
modulo \(S\).  Exhaustive enumeration gives:

| Ring | \(|S|\) | full one-coordinate syzygy size | residual syzygy dimension after quotienting by \(S\) |
|---|---:|---:|---:|
| \(B_{00}\) | 8 | 512 | 0 |
| \(B_1\) | 4 | 32 | 1 |
| \(C_4\) | 4 | 32 | 1 |
| \(C_8\) | 4 | 32 | 1 |

The script exhaustively compares the parametrized and full syzygy sets.  In
the last three cases only one \(\mathbf F_2\) choice remains per coordinate
of \(I\), so only \(2^3=8\) cases must be unrolled.  In \(B_{00}\) the
division is deterministic modulo the socle.

For each nonprincipal ring and each fiber, the script runs three split
queries, one for failure at each basis element \(e_i\).  All 24 split failure
queries are UNSAT.  The two principal failure queries per fiber are also
UNSAT.  Every corresponding S'-HOLDS non-vacuity query is SAT.

The complete terminal transcript, including every gate and timing, is
`scripts/sprime_ramified_length4_six_20260709.log`.  The implementation is
`scripts/sprime_ramified_length4_six_20260709.py`; an independent subagent
audited the four ring arithmetics, maximal-ideal parametrizations, the
original quantified formula, and the socle-quotient reduction and found no
semantic or bit-width error.  A second independent audit checked the
minimal-counterexample argument, Hilbert-function analysis, and six-target
reduction and found no omitted residue-\(\mathbf F_2\) length-five quotient
profile.  This classifies the possible socle quotients needed by the
extension theorem; it is not a claim that every length-five ring was listed
up to isomorphism.

## 5. Structural consequence

The socle-extension theorem says that if \(S'\) holds on a quotient
\(R/M\), where \(M\) is a one-dimensional socle ideal, then every relevant
rank-four lift over \(R\) is killed by four.  The classification in
`STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md` shows that the six computations
above, together with the previously proved equal-characteristic and shallow
mixed-characteristic cases, cover every possible residue-\(\mathbf F_2\)
length-five Gorenstein base.  A length-minimal counterexample base is
Gorenstein.  Hence:

\[
 \boxed{\text{No residue-}\mathbf F_2\text{ rank-four counterexample exists
 over a base of length }\le5.}
\]

Consequently any finite-base counterexample has cardinality at least \(64\).
At cardinality \(64\), the already-covered larger-residue-field shallow
cases leave a residue-\(\mathbf F_2\), length-six base as the only possible
profile.  Its length-five socle quotient must **fail** \(S'\); mere
killedness of that quotient is not enough to apply the extension theorem.

## 6. Deeper searches and evidence discipline

The general tower driver
`scripts/order4sat_ramified_towers_20260709.py` encodes

\[
 R(e,N)=\mathbf Z_2[p]/(p^e-2,p^N)
\]

with exact varying-width bitvectors.  It found direct H1 UNSAT on
\(R(3,4)\).  A direct \(R(3,5)\) bialgebra query was deliberately interrupted
after the stronger \(S'\) theorem on \(R(3,4)\) had already killed every
socle lift; its resulting `unknown` is an interruption artifact and must not
be cited as a natural solver verdict.

The genuinely deeper \(S'\) query on
\(R(2,5)=\mathbf Z_2[p]/(p^2-2,p^5)\) has a split verdict.  For the
\(t^4\) fiber, S'-FAIL is UNSAT in 1.36 seconds.  For the \(xy\) fiber it
returns `unknown` at the natural 1800.10-second timeout.  Thus \(S'\) is
universal in the former row, while the latter is now a precise principal
depth-five frontier.  See
`scripts/sprime_ramified_principal_r25_20260709.log`.

The direct \(R(2,6)\) H1 query is likewise split.  The \(t^4\) row is
bialgebra-level UNSAT in 41.18 seconds.  The \(xy\) row returns `unknown` at
the natural 1800.01-second timeout.  See
`scripts/order4sat_ramified_r26_20260709.log`.  A separate direct xy H2 query
with all 48 antipode constraints also returns `unknown` at its natural
1800.14-second timeout.  It produces no SAT Hopf seed, but it does not exclude
one.

Likewise, an exploratory direct sweep of four coordinate presentations
\(p^2=2+2cp+4d\) at length five was stopped after the length-four \(S'\)
results made every row redundant at theorem level.  Interrupted `unknown` rows
from that sweep are not negative evidence.

## 7. Reproducible artifacts

Core new scripts:

- `scripts/order4sat_ramified_towers_20260709.py`
- `scripts/order4sat_ramified_chain_twist_len4_20260709.py`
- `scripts/order4sat_ramified_char4_gorenstein_len4_20260709.py`
- `scripts/order4sat_ramified_ru_len4_20260709.py`
- `scripts/order4sat_ramified_gorenstein_len5_20260709.py`
- `scripts/order4sat_ramified_xy_gorenstein_len5_20260709.py`
- `scripts/sprime_ramified_length4_six_20260709.py`

Banked terminal logs:

- `scripts/order4sat_ramified_gorenstein_len4_20260709.log`
- `scripts/sprime_ramified_length4_six_20260709.log`
- `scripts/sprime_ramified_principal_r25_20260709.log`
- `scripts/order4sat_ramified_r26_20260709.log`

Structural synthesis:

- `STRUCTURAL_MINIMAL_BASE_ORDER4_2026-07-09.md`

No SAT model satisfying the full Hopf requirements and
\([4]^\#\ne0\) was found.
