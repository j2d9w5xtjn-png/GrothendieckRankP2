# Principal residue-F2 length-six chain rings: exact classification

Date: 2026-07-10

## Result

There are exactly **10** isomorphism classes of commutative local principal
rings of length six with residue field \(\mathbf F_2\).

Every class has a presentation with \(t^6=0\).  The following list is
complete; all displayed coefficients are ordinary integers in the unital
ring.

| class | \(e=\operatorname{ord}_{\mathfrak m}(2)\) | characteristic | canonical relation |
|---|---:|---:|---|
| C01 | 1 | 64 | \(2=t\) |
| C02 | 2 | 8 | \(2=t^2\) |
| C03 | 2 | 8 | \(2=t^2+t^5\) |
| C04 | 2 | 8 | \(2=t^2+t^3\) |
| C05 | 2 | 8 | \(2=t^2+t^3+t^4\) |
| C06 | 3 | 4 | \(2=t^3\) |
| C07 | 4 | 4 | \(2=t^4\) |
| C08 | 4 | 4 | \(2=t^4+t^5\) |
| C09 | 5 | 4 | \(2=t^5\) |
| C10 | \(\infty\) | 2 | \(2=0\) |

Thus C01 is \(\mathbf Z/64\), while C10 is
\(\mathbf F_2[t]/t^6\).  The important new count is four classes at
\(e=2\), one at \(e=3\), and two at \(e=4\).

The machine-readable table, including complete coordinate-presentation
orbits, is
[`scripts/principal_length6_chain_classes_evidence_map_20260710.tsv`](scripts/principal_length6_chain_classes_evidence_map_20260710.tsv).

## Completeness of the raw carry list

Let \(R\) be such a ring and choose a uniformizer \(t\).  Since every
successive quotient \(\mathfrak m^i/\mathfrak m^{i+1}\) is \(\mathbf F_2\),
every element has a unique expansion

\[
 a_0+a_1t+\cdots+a_5t^5,\qquad a_i\in\{0,1\}.
\]

If \(2\ne0\), put \(e=\operatorname{ord}_{\mathfrak m}(2)\).  Necessarily
\(1\le e\le5\), and the unit multiplying \(t^e\) has a unique binary
expansion.  Hence

\[
 2=t^e+c_{e+1}t^{e+1}+\cdots+c_5t^5,
 \qquad c_i\in\mathbf F_2.
\]

Conversely, each such carry relation together with \(t^6=0\) gives a
64-element chain ring.  Therefore the complete coordinate list has

\[
 1+2^4+2^3+2^2+2+1=32
\]

members: one equal-characteristic form and respectively 16, 8, 4, 2, and
1 mixed-characteristic forms for \(e=1,2,3,4,5\).

## Exact arithmetic and orbit audit

The checker
[`scripts/principal_length6_chain_classification_evidence_map_20260710.py`](scripts/principal_length6_chain_classification_evidence_map_20260710.py)
constructs each table directly from the carry rule.  For every one of the
32 presentations it exhausts all 64 elements and checks:

- the additive and multiplicative identities, inverses, commutativity,
  associativity, and distributivity, including all \(64^3\) triples;
- \(|\mathfrak m^i|=32,16,8,4,2,1\), with
  \(\mathfrak m^i=(t^i)\) exactly;
- locality and the exact unit complement;
- \(\operatorname{Soc}(R)=\mathfrak m^5\) of order two;
- the characteristic and the displayed carry relation.

No assumed normal-form change is used to identify presentations.  A unital
isomorphism must send the chosen \(t\) to one of the 16 elements of
\(\mathfrak m\setminus\mathfrak m^2\).  The checker tests all 16 possible
images for every ordered pair of the 32 presentations.  Every accepted map
is then independently checked on all \(64^2\) addition and multiplication
pairs.  A further partition gate proves that every target uniformizer
induces exactly one of the 32 raw carry presentations.

The resulting raw-coordinate orbits are

\[
\begin{aligned}
e=1:&\quad \{0000,0001,\ldots,1111\};\\
e=2:&\quad \{000,011\},\ \{001,010\},\
             \{100,101\},\ \{110,111\};\\
e=3:&\quad \{00,01,10,11\};\\
e=4:&\quad \{0\},\ \{1\};\\
e=5:&\quad \{-\},
\end{aligned}
\]

plus the single equal-characteristic form.  Here a bit string records the
coefficients of \(t^{e+1},\ldots,t^5\), in that order.

The clean raw run is
[`scripts/principal_length6_chain_classification_evidence_map_20260710_final.log`](scripts/principal_length6_chain_classification_evidence_map_20260710_final.log).
It ends with `ISOMORPHISM_CLASSES 10` and the expected `DONE` marker.

## Consequence and scope

This completes the ring-classification prerequisite in §3 of
`STRUCTURAL_LENGTH7_FRONTIER_F2_2026-07-10.md`.  In particular, a complete
principal length-six \(S'\) sweep requires ten base-ring classes, not merely
the pure Eisenstein representatives.  No \(S'\) or Grothendieck-conjecture
coverage is claimed here; those tests must use the ten-class table above.
