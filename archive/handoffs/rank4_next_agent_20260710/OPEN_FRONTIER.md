# Open frontier after the 2026-07-10 pass

## Exact mathematical wall

For rank four, let

\[
 q=[2]^\#,\quad D=[4]^\#-e,\quad
 J=((\operatorname{Id}-S)(A))=((q-e)(A)).
\]

The current theorems give

\[
 D=(1+\delta)(q-e),\quad
 (1+\delta)J^2=0,\quad
 2(1+\delta)J=0.
\]

Thus

\[
 [4]=e\iff(1+\delta)J=0.
\]

The obstruction \(M=(1+\delta)J\) is a module over
\(A/(2,1+\delta,J)\). This linear conormal class is the universal gap.

## Remaining geometric fibers

After Deligne, block rigidity, and Torti, a counterexample must have a
local--local special fiber:

- \(\alpha_2^2\);
- \(W_2[F]\);
- one of the four \(t^4(c_1,c_4)\) forms.

The old \(\alpha_2\rtimes\mu_2\) flag is closed. All commutative fibers with
nontrivial multiplicative part are closed.

## Remaining computational ranges

- Principal residue-\(\mathbf F_2\), length-seven quotient profile:
  12/2/5/41 closed/vacuous/unknown/incomplete after filtering to 60
  local--local rows at the freeze.
- Larger residue fields beyond the banked orbit rows.
- Arbitrary base length and arbitrary mixed-characteristic carries.
- The inherited s5t4gen and FatPoint3 fp3gen module computations remain
  nonterminal snapshots.

The stretched residue-\(\mathbf F_2\) length-seven profile is no longer open
for the rank-four conjecture: the two \(S'\) timeout rows were closed by the
direct-[4] socle-lift computation.

## Best proof target

In equal characteristic two put \(z=\delta-1\) and \(Q=q|_I\). Then

\[
 z^2=0,\quad q(z)=0,\quad Q^2=M_zQ,\quad Q^3=0.
\]

For a monogenic \(t^4\) lift, \(J=(q(T))\), so the whole defect is
\(D(T)=zq(T)\). The next proof should combine quartic relation stability
with the first-layer primitive theorem and trace-depth restrictions to rule
out this single cyclic conormal class. Scalar trace/determinant identities
alone are known to be insufficient.
