# Grothendieck's rank-$p^2$ group-scheme conjecture

This repository collects the focused work on Grothendieck's question:

> Is every finite locally free group scheme of order `n` annihilated by `n`?

The current primary result is the rank-four construction in residue
characteristic `2`. The arbitrary-prime rank-$p^2$ material is retained as a
separate draft area until its formal proof boundary is complete.

## Start here

1. Read `manuscripts/main/A_RANK_FOUR_COUNTEREXAMPLE_TO_GROTHENDIECKS_POWER_QUESTION_2026-07-12.tex`.
2. Read `manuscripts/main/RANK4_LENGTH9_COUNTEREXAMPLE_AUDIT_AND_CONCEPTUAL_SIMPLIFICATION_2026-07-11.tex` for the shorter length-nine presentation and audit.
3. Use `lean/FiniteFlatGroupSchemes/GrothendieckCounterexample.lean` for the Lean formalization of the rank-four example.
4. Use `lean/FiniteFlatGroupSchemes/GrothendieckCounterexampleAllPrimes.lean` for the arbitrary-prime formalization draft and check its theorem boundary before citing it.

## Repository map

- `manuscripts/main/`: current rank-four manuscripts and audits;
- `manuscripts/archive/rank4/`: earlier length-ten and fourth-power-carry constructions;
- `manuscripts/drafts/arbitrary-prime/`: rank-$p^2$-for-every-prime drafts and formalization notes;
- `docs/`: mathematical reports and project-level audits;
- `lean/`: the Lean formalizations, as a Lake project;
- `scripts/`: Python verification and search programs;
- `m2/`: Macaulay2 calculations;
- `notes/`: remaining Markdown working notes;
- `archive/handoffs/`: historical agent handoffs, run manifests, claim ledgers, and reproducibility material.

## Building the Lean formalizations

The `lean/` directory is a Lake project pinning Lean `v4.31.0` and the matching
Mathlib release. Build with:

```bash
cd lean
lake build
```

The maintained modules live under `lean/FiniteFlatGroupSchemes/`:
`GrothendieckCounterexample.lean` (rank four, namespace
`Counterexample.GrothendieckPower`), `GrothendieckCounterexampleAllPrimes.lean`
(rank `p^2`, namespace `Counterexample.GrothendieckPowerAllPrimes`), and the
general-purpose `ConvolutionPower.lean` (convolution powers of the identity of
a bialgebra, namespace `AlgHom`, intended for upstreaming to Mathlib; see
`docs/LEAN_ALL_PRIMES.md` for the intended PR structure). The build enables Mathlib's
standard linter set (`weak.linter.mathlibStandardSet`) and is warning-free; the
package passes Batteries' `#lint`, and the main theorems depend only on the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`). See
`docs/LEAN_COUNTEREXAMPLE.md` and `docs/LEAN_ALL_PRIMES.md` for details.

The Lean formalizations were written by the AI assistants Codex (OpenAI) and
Claude (Anthropic); each module records this in its docstring.

## Which construction is primary?

The length-nine rank-four example is the main current construction:

\[
R=(\mathbb Z/4)[x,y]/(x^3,y^3,xy^2-2),
\]

with a rank-four Hopf algebra whose fourth power map is nontrivial and whose
eighth power map is trivial.

The length-ten construction in `manuscripts/archive/rank4/` is a distinct,
useful model: it is a compressed quotient of the earlier universal cubic
construction and contains additional subgroup, embedding, deformation, and
conditional minimality analysis. It is archived rather than discarded.

## Handoff protocol for agents

- Begin with this README and the two current rank-four manuscripts above.
- Treat `archive/handoffs/` as historical context, not as an automatically current claim ledger.
- Before extending a claim, check the newest audit and distinguish proved statements from conditional computational conclusions.
- Keep generated logs, caches, scratch directories, run outputs, ZIP archives, and LaTeX intermediates out of commits.
- Record new computations with the host, software versions, parameters, commit hash, output path, and verification status.

## Provenance

The files were curated from the larger `FiniteFlatGroupSchemes` workspace on
2026-07-13. The original workspace was not modified by this curation.

The file `lean/FiniteFlatGroupSchemes/GrothendieckCounterexample.lean` is the
polished version of the public GitHub gist
[b1fc94332439e1d43944163e1dae3aef](https://gist.github.com/j2d9w5xtjn-png/b1fc94332439e1d43944163e1dae3aef);
the superseded pre-gist first draft survives in git history as
`lean/GrothendieckCounterexample.lean`.
