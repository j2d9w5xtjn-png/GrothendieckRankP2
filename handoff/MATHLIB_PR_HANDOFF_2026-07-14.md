# Handoff: PRing the Lean formalization into mathlib (2026-07-14)

Audience: the next agent (or human) preparing mathlib pull requests from this
repository. Everything described here is committed on `main` (through
`c1b0c70`) and pushed to
`https://github.com/j2d9w5xtjn-png/GrothendieckRankP2`.

## Current state

The Lake project `lean/` (Lean `v4.31.0`, mathlib release `v4.31.0`, rev
`fabf563a7c95`) contains three modules under `lean/FiniteFlatGroupSchemes/`:

1. `GrothendieckCounterexample.lean` (~1360 lines, namespace
   `Counterexample.GrothendieckPower`): the **complete, standalone** rank-four
   counterexample. Main declarations:
   - `counterexample`: `Nontrivial R ∧ Module.Free R A ∧ Module.Finite R A ∧
     finrank R A = 4 ∧ powerMap 4 ≠ unit ∘ counit`;
   - `instHopfAlgebra`, `coordinateHopfAlgebra : CommHopfAlgCat R`;
   - `affineGroupScheme : Grp (CommAlgCat R)ᵒᵖ` and
     `monPowMap_affineGroupScheme_four_ne` (group-scheme formulation via
     `commHopfAlgCatEquivCogrpCommAlgCat`);
   - `orderOf_universalPoint : orderOf universalPoint = 8`;
   - `not_isCocomm : ¬Coalgebra.IsCocomm R A` (Deligne consistency check);
   - `isGroupLikeElem_lambda`.
2. `GrothendieckCounterexampleAllPrimes.lean` (namespace
   `Counterexample.GrothendieckPowerAllPrimes`): the uniform rank-`p^2`
   construction; unconditional up to the explicit proof boundary `HopfPackage`
   / `PowerCertificate`. **Not PR-ready** (see last section).
3. `ConvolutionPower.lean` (namespace `AlgHom`): generic convolution powers of
   the identity of a bialgebra. Self-contained, imports three mathlib files.

Verification status (all three modules): `lake build` is warning-free with
`weak.linter.mathlibStandardSet = true`; Batteries' `#lint in
FiniteFlatGroupSchemes` reports 0 errors across 16 linters; every theorem
named above depends only on `propext`, `Classical.choice`, `Quot.sound`; no
`sorry`, no added axioms.

Reproduce the checks:

```bash
cd lean && lake build          # expect zero warnings
```

```lean
-- scratch file, run with `lake env lean <file>`
import FiniteFlatGroupSchemes
#lint in FiniteFlatGroupSchemes
#print axioms Counterexample.GrothendieckPower.counterexample
#print axioms Counterexample.GrothendieckPower.monPowMap_affineGroupScheme_four_ne
```

## PR 1 (primary): the rank-four counterexample

**Scope: exactly one file.** `GrothendieckCounterexample.lean` imports only
mathlib (eight files) and nothing from this repository; in particular it does
NOT use `ConvolutionPower.lean` (it carries its own inline convolution
lemmas, which is correct for a self-contained `Counterexamples/` file).

Steps:

1. *(Recommended)* Open a Zulip thread first (`#mathlib4` on
   leanprover.zulipchat.com) announcing the result, with the statement of
   `counterexample`, the gist link
   (https://gist.github.com/j2d9w5xtjn-png/b1fc94332439e1d43944163e1dae3aef),
   and the manuscript reference. A research-level counterexample will get
   naming/placement feedback that is cheaper to absorb before the PR.
2. Fork/clone mathlib master; `lake exe cache get`; create a branch, e.g.
   `grothendieck-power-counterexample`.
3. Copy the file to `Counterexamples/GrothendieckPower.lean`. The namespace
   `Counterexample.GrothendieckPower` already follows that library's
   convention. Keep the copyright header; `Authors:` stays the human
   maintainer.
4. Register it: add `import Counterexamples.GrothendieckPower` to
   `Counterexamples.lean` (alphabetical order).
5. Add to `docs/references.bib` (keys must match the docstring citations):

   ```bibtex
   @Article{ oorttate1970,
     author = {Oort, Frans and Tate, John},
     title = {Group schemes of prime order},
     journal = {Ann. Sci. \'{E}cole Norm. Sup. (4)},
     volume = {3},
     year = {1970},
     pages = {1--21}
   }
   @InCollection{ tate1997,
     author = {Tate, John},
     title = {Finite flat group schemes},
     booktitle = {Modular forms and {F}ermat's last theorem ({B}oston, {MA},
                  1995)},
     pages = {121--154},
     publisher = {Springer, New York},
     year = {1997}
   }
   ```

6. Rebase fixes: the file is developed against mathlib `v4.31.0`, and the
   APIs it uses are young and moving — expect (mechanical) drift in
   `QuadraticAlgebra`, `WithConv`/`AlgHom` convolution,
   `CommHopfAlgCat`/`CommBialgCat`/`CommAlgCat.Monoidal`, `IsGroupLikeElem`,
   `MonObj`/`GrpObj`/`Grp`, `orderOf_eq_prime_pow`. Also check whether
   `Counterexamples/` has migrated to the module system (`module` +
   `public import` headers) by then; if so, mirror a neighboring file.
7. Local checks before pushing: `lake build Counterexamples.GrothendieckPower`
   and `lake exe lint-style`; CI runs the environment linters.
8. PR description must include: the informal statement; one-paragraph
   background (Grothendieck's question; Deligne's theorem for the commutative
   case; references as in the docstring); a five-line proof sketch (base ring
   with `2b ≠ 0` certified by an explicit 512-element model; two nested
   quadratic algebras; `λ = (1+aU)(1+bV)` group-like; `[4]♯U = 2bUV ≠ 0`;
   `[8]♯ = unit`, antipode `= [7]♯`); the axiom audit; and — required by
   mathlib policy — **explicit disclosure that the formalization was written
   by the AI assistants Codex (OpenAI) and Claude (Anthropic)** (the module
   docstring already states this; repeat it in the PR body). Suggested
   title: `feat(Counterexamples): a finite free group scheme of order four
   not killed by four`. Label: `t-algebra`.
9. Anticipated review requests, with prepared answers:
   - *"Factor the convolution power-map lemmas into `RingTheory/Bialgebra`"*:
     `lean/FiniteFlatGroupSchemes/ConvolutionPower.lean` is the ready-made
     answer (see PR 2); offer it as a follow-up or fold it in, as the
     reviewer prefers.
   - *"`monPowMap` belongs in `CategoryTheory/Monoidal/Cartesian`"*: also
     fine; it is deliberately general.
   - Naming bikesheds (`lambda`, `theta`, file name): no attachment; rename
     freely.

## PR 2 (optional, independent): convolution powers of the identity

`ConvolutionPower.lean` → `Mathlib/RingTheory/Bialgebra/ConvolutionPower.lean`
(or merged into the existing `Convolution.lean`). Contents: `AlgHom.convPowId`
plus evaluation on group-like elements (`= a ^ n`) and on skew-primitive
elements (geometric sums). It depends on nothing in this repository and can
be PRed before or after PR 1; if PR 1 lands first, this PR can refactor the
counterexample file to use it.

## Not PR-ready: the all-primes file

`GrothendieckCounterexampleAllPrimes.lean` is conditional on `HopfPackage p`
(the Hopf closure) and `PowerCertificate` (two geometric-sum identities).
Mathlib's `Counterexamples/` will not take a conditional framework, so do not
PR it yet. The formalization path to discharge it, in order (details in
`docs/LEAN_ALL_PRIMES.md` and the manuscript
`manuscripts/drafts/arbitrary-prime/A_RANK_P_SQUARED_COUNTEREXAMPLE_FOR_EVERY_PRIME_2026-07-12.tex`):

1. Construct `HopfPackage 2` in the `AdjoinRoot` presentation (the quadratic
   `linear_combination` certificates from the `p = 2` file adapt); this
   validates the whole pipeline and gives the template for odd `p`.
2. The Oort–Tate divided affine identity (manuscript Lemma 4.1), proved in
   the universal domain `ℤ[c,d,X,Y]/(c^(p-1)·d - p)` and transported.
3. The divided bridge lemma (manuscript §5.2, truncated logarithm) — the hard
   step; either via `MvPowerSeries.subst` and `PowerSeries.Log`, or via a
   finitary route through the congruence `wᵢ ≡ (-1)^(i-1)/i (mod p)`.
4. Closure of both relations, group-likeness of `λ`, the antipode, and the
   `p^2` geometric-sum carry (`PowerCertificate`).

## Repository pointers

- `docs/LEAN_COUNTEREXAMPLE.md` — the `p = 2` file's contents and build
  instructions.
- `docs/LEAN_ALL_PRIMES.md` — the all-primes proof boundary and the intended
  PR split.
- The mathlib build cache is shared at
  `~/.cache/finite-flat-group-schemes/lake`; `cd lean && lake build` needs no
  downloads on this machine.
