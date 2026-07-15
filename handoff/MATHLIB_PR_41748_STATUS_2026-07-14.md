# Handoff: mathlib PR #41748 (rank-four Grothendieck counterexample) — status & next steps

Audience: the next agent (or human) continuing the upstreaming of the rank-four
counterexample into mathlib. This continues
`handoff/MATHLIB_PR_HANDOFF_2026-07-14.md` (which described how to open the PR);
this file records what happened after it was opened.

Date: 2026-07-14.

## TL;DR

- **PR #41748 is OPEN and live**:
  https://github.com/leanprover-community/mathlib4/pull/41748
  Title: `feat(Counterexamples): a finite free group scheme of order four not killed by four`.
- It is **blocked on #40500** (`- [ ] depends on: #40500` is in the PR
  description). Do not push for merge until #40500 lands.
- All reviewer feedback so far is **addressed in code and pushed**. CI green
  locally (build warning-free, `#lint` 0 errors, `lint-style` clean, axioms =
  `[propext, Classical.choice, Quot.sound]`).
- **The human (Akhil) posts all GitHub review replies** — the agent must NOT
  post comments on GitHub. Provide reply scaffolds only.

## Environment / locations

- **mathlib clone**: `/Users/akhilmathew/mathlib4`
  - Fork remote `origin`: `https://github.com/j2d9w5xtjn-png/mathlib4.git`
  - `upstream`: `leanprover-community/mathlib4`
  - Branch: `grothendieck-power-counterexample`
  - Toolchain: `leanprover/lean4:v4.32.0` (master moved from the source repo's
    v4.31.0). Cache already fetched (`lake exe cache get`).
- **`gh` CLI** is authenticated as GitHub account `j2d9w5xtjn-png` (the PR
  author). If a different account should own the PR, that must be changed before
  any further pushes.
- **Source of truth for the maths**: this repo `GrothendieckRankP2`, file
  `lean/FiniteFlatGroupSchemes/GrothendieckCounterexample.lean`. The mathlib copy
  is `Counterexamples/GrothendieckPower.lean` (namespace
  `Counterexample.GrothendieckPower`). NOTE: fixes made on the mathlib copy have
  NOT been back-ported to the source repo (see "Drift" below).

## The PR: scope and commits

Base (upstream merge-base): `383070160f`. Four commits on the branch:

1. `8fa46dee5a` feat: the file itself — `Counterexamples/GrothendieckPower.lean`
   (the p=2 counterexample, ~1360 lines), an `import` line in
   `Counterexamples.lean`, and two `docs/references.bib` entries
   (`oorttate1970`, `tate1997`). The all-primes file is intentionally excluded.
2. `721aeaa63d` docs: reworded the group-scheme docstrings (metakunt).
3. `64a4f99c0e` refactor: removed 4 redundant scalar-tower instances (metakunt).
4. `82d43c5af1` feat: added `exists_hopfAlgebra_not_killed_by_finrank` +
   riccardobrasca's cleanups.

Disclosure/authorship (mathlib policy — keep this way): `Authors: Akhil Mathew`;
NO `Co-Authored-By: Claude` trailer; AI involvement disclosed as prose in the
module docstring, commit bodies, and PR body. Human is the responsible author.

## Review threads — status and reply scaffolds (human to post)

The agent posted NOTHING. These threads await Akhil's replies. Best practice:
reply per-thread and mark resolved, not one big comment.

1. **metakunt — "why not `AffineScheme`/`Scheme` API; `Spec A` appears in
   docstrings but there's no `Spec`."** Resolved in code (`721aeaa63d`):
   reworded docstrings to name `op A` in `(CommAlgCat R)ᵒᵖ` and added a section
   note. Verified there is currently NO Hopf-algebra ↔ scheme-group-object bridge
   in mathlib (`grep HopfAlgebra Mathlib/AlgebraicGeometry` is empty; the scheme
   group-scheme dev in `AlgebraicGeometry/Group/` is `GrpObj (Over (Spec R))`
   with no Hopf link). #40500 is exactly that bridge → tie the reply to it.

2. **metakunt — redundant `IsScalarTower R B B` (suggested
   `QuadraticAlgebra.instIsScalarTower`).** Resolved (`64a4f99c0e`). It's really
   `IsScalarTower.right` (general). Testing showed 3 MORE redundant instances
   (`IsScalarTower R A A`, `IsScalarTower R B A`, `SMulCommClass R A A`) — all
   removed; only the explicit `Algebra R A` kept.

3. **metakunt & eric-wieser — "write a theorem that spells out Grothendieck's
   question in the statement."** Resolved (`82d43c5af1`):
   `exists_hopfAlgebra_not_killed_by_finrank` — an existential over any
   commutative Hopf algebra, exponent = `Module.finrank S H`, so it reads "not
   killed by its own order." NOTE: it's stated Hopf-algebra-side (via the
   `WithConv` convolution monoid). eric commented on the group-scheme
   (`monPowMap`) theorem, so his reply should offer a `monPowMap`/group-object
   variant — which #40500 will make clean.

4. **riccardobrasca — batch of local suggestions.** All resolved (`82d43c5af1`):
   `reduce` → `RingHom` (`ZMod.castHom` directly); `aEnd`/`bEnd` docstrings
   clarify `a`,`b` are the two base-ring generators; `aEnd_bEnd_comm : Commute`;
   `generators_commute` uses `{x y} (hx) (hy)` binders; dropped `Nontrivial B`/`A`
   (auto from `QuadraticAlgebra.instNontrivial` + `Nontrivial R`); `ap`/`bp` →
   `abbrev`.

5. **riccardobrasca — "use `grind` as much as possible / does grind help here?"**
   NOT viable, no code change. `grind` errors on the ring-identity proofs:
   `` `grind` internal error, `NoNatZeroDivisors` instance is needed, but it is
   not available for S ``. This is fundamental: the base ring has `4 = 0` while
   `2b ≠ 0` (the crux of the counterexample), so `NoNatZeroDivisors` is false and
   grind's ring solver cannot run. `linear_combination` certificates are
   necessary. Reply: say exactly this.

## Blocked on #40500 — the planned rewrite

#40500 (Yaël Dillies, branch `hopf_affine`): "feat: correspondence between
affine group schemes and Hopf algebras". This is the bridge metakunt/eric wanted.

**Plan once #40500 merges:**
1. Rebase this branch onto new master (`git fetch upstream && git rebase
   upstream/master`; `lake exe cache get`).
2. Restate the group-scheme formulation (`affineGroupScheme`,
   `monPowMap_affineGroupScheme_four_ne`) and ideally
   `exists_hopfAlgebra_not_killed_by_finrank` through the real
   `AlgebraicGeometry` affine-group-scheme ↔ Hopf correspondence from #40500 —
   replacing the ad-hoc `Grp (CommAlgCat R)ᵒᵖ` + `WithConv` encoding with the
   genuine `Spec`/`Scheme` group-object statement. This directly answers
   metakunt (use the scheme API) and eric (group-scheme-side spelled-out
   statement).
3. Remove the `depends on: #40500` line from the PR body once done.

Until then: no statement rework; just keep CI green on rebases.

## Other open (NON-blocked) items

- **File/theorem RENAME (undecided).** `GrothendieckPower.lean` names the
  *question's poser*, not the construction (Grothendieck didn't build this).
  mathlib `Counterexamples/` convention for "refutes statement X" is descriptive
  (`CliffordAlgebraNotInjective`, `HomogeneousPrimeNotPrime`). A descriptive
  name like `GroupSchemeNotKilledByOrder` was floated. Renaming touches: file
  name, the `import` in `Counterexamples.lean`, and the `namespace`. The original
  handoff says naming is "no attachment; rename freely." DECISION NEEDED FROM
  AKHIL.
- **Extend `abbrev` change.** riccardobrasca's general point ("defs that are just
  an existing object should be `abbrev`") could extend to `a`, `b`, `U`, `V`,
  `v`. Held off: flipping these risks perturbing the many `simp [U]`/`unfold`
  proofs. Test individually if desired.
- **Back-port fixes to the source repo.** The mathlib copy has diverged from
  `lean/FiniteFlatGroupSchemes/GrothendieckCounterexample.lean`: two removed
  `ring` calls (v4.31→v4.32 drift), the 4 removed scalar-tower instances, the
  riccardobrasca cleanups, and the new theorem. If keeping the source repo in
  sync matters, port these back. Not required for the PR.

## Verification (run in `/Users/akhilmathew/mathlib4`)

```bash
lake build Counterexamples.GrothendieckPower        # expect warning-free
lake exe lint-style                                 # style; expect no GrothendieckPower output
```

```lean
-- scratch file, run: lake env lean <file>
import Counterexamples.GrothendieckPower
#print axioms Counterexample.GrothendieckPower.counterexample
#print axioms Counterexample.GrothendieckPower.exists_hopfAlgebra_not_killed_by_finrank
#lint in Counterexamples.GrothendieckPower          -- expect 0 errors, 14 linters
```

Expected: 0 errors / 141 declarations; axioms `[propext, Classical.choice,
Quot.sound]`; no `sorry`, no added axioms.

## Gotchas learned (save time)

- **HopfAlgebra hypothesis incantation**: use `[CommSemiring S] [Semiring H]
  [HopfAlgebra S H]` — do NOT also add `[Algebra S H]`; `HopfAlgebra` (via
  `Bialgebra`) already provides it, and the extra binder creates an
  `SMul S H` instance diamond that breaks `Monoid (WithConv …)` synthesis.
- **`WithConv` convolution API** (`Mathlib/RingTheory/Bialgebra/Convolution.lean`):
  `Monoid (WithConv (C →ₐ[R] A))` needs `[CommSemiring R] [CommSemiring A]
  [Semiring C] [Bialgebra R C] [Algebra R A]`; `1` = `unit ∘ counit`;
  "killed by n" ⟺ `toConv (AlgHom.id) ^ n = 1`. The file's `orderOf universalPoint
  = 8` gives `^4 ≠ 1` via `pow_ne_one_of_lt_orderOf`.
- **`Commute` + `decide`**: `Decidable (Commute a b)` does NOT synthesize
  (Commute doesn't unfold for TC). Prove the equation and let defeq coerce:
  `theorem … : Commute a b := (by decide +kernel : a * b = b * a)`.
- **`show` linter**: the mathlib linter flags the `show` *tactic* used for a
  defeq goal change. Use a typed `have` (e.g. `have h8 : orderOf (…) = 8 :=
  orderOf_universalPoint; rw [h8]`) instead.
- **`grind` + small characteristic**: grind's ring solver requires
  `NoNatZeroDivisors`; unusable on this base ring (`4 = 0`).

## Constraints to respect

- **No LLM-authored GitHub comments** — Akhil writes all review replies himself.
  The agent may push commits and edit the PR description, but must not post
  review/issue comments (`gh pr comment`, thread replies, etc.). Provide
  scaffolds only.
- **Human authorship / no AI co-author trailer**; AI disclosed as prose.
- **Confirm before pushing** — Akhil has wanted to proofread diffs before they go
  public; show the diff and get a go-ahead before `git push` / `gh pr edit`.
