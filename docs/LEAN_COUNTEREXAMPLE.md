# Lean formalization of the rank-four counterexample

The complete formalization is in
`lean/FiniteFlatGroupSchemes/GrothendieckCounterexample.lean`, in the namespace
`Counterexample.GrothendieckPower`.  (An earlier draft of the same proof, superseded by this
file, survives in git history as `lean/GrothendieckCounterexample.lean`.)

The construction and its formalization were carried out by the AI assistants Codex (OpenAI)
and Claude (Anthropic).

It constructs

```text
R = ℤ[a,b]/(a³,b³,a²b+2),
A = R[U,V]/(U²-abU+b²V,V²-a²V),
λ = (1+aU)(1+bV),
Δ(U) = U⊗1+λ⊗U,
Δ(V) = V⊗λ+1⊗V.
```

The main theorem is `counterexample`.  It states, as explicit conjuncts, that `R` is
nontrivial, that `A` is free and finite as an `R`-module with `Module.finrank R A = 4`, and
that the fourth convolution power map is not the unit map.  (The freeness and finiteness
conjuncts ensure the `finrank` conjunct expresses the honest rank.)  The stronger coordinate
calculations are

```text
powerMap_four_U : [4]♯(U) = 2bUV
two_b_U_v_ne_zero : 2bUV ≠ 0
powerMap_four_v : [4]♯(V) = 0
powerMap_eight : [8]♯ = unit
```

The file also supplies a `Bialgebra R A` instance, a `HopfAlgebra R A` instance whose antipode is
the seventh convolution power of the identity, and the bundled object
`coordinateHopfAlgebra : CommHopfAlgCat R`.

`counterexample` and `instHopfAlgebra` depend only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); there is no `sorry` and no added axiom.

## Build

The Lake project lives in `lean/` and pins Lean `v4.31.0` with the matching Mathlib release:

```bash
cd lean
lake build
```

The lakefile enables Mathlib's standard syntax/style linter set
(`weak.linter.mathlibStandardSet`), and the build is warning-free; the package also passes
Batteries' environment linters (`#lint in FiniteFlatGroupSchemes`).

Lake resolves the dependencies through the shared cache at
`~/.cache/finite-flat-group-schemes/lake`, so Mathlib is not re-downloaded or rebuilt;
project-local build products go to `lean/.lake/build`.
