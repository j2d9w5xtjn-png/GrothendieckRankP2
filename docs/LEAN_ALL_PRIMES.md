# Arbitrary-prime Lean formalization

The main source is
`lean/FiniteFlatGroupSchemes/GrothendieckCounterexampleAllPrimes.lean`, in the namespace
`Counterexample.GrothendieckPowerAllPrimes`.  Its convolution-theoretic input is the
separate general-purpose module
`lean/FiniteFlatGroupSchemes/ConvolutionPower.lean` (namespace `AlgHom`), which knows
nothing about the counterexample.  Both are imported by the root module
`lean/FiniteFlatGroupSchemes.lean`.

The formalization was carried out by the AI assistants Codex (OpenAI) and
Claude (Anthropic).

## Verified unconditionally

For every `p : ℕ` with `[Fact p.Prime]`, Lean verifies:

- the base
  `R p = ℤ[a,b] / (a^(p+1), b^(2*p-1), a^p*b^(p-1)+p)` is nontrivial;
- `p^2 = 0`, `p * b^p = 0`, and `p * b^(p-1) ≠ 0` in `R p`;
- the two monic degree-`p` extensions defining `B p` and `A p`;
- `Module.Free (R p) (A p)` and `Module.Finite (R p) (A p)`;
- `Module.finrank (R p) (A p) = p^2` (`finrank_A`);
- the defining `U`- and `V`-relations;
- `p * b^(p-1) * U * V^(p-1) ≠ 0` in `A p` (`carry_ne_zero`);
- for an arbitrary commutative bialgebra (in `ConvolutionPower.lean`): the `n`-th
  convolution power of the identity is `g ^ n` on a group-like element `g`
  (`AlgHom.convPowId_apply_of_isGroupLikeElem`) and a geometric sum on a skew-primitive
  element (`AlgHom.convPowId_apply_of_comul_eq_tmul_one_add_tmul` and its mirror).

The nonzero base coefficient is proved by the explicit functional

```text
[b^(p-1)]q - p * [a^p b^(2p-2)]q  in ZMod (p^2),
```

which annihilates each generator of the base ideal and detects
`p * b^(p-1)`. No Gröbner-basis computation is used.

## Explicit remaining proof boundary

The files have no `sorry`, `admit`, or axiom declaration, and the main theorems
depend only on the standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). They do not claim that the arbitrary-prime Hopf closure has
already been checked.

- `HopfPackage p` asks for the concrete coproduct, counit, antipode, all Hopf
  laws, and the skew-primitive coproduct formulas on `U`, `V` (stated with
  `⊗ₜ`), together with the group-likeness of `lambda` and `lambdaInv`.
- `HopfPackage.PowerCertificate` asks for the two geometric-sum identities at
  `p^2` (fields `geom_sum_lambda`, `geom_sum_lambdaInv`).
- `HopfPackage.counterexample` proves the rank-`p^2` counterexample from those
  explicit certificates; its statement includes `Nontrivial (R p)`,
  `Module.Free (R p) (A p)`, and `Module.Finite (R p) (A p)` as explicit
  conjuncts, so the `finrank` conjunct expresses the honest rank.

The main unresolved identity is the odd-prime divided-bridge/truncated-log
calculation ensuring that the proposed coproduct preserves the two defining
relations. An `IsArtinianRing (R p)` instance is also not yet encoded.

## Intended mathlib PR structure

1. **Convolution powers** (`ConvolutionPower.lean`): additions to
   `Mathlib.RingTheory.Bialgebra.Convolution` (or a new
   `Mathlib/RingTheory/Bialgebra/ConvolutionPower.lean`).  The file is fully
   general: `AlgHom.convPowId`, the group-like evaluation lemmas, and the
   skew-primitive geometric-sum lemmas, phrased with mathlib's
   `IsGroupLikeElem` and geometric sums (`Mathlib.Algebra.Ring.GeomSum`).
2. **The counterexample base**: the remainder of
   `GrothendieckCounterexampleAllPrimes.lean`, targeted at mathlib's
   `Counterexamples/` library (namespace `Counterexample.…` follows its
   convention).  The general `AdjoinRoot` lemma
   `algebraMap_mul_root_pow_ne_zero` (nonvanishing of scalar multiples of
   power-basis vectors, without a domain hypothesis) could be split into
   `Mathlib.RingTheory.AdjoinRoot` on the way.

## Build

The Lake project lives in `lean/` and pins Lean `v4.31.0` with the matching
Mathlib release:

```bash
cd lean
lake build
```

The lakefile enables Mathlib's standard syntax/style linter set
(`weak.linter.mathlibStandardSet`), and the build is warning-free; the package
also passes Batteries' environment linters (`#lint in FiniteFlatGroupSchemes`).

Lake resolves the dependencies through the shared cache at
`~/.cache/finite-flat-group-schemes/lake`, so Mathlib is not re-downloaded or
rebuilt; project-local build products go to `lean/.lake/build`.

The detailed mathematical and formalization report is
`ALL_PRIMES_LEAN_FORMALIZATION_2026-07-13.tex` (see `manuscripts/`), with a
compiled PDF beside it.
