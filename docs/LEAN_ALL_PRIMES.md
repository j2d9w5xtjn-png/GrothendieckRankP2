# Arbitrary-prime Lean formalization

The main source is
[`FiniteFlatGroupSchemes/GrothendieckCounterexampleAllPrimes.lean`](FiniteFlatGroupSchemes/GrothendieckCounterexampleAllPrimes.lean).
It is imported by [`FiniteFlatGroupSchemes.lean`](FiniteFlatGroupSchemes.lean).

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
- the convolution formulas for power maps from any Hopf structure with the
  displayed skew-primitive coproduct.

The nonzero base coefficient is proved by the explicit functional

```text
[b^(p-1)]q - p * [a^p b^(2p-2)]q  in ZMod (p^2),
```

which annihilates each generator of the base ideal and detects
`p * b^(p-1)`. No Gröbner-basis computation is used.

## Explicit remaining proof boundary

The file has no `sorry`, `admit`, or axiom declaration. It does not claim that
the arbitrary-prime Hopf closure has already been checked.

- `HopfPackage p` asks for the concrete coproduct, counit, antipode, all Hopf
  laws, and the required formulas on `U`, `V`, `lambda`, and `lambdaInv`.
- `PowerCertificate p H` asks for the two geometric-sum identities at `p^2`.
- `counterexample H hpow` proves the rank-`p^2` counterexample from those
  explicit certificates.

The main unresolved identity is the odd-prime divided-bridge/truncated-log
calculation ensuring that the proposed coproduct preserves the two defining
relations. An `IsArtinianRing (R p)` instance is also not yet encoded.

## Build

Mathlib was not downloaded into Dropbox. `.lake` remains a symlink to:

```text
~/.cache/finite-flat-group-schemes/lake
```

The following completed successfully:

```bash
lake env lean FiniteFlatGroupSchemes/GrothendieckCounterexampleAllPrimes.lean
lake build
```

The detailed mathematical and formalization report is
[`ALL_PRIMES_LEAN_FORMALIZATION_2026-07-13.tex`](ALL_PRIMES_LEAN_FORMALIZATION_2026-07-13.tex),
with a compiled PDF beside it.
