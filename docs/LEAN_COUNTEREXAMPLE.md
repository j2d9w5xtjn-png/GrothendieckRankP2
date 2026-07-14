# Lean formalization of the rank-four counterexample

The complete formalization is in
`FiniteFlatGroupSchemes/GrothendieckCounterexample.lean`.

It constructs

```text
R = ℤ[a,b]/(a³,b³,a²b+2),
A = R[U,V]/(U²-abU+b²V,V²-a²V),
λ = (1+aU)(1+bV),
Δ(U) = U⊗1+λ⊗U,
Δ(V) = V⊗λ+1⊗V.
```

The main theorem is `counterexample`.  It states that `A` is finite free of rank four and that
its fourth convolution power map is not the unit map.  The stronger coordinate calculations are

```text
powerMap_four_U : [4]♯(U) = 2bUV
two_b_U_v_ne_zero : 2bUV ≠ 0
powerMap_four_v : [4]♯(V) = 0
powerMap_eight : [8]♯ = unit
```

The file also supplies a `Bialgebra R A` instance, a `HopfAlgebra R A` instance whose antipode is
the seventh power word, and the bundled object `coordinateHopfAlgebra : CommHopfAlgCat R`.

Build with:

```bash
lake build
```

The Mathlib checkout is stored outside Dropbox at
`~/.cache/finite-flat-group-schemes/lake`; the project-local `.lake` entry is only a symlink.
