# A lower-memory route to the `certs.m2` certificates

## Executive conclusion

The original `scripts/certs.m2` spends memory on the wrong certificate
problem.  It computes a degree-limited Groebner basis with a change matrix for
all Hopf equations: 403 generators in the `xy` branch and 427 in the `t4`
branch.  The already completed computation in `scripts/minassoc.m2` proves the
strictly stronger containment using only associativity and multiplicativity of
the coproduct:

| branch | generators | targets | first degree at which all targets reduce to zero |
|---|---:|---:|---:|
| `xy` | 157 | 21 | 5 |
| `t4` | 178 | 24 | 6 |

These numbers and the successful membership verdicts are recorded in
`scripts/minassoc.log`.  The longest no-change-matrix stage there took about
205 seconds.  This motivated using a certificate version of `minassoc.m2`
instead of another 403/427-generator calculation.

The completed implementation uses four reductions, in this order:

1. use the 157/178 minimal-axiom generators;
2. quotient out their 19/28 linear generators and let `prune` eliminate the
   corresponding variables before the expensive calculation;
3. use both `DegreeLimit` and `HardDegreeLimit`, and run the two branches in
   separate operating-system processes;
4. reduce each target directly against the change-matrix-bearing
   `GroebnerBasis` object, without materializing `gens G`,
   `getChangeMatrix G`, or `forceGB`.

Every resulting certificate must finally be multiplied out in the original
117-variable polynomial ring.  That last assertion makes all the
degree-limit, pruning, and heuristic choices proof-irrelevant.

## Execution result (2026-07-10)

The low-memory route has now completed both branches.  The implementation is
[`scripts/certs_lowmem.m2`](scripts/certs_lowmem.m2); a fresh-process verifier
is [`scripts/verify_certs_lowmem.m2`](scripts/verify_certs_lowmem.m2).

| branch | linear quotient | reduced equations | tracked degree cap | result | maximum sampled RSS |
|---|---:|---:|---:|---|---:|
| `xy` | 117 to 100 variables | 109 nonzero images | 5 | 21/21 direct certificates | 2,278,368 KiB observed at 9 s |
| `t4` | 117 to 95 variables | 133 nonzero, 119 distinct images | 5 | 24/24 direct certificates | 7,519,104 KiB |

The `t4` quotient-and-deduplication scan changed the apparent degree frontier:
the open target indices were

```text
degree 2: {1,3,4,6,7,12,15,20,23}
degree 3: {1,4,6,7,12,15,20}
degree 4: {1,4,7,23}
degree 5: {}
```

Thus no degree-6 change-matrix run and no equation-core search were needed.
The exact scan data, including all eliminated and representative generator
indices, is in
[`scripts/certs_lowmem_t4_pruned_scan_20260710.m2data`](scripts/certs_lowmem_t4_pruned_scan_20260710.m2data)
(SHA-256 `28c6dc18ef9cb6de1321e8f5974c890c3afb650f3b08e6accd0fcacbeb28e586`).

The final certificate artifacts are:

- [`scripts/certs_lowmem_pruned_xy.m2out`](scripts/certs_lowmem_pruned_xy.m2out),
  SHA-256 `f9918bfc253397bb40a73e8b4d52561de4ea1918fd5d4f92cbee4fe52c98dad4`;
- [`scripts/certs_lowmem_pruned_t4_d5.m2out`](scripts/certs_lowmem_pruned_t4_d5.m2out),
  SHA-256 `bcc97695dabf5d6a8b225c470861c652a988a8a4129d0bf1512551720caa29f0`.

Both were loaded in fresh Macaulay2 processes.  The verifier multiplied every
printed cofactor vector by the printed 157- or 178-generator row in the
original 117-variable ring and obtained the printed target exactly: 21/21 for
`xy` and 24/24 for `t4`.

The clean `xy` pruned run had sampled RSS 2,278,368 KiB at 9 seconds and had
finished before the next five-second sample; the tracked-basis time was not
separately instrumented.  The final `t4` tracked basis took 31.2485 seconds,
the whole monitored process took 52 seconds, and it exited 0 with sampled peak
RSS 7,519,104 KiB (about 7.17 GiB), below its 7.5 GiB cutoff.  Its crash-safe
status is `state=complete, exit=0` in
[`scripts/certs_lowmem_certpruned5_t4_run_20260710.status`](scripts/certs_lowmem_certpruned5_t4_run_20260710.status).
The full monitored transcript is
[`scripts/certs_lowmem_certpruned5_t4_run_20260710.log`](scripts/certs_lowmem_certpruned5_t4_run_20260710.log).

The independent verification commands are

```sh
env CERT_BRANCH=xy CERT_VARIANT=pruned \
  /opt/homebrew/bin/M2 --script scripts/verify_certs_lowmem.m2
env CERT_BRANCH=t4 CERT_VARIANT=pruned5 \
  /opt/homebrew/bin/M2 --script scripts/verify_certs_lowmem.m2
```

Both exited 0 with every target marked `PASS`.  The `t4` output is archived in
[`scripts/verify_certs_lowmem_pruned_t4_d5_20260710.log`](scripts/verify_certs_lowmem_pruned_t4_d5_20260710.log)
(SHA-256 `553b0fda9fd6e213425b7720f59a81f13dfacecbf3768a9e1170d86f8737c62e`).
The clean `xy` fresh-verifier output was observed in its launching transcript
but was not separately redirected; as persistent belt-and-braces evidence,
the earlier atomic artifact
[`scripts/certs_lowmem_xy.m2out`](scripts/certs_lowmem_xy.m2out) and its
generation log
[`scripts/certs_lowmem_xy_run_20260710.log`](scripts/certs_lowmem_xy_run_20260710.log)
record all 21 direct verifications before the post-save watchdog termination.
Their SHA-256 hashes are respectively
`50dcca3f999ee40b59e4ebe0b4622ca2f21ff16032a7d6dd0d7ffd0d058d0651` and
`eb311ac2a8841c9ef166e6abb36eeb72f0bc1e1dbc823030cbd5aaab3ed3c401`.

The final `t4` generation log and status hashes are, respectively,
`002e5820bde6f47ccebe9e1a191209414888d059f6b930d56753cf7a6e212d56`
and `b6b1086cff3559aa2b05724c14e6842fab8334ed355a0f0eed802414bf5001ee`.
The verifier script used for both branches has SHA-256
`d5df59262b39e50445d18f90e532ad472ddf7705a4bcae5d832cd915035e6232`.

### Theorem strength

For each of the two special-fiber multiplication types, let `I_MA` be the
ideal in the universal 117-variable coefficient ring over `F_2` generated by
the epsilon-digit equations for multiplication associativity and
Delta-multiplicativity.  The artifacts give an explicit identity

```text
b = sum_j v_j g_j
```

for every nonzero coefficient `b` of `[4]^#`, with every `g_j` an original
generator of `I_MA`.  Hence every coefficient of `[4]^#` lies in `I_MA` as a
universal polynomial identity.  The result therefore specializes to every
`F_2`-algebra `k`: every encoded rank-four structure over
`k[eps]/(eps^3)` in either branch that is associative and has multiplicative
coproduct is killed by four.

This is stronger than the original certificate target: the certificate ideal
does not use coassociativity, an antipode, or the special-fiber `[2]=0`
equations.  In particular it applies to the intended commutative rank-four
Hopf algebras.  It settles this universal equal-characteristic length-three
step; by itself it is not a proof over arbitrary Artin local bases and hence
is not a complete resolution of Grothendieck's conjecture.

An initial implementation of reductions 1, 3, and 4 is now in
`scripts/certs_lowmem.m2`.  Its untracked checks reproduced the archived
memberships in 3.4 seconds (`xy`, degree 5) and 23.3 seconds (`t4`, degree 6).
The first tracked `xy` basis finished in 37.42 seconds.  It passed the
membership gate, directly verified all 21 certificates, and atomically saved
`scripts/certs_lowmem_xy.m2out` (SHA-256
`50dcca3f999ee40b59e4ebe0b4622ca2f21ff16032a7d6dd0d7ffd0d058d0651`).
A conservative 8 GB watchdog sent SIGTERM only after the save, when a brief
post-computation RSS sample reached 8,895,168 KiB; this explains the otherwise
misleading `exit=143` status.  Thus the refactor has reduced the old
multi-hour/roughly-45-GB computation dramatically, while also showing that the
linear-elimination step below remains worthwhile for `t4` and for a clean
low-peak independent rerun.

## Why the present script is expensive

The expensive line is

```m2
G = gb(ideal gensList, DegreeLimit => 6, ChangeMatrix => true);
```

`ChangeMatrix => true` makes the engine retain, for every basis element, a
polynomial vector indexed by every original generator.  The current script
then creates further front-end copies:

```m2
gbMat = gens G;
chg = getChangeMatrix G;
F = forceGB gbMat;
u = matrix{{b}} // F;
v = chg * u;
```

Those copies are unnecessary.  In Macaulay2 1.25.11 a Groebner basis that was
created with `ChangeMatrix => true` can itself perform the lift:

```m2
v = matrix{{b}} // G;
assert(Gmat * v == matrix{{b}});
```

Here `v` has one row per original column of `Gmat`.  This behavior was checked
directly in the installed Macaulay2.  It does not remove the engine's change
matrix, but it avoids materializing the whole basis and transformation matrix
a second time after the computation.

By contrast, the apparently attractive command

```m2
v = quotient(matrix{{b}}, Gmat, DegreeLimit => 6,
             MinimalGenerators => false);
```

should not be used as the main route.  It does return coefficients against the
original generators without an explicit `ChangeMatrix` option, but the default
implementation goes through `Hom`/kernel machinery.  A modest synthetic probe
with 18 variables and 36 generators had already reached 5.5 GB RSS after 80
seconds without finishing.  It hides, rather than solves, the provenance
problem.

## Exact linear-elimination construction

Let `gensList` be the 157 or 178 original minimal-axiom polynomials in `Q2`,
and let `bQ2` be the target list.  The following is executable Macaulay2-style
pseudocode; the final script should retain the assertions shown here.

```m2
linPos = select(toList(0..#gensList-1),
    i -> first degree(gensList#i) == 1);
nonPos = select(toList(0..#gensList-1),
    i -> not member(i, linPos));

linList = apply(linPos, i -> gensList#i);
Lmat = matrix{linList};
L = ideal linList;

T = Q2/L;
S = prune T;
rho = T.minimalPresentationMap * map(T,Q2); -- S <-- Q2
rhoInv = T.minimalPresentationMapInv;       -- T <-- S
liftS = q -> lift(rhoInv(q), Q2);

assert all(linList, g -> rho(g) == 0);

pairs = select(apply(nonPos, i -> {i, rho(gensList#i)}),
               p -> p#1 != 0);
redPos = apply(pairs, p -> p#0);
redList = apply(pairs, p -> p#1);
RedMat = matrix{redList};

G = gb(RedMat,
       DegreeLimit => d,
       HardDegreeLimit => d,
       ChangeMatrix => true);

GL = gb(Lmat, ChangeMatrix => true, HardDegreeLimit => 1);

for b in bQ2 do (
    bb := rho(b);
    qS := matrix{{bb}} // G;
    if RedMat*qS == matrix{{bb}} then (
        qQ := matrix apply(entries qS,
                            row -> apply(row, liftS));
        RedQ := matrix{apply(redPos, i -> gensList#i)};
        residual := matrix{{b}} - RedQ*qQ;

        -- residual maps to zero in S, hence lies in the linear ideal L.
        assert(rho((entries residual)#0#0) == 0);
        qL := residual // GL;
        assert(Lmat*qL == residual);

        -- Insert qL and qQ in their original positions.
        vv := new MutableList from toList(#gensList:0_Q2);
        for j from 0 to #linPos-1 do vv#(linPos#j) = qL_(j,0);
        for j from 0 to #redPos-1 do vv#(redPos#j) = qQ_(j,0);
        v := transpose matrix{toList vv};

        -- This is the proof.  It takes place in the original ring Q2.
        assert(matrix{gensList}*v == matrix{{b}});
        );
    );
```

The implemented runs printed and checked the actual ranks.  In `xy`, the 19
linear equations eliminate 17 variables, reducing 117 variables to 100 and
leaving 109 nonzero equation images.  In `t4`, the 28 linear equations
eliminate 22 variables, reducing 117 variables to 95; the 133 nonzero images
collapse to 119 distinct equations after exact deduplication.  The `prune`
maps and their inverses are used explicitly in the certificate reconstruction.

It is harmless to remove duplicate nonzero entries of `redList`, provided one
retains one original index for every surviving polynomial.  That can reduce
the change-matrix row count below the initial upper bounds of 138 and 150.

## Soundness of the quotient-and-reconstruct step

Write `L` for the ideal of selected linear axioms and
`rho : Q2 -> S = Q2/L` for the exact quotient map followed by the isomorphism
created by `prune`.  Suppose the reduced calculation produces

```text
rho(b) = sum_i qbar_i rho(g_i).
```

Choose arbitrary polynomial lifts `q_i` of the `qbar_i`.  Then

```text
r = b - sum_i q_i g_i
```

lies in `ker(rho)=L`.  Dividing `r` by the linear Groebner basis gives
`r=sum_j ell_j l_j`.  Consequently

```text
b = sum_i q_i g_i + sum_j ell_j l_j
```

in the original ring.  The final direct matrix multiplication verifies this
identity independently of every Groebner-basis claim.

`HardDegreeLimit` is also safe in this workflow.  For an inhomogeneous system
it may make the partial basis incomplete; that can cause a genuine member to
fail to reduce to zero, but it cannot create a false certificate once the
displayed original-ring multiplication assertion passes.

## Degree and target stratification

The completed no-change-matrix run gives a useful schedule.

For `xy`, the number of unresolved targets after degrees 2, 3, 4, 5 was
`7, 7, 2, 0`.  Thus 14 certificates need only degree 2, five more need degree
4, and only two need degree 5.

For `t4`, the unresolved counts after degrees 2, 3, 4, 5, 6 were
`12, 9, 6, 2, 0`.  Thus 12 certificates need degree 2, then respectively
3, 3, 4, and 2 new certificates at degrees 3, 4, 5, and 6.

These `t4` numbers describe the original, unquotiented system. Exact linear
elimination plus deduplication closes all 24 reduced targets by degree 5, as
recorded in the execution result above.

A scan-only run should print the target indices at each stage.  Certificate
runs can then be made in increasing degree with
`HardDegreeLimit => d`.  This banks most certificates at low peak memory.  The
equation-core procedure below remains available if a future variant retains
hard top-degree targets; it was unnecessary for the completed branches.

## Equation-core pruning fallback (not needed in the completed runs)

Keep provenance labels before flattening `assocV` and `compatV`, grouped at
least by axiom, input tuple, output coordinate, and epsilon digit.  Starting
from all 157/178 equations, use no-change-matrix partial bases to delete groups:

1. remove half of the remaining groups;
2. retain the deletion if the chosen target still reduces to zero;
3. otherwise restore it and split the group;
4. repeat to a one-group-minimal core;
5. run the linear-eliminated change-matrix computation only on that core.

Every successful deletion would be exact: it only strengthens the resulting
ideal identity.  Failure to reduce to zero would merely mean the proposed core
was too small.  This fallback was implemented with checkpointed core data but
was not needed once all 24 pruned `t4` targets closed at degree 5.

## Process and engine discipline

- Give the script a `--branch xy|t4` and ideally a `--target` option.  Never
  compute both branches in one Macaulay2 process.
- Use `DegreeLimit => d, HardDegreeLimit => d`; the latter prevents storage of
  queued pairs above the only degree of interest.
- Try `Strategy => UseSyzygies`; retain it only after a no-change-matrix scan
  reproduces the archived zero remainders.
- Run each tracked branch in a fresh process and let it exit immediately after
  atomically saving the verified artifact.  A forced final garbage collection
  caused a needless post-success RSS spike in the first `xy` run and was
  removed.
- Write one certificate per file or append it immediately after its direct
  verification.  A later crash then loses no completed target.
- Record the exact M2 version, branch, target indices, generator list, and
  direct-verification marker in each output.

## Routes not recommended as the primary attempt

- `quotient(b,Gmat)` without an explicit change matrix: correct API, but the
  installed implementation was strongly memory-hungry in a synthetic probe.
- `Algorithm => LinearAlgebra`: useful for fast membership scans, but in
  Macaulay2 1.25.11 `getChangeMatrix` reports that change matrices are not
  computed for this algorithm.  It therefore does not by itself emit the
  requested cofactors.
- `msolve`: installed and potentially useful for fast grevlex scans, but its
  command-line interface emits bases/normal forms, not lifts to the original
  generators.
- Singular `lift`/`liftstd`: Singular is not installed in the current
  environment.  In any event, `liftstd` normally retains a full transformation
  matrix and would need the same minimal-axiom and elimination reductions.

## Optional homogeneous fallback

If the reduced inhomogeneous computation is still too large, homogenize the
surviving equations with one variable `h`.  For a target `b`, test
`h^N homogenize(b,h)` for increasing `N`.  Any homogeneous identity

```text
h^N b^h = sum_i q_i g_i^h
```

dehomogenizes at `h=1` to the desired original identity.  This can make the
homogeneous engine and degree-by-degree pair handling more predictable.  It is
a fallback to benchmark after the much larger gains from minimal axioms and
linear elimination; it should not displace them.
