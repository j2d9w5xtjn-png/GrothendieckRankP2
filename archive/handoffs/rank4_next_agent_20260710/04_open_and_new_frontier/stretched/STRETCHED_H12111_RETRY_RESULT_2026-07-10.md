# Result of the 7200-second stretched `H=(1,2,1,1,1)` retries

## Executive conclusion

The two isolated 7200-second retries completed normally as processes, but
neither produced a mathematical verdict.  In both cases Z3 returned
`unknown` with `reason=timeout` on the first `S'-FAIL` coordinate.  The
outcome classification is therefore:

- process/software outcome: **successful** (`rc=0`, complete terminal log);
- solver outcome: **unknown because of timeout**;
- mathematical outcome: **inconclusive**;
- out of memory or software failure: **no**.

Consequently the ordinary stretched-frontier result is unchanged:

| row outcome | rows |
|---|---:|
| all three `S'-FAIL_i` queries UNSAT | 83 |
| H0 UNSAT, hence the pinned fibre is vacuous | 25 |
| solver unknown because of timeout | 2 |
| SAT `S'`-failure candidate | 0 |
| incomplete or audit error | 0 |
| **total** | **110** |

In particular, the two longer runs do **not** close either unknown row and do
not turn the ordinary `83/25/2` computation into a complete negative result.
The immutable ordinary-sweep record
`STRETCHED_H12111_COMPLETE_RESULT_2026-07-10.md` has not been modified.

## Scope and provenance

The retries target exactly the two coordinates left unknown by the ordinary
3600-second sweep:

```text
s_f2 / t4(c1=1,c4=1) / i1
q00  / t4(c1=1,c4=1) / i1
```

Each retry used the same frozen exact driver as the ordinary sweep,
sequentially with one solver thread, with only these resource options changed
or restricted:

```text
--t4-forms 11 --only-i 1 --timeout 7200 --memory-mb 3072
```

The driver named by both terminal `COMMAND` records is the staged file

```text
/tmp/rank4_stretched_20260710T084004Z/scripts/
  sprime_length6_stretched_h12111_eleven_stratified_20260710.py
```

Its SHA-256 is

```text
6881d27246519a453cbd07b3ab4f8e2246b0ed2b37e2788146e18400cbc3e81d
```

The banked copy in `scripts/` has exactly the same hash.  Thus these retries
did not use the later trace-accelerated wrapper or any modified constraint
system.

The launchers ran under `caffeinate -i` through the two launchd labels

```text
com.openai.rank4.stretched.retry.s_f2_t4_11_i1.20260710
com.openai.rank4.stretched.retry.q00_t4_11_i1.20260710
```

and published a final log atomically only after the Python driver returned
zero.  Both launcher standard-error files are empty.  No computation was
launched as part of the present audit.

## Exact retry results and resources

All displayed durations below are copied from the terminal logs.  The gate
and `S2.1` durations are the driver's measured solver/gate times; “process
elapsed” is its monotonic elapsed time for the complete Python invocation.
Peak RSS is `ru_maxrss`, converted to MiB according to the driver's Darwin
branch.

| case | ring gate | H0 | S1 | `S2.1` | process elapsed | peak RSS |
|---|---:|---:|---:|---:|---:|---:|
| `s_f2/t4_11/i1` | 15.12 s | 6.31 s, SAT | 7.99 s, SAT | 7244.62 s, unknown (`timeout`) | 7437.32 s | 1110.45 MiB |
| `q00/t4_11/i1` | 14.44 s | 5.13 s, SAT | 7.30 s, SAT | 7266.73 s, unknown (`timeout`) | 7495.44 s | 1104.73 MiB |

The requested timeout was 7200 seconds per solver stage.  The slightly larger
reported `S2.1` durations are measured return times and include timeout/check
overhead; they do not signify a longer conclusive search.  Both peak-RSS
values are far below the explicit 3072 MiB Z3 ceiling, and each solver stated
`reason=timeout`, so neither run was an OOM.

The launcher lifecycle records are:

| case | `RETRY_START` (UTC) | atomic final / `RETRY_DONE` (UTC) | launcher wall interval | launcher exit |
|---|---|---|---:|---:|
| `s_f2/t4_11/i1` | `2026-07-10T10:16:28Z` | `2026-07-10T12:22:43Z` | 7575 s | 0 |
| `q00/t4_11/i1` | `2026-07-10T10:22:04Z` | `2026-07-10T12:29:13Z` | 7629 s | 0 |

For both cases, the split-coordinate isomorphism gate, the
ring/presentation/locality/Hilbert/type gate, and the exact full-syzygy/coset
gate passed.  H0 was SAT, the `S'-HOLDS` witness gate S1 was SAT, and the exact
unroll cache had 512 combined representatives and 1,512 distinct coefficient
shifts.  Only `S2.1` remained unknown.  The ordinary `i2` and `i3` logs for
both rows remain UNSAT.

## Original and retry log hashes

The retry launchers recorded the SHA-256 of the corresponding ordinary
3600-second log before running.  Those recorded values were independently
recomputed from the canonical files in `scripts/`:

| case | ordinary 3600-second log SHA-256 | retry 7200-second log SHA-256 |
|---|---|---|
| `s_f2/t4_11/i1` | `c0674d044d8e0f1eaf0257e10442af73a2b170646a087d9ecc066e3f8f71d382` | `82c6a4d1933b1897dbe7a5f7e1e8353450256e95ca447477bc35599706dd08ca` |
| `q00/t4_11/i1` | `62acd7f7dd4063fd656db51f0bae52baff5d54507ddf79b7d455370cfdcac946` | `6bfed288f5b45804ff1ea9de2cdf59e5573995edf18ba0d8520e4a326cfb6eed` |

The retry finals are deliberately separate from the ordinary logs; they do
not overwrite or replace them.

## Verification of the banked copies

The complete retry evidence is banked under

```text
results/stretched_retry_s_f2_t4_11_i1_20260710/
results/stretched_retry_q00_t4_11_i1_20260710/
```

The final log, launcher standard output, empty launcher standard error, and
launcher script in each banked directory were compared by SHA-256 with their
counterparts in the corresponding `/tmp/rank4_stretched_retry_*` staging
directory.  Every pair agrees byte for byte:

| artifact | `s_f2` SHA-256 | `q00` SHA-256 |
|---|---|---|
| `run_retry.zsh` | `a588a3c056427972e5a1e00683cd03aec67eebb1628e8fc0c8718f4122f5511c` | `a032af18cc7fcc64a786af7c92f43d40f33f46ea820744ca20dfb431710131d1` |
| `launcher.stdout.log` | `18eff6735c7b7caea704dd3a3052a3cb844376ac883ffc1427ba768c89140f6b` | `654126c5282df6a8837e4724bf2a620ed81c58f5dbe24e9664049fd7215e4e62` |
| `launcher.stderr.log` (empty) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| terminal retry log | `82c6a4d1933b1897dbe7a5f7e1e8353450256e95ca447477bc35599706dd08ca` | `6bfed288f5b45804ff1ea9de2cdf59e5573995edf18ba0d8520e4a326cfb6eed` |

The banked plist files also pass `plutil -lint`.  Their hashes are,
respectively,

```text
ba8e38d7e806d6744bbb756c75233e40f70ef7f41b69c44edb37046a81e7a7a5
ee875f1c35f825fcbc2c4b2fa6de256f300a6a49debf7b733f16482628762765
```

## Combined terminal-log audit

The standalone auditor
`scripts/audit_sprime_length6_stretched_logs_20260710.py` (SHA-256
`6b69f27d4d6a3a6dee201d1d2fef8bdf699a5d9a8d8267c5671370b5230f0796`)
was run over `scripts/` and both banked retry directories.  Its effective
selection rule prefers a later valid conclusive result over an unknown and,
when outcomes remain equal, selects the newest valid terminal copy.

The combined audit found:

```text
universe:                    11 rings, 110 rows, 330 coordinate tasks
files matched/recognized:   283 / 283
duplicate task copies:      3
malformed/out of scope:     0
effective terminal tasks:  280
intentional missing tasks:   50
truncated/error tasks:        0 / 0
terminal outcomes:          25 H0-vacuous, 253 UNSAT, 0 SAT, 2 unknown
global rows:                83 closed UNSAT, 25 H0-vacuous, 2 unknown
audit issues:                0
```

The three duplicate task copies are the two longer retry logs plus the one
already-disclosed ordinary canary copy.  The 50 missing coordinate tasks are
exactly the unnecessary `i2` and `i3` invocations for the 25 H0-vacuous rows.

Because the two newer retry logs are selected for the two unknown tasks, the
effective 280-log resource aggregate is:

```text
elapsed_sum_seconds=25925.15
maxrss_max_mib=1593.75
platforms=darwin:280
```

A structural combined invocation without `--strict` exited zero.  The same
invocation with `--strict` exited one, as it must: that option's contract
requires every row to be either closed UNSAT or H0-vacuous, and it displayed
exactly these two failures of that condition:

```text
s_f2 t4/c1=1,c4=1: unknown; i1:unknown,i2:UNSAT,i3:UNSAT
q00  t4/c1=1,c4=1: unknown; i1:unknown,i2:UNSAT,i3:UNSAT
```

The strict nonzero exit is therefore not an audit failure.  It is a faithful
machine-checkable statement that the two rows remain open.  The same output
reports `AUDIT ISSUES count=0`, with zero SAT candidates, incomplete rows, or
errors.

## Mathematical interpretation

Doubling the timeout from 3600 to 7200 seconds did not resolve either hard
`S2.1` query.  It found no counterexample, but a timeout is not a negative
mathematical result.  The only justified conclusion is that these two bounded
retry experiments are inconclusive and leave the ordinary stretched
`H=(1,2,1,1,1)` frontier status exactly at **83 closed UNSAT rows, 25
H0-vacuous rows, and 2 unknown rows**.

As in the ordinary sweep, these are exact finite-ring tests of the auxiliary
condition `S'`, not direct computations of `[4]`, and they do not by themselves
prove Grothendieck's conjecture or disprove the existence of a rank-four
counterexample.
