# Complete H=(1,2,2,1), type-two exact S' sweep

Date: 2026-07-10

## Result

The exact rational-fiber `S'` sweep is complete on all 19 classified
Gorenstein-liftable length-six quotient rings with Hilbert function
`(1,2,2,1)` and type two.

For every ring the computation covered all six rational `xy` Hopf fibers
and all four rational `t4` normal forms.  Every nonvacuous row was split
into three fresh solver processes, one for each failure coordinate.

The complete row count is:

| outcome | rows | coordinate verdicts |
|---|---:|---:|
| closed by exact S2 UNSAT | 160 | 480 UNSAT |
| H0-vacuous | 30 | S2 not needed |
| SAT `S'`-failure candidate | 0 | 0 |
| unknown, error, or incomplete | 0 | 0 |
| **total** | **190** | **480 UNSAT** |

Thus no `S'`-failure seed occurs anywhere in this finite universe.

The 13 rings

```text
q01 q03 q05 q06 q07 q08 q09 q10 q15 q16 q17 q18 q20
```

have ten nonvacuous, three-coordinate-UNSAT rows each.  Each of

```text
q21 q22 q23 q24 q25 q27
```

has five H0-vacuous rows and five nonvacuous rows with all 15 failure
coordinates UNSAT.

## Independent evidence audit

The banked strict auditor and a separate ad hoc independent parser run
agree:

- `scripts/audit_sprime_length6_h1221_logs_20260710.py --strict` exits zero
  with no audit issue;
- an independent parser reconstructs the same 19-ring by 10-fiber universe
  and reports no discrepancy.

There are exactly 510 terminal case logs:

- 510/510 ring/direct-sum/lift/locality/type gates pass;
- 510/510 exact full-syzygy/coset gates pass;
- 480 case logs have H0 SAT, S1 SAT, and their requested S2 coordinate
  UNSAT;
- 30 case logs have H0 UNSAT and close their rows as vacuous;
- 510/510 have consistent summaries, `PROCESS_RESOURCE` records, and final
  driver markers;
- no terminal log contains S2 SAT, solver `unknown`, a malformed result, or
  a missing terminal marker.

The 60 absent coordinate files are exactly `i2,i3` for the 30 H0-vacuous
rows.  They are intentionally unnecessary and are not missing evidence.

## Resources

Across all 510 case processes:

- summed process elapsed time: 15,715.66 seconds;
- peak RSS: 1,645.00 MiB;
- longest case: 213.23 seconds.

The peak and longest case are both
`q17/xy_mu2mu2_irreducible/i1`.

The final six-ring resume (`q01,q03,q05,q06,q07,q08`) ran from
08:46:35Z to 09:05:50Z.  Its 180 terminal cases summed to 7,259.12 seconds;
its peak RSS was 996.08 MiB, and its longest case took 92.81 seconds.

## Provenance qualification

All 19 raw queue ledgers end in exactly one `QUEUE_DONE`.  The six final
ledgers are append-only files copied from the earlier interrupted attempt,
so they deliberately retain 88 historical `rc!=0` records and six
historical unmatched starts.  Every affected task now has a valid terminal
replacement.  These old records document the computer interruption; they
are not unresolved mathematical outcomes.  The immutable terminal case
logs, rather than a cleaned queue transcript, are the canonical evidence.

One valid terminal case,
`q01/xy_mu2a2/i1`, is stored under the earlier `..._i1_canary_20260710.log`
name.  It has both structural gates passing and S2.1 UNSAT, with 21.54
seconds elapsed and 889.80 MiB RSS.  It used a 300-second timeout and no Z3
memory ceiling; every later batch process used a 3600-second timeout and a
6144 MiB ceiling.  The strict auditor accepts the canary as conclusive, and
the hashes below include it.

## Hashes

Each hash concatenates raw files without separators in basename-sorted byte
order.  Independent Python and `shasum -a 256` calculations agree.

```text
final six-ring resume, 180 case logs:
cc187d9267916c6e758d51f7b089b3360ff92cefd876411dfa1d8d135abead07

final six-ring resume, 180 cases + 6 raw queues:
1f0f12d5c71fb2725b75e029f000299022aae30b34f455855287b91ec56c26b4

complete universe, 510 case logs:
84e33365fd4cb1e9629fb20618ade3911880ecfdd3cf9d59a12c20415d29bf12

complete universe, 510 cases + 19 raw queues:
702e11eabb623a30eefe2ee4b6bfd63abe2f7925040cae979e7dac4dbe60f32f
```

The full case logs use the pattern
`scripts/sprime_length6_h1221_q*_20260710.log`.

## Mathematical interpretation

These are exact bialgebra-level `S'` exclusions, not direct `[4]` searches.
Subject to the minimal Gorenstein-base reduction and the socle-extension
theorem used throughout the project, a first residue-F2 length-seven
counterexample with base Hilbert function `(1,2,2,1,1)` would require an
`S'`-failing bialgebra over one of precisely these 19 liftable quotients.
The complete negative sweep therefore eliminates that entire Hilbert
profile.

This is a bounded computational theorem.  It does not by itself resolve
arbitrary base length, larger residue fields, or the full conjecture.
