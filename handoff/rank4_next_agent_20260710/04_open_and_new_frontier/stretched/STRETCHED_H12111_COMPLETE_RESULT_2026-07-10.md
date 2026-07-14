# Complete ordinary sweep for the stretched H=(1,2,1,1,1) frontier

## Frozen result

The ordinary exact rational-fiber `S'` sweep finished on all eleven validated
coordinate rings in the length-six, type-two, stretched
`H_Q=(1,2,1,1,1)` upper list.  Every coordinate ring was tested against all
six rational `xy` Hopf fibers and all four rational `t4` normal forms.

The three-lane run began at `2026-07-10T08:41:12Z` and ended at
`2026-07-10T11:09:02Z`.  All eleven ring queues reached `QUEUE_DONE` and all
three lanes were reaped with `rc=0`.  The independent terminal-log audit gives:

| row outcome | rows | terminal task logs |
|---|---:|---:|
| all three `S'-FAIL_i` queries UNSAT | 83 | 249 |
| H0 UNSAT, hence the pinned fiber is vacuous | 25 | 25 |
| solver unknown because of timeout | 2 | 2 unknown + 4 UNSAT |
| SAT `S'`-failure candidate | 0 | 0 |
| incomplete or audit error | 0 | 0 |
| **total** | **110** | **280** |

Thus 108 of the 110 rows are negatively closed, while two rows remain
computationally inconclusive.  This ordinary sweep is **not** a complete
mathematical negative result for the stretched frontier.

## The two inconclusive coordinates

Both unknowns occur in the `t4/c1=1,c4=1` row, and only for the first split
failure coordinate:

| ring/row | coordinate | result | solver time | process time | peak RSS |
|---|---:|---|---:|---:|---:|
| `s_f2/t4_11` | i1 | `unknown`, reason `timeout` | 3600.05 s | 3636.47 s | 1076.59 MiB |
| `q00/t4_11` | i1 | `unknown`, reason `timeout` | 3600.30 s | 3647.82 s | 1057.97 MiB |

For both rows, coordinates i2 and i3 terminated UNSAT.  A timeout is not a
negative mathematical verdict and is not counted as evidence for universal
`S'`.

## Per-ring audit

| coordinate ring | three-coordinate UNSAT | H0-vacuous | unknown |
|---|---:|---:|---:|
| `s_f2` | 9 | 0 | 1 |
| `s_z32` | 5 | 5 | 0 |
| `s_e2_00` | 10 | 0 | 0 |
| `s_e2_10` | 10 | 0 | 0 |
| `s_e2_11` | 10 | 0 | 0 |
| `s_e3` | 10 | 0 | 0 |
| `s_e4` | 10 | 0 | 0 |
| `q00` | 4 | 5 | 1 |
| `q01` | 5 | 5 | 0 |
| `q10` | 5 | 5 | 0 |
| `q11` | 5 | 5 | 0 |
| **total** | **83** | **25** | **2** |

The task-level audit selected 280 terminal logs: 253 coordinate-UNSAT logs,
25 H0-vacuous logs, and two unknown logs.  The 50 absent tasks in the nominal
330-coordinate rectangle are exactly the unnecessary i2 and i3 processes for
the 25 H0-vacuous rows.  There were no missing required tasks, truncated
selected logs, malformed logs, contradictory outcomes, SAT candidates, OOMs,
or process errors.  One earlier canary is a duplicate task copy and is not one
of the 280 canonical logs used below.

Every selected log passed the command-tag, split-coordinate isomorphism,
ring/presentation/locality/Hilbert/type, exact full-syzygy/coset,
direct-versus-summary, terminal-marker, and resource-record checks.  The
selected fresh processes have summed elapsed time `18276.68` seconds and
maximum measured RSS `1593.75` MiB.  The ordinary run used one solver thread
per process, a 3072 MiB Z3 ceiling, and a 3600-second per-stage timeout.

## Queue provenance and banked evidence

The canonical evidence is banked in `scripts/` as:

- 280 case logs matching
  `sprime_length6_stretched_*_i[123]_20260710.log`;
- eleven logs matching
  `sprime_length6_stretched_*_memorysafe_queue_20260710.log`;
- the three lane logs and the overall local-run summary.

Each queue contains exactly one `QUEUE_DONE`.  All 280 canonical cases have
successful `END ... rc=0` or prior-complete `SKIP` provenance, and no queue
records a nonzero case exit.  The raw append-only histories retain three
pre-restart orphan `START` records:

- `s_f2/xy_mu2a2/i1`;
- `s_z32/xy_a2a2/i1`;
- `s_e2_00/xy_mu2a2/i1`.

Their restarted canonical processes are terminal and valid.  These historical
prefix records are disclosed here rather than silently removed.

For raw-file concatenation in lexicographic basename order, restricted to the
280 canonical case logs, the SHA-256 value is:

```text
8e16dc626592b13a8e01aa6026945a8673b2f7bf9d4c67b658b3a1cfceba6be1
```

For the same 280 canonical case logs together with the eleven queue logs, the
SHA-256 value is:

```text
9703aba9d75b2ee32c3d1c4018cd64a5bc3b14307a8e857861dad96f8e17b4a2
```

The staged and banked copies give the same two hashes.  The exact driver
`scripts/sprime_length6_stretched_h12111_eleven_stratified_20260710.py` has
SHA-256:

```text
6881d27246519a453cbd07b3ab4f8e2246b0ed2b37e2788146e18400cbc3e81d
```

## Separate longer retries

Two diagnosed isolated retries were started with a 7200-second timeout and
the same 3072 MiB ceiling, under the separate live directories

```text
/tmp/rank4_stretched_retry_s_f2_t4_11_i1_20260710
/tmp/rank4_stretched_retry_q00_t4_11_i1_20260710
```

At the freeze time `2026-07-10T11:13:10Z`, each directory contained only a
`.partial.*.log`; neither had published its atomic canonical final log.
Consequently those retries are not included in the counts, audit, resources,
or hashes in this note.  Any later retry verdict must be audited and recorded
as a separate addendum; it does not alter this immutable record of the
ordinary 3600-second sweep.

## Mathematical interpretation

No `S'`-failure candidate was found in this finite upper list.  The ordinary
sweep proves universal `S'` on the 83 fully UNSAT rows and disposes of another
25 rows already at H0, subject to the explicit finite-ring and Hopf encodings.
It does not close the two timeout rows and therefore does not yet eliminate
the complete stretched `H_Q=(1,2,1,1,1)` frontier.  This is an `S'` computation,
not a direct computation of `[4]`, and it is not by itself a proof of
Grothendieck's conjecture in rank four.
