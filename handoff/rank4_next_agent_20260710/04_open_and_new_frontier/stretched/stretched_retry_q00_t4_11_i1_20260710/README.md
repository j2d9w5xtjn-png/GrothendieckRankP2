# Stretched `q00/t4_11/i1` 7200-second retry

This directory separately preserves the bounded local retry of the sole
unresolved coordinate in the `q00/t4_11` row.  It does not overwrite or
replace the canonical 3600-second log in `scripts/`.

- Start: `2026-07-10T10:22:04Z`.
- Atomic final published: `2026-07-10T12:29:13Z`, launcher exit 0.
- Original 3600-second log SHA-256:
  `62acd7f7dd4063fd656db51f0bae52baff5d54507ddf79b7d455370cfdcac946`.
- Retry final SHA-256:
  `6bfed288f5b45804ff1ea9de2cdf59e5573995edf18ba0d8520e4a326cfb6eed`.

The retry passed its ring, syzygy, fibre, and S1 gates, then returned
`S2.1 = unknown` with `reason=timeout` after 7266.73 seconds.  Its resource
record is 7495.44 seconds elapsed and 1104.73 MiB maximum RSS.  The final has
the terminal summary, `PROCESS_RESOURCE`, and driver `DONE` marker required
by the strict stretched auditor.

Combining `scripts/` and both banked 7200-second retry directories gives 83
closed UNSAT rows, 25 H0-vacuous rows, and two unknown rows, with zero
incomplete/error rows and zero audit issues.  Thus this retry is
**computationally successful but mathematically inconclusive**: it does not
replace the original unknown or close the `q00/t4_11` row.
