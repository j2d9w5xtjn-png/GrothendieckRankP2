# Stretched `s_f2/t4_11/i1` 7200-second retry

This directory separately preserves the bounded local retry of the sole
unresolved coordinate in the `s_f2/t4_11` row.  It does not overwrite or
replace the canonical 3600-second log in `scripts/`.

- Start: `2026-07-10T10:16:28Z`.
- Atomic final published: `2026-07-10T12:22:43Z`, launcher exit 0.
- Original 3600-second log SHA-256:
  `c0674d044d8e0f1eaf0257e10442af73a2b170646a087d9ecc066e3f8f71d382`.
- Retry final SHA-256:
  `82c6a4d1933b1897dbe7a5f7e1e8353450256e95ca447477bc35599706dd08ca`.

The retry passed its ring, syzygy, fibre, and S1 gates, then returned
`S2.1 = unknown` with `reason=timeout` after 7244.62 seconds.  Its resource
record is 7437.32 seconds elapsed and 1110.45 MiB maximum RSS.  The final has
the terminal summary, `PROCESS_RESOURCE`, and driver `DONE` marker required
by the strict stretched auditor.

Combining `scripts/`, this retry directory, and the still-running `q00`
retry directory gives 83 closed UNSAT rows, 25 H0-vacuous rows, and two
unknown rows, with zero incomplete/error rows and zero audit issues.  Thus
this retry is **computationally successful but mathematically inconclusive**:
it does not replace the original unknown or close the `s_f2/t4_11` row.
