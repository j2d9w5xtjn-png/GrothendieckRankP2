# Supersession and errata

START_HERE.md in this archive supersedes every earlier handoff, live-status
note, and archive README in the origin workspace.

Important corrections:

- The strongest unconditional rank-four bound is now 8, not 16.
  REGULAR_TRANSLATION_RANK4_EXPONENT16 remains a valid prerequisite proof,
  but its headline is superseded.
- THEORY_order4 section 17.4 describes the regular-translation route as
  provisional and leaves Hopf--Frobenius obligations open. Those obligations
  are now discharged in the exponent-16 report, and the exponent is further
  improved to 8.
- THEORY_order4 retains a Schoof-fiber flag for
  \(\alpha_2\rtimes\mu_2\). Torti's theorem closes this branch; read the
  dedicated audit because the paper's last paragraph contains a false
  stronger killed-by-\(2\) statement.
- HANDOFF_NEXT_AGENT_2026-07-10.md has stale principal counts and stale
  advice to launch F4 tasks 16/17 or retry a multiplicative principal OOM.
  Those rows are retired by block rigidity.
- The old stretched audit still honestly reports two \(S'\) timeouts.
  They remain \(S'\)-unknown, but the actual rank-four counterexample
  branches above them are now closed by the direct-[4] computation.
- rank4_grothendieck_push.md is the uncorrected draft which overstates case
  exhaustion. Do not cite it.
- The block-handoff claim ledger included under 01_current_theory is retained
  only as provenance and is explicitly named SUPERSEDED. Use the root
  CLAIM_LEDGER.tsv.
- RESPONSE_TO_rank16_push.md has a surviving negative verdict but a known
  false explanation; it is excluded.
- slurm/verify_m2.sbatch from the origin only prints the M2 version despite
  its name; it is excluded.

No timeout, OOM, missing output, nonzero exit, or nonzero bounded-degree
remainder is mathematical negative evidence.
