# Verification instructions

Run these from the extracted archive root.

## Archive integrity

    shasum -a 256 -c SHA256SUMS

The zip itself has a separate SHA-256 reported outside the archive.

## New direct-[4] result

Use Python with Z3 4.16.0 available:

    python scripts/audit_monogenic_stretched_direct4_local_20260710.py \
      04_open_and_new_frontier/direct4/local1g_20260710 \
      --project-root .

Expected final line:

    AUDIT PASS six_of_six_H0_SAT_and_direct4_UNSAT errors=0 unknown=0 SAT=0

The auditor is standard-library only and does not launch Z3, but it hashes
the current mathematical driver and runner under scripts.

## H1221 completed frontier

    python scripts/audit_sprime_length6_h1221_logs_20260710.py \
      --log-dir 03_completed_evidence/h1221 --strict

Expected global result: 160 closed UNSAT, 30 H0-vacuous, no other status.

## Historical stretched S-prime evidence

    python scripts/audit_sprime_length6_stretched_logs_20260710.py \
      --log-dir 04_open_and_new_frontier/stretched \
      --no-commands

Expected historical result: 83 closed UNSAT, 25 H0-vacuous, 2 unknown. The
two unknowns are subsequently closed for actual [4] by the direct search;
this auditor intentionally does not merge two different statements.

## Frozen principal evidence

    python scripts/audit_sprime_principal_slurm_logs_20260710.py \
      --local-log-dir 04_open_and_new_frontier/principal_partial \
      --no-commands

Expected frozen unfiltered result: 103 terminal logs, 16 closed rows,
3 H0-vacuous, 13 unknown, 68 incomplete, no SAT or audit error.

## Small model audits

    python scripts/audit_rank4_no_normal_rank2_filtration_20260710.py
    python scripts/audit_tight_chain_hopf_model_20260710.py
    python scripts/audit_tight_chain_family_independent_20260710.py
    python scripts/audit_rt_hf_triangular_family_20260710.py

Each must end in its documented PASS banner.

Do not run the two inherited M2 scripts merely to verify the archive. Their
included logs are explicitly nonterminal snapshots.
