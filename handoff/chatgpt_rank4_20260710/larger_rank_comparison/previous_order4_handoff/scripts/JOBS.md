# JOBS.md — canonical job table (session 13, 2026-07-09)

**Purpose.** The machine crashes frequently (load average has been 10× core
count). This file + `relaunch_all.sh` make recovery a one-command operation.
Any agent resuming after a crash should:

```
cd "/Users/akhilmathew/Library/CloudStorage/Dropbox/FiniteFlatGroupSchemes/scripts"
./relaunch_all.sh          # idempotent: relaunches ONLY unfinished, not-running jobs
./relaunch_all.sh --dry    # show what it would do, do nothing
```

**Environment.** Z3 jobs: `~/.venvs/z3env/bin/python` (python3.14 + z3 4.16.0;
NEVER bare `python3`). M2 jobs: `/opt/homebrew/bin/M2 --script`. zsh gotcha:
never launch via a `$cmd` variable holding flags — word-splitting is off;
write each command out explicitly. Process check: grep SCRIPT NAMES
(`ps aux | grep s5t4gen`), not `python3` or `M2` (venv python resolves to
/opt/homebrew/Cellar/...).

**Golden rules.** (1) Read a job's log for its DONE marker before citing any
result it "should" have produced. (2) M2 partial logs = partial PROOFS (a
target reducing to 0 against a DegreeLimit GB is a complete certificate).
(3) All jobs are deterministic — a from-scratch rerun reproduces verdicts.

## Active jobs (auto-relaunched by relaunch_all.sh)

| # | command (from scripts/) | log | DONE marker | content |
|---|---|---|---|---|
| 1 | `/opt/homebrew/bin/M2 --script s5t4gen.m2` | s5t4gen.log | `DONE s5t4gen` | **FRONTIER**: s=5 t⁴ cotangent row, arbitrary-k′ (banked s≤4 boost). Cotangent banner: `COTANGENT ROW D5[1,*] all in J_aug` |
| 2 | `/opt/homebrew/bin/M2 --script s5xygen.m2` | s5xygen.log | `DONE s5xygen` | **FRONTIER**: s=5 xy per split model, cotangent rows i=1,2 |
| 3 | `~/.venvs/z3env/bin/python s5gates.py` | s5gates.log | `DONE s5gates` | fifth-note gates: Theorem N + pairwise (battery A ✅ done 11:39), D5 rows + **D5(1,3) gap** (battery B; relaunch with `--skip-a` if battery A lines already in log) |
| 4 | `/opt/homebrew/bin/M2 --script s4t4gen.m2` | s4t4gen.log | `DONE s4t4gen` | belt-and-braces: direct D4 memberships (Theorem M(t⁴) ALREADY banked via scalars, THEORY §14.9 — do NOT block on this) |
| 5 | `~/.venvs/z3env/bin/python s4cert.py` | s4cert.log | `ALL S4CERT GATES PASSED` | s=4/t⁴ cross-validation batteries (DN done; F₄ in flight) |
| 6 | `~/.venvs/z3env/bin/python s4xycert.py` | s4xycert.log | `ALL S4XYCERT GATES PASSED` | queued behind #5 (launch only after #5's marker appears — relaunch_all handles this) |
| 7 | `~/.venvs/z3env/bin/python s3xy2gates.py --f4only` | s3xy2gates.log | `ALL S3XY2 GATES PASSED` | Theorem L F₄ validation (needed before citing L at F₄; F₂ half passed 100%) |
| 8 | `~/.venvs/z3env/bin/python s2check_np3.py` | s2check_np3.log | `DONE s2check_np3` | FatPoint3/xy S′ gap, THIRD encoding (cotangent-split, THEORY 15.5.1; np2's --gaponly rerun returned `unknown` at its 2 h timeout — np3 has 12 h/query + smaller queries) |
| 9 | `~/.venvs/z3env/bin/python s2check.py --ext` | s2check_ext.log | `DONE s2check` | S′ probes over MIXED-CHAR F₄ rings W(F₄)/8, W(F₄)[π]/(π²−2,π³) (equal-char F₄ row removed session 13 — theorem-subsumed) |
| 10 | `~/.venvs/z3env/bin/python ringcheck.py` | ringcheck.log | `ALL RING CHECKS PASSED` | ring-class validation incl. NEW FatPoint2 (gates the s5gates battery A rows) |

## Deferred / dead (NOT auto-relaunched — relaunch manually only if idle capacity)

| job | why stopped | relaunch when |
|---|---|---|
| `order4sat_f8ram.py` | heaviest job (4 cores, 6 GB); lost ~19 h to crashes TWICE; cannot checkpoint inside its one long query; content = Cor C→F₈ extension (off the critical path) | machine stable & mostly idle: `nohup ~/.venvs/z3env/bin/python order4sat_f8ram.py >> order4sat_f8ram.log 2>&1 &` |
| `s3xygates.py --f4only` | post-hoc calibration for banked Theorem L; F₂ half + GX9nc discovery already harvested | probably never |
| `order4sat_beyond.py` | remaining job list FULLY theorem-subsumed (Theorem M + Cor J) | never (cross-validation only) |
| `s4gen.m2` | subsumed by s4t4gen + s4xygen | never |
| `order4sat_f8nofib.py` | written, never launched (F₈ nofiber2 = B′→F₈) | idle capacity only |
| `s2gen.m2`, `symbolsq.m2`, `len3gen.m2` | audit-only since Cor J / Thms K,L | never |

## Load discipline (crash mitigation)

The 2026-07-09 08:05 crash and the frequent earlier ones coincide with load
average 150–230 on 18 cores. Keep the ACTIVE table ≤ ~6 heavy processes.
Z3 runs multi-threaded (`parallel.enable`): each s2check/s4cert-family job
can take 3–4 cores. M2 is single-core. When adding a new job, prefer killing
a Deferred-tier job first. `relaunch_all.sh` prints current load and warns
above 20.
