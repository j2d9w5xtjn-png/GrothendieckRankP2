# Monitoring record for the two inherited Macaulay2 jobs

**Date:** 2026-07-10  
**Status at final recorded snapshot:** both processes remain active; neither
log contains a terminal verdict.

## Provenance

The processes were launched by a previous agent and were orphaned when that
agent ended. Both have parent PID 1. They started together at
2026-07-10 15:19:23 BST from the workspace scripts directory.

| PID | script | stdout/stderr | script SHA-256 |
|---:|---|---|---|
| 91870 | scripts/s5t4gen.m2 | scripts/s5t4gen.log | 818537309e6f340355e154eda068485722fc9332bcae1614bd5617067a7696b5 |
| 91872 | scripts/fp3gen.m2 | scripts/fp3gen.log | 93dbaae0746d1aaf9426f8c5cb580b380bc8002858938b61cfba65ac53749e27 |

Standard input is /dev/null for both jobs. The displayed logs are the actual
open file descriptors for both stdout and stderr.

## Mathematical purpose and current phase

### s5t4gen, PID 91870

This is the arbitrary-coefficient \(s=5\), local--local \(t^4\) computation.
It tests the nine \(D_5\) components, with the cotangent row carrying the
new content. A previous run completed DegreeLimit 5 after 63,025 seconds
with all 9 targets still open, then died during DegreeLimit 6. The inherited
process is a fresh restart which must recompute lower degrees before reaching
6.

Its current log has passed all pin/fiber gates and DegreeLimits 2--4. It ends
at the start of DegreeLimit 5:

    -- gb DegreeLimit 5:

No nonzero remainder at a bounded DegreeLimit is a mathematical
nonmembership result. A useful positive verdict requires a target to reduce
to zero, preferably the explicit cotangent or all-target banner, followed by
the terminal line

    DONE s5t4gen

### fp3gen, PID 91872

This tests the remaining module-membership systems on the RingT and
FatPoint3 embdim-two bases. The RingT \(t^4,\alpha_2^2,W_2[F]\), and
multiplicative models in the current log have completed. The inherited
process is now on the genuinely relevant FatPoint3 \(t^4\) case.

At DegreeLimit 5 the 42 ideal targets are all certified. The log ends while
computing the remaining module Gröbner basis:

    ideal targets open: 0 / 42
    module gb:

The desired positive line is

    Msys open at g in {}  (certified: 1 / 1)

and a fully terminal run would eventually end with

    DONE fp3gen

The missing module line is not a negative result and not yet a certificate.

## Resource snapshots

RSS values are resident bytes as reported by macOS ps, converted here only
approximately in the prose.

| UTC | s5t4gen RSS | fp3gen RSS | interpretation |
|---|---:|---:|---|
| 16:27 approx. | 24,413,552 KiB | 6,607,264 KiB | first adopted snapshot |
| 16:30 approx. | 25,204,816 KiB | 7,898,592 KiB | both active near 99% CPU |
| 16:44 approx. | 24,495,888 KiB | 9,087,008 KiB | logs still unchanged |
| 16:52:34 | 26,427,328 KiB | 8,059,328 KiB | both active; s5 state UN, fp3 state RN |

At an earlier memory-pressure check the machine reported 68% system-wide
free memory, with no throttled pages. The jobs were not killed because both
still target genuine local--local open problems and memory pressure was not
critical. The user explicitly authorized stopping them if they cease to be
useful.

Neither inherited process has a retroactive hard memory ceiling. Any future
restart should be bounded and should preserve this log rather than overwrite
it. On RCC, Macaulay2 must be run through Slurm. On the Mac, the user's
latest instruction permits a bounded local run.

## Safe polling commands

    ps -p 91870,91872 -o pid,ppid,lstart,etime,state,pcpu,rss,command
    ls -lhT scripts/s5t4gen.log scripts/fp3gen.log
    tail -n 40 scripts/s5t4gen.log
    tail -n 40 scripts/fp3gen.log

Do not infer a theorem from process exit alone. On exit, inspect the full
log, terminal banner, exit status if available, and resource outcome, and
classify it as successful, mathematically negative, timeout, OOM, software
failure, or inconclusive.
