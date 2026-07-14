# Environment and compute provenance

The origin directory is not a Git worktree. There is no commit hash.
Byte-level SHA-256 values in SHA256SUMS and the per-run manifests are the
provenance.

The canonical new direct run used:

- macOS on a 64-GiB workstation;
- /Users/akhilmathew/.venvs/z3env/bin/python;
- Python 3.14;
- Z3 4.16.0;
- one thread per process;
- a 1024 MiB Z3 ceiling;
- six fresh sequential subprocesses.

The exact executable, version, command, source hashes, run start/end, result,
elapsed time, and peak RSS are inside each canonical direct4 log.

The workspace AGENTS.md records the original policy requiring substantive
M2 to use Slurm. During this session the user explicitly superseded the
local part of that instruction: bounded M2 may run on the Mac, while any M2
on RCC must still use Slurm. A next agent who does not inherit that explicit
authorization should follow its own current instructions rather than infer
permission from this historical note.

Noninteractive RCC authentication failed in this session. No job was
submitted and no Slurm ID is claimed. The included Slurm script is an
optional reproduction template, not evidence of a run.

Two inherited local M2 jobs were active at freeze and have no retroactive
memory limit. Their exact status is recorded in
04_open_and_new_frontier/inherited_m2. The archive contains snapshots of
their logs, not live files.
