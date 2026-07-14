# RCC / Slurm instructions for Codex

This workspace is on the University of Chicago RCC Midway cluster.

## Compute policy

- Do not run substantial Macaulay2 computations directly on the login node.
- All substantive Macaulay2 computations must be submitted through Slurm using `sbatch`.
- It is acceptable to edit files, use Git, generate inputs, submit jobs, inspect queues, and read logs on the login node.
- Do not run M2 or `apptainer exec ... M2` directly unless it is explicitly a tiny syntax check expected to finish in under 30 seconds.

## Standard workflow

1. Edit or create Macaulay2 files under `m2/`.
2. Edit or create Slurm scripts under `slurm/`.
3. Submit jobs with:

   ```bash
   sbatch slurm/run.sbatch
   ```

4. Check running or pending jobs with:

   ```bash
   squeue -u "$USER"
   ```

5. Inspect completed jobs with:

   ```bash
   sacct -j JOBID --format=JobID,State,Elapsed,MaxRSS,ReqMem,AllocCPUS,ExitCode
   ```

6. Read standard output and errors from `logs/`.

## Macaulay2 environment

Use the Apptainer image:

```text
$HOME/software/macaulay2/macaulay2.sif
```

Load Apptainer inside Slurm jobs with:

```bash
module load apptainer
```

Run Macaulay2 inside a Slurm job using:

```bash
apptainer exec \
  "$HOME/software/macaulay2/macaulay2.sif" \
  M2 --script m2/search.m2
```

## Resource policy

- Assume Macaulay2 is single-threaded unless the specific package is known to use several cores.
- Start with one CPU.
- Choose memory and wall time based on measured runs.
- Prefer Slurm job arrays for many independent cases.
- Do not request many CPUs merely because a problem is large.
- Do not repeatedly resubmit failed jobs without diagnosing the failure.
- For exploratory jobs, start modestly and increase memory or time only when measurements justify it.

## Reliability

- A timeout is not a mathematical negative result.
- An out-of-memory failure is not a mathematical negative result.
- A missing output file is not a mathematical negative result.
- A nonzero exit code must be diagnosed before interpreting the computation.
- Long jobs should write intermediate results incrementally.
- Record the Slurm job ID for every experiment.
- Do not silently modify scripts associated with an already running job.

## Project organization

Use this layout when practical:

```text
m2/
slurm/
inputs/
results/
logs/
notes/
```

Keep source code, manifests, and concise conclusions in Git. Avoid committing large logs, container images, and generated result files.

## Before submitting a job

- State the mathematical purpose of the experiment.
- Check the input parameters.
- Confirm the output location.
- Confirm the requested CPUs, memory, and wall time.
- Verify that the computation is bounded.
- Ensure output filenames are unique.
- Commit relevant source changes when practical.

## After a job completes

- Inspect the Slurm state.
- Inspect both standard output and standard error.
- Report elapsed time and maximum memory usage.
- Classify the outcome as one of:
  - successful;
  - mathematically negative;
  - timeout;
  - out of memory;
  - software failure;
  - inconclusive.
- Summarize the mathematical result in `notes/`.
- Propose the next experiment only after diagnosing any failures.

## Codex behavior

- Read this file before changing or running anything.
- Do not run substantial Macaulay2 computations on the login node.
- Use Slurm for all real computations.
- Do not interpret computational failure as mathematical evidence.
- Prefer small representative tests before large jobs.
- Prefer bounded batches and job arrays over uncontrolled searches.
