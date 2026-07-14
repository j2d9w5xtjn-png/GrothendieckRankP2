#!/usr/bin/env python3
"""Crash-safe local runner for the six monogenic direct-[4] cases.

The mathematical driver is never imported or edited.  Each case is a fresh
subprocess.  Output is written to a partial file, flushed and fsynced, and
published under its canonical name only after a zero exit and the runner's
terminal record.  A nonzero process is preserved under ``failures/``.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Mapping


FORMAT = "rank4-monogenic-direct4-local-run-v1"
EXPECTED_DRIVER_SHA256 = "ac70fdf145989723133d4c4efecb740353b0d8530bc9ee060089271de7a3caac"
EXPECTED_Z3 = "4.16.0"
CASES = (
    "sf2_g0_a0", "sf2_g0_a1", "sf2_g1_a0",
    "sf2_g1_a1", "q00_a0", "q00_a1",
)
RUN_ID_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]{0,63}")


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def canonical_json(payload: Mapping) -> str:
    return json.dumps(payload, sort_keys=True, separators=(",", ":"))


def atomic_json(path: Path, payload: Mapping) -> None:
    temporary = path.with_name(path.name + f".part.{os.getpid()}")
    with temporary.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def checked_output(command: list[str]) -> str:
    result = subprocess.run(
        command, check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, encoding="utf-8",
    )
    return result.stdout.strip()


def source_manifest(source_paths: Mapping[str, Path]) -> tuple[dict[str, str], str]:
    hashes = {label: sha256(path) for label, path in source_paths.items()}
    payload = "".join(f"{label}\t{hashes[label]}\n" for label in sorted(hashes))
    return hashes, hashlib.sha256(payload.encode("utf-8")).hexdigest()


def case_command(args, driver: Path, case: str) -> list[str]:
    return [
        str(args.python), "-u", str(driver),
        "--case", case,
        "--engine", args.engine,
        "--gate-timeout", str(args.gate_timeout),
        "--timeout", str(args.timeout),
        "--memory-mb", str(args.memory_mb),
    ]


def canonical_log_name(run_id: str, task: int, case: str) -> str:
    return f"monogenic_direct4_local_{run_id}_task{task}_{case}.log"


def completed_log(path: Path, run_id: str, task: int, case: str) -> bool:
    if not path.is_file():
        return False
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except (OSError, UnicodeError):
        return False
    terminal = f"LOCAL_TASK_DONE run={run_id} task={task} case={case}"
    return any(line.startswith(terminal) and line.endswith(" rc=0") for line in lines)


def run_one(args, manifest: Mapping, task: int, case: str, logs_dir: Path,
            failures_dir: Path) -> Path:
    canonical = logs_dir / canonical_log_name(args.run_id, task, case)
    if canonical.exists():
        if completed_log(canonical, args.run_id, task, case):
            print(f"SKIP terminal task={task} case={case} path={canonical}", flush=True)
            return canonical
        raise RuntimeError(f"canonical log exists but is not terminal: {canonical}")

    command = manifest["case_commands"][case]
    partial = logs_dir / (canonical.name + f".partial.{os.getpid()}")
    started = utc_now()
    with partial.open("x", encoding="utf-8") as handle:
        def record(line: str) -> None:
            handle.write(line + "\n")
            handle.flush()

        record(f"LOCAL_RUN_HEADER format={FORMAT} run={args.run_id}")
        record(f"LOCAL_CASE_SPEC run={args.run_id} task={task} case={case}")
        for label in sorted(manifest["source_sha256"]):
            record(f"SOURCE_FILE_SHA256 path={label} sha={manifest['source_sha256'][label]}")
        record(
            f"SOURCE_MANIFEST_SHA256 files={len(manifest['source_sha256'])} "
            f"digest={manifest['source_manifest_sha256']}"
        )
        record("PYTHON_EXECUTABLE_JSON " + json.dumps(manifest["python_executable"]))
        record("PYTHON_VERSION_JSON " + json.dumps(manifest["python_version"]))
        record(f"Z3_VERSION {manifest['z3_version']}")
        record("COMMAND_JSON " + canonical_json(command))
        record(f"LOCAL_TASK_START run={args.run_id} task={task} case={case} utc={started}")
        handle.flush()
        os.fsync(handle.fileno())
        process = subprocess.Popen(
            command, stdout=handle, stderr=subprocess.STDOUT,
            text=True, encoding="utf-8", cwd=manifest["project_root"],
            env={
                **os.environ,
                "OMP_NUM_THREADS": "1", "OPENBLAS_NUM_THREADS": "1",
                "MKL_NUM_THREADS": "1", "NUMEXPR_NUM_THREADS": "1",
            },
        )
        return_code = process.wait()
        ended = utc_now()
        if return_code == 0:
            record(
                f"LOCAL_TASK_DONE run={args.run_id} task={task} case={case} "
                f"utc={ended} rc=0"
            )
        else:
            record(
                f"LOCAL_TASK_FAILED run={args.run_id} task={task} case={case} "
                f"utc={ended} rc={return_code}"
            )
        handle.flush()
        os.fsync(handle.fileno())

    if return_code == 0:
        os.replace(partial, canonical)
        print(f"PUBLISH task={task} case={case} path={canonical}", flush=True)
        return canonical
    failures_dir.mkdir(parents=True, exist_ok=True)
    failed = failures_dir / (
        canonical.name.removesuffix(".log") + f".failed.{int(time.time())}.log"
    )
    os.replace(partial, failed)
    raise RuntimeError(
        f"task {task} case {case} exited {return_code}; preserved at {failed}"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--run-dir", type=Path, required=True)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    parser.add_argument("--python", type=Path, default=Path(sys.executable))
    parser.add_argument("--driver", type=Path,
                        default=Path("scripts/monogenic_stretched_direct4_20260710.py"))
    parser.add_argument("--auditor", type=Path,
                        default=Path("scripts/audit_monogenic_stretched_direct4_local_20260710.py"))
    parser.add_argument("--engine", choices=("smt", "qfbv"), default="smt")
    parser.add_argument("--gate-timeout", type=int, default=300)
    parser.add_argument("--timeout", type=int, default=300)
    parser.add_argument("--memory-mb", type=int, default=1024)
    args = parser.parse_args()
    if not RUN_ID_RE.fullmatch(args.run_id):
        parser.error("--run-id must match [A-Za-z0-9][A-Za-z0-9_.-]{0,63}")
    if min(args.gate_timeout, args.timeout, args.memory_mb) <= 0:
        parser.error("timeouts and memory must be positive")

    project_root = args.project_root.expanduser().resolve(strict=True)
    # Preserve a virtual-environment launcher path.  Resolving its symlink to
    # the base interpreter can lose the venv's site-packages (including Z3).
    python_candidate = args.python.expanduser()
    if not python_candidate.is_absolute():
        python_candidate = Path.cwd() / python_candidate
    args.python = Path(os.path.abspath(python_candidate))
    if not args.python.exists():
        parser.error(f"Python does not exist: {args.python}")
    driver = (project_root / args.driver).resolve(strict=True) \
        if not args.driver.is_absolute() else args.driver.resolve(strict=True)
    auditor = (project_root / args.auditor).resolve(strict=True) \
        if not args.auditor.is_absolute() else args.auditor.resolve(strict=True)
    runner = Path(__file__).resolve(strict=True)
    if not os.access(args.python, os.X_OK):
        parser.error(f"Python is not executable: {args.python}")

    source_paths = {
        "scripts/audit_monogenic_stretched_direct4_local_20260710.py": auditor,
        "scripts/monogenic_stretched_direct4_20260710.py": driver,
        "scripts/run_monogenic_stretched_direct4_local_20260710.py": runner,
    }
    source_hashes, source_digest = source_manifest(source_paths)
    if source_hashes["scripts/monogenic_stretched_direct4_20260710.py"] \
            != EXPECTED_DRIVER_SHA256:
        parser.error("mathematical driver hash differs from the frozen audited hash")
    python_version = checked_output([str(args.python), "--version"])
    z3_version = checked_output([
        str(args.python), "-c", "import z3; print(z3.get_version_string())",
    ])
    if z3_version != EXPECTED_Z3:
        parser.error(f"expected Z3 {EXPECTED_Z3}, found {z3_version}")

    run_dir = args.run_dir.expanduser().resolve()
    run_dir.mkdir(parents=True, exist_ok=True)
    logs_dir = run_dir / "logs"
    logs_dir.mkdir(exist_ok=True)
    failures_dir = run_dir / "failures"
    manifest_path = run_dir / "RUN_MANIFEST.json"
    complete_path = run_dir / "RUN_COMPLETE.json"
    commands = {case: case_command(args, driver, case) for case in CASES}
    manifest = {
        "format": FORMAT,
        "run_id": args.run_id,
        "created_utc": utc_now(),
        "project_root": str(project_root),
        "python_executable": str(args.python),
        "python_version": python_version,
        "z3_version": z3_version,
        "cases": list(CASES),
        "engine": args.engine,
        "gate_timeout": args.gate_timeout,
        "timeout": args.timeout,
        "memory_mb": args.memory_mb,
        "source_sha256": source_hashes,
        "source_manifest_sha256": source_digest,
        "case_commands": commands,
        "runner_command": [str(runner)] + sys.argv[1:],
    }
    if manifest_path.exists():
        existing = json.loads(manifest_path.read_text(encoding="utf-8"))
        comparable = dict(manifest)
        comparable["created_utc"] = existing.get("created_utc")
        if existing != comparable:
            parser.error(f"existing manifest does not match this resume: {manifest_path}")
        manifest = existing
    else:
        atomic_json(manifest_path, manifest)
    if complete_path.exists():
        parser.error(f"run is already marked complete: {complete_path}")

    started_monotonic = time.monotonic()
    published = {}
    for task, case in enumerate(CASES):
        path = run_one(args, manifest, task, case, logs_dir, failures_dir)
        published[case] = {
            "task": task, "path": str(path.relative_to(run_dir)),
            "sha256": sha256(path),
        }
    completion = {
        "format": FORMAT,
        "run_id": args.run_id,
        "completed_utc": utc_now(),
        "elapsed_seconds": round(time.monotonic() - started_monotonic, 3),
        "logs": published,
        "manifest_sha256": sha256(manifest_path),
    }
    atomic_json(complete_path, completion)
    print(f"LOCAL_RUN_COMPLETE run={args.run_id} cases=6 path={complete_path}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
