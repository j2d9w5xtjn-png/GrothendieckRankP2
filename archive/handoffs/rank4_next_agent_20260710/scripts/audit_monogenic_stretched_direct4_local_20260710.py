#!/usr/bin/env python3
"""Strict standard-library auditor for the six local direct-[4] logs.

This program never imports Z3 and never launches a subprocess.  Success means
that all six reconstructed cases have H0 SAT and the actual direct-[4]
disequality UNSAT, with exact frozen sources, commands, versions, resource
records, atomic-run provenance, and no unknown/SAT/error/malformed artifacts.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import shlex
import sys
from typing import Iterable, Mapping


FORMAT = "rank4-monogenic-direct4-local-run-v1"
EXPECTED_DRIVER_SHA256 = "ac70fdf145989723133d4c4efecb740353b0d8530bc9ee060089271de7a3caac"
EXPECTED_Z3 = "4.16.0"
CASES = (
    "sf2_g0_a0", "sf2_g0_a1", "sf2_g1_a0",
    "sf2_g1_a1", "q00_a0", "q00_a1",
)
SOURCE_LABELS = (
    "scripts/audit_monogenic_stretched_direct4_local_20260710.py",
    "scripts/monogenic_stretched_direct4_20260710.py",
    "scripts/run_monogenic_stretched_direct4_local_20260710.py",
)
UTC = r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z"
SHA_RE = re.compile(r"^SOURCE_FILE_SHA256 path=(\S+) sha=([0-9a-f]{64})$")
SOURCE_MANIFEST_RE = re.compile(
    r"^SOURCE_MANIFEST_SHA256 files=([0-9]+) digest=([0-9a-f]{64})$"
)
H0_RE = re.compile(r"^H0 core -> (sat|unsat|unknown) elapsed=([0-9]+(?:\.[0-9]+)?)s(?: reason=(.*))?$")
D1_RE = re.compile(r"^D1 core\+\[4\]\(T\)!=0 -> (sat|unsat|unknown) elapsed=([0-9]+(?:\.[0-9]+)?)s(?: reason=(.*))?$")
RESULT_RE = re.compile(
    r"^DIRECT4_RESULT case=(\S+) classification=(\S+) engine=(smt|qfbv) "
    r"elapsed_total=([0-9]+(?:\.[0-9]+)?)s maxrss_mib=([0-9]+(?:\.[0-9]+)?) "
    r"platform=(\S+)$"
)
ERROR_MARKERS = (
    "Traceback (most recent call last):", "MemoryError", "Segmentation fault",
    "Bus error", "Killed", "Command terminated by signal", "Z3Exception",
    "out_of_memory", "LOCAL_TASK_FAILED", "SAT_CERTIFICATE",
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def source_digest(hashes: Mapping[str, str]) -> str:
    payload = "".join(f"{label}\t{hashes[label]}\n" for label in sorted(hashes))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def exactly(lines: Iterable[str], prefix: str) -> list[str]:
    return [line for line in lines if line.startswith(prefix)]


def canonical_name(run_id: str, task: int, case: str) -> str:
    return f"monogenic_direct4_local_{run_id}_task{task}_{case}.log"


def issue_if_not_one(issues: list[str], matches: list, label: str):
    if len(matches) != 1:
        issues.append(f"expected exactly one {label}, found {len(matches)}")
        return None
    return matches[0]


def audit_log(path: Path, manifest: Mapping, task: int, case: str) -> tuple[list[str], dict | None]:
    issues: list[str] = []
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        return [f"cannot read UTF-8 log: {error}"], None
    lines = text.splitlines()
    if any(marker in text for marker in ERROR_MARKERS):
        issues.append("error/failure/SAT-certificate marker present")
    if "unknown" in text:
        issues.append("unknown solver outcome present")

    expected_header = f"LOCAL_RUN_HEADER format={FORMAT} run={manifest['run_id']}"
    issue_if_not_one(issues, [line for line in lines if line == expected_header], "run header")
    expected_case = f"LOCAL_CASE_SPEC run={manifest['run_id']} task={task} case={case}"
    issue_if_not_one(issues, [line for line in lines if line == expected_case], "case record")

    seen_sources = {}
    for line in lines:
        match = SHA_RE.fullmatch(line)
        if match:
            label, digest = match.groups()
            if label in seen_sources:
                issues.append(f"duplicate source hash for {label}")
            seen_sources[label] = digest
    if seen_sources != manifest["source_sha256"]:
        issues.append("per-log source hashes differ from RUN_MANIFEST")
    source_lines = [SOURCE_MANIFEST_RE.fullmatch(line) for line in lines]
    source_lines = [match for match in source_lines if match]
    match = issue_if_not_one(issues, source_lines, "source-manifest digest")
    if match and (int(match.group(1)) != len(SOURCE_LABELS)
                  or match.group(2) != manifest["source_manifest_sha256"]):
        issues.append("source-manifest count/digest mismatch")

    py_exec_lines = exactly(lines, "PYTHON_EXECUTABLE_JSON ")
    py_exec = issue_if_not_one(issues, py_exec_lines, "Python executable record")
    if py_exec:
        try:
            if json.loads(py_exec.split(" ", 1)[1]) != manifest["python_executable"]:
                issues.append("Python executable differs from manifest")
        except json.JSONDecodeError:
            issues.append("malformed Python executable JSON")
    py_version_lines = exactly(lines, "PYTHON_VERSION_JSON ")
    py_version = issue_if_not_one(issues, py_version_lines, "Python version record")
    if py_version:
        try:
            if json.loads(py_version.split(" ", 1)[1]) != manifest["python_version"]:
                issues.append("Python version differs from manifest")
        except json.JSONDecodeError:
            issues.append("malformed Python version JSON")
    z3_line = issue_if_not_one(issues, exactly(lines, "Z3_VERSION "), "Z3 version record")
    if z3_line and z3_line != f"Z3_VERSION {EXPECTED_Z3}":
        issues.append("wrong Z3 version")

    command_line = issue_if_not_one(issues, exactly(lines, "COMMAND_JSON "), "command JSON")
    expected_command = manifest["case_commands"][case]
    if command_line:
        try:
            if json.loads(command_line.split(" ", 1)[1]) != expected_command:
                issues.append("command JSON differs from manifest")
        except json.JSONDecodeError:
            issues.append("malformed command JSON")
    driver_command = issue_if_not_one(issues, exactly(lines, "COMMAND "), "driver COMMAND")
    if driver_command:
        try:
            # Python consumes ``-u`` before constructing sys.argv, so the
            # driver's self-reported command omits exactly that launcher flag.
            expected_driver_command = [expected_command[0]] + expected_command[2:]
            if shlex.split(driver_command[len("COMMAND "):]) != expected_driver_command:
                issues.append("driver COMMAND differs from launched command")
        except ValueError as error:
            issues.append(f"malformed driver COMMAND: {error}")

    start_re = re.compile(
        rf"^LOCAL_TASK_START run={re.escape(manifest['run_id'])} task={task} "
        rf"case={re.escape(case)} utc={UTC}$"
    )
    done_re = re.compile(
        rf"^LOCAL_TASK_DONE run={re.escape(manifest['run_id'])} task={task} "
        rf"case={re.escape(case)} utc={UTC} rc=0$"
    )
    issue_if_not_one(issues, [line for line in lines if start_re.fullmatch(line)], "task start")
    issue_if_not_one(issues, [line for line in lines if done_re.fullmatch(line)], "task done")

    config = (
        f"CONFIG case={case} engine={manifest['engine']} "
        f"gate_timeout={manifest['gate_timeout']}s main_timeout={manifest['timeout']}s "
        f"memory={manifest['memory_mb']}MiB threads=1"
    )
    issue_if_not_one(issues, [line for line in lines if line == config], "driver config")
    pin = ("FIBER_PIN_GATE t4_11 relation_stability=PASS coassoc=PASS "
           "q_T_zero=PASS arithmetic=independent_F2_bitmask")
    issue_if_not_one(issues, [line for line in lines if line == pin], "F2 pin gate")
    ring_prefix = f"RING_GATE case={case} |R|=128 exhaustive_assoc_distrib=128^3 "
    ring_line = issue_if_not_one(issues, exactly(lines, ring_prefix), "ring gate")
    if ring_line and not all(token in ring_line for token in (
            "units=64", "m_powers=64,16,8,4,2,1", "socle=<z>",
            "fibres=2", "all_128^2_ops=PASS")):
        issues.append("ring gate lacks required exact checks")
    duplicate_lines = exactly(lines, "DUPLICATE_ISOMORPHISM_GATE ")
    if case.endswith("a1"):
        if len(duplicate_lines) != 1 or "all_128^2_ops=PASS" not in duplicate_lines[0]:
            issues.append("missing or malformed duplicate-isomorphism gate")
    elif duplicate_lines:
        issues.append("unexpected duplicate-isomorphism gate")
    system_prefix = f"SYSTEM_BUILT case={case} core_constraints=84 ring_variables=12 "
    issue_if_not_one(issues, exactly(lines, system_prefix), "system-build record")

    h0_matches = [H0_RE.fullmatch(line) for line in lines]
    h0_matches = [match for match in h0_matches if match]
    h0 = issue_if_not_one(issues, h0_matches, "H0 result")
    if h0 and h0.group(1) != "sat":
        issues.append(f"H0 is {h0.group(1)}, expected sat")
    d1_matches = [D1_RE.fullmatch(line) for line in lines]
    d1_matches = [match for match in d1_matches if match]
    d1 = issue_if_not_one(issues, d1_matches, "D1 result")
    if d1 and d1.group(1) != "unsat":
        issues.append(f"direct [4] disequality is {d1.group(1)}, expected unsat")

    result_matches = [RESULT_RE.fullmatch(line) for line in lines]
    result_matches = [match for match in result_matches if match]
    result = issue_if_not_one(issues, result_matches, "DIRECT4_RESULT")
    resource = None
    if result:
        result_case, classification, engine, elapsed, maxrss, platform = result.groups()
        if (result_case, classification, engine) != (
                case, "direct-[4]-UNSAT", manifest["engine"]):
            issues.append("DIRECT4_RESULT case/classification/engine mismatch")
        elapsed_value, maxrss_value = float(elapsed), float(maxrss)
        if elapsed_value <= 0 or maxrss_value <= 0:
            issues.append("nonpositive elapsed time or MaxRSS")
        if maxrss_value > manifest["memory_mb"] * 1.05:
            issues.append("reported MaxRSS exceeds configured memory ceiling by >5%")
        resource = {"elapsed_seconds": elapsed_value, "maxrss_mib": maxrss_value,
                    "platform": platform}
    final = f"DONE monogenic_stretched_direct4_20260710 case={case}"
    issue_if_not_one(issues, [line for line in lines if line == final], "driver final marker")
    return issues, resource


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("run_dir", type=Path)
    parser.add_argument("--project-root", type=Path, default=Path.cwd())
    args = parser.parse_args()
    run_dir = args.run_dir.expanduser().resolve()
    project_root = args.project_root.expanduser().resolve()
    issues: list[str] = []

    manifest_path, completion_path = run_dir / "RUN_MANIFEST.json", run_dir / "RUN_COMPLETE.json"
    try:
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    except Exception as error:
        print(f"AUDIT FAIL: cannot read RUN_MANIFEST.json: {error}")
        return 1
    try:
        completion = json.loads(completion_path.read_text(encoding="utf-8"))
    except Exception as error:
        print(f"AUDIT FAIL: cannot read RUN_COMPLETE.json: {error}")
        return 1

    if manifest.get("format") != FORMAT or completion.get("format") != FORMAT:
        issues.append("wrong manifest/completion format")
    if manifest.get("run_id") != completion.get("run_id"):
        issues.append("manifest/completion run IDs differ")
    if tuple(manifest.get("cases", ())) != CASES:
        issues.append("manifest does not contain the exact six-case universe")
    if manifest.get("z3_version") != EXPECTED_Z3:
        issues.append("manifest has wrong Z3 version")
    if manifest.get("engine") not in ("smt", "qfbv"):
        issues.append("manifest has invalid engine")
    if manifest.get("source_sha256", {}).get(
            "scripts/monogenic_stretched_direct4_20260710.py") != EXPECTED_DRIVER_SHA256:
        issues.append("manifest has wrong frozen driver hash")
    if set(manifest.get("source_sha256", {})) != set(SOURCE_LABELS):
        issues.append("manifest source-file universe is wrong")
    elif source_digest(manifest["source_sha256"]) != manifest.get("source_manifest_sha256"):
        issues.append("manifest source digest does not recompute")
    if sha256(manifest_path) != completion.get("manifest_sha256"):
        issues.append("completion has wrong manifest hash")

    current_paths = {
        "scripts/audit_monogenic_stretched_direct4_local_20260710.py": Path(__file__).resolve(),
        "scripts/monogenic_stretched_direct4_20260710.py": project_root / "scripts/monogenic_stretched_direct4_20260710.py",
        "scripts/run_monogenic_stretched_direct4_local_20260710.py": project_root / "scripts/run_monogenic_stretched_direct4_local_20260710.py",
    }
    for label, path in current_paths.items():
        try:
            current = sha256(path)
        except OSError as error:
            issues.append(f"cannot hash current source {label}: {error}")
            continue
        if current != manifest.get("source_sha256", {}).get(label):
            issues.append(f"current source hash differs for {label}")

    logs_dir = run_dir / "logs"
    expected_names = {
        canonical_name(manifest.get("run_id", "INVALID"), task, case)
        for task, case in enumerate(CASES)
    }
    actual_names = {path.name for path in logs_dir.glob("*.log")} if logs_dir.is_dir() else set()
    if actual_names != expected_names:
        issues.append(
            f"canonical log universe mismatch: missing={sorted(expected_names-actual_names)} "
            f"extra={sorted(actual_names-expected_names)}"
        )
    debris = []
    if logs_dir.is_dir():
        debris.extend(path.name for path in logs_dir.iterdir() if ".partial." in path.name)
    failures = run_dir / "failures"
    if failures.is_dir():
        debris.extend(str(path.relative_to(run_dir)) for path in failures.iterdir())
    if debris:
        issues.append(f"partial/failed artifacts present: {sorted(debris)}")

    resources = {}
    for task, case in enumerate(CASES):
        path = logs_dir / canonical_name(manifest.get("run_id", "INVALID"), task, case)
        if not path.is_file():
            continue
        log_issues, resource = audit_log(path, manifest, task, case)
        issues.extend(f"{path.name}: {issue}" for issue in log_issues)
        if resource:
            resources[case] = resource
        entry = completion.get("logs", {}).get(case)
        if not isinstance(entry, dict):
            issues.append(f"completion missing log entry for {case}")
        else:
            if entry.get("task") != task or entry.get("path") != f"logs/{path.name}":
                issues.append(f"completion mapping mismatch for {case}")
            if entry.get("sha256") != sha256(path):
                issues.append(f"completion log hash mismatch for {case}")
    if set(completion.get("logs", {})) != set(CASES):
        issues.append("completion log universe differs from six cases")

    print("MONOGENIC DIRECT-[4] STRICT LOCAL AUDIT")
    print(f"run={manifest.get('run_id')} cases={len(CASES)} audited_resources={len(resources)}")
    for case in CASES:
        if case in resources:
            item = resources[case]
            print(f"  {case}: H0=SAT D1=UNSAT elapsed={item['elapsed_seconds']:.2f}s "
                  f"maxrss={item['maxrss_mib']:.2f}MiB platform={item['platform']}")
    if issues:
        print(f"AUDIT FAIL issues={len(issues)}")
        for issue in issues:
            print(f"  - {issue}")
        return 1
    print("AUDIT PASS six_of_six_H0_SAT_and_direct4_UNSAT errors=0 unknown=0 SAT=0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
