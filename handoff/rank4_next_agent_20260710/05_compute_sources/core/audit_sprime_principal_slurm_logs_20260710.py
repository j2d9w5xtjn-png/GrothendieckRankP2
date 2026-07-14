#!/usr/bin/env python3
"""Strictly audit the 300-task principal-chain-ring evidence sweep.

The canonical input is the per-coordinate output of
``slurm/run_principal_array.sbatch``.  The array mapping is reconstructed
here rather than trusted from a log:

    i = T % 3 + 1
    row = (T // 3) % 10
    ring = RINGS[T // 30]

A row is mathematically closed only by one audited H0=unsat task or by
three audited S2.i=unsat tasks.  SAT is reported as a candidate.  Unknown,
truncated, malformed, and missing tasks never count as negative evidence.

Repeated ``--log-dir`` options combine Slurm retries or banked copies.
Repeated ``--local-log-dir`` options add honestly labelled local-process
evidence without relabelling it as Slurm output.  Valid duplicates across
both origins are compared; contradictory conclusive results are errors.
Optional legacy coarse logs are summarized as explicitly noncanonical
supplemental evidence and never affect canonical closure.

This script uses only the Python standard library and never launches Z3.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import hashlib
import math
from pathlib import Path
import re
import shlex
import sys
from typing import Iterable


DRIVER_BASENAME = "sprime_principal_length6_ten_stratified_evidence_map_20260710.py"
FINAL_MARKER = "DONE sprime_principal_length6_ten_stratified_evidence_map_20260710"
SBATCH_DEFAULT = "slurm/run_principal_array.sbatch"
EXPECTED_Z3 = "4.16.0"

PRINCIPAL_SOURCE_FILES = (
    "scripts/order4sat.py",
    "scripts/order4sat_beyond.py",
    "scripts/order4sat_f8.py",
    "scripts/order4sat_f8ram_alpha2mu2_pinned_20260709.py",
    "scripts/order4sat_ramified_embdim2_len6_20260709.py",
    "scripts/order4sat_ramified_towers_20260709.py",
    "scripts/principal_length6_chain_classification_evidence_map_20260710.py",
    "scripts/ringcheck.py",
    "scripts/s2check.py",
    "scripts/sprime_principal_length6_ten_stratified_evidence_map_20260710.py",
    "scripts/sprime_ramified_principal_depth5_stratified_20260709.py",
)

RINGS = (
    "e1_0000",
    "e2_000", "e2_001", "e2_100", "e2_110",
    "e3_00",
    "e4_0", "e4_1",
    "e5_-",
    "eqchar",
)
XY_MODELS = (
    "a2a2", "W2F", "mu2mu2", "mu2a2",
    "mu2mu2_unipotent", "mu2mu2_irreducible",
)
T4_FORMS = ("00", "01", "10", "11")
ROW_STATUSES = (
    "closed UNSAT", "H0-vacuous", "SAT candidate",
    "unknown", "incomplete", "error",
)
COUNT_KEYS = (
    "H0-vacuous", "SAT S'-failure", "UNSAT", "partial-UNSAT", "unknown",
)

FILENAME_RE = re.compile(r"^principal_([0-9]+)_([0-9]+)\.log$")
LOCAL_RUN_PATTERN = r"[A-Za-z0-9][A-Za-z0-9_.-]{0,63}"
LOCAL_FILENAME_RE = re.compile(
    rf"^principal_local_({LOCAL_RUN_PATTERN})_task_([0-9]+)\.log$"
)
CASE_MAIN_RE = re.compile(
    r"^CASE_SPEC job=(\S+) array_job=(\S+) task=([0-9]+) "
    r"ring=(\S+) row=([0-9]+) i=([0-9]+)$"
)
LOCAL_CASE_MAIN_RE = re.compile(
    rf"^LOCAL_CASE_SPEC run=({LOCAL_RUN_PATTERN}) task=([0-9]+) "
    r"ring=(\S+) row=([0-9]+) i=([0-9]+)$"
)
CASE_FIBER_RE = re.compile(
    r"^CASE_SPEC fiber=(xy|t4) (model|form)=([A-Za-z0-9_-]+)$"
)
SHA_RE = re.compile(r"^SOURCE_SHA256 driver=([0-9a-f]{64})$")
SOURCE_FILE_RE = re.compile(
    r"^SOURCE_FILE_SHA256 path=(\S+) sha=([0-9a-f]{64})$"
)
SOURCE_MANIFEST_RE = re.compile(
    r"^SOURCE_MANIFEST_SHA256 files=([0-9]+) digest=([0-9a-f]{64})$"
)
PYTHON_RE = re.compile(r"^Python ([0-9]+\.[0-9]+\.[0-9]+(?:[^\s]*)?)$")
Z3_RE = re.compile(r"^Z3 ([0-9]+\.[0-9]+\.[0-9]+)$")
TASK_DONE_RE = re.compile(
    r"^TASK_DONE job=(\S+) task=([0-9]+) "
    r"utc=([0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z)$"
)
LOCAL_TASK_DONE_RE = re.compile(
    rf"^LOCAL_TASK_DONE run=({LOCAL_RUN_PATTERN}) task=([0-9]+) "
    r"utc=([0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z) rc=0$"
)
H0_RE = re.compile(
    r"^\s*\[H0 axioms\+fiber2\] -> (sat|unsat|unknown) "
    r"\(([0-9]+(?:\.[0-9]+)?)s\)(?: reason=(.+))?$"
)
S1_RE = re.compile(
    r"^\s*\[S1 axioms\+fiber2\+S'-HOLDS\] -> (sat|unsat|unknown) "
    r"\(([0-9]+(?:\.[0-9]+)?)s\)(?: reason=(.+))?$"
)
S2_RE = re.compile(
    r"^\s*\[S2\.([123]) exact S'-FAIL_i\] -> (sat|unsat|unknown) "
    r"\(([0-9]+(?:\.[0-9]+)?)s\)(?: reason=(.+))?$"
)
ROW_CLASS_RE = re.compile(r"^\s*\[ROW CLASS\] (.+?)\s*$")
RESOURCE_RE = re.compile(
    r"^PROCESS_RESOURCE elapsed_seconds=([0-9]+(?:\.[0-9]+)?) "
    r"maxrss_mib=([0-9]+(?:\.[0-9]+)?) platform=(\S+)\s*$"
)
ERROR_MARKERS = (
    "Traceback (most recent call last):",
    "MemoryError",
    "Segmentation fault",
    "Bus error",
    "Killed",
    "Command terminated by signal",
    "z3.z3types.Z3Exception",
    "slurmstepd: error:",
    "OUT_OF_MEMORY",
)


@dataclasses.dataclass(frozen=True, order=True)
class Row:
    index: int
    fiber: str
    model: str

    @property
    def label(self) -> str:
        if self.fiber == "xy":
            return f"xy/{self.model}"
        return f"t4/c1={self.model[0]},c4={self.model[1]}"

    @property
    def option(self) -> str:
        return "--xy-models" if self.fiber == "xy" else "--t4-forms"


ROWS = tuple(
    [Row(index, "xy", model) for index, model in enumerate(XY_MODELS)]
    + [Row(index + 6, "t4", form) for index, form in enumerate(T4_FORMS)]
)


@dataclasses.dataclass(frozen=True, order=True)
class Task:
    task_id: int
    ring_index: int
    ring: str
    row: Row
    coordinate: int

    @classmethod
    def from_id(cls, task_id: int) -> "Task":
        if not 0 <= task_id < 300:
            raise ValueError(f"array task ID {task_id} is outside 0..299")
        coordinate = task_id % 3 + 1
        row_index = (task_id // 3) % 10
        ring_index = task_id // 30
        return cls(task_id, ring_index, RINGS[ring_index], ROWS[row_index], coordinate)


TASKS = tuple(Task.from_id(task_id) for task_id in range(300))
TASK_BY_ROW_COORD = {
    (task.ring, task.row.index, task.coordinate): task for task in TASKS
}


@dataclasses.dataclass(frozen=True)
class Resource:
    elapsed_seconds: float
    maxrss_mib: float
    platform: str


@dataclasses.dataclass
class LogAudit:
    path: Path
    filename_job: str | None
    task: Task | None
    state: str
    outcome: str | None = None
    h0: str | None = None
    s1: str | None = None
    s2: str | None = None
    resource: Resource | None = None
    driver_sha: str | None = None
    slurm_job: str | None = None
    issues: list[str] = dataclasses.field(default_factory=list)
    origin: str = "slurm"
    local_run: str | None = None

    @property
    def valid_terminal(self) -> bool:
        return self.state == "terminal"


@dataclasses.dataclass
class EffectiveTask:
    task: Task
    state: str
    outcome: str | None
    h0: str | None
    s1: str | None
    s2: str | None
    source: Path | None
    audits: list[LogAudit]
    issues: list[str] = dataclasses.field(default_factory=list)


@dataclasses.dataclass
class RowAudit:
    ring: str
    row: Row
    status: str
    tasks: dict[int, EffectiveTask]
    issues: list[str] = dataclasses.field(default_factory=list)


def one_option(tokens: list[str], option: str) -> list[str] | None:
    positions = [index for index, token in enumerate(tokens) if token == option]
    if len(positions) != 1:
        return None
    start = positions[0] + 1
    end = start
    while end < len(tokens) and not tokens[end].startswith("--"):
        end += 1
    return tokens[start:end]


def parse_s2_summary(text: str) -> tuple[dict[int, str], str | None]:
    if text == "not-run":
        return {}, None
    result: dict[int, str] = {}
    for item in text.split(","):
        match = re.fullmatch(r"([123]):(sat|unsat|unknown)", item)
        if not match:
            return {}, f"malformed summary S2 field {text!r}"
        coordinate = int(match.group(1))
        if coordinate in result:
            return {}, f"duplicate coordinate in summary S2 field {text!r}"
        result[coordinate] = match.group(2)
    return result, None


def parse_counts(line: str) -> tuple[dict[str, int], str | None]:
    if not line.startswith("COUNTS "):
        return {}, "missing COUNTS prefix"
    counts: dict[str, int] = {}
    for part in line[len("COUNTS "):].split(", "):
        if "=" not in part:
            return {}, f"malformed COUNTS item {part!r}"
        key, value = part.rsplit("=", 1)
        if key in counts or not value.isdigit():
            return {}, f"malformed COUNTS item {part!r}"
        counts[key] = int(value)
    return counts, None


def result_values(
    lines: Iterable[str], regex: re.Pattern[str], result_group: int = 1
) -> list[tuple[str, str | None]]:
    values: list[tuple[str, str | None]] = []
    for line in lines:
        match = regex.fullmatch(line)
        if match:
            result = match.group(result_group)
            reason = match.group(result_group + 2)
            if result == "unknown" and not reason:
                reason = "__MISSING_REASON__"
            elif result != "unknown" and reason:
                reason = "__SPURIOUS_REASON__"
            values.append((result, reason))
    return values


def audit_log(
    path: Path,
    expected_sha: str,
    expected_manifest: tuple[tuple[str, str], ...],
    expected_manifest_sha: str,
    origin: str = "slurm",
) -> LogAudit:
    if origin not in ("slurm", "local"):
        raise ValueError(f"unknown evidence origin {origin!r}")
    filename_re = FILENAME_RE if origin == "slurm" else LOCAL_FILENAME_RE
    match = filename_re.fullmatch(path.name)
    if not match:
        return LogAudit(
            path, None, None, "error",
            issues=[f"malformed principal {origin} task-log filename"],
            origin=origin,
        )
    filename_identity, task_text = match.groups()
    try:
        task = Task.from_id(int(task_text))
    except ValueError as exc:
        return LogAudit(
            path,
            filename_identity if origin == "slurm" else None,
            None,
            "error",
            issues=[str(exc)],
            origin=origin,
            local_run=filename_identity if origin == "local" else None,
        )
    audit = LogAudit(
        path,
        filename_identity if origin == "slurm" else None,
        task,
        "error",
        origin=origin,
        local_run=filename_identity if origin == "local" else None,
    )

    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        audit.issues.append(f"could not read log: {exc}")
        return audit
    lines = text.splitlines()
    crash_markers = [marker for marker in ERROR_MARKERS if marker in text]

    final_positions = [
        index for index, line in enumerate(lines) if line.strip() == FINAL_MARKER
    ]
    task_done_re = TASK_DONE_RE if origin == "slurm" else LOCAL_TASK_DONE_RE
    task_done_matches = [
        (index, match)
        for index, line in enumerate(lines)
        if (match := task_done_re.fullmatch(line))
    ]
    terminal_claimed = bool(final_positions or task_done_matches)

    case_main_re = CASE_MAIN_RE if origin == "slurm" else LOCAL_CASE_MAIN_RE
    case_main = [
        (index, match)
        for index, line in enumerate(lines)
        if (match := case_main_re.fullmatch(line))
    ]
    if len(case_main) != 1:
        audit.issues.append(f"expected one main CASE_SPEC, found {len(case_main)}")
    else:
        _, case = case_main[0]
        if origin == "slurm":
            job, array_job, observed_task, ring, row, coordinate = case.groups()
            audit.slurm_job = job
            expected = (
                filename_identity, str(task.task_id), task.ring,
                str(task.row.index), str(task.coordinate),
            )
            observed = (array_job, observed_task, ring, row, coordinate)
            fields = "array_job,task,ring,row,i"
        else:
            run, observed_task, ring, row, coordinate = case.groups()
            expected = (
                filename_identity, str(task.task_id), task.ring,
                str(task.row.index), str(task.coordinate),
            )
            observed = (run, observed_task, ring, row, coordinate)
            fields = "run,task,ring,row,i"
        if observed != expected:
            audit.issues.append(
                "main CASE_SPEC/mapping mismatch: "
                f"expected {fields}={expected}, observed={observed}"
            )

    case_fiber = [
        (index, match)
        for index, line in enumerate(lines)
        if (match := CASE_FIBER_RE.fullmatch(line))
    ]
    if len(case_fiber) != 1:
        audit.issues.append(f"expected one fiber CASE_SPEC, found {len(case_fiber)}")
    else:
        _, case = case_fiber[0]
        observed = case.groups()
        expected_kind = "model" if task.row.fiber == "xy" else "form"
        expected = (task.row.fiber, expected_kind, task.row.model)
        if observed != expected:
            audit.issues.append(
                f"fiber CASE_SPEC mismatch: expected {expected}, observed {observed}"
            )

    sha_matches = [
        (index, match.group(1))
        for index, line in enumerate(lines)
        if (match := SHA_RE.fullmatch(line))
    ]
    if len(sha_matches) != 1:
        audit.issues.append(f"expected one SOURCE_SHA256 line, found {len(sha_matches)}")
    else:
        _, audit.driver_sha = sha_matches[0]
        if audit.driver_sha != expected_sha:
            audit.issues.append(
                f"driver SHA mismatch: expected {expected_sha}, observed {audit.driver_sha}"
            )

    source_file_matches = [
        (index, match.group(1), match.group(2))
        for index, line in enumerate(lines)
        if (match := SOURCE_FILE_RE.fullmatch(line))
    ]
    observed_manifest = tuple(
        (source_path, source_sha)
        for _, source_path, source_sha in source_file_matches
    )
    if observed_manifest != expected_manifest:
        audit.issues.append(
            "source-file manifest mismatch: expected "
            f"{len(expected_manifest)} exact sorted entries, observed "
            f"{len(observed_manifest)} entries"
        )
        expected_map = dict(expected_manifest)
        observed_map = dict(observed_manifest)
        missing = [path for path in expected_map if path not in observed_map]
        extra = [path for path in observed_map if path not in expected_map]
        changed = [
            path for path in expected_map
            if path in observed_map and expected_map[path] != observed_map[path]
        ]
        if missing:
            audit.issues.append("source manifest missing: " + ", ".join(missing))
        if extra:
            audit.issues.append("source manifest extra: " + ", ".join(extra))
        if changed:
            audit.issues.append("source manifest changed hash: " + ", ".join(changed))

    manifest_matches = [
        (index, int(match.group(1)), match.group(2))
        for index, line in enumerate(lines)
        if (match := SOURCE_MANIFEST_RE.fullmatch(line))
    ]
    if len(manifest_matches) != 1:
        audit.issues.append(
            f"expected one SOURCE_MANIFEST_SHA256 line, found {len(manifest_matches)}"
        )
    else:
        _, observed_count, observed_digest = manifest_matches[0]
        if (observed_count, observed_digest) != (
            len(expected_manifest), expected_manifest_sha,
        ):
            audit.issues.append(
                "source-manifest aggregate mismatch: expected "
                f"files={len(expected_manifest)} digest={expected_manifest_sha}, "
                f"observed files={observed_count} digest={observed_digest}"
            )
        observed_payload = "".join(
            f"{source_path}\t{source_sha}\n"
            for source_path, source_sha in observed_manifest
        ).encode("utf-8")
        observed_recomputed = hashlib.sha256(observed_payload).hexdigest()
        if observed_digest != observed_recomputed:
            audit.issues.append(
                "logged source-manifest digest does not match its individual entries: "
                f"logged={observed_digest} recomputed={observed_recomputed}"
            )
    if len(sha_matches) == 1 and observed_manifest:
        logged_map = dict(observed_manifest)
        driver_rel = "scripts/" + DRIVER_BASENAME
        if logged_map.get(driver_rel) != sha_matches[0][1]:
            audit.issues.append(
                "SOURCE_SHA256 driver does not agree with its source-manifest entry"
            )

    python_matches = [
        (index, match.group(1))
        for index, line in enumerate(lines)
        if (match := PYTHON_RE.fullmatch(line))
    ]
    z3_matches = [
        (index, match.group(1))
        for index, line in enumerate(lines)
        if (match := Z3_RE.fullmatch(line))
    ]
    if len(python_matches) != 1:
        audit.issues.append(f"expected one Python version banner, found {len(python_matches)}")
    if len(z3_matches) != 1:
        audit.issues.append(f"expected one Z3 version banner, found {len(z3_matches)}")
    elif z3_matches[0][1] != EXPECTED_Z3:
        audit.issues.append(
            f"Z3 version mismatch: expected {EXPECTED_Z3}, observed {z3_matches[0][1]}"
        )

    command_lines = [
        (index, line[len("COMMAND "):])
        for index, line in enumerate(lines) if line.startswith("COMMAND ")
    ]
    if len(command_lines) != 1:
        audit.issues.append(f"expected one COMMAND line, found {len(command_lines)}")
    else:
        _, command = command_lines[0]
        try:
            tokens = shlex.split(command)
        except ValueError as exc:
            tokens = []
            audit.issues.append(f"could not parse COMMAND line: {exc}")
        driver_tokens = [token for token in tokens if Path(token).name == DRIVER_BASENAME]
        if len(driver_tokens) != 1:
            audit.issues.append(
                f"COMMAND must name {DRIVER_BASENAME} exactly once; "
                f"found {len(driver_tokens)}"
            )
        expected_options = {
            "--rings": [task.ring],
            "--only-i": [str(task.coordinate)],
            "--timeout": ["3600"],
            "--memory-mb": ["6144"],
            "--fibers": [task.row.fiber],
            task.row.option: [task.row.model],
        }
        for option, expected in expected_options.items():
            observed = one_option(tokens, option)
            if observed != expected:
                audit.issues.append(
                    f"COMMAND {option} mismatch: expected {expected}, observed {observed}"
                )
        opposite = "--t4-forms" if task.row.fiber == "xy" else "--xy-models"
        if opposite in tokens:
            audit.issues.append(f"COMMAND unexpectedly contains {opposite}")
        if "--validate-only" in tokens:
            audit.issues.append("COMMAND unexpectedly contains --validate-only")

    exact_header = "EXACT S' SWEEP -- TEN PRINCIPAL LENGTH-SIX CHAIN RINGS"
    headers = [index for index, line in enumerate(lines) if line == exact_header]
    if len(headers) != 1:
        audit.issues.append(f"expected one exact-sweep header, found {len(headers)}")
    memory_banner = [
        index for index, line in enumerate(lines)
        if line == "Sequential/single-threaded; Z3 memory ceiling=6144MiB."
    ]
    if len(memory_banner) != 1:
        audit.issues.append(
            f"expected one serial/6144MiB memory banner, found {len(memory_banner)}"
        )

    ring_headers = [
        (index, line[6:-6])
        for index, line in enumerate(lines)
        if line.startswith("===== ") and line.endswith(" =====")
        and line[6:-6] in RINGS
    ]
    if [ring for _, ring in ring_headers] != [task.ring]:
        audit.issues.append(
            f"ring header mismatch: expected [{task.ring!r}], "
            f"observed {[ring for _, ring in ring_headers]}"
        )
    expected_gate = (
        f"  [symbolic-vs-concrete 64^2 gate] {task.ring}: add/sub/mul exact; "
        "ann(t)={0,t^5} -> PASS"
    )
    gates = [index for index, line in enumerate(lines) if line == expected_gate]
    all_gates = [
        line for line in lines if "[symbolic-vs-concrete 64^2 gate]" in line
    ]
    if len(gates) != 1 or len(all_gates) != 1:
        audit.issues.append("missing, repeated, failed, or mistagged symbolic ring gate")

    row_headers = [
        (index, line.strip()[4:-4])
        for index, line in enumerate(lines)
        if line.strip().startswith("--- ") and line.strip().endswith(" ---")
    ]
    if [label for _, label in row_headers] != [task.row.label]:
        audit.issues.append(
            f"row header mismatch: expected [{task.row.label!r}], "
            f"observed {[label for _, label in row_headers]}"
        )

    h0_values = result_values(lines, H0_RE)
    s1_values = result_values(lines, S1_RE)
    s2_matches: list[tuple[int, str, str | None]] = []
    for line in lines:
        match = S2_RE.fullmatch(line)
        if match:
            result, reason = match.group(2), match.group(4)
            if result == "unknown" and not reason:
                reason = "__MISSING_REASON__"
            elif result != "unknown" and reason:
                reason = "__SPURIOUS_REASON__"
            s2_matches.append((int(match.group(1)), result, reason))
    for label, values in (("H0", h0_values), ("S1", s1_values)):
        for result, reason in values:
            if reason == "__MISSING_REASON__":
                audit.issues.append(f"{label}=unknown is missing reason_unknown")
            elif reason == "__SPURIOUS_REASON__":
                audit.issues.append(f"{label}={result} has a spurious unknown reason")
    for coordinate, result, reason in s2_matches:
        if reason == "__MISSING_REASON__":
            audit.issues.append(f"S2.{coordinate}=unknown is missing reason_unknown")
        elif reason == "__SPURIOUS_REASON__":
            audit.issues.append(
                f"S2.{coordinate}={result} has a spurious unknown reason"
            )
    if len(h0_values) != 1:
        audit.issues.append(f"expected one H0 result, found {len(h0_values)}")

    summary_re = re.compile(
        rf"^  {re.escape(task.row.label)}: class=(.+?); "
        rf"H0=(sat|unsat|unknown); S1=(sat|unsat|unknown|not-run); S2=(.+)$"
    )
    summaries = [
        (index, match.groups())
        for index, line in enumerate(lines)
        if (match := summary_re.fullmatch(line))
    ]
    all_summaries = [
        line for line in lines
        if re.match(r"^  (?:xy/|t4/c1=).+: class=", line)
    ]
    if len(summaries) != 1 or len(all_summaries) != 1:
        audit.issues.append(
            "expected exactly one correctly tagged row summary; "
            f"tagged={len(summaries)} all={len(all_summaries)}"
        )
        summary_class = summary_h0 = summary_s1 = None
        summary_s2: dict[int, str] = {}
    else:
        _, groups = summaries[0]
        summary_class, summary_h0, summary_s1, summary_s2_text = groups
        summary_s2, summary_error = parse_s2_summary(summary_s2_text)
        if summary_error:
            audit.issues.append(summary_error)

    audit.h0 = summary_h0
    audit.s1 = summary_s1
    if len(h0_values) == 1 and summary_h0 is not None:
        if h0_values[0][0] != summary_h0:
            audit.issues.append(
                f"H0 direct/summary mismatch: {h0_values[0][0]} versus {summary_h0}"
            )
    if summary_s1 is not None:
        expected_direct = [] if summary_s1 == "not-run" else [summary_s1]
        observed_direct = [value for value, _ in s1_values]
        if observed_direct != expected_direct:
            audit.issues.append(
                f"S1 direct/summary mismatch: {observed_direct} versus {summary_s1}"
            )
    observed_s2 = [(coordinate, result) for coordinate, result, _ in s2_matches]
    if len(dict(observed_s2)) != len(observed_s2) or dict(observed_s2) != summary_s2:
        audit.issues.append(
            f"S2 direct/summary mismatch: {observed_s2} versus {summary_s2}"
        )

    vacuous_markers = [line for line in lines if line.strip() == "[H0-VACUOUS]"]
    sat_validation = [
        line for line in lines
        if line.strip() ==
        "[independent SAT validation] equations, division, all 8 shifts -> PASS"
    ]
    if summary_h0 == "unsat":
        if (summary_class, summary_s1, summary_s2) != (
            "H0-vacuous", "not-run", {},
        ):
            audit.issues.append("H0=unsat row lacks canonical H0-vacuous summary")
        if len(vacuous_markers) != 1:
            audit.issues.append(
                f"expected one H0-VACUOUS marker, found {len(vacuous_markers)}"
            )
        if s1_values or s2_matches or sat_validation:
            audit.issues.append("H0-vacuous row unexpectedly contains S1/S2 evidence")
        expected_classes: list[str] = []
        audit.outcome = "H0-vacuous"
    elif summary_h0 == "unknown":
        if summary_class != "unknown" or summary_s1 != "not-run" or summary_s2:
            audit.issues.append("H0=unknown row lacks canonical unknown summary")
        if vacuous_markers or s1_values or s2_matches or sat_validation:
            audit.issues.append("H0=unknown row unexpectedly contains later evidence")
        expected_classes = []
        audit.outcome = "unknown"
    elif summary_h0 == "sat":
        if summary_s1 != "sat":
            audit.issues.append(
                "H0=sat split query requires the S1=sat witness gate; "
                f"observed {summary_s1}"
            )
        if set(summary_s2) != {task.coordinate}:
            audit.issues.append(
                f"summary must contain exactly S2.{task.coordinate}: {summary_s2}"
            )
        audit.s2 = summary_s2.get(task.coordinate)
        if audit.s2 == "sat":
            expected_class, audit.outcome = "SAT S'-failure", "SAT"
            if len(sat_validation) != 1:
                audit.issues.append(
                    f"expected one independent SAT validation, found {len(sat_validation)}"
                )
        elif audit.s2 == "unsat":
            expected_class, audit.outcome = "partial-UNSAT", "UNSAT"
            if sat_validation:
                audit.issues.append("UNSAT task unexpectedly has SAT validation marker")
        elif audit.s2 == "unknown":
            expected_class, audit.outcome = "unknown", "unknown"
            if sat_validation:
                audit.issues.append("unknown task unexpectedly has SAT validation marker")
        else:
            expected_class = None
            audit.issues.append("H0=sat row has no recognized S2 result")
        if expected_class is not None and summary_class != expected_class:
            audit.issues.append(
                f"row class mismatch: expected {expected_class!r}, observed {summary_class!r}"
            )
        expected_classes = [expected_class] if expected_class else []
        if vacuous_markers:
            audit.issues.append("H0=sat row unexpectedly has H0-VACUOUS marker")
    else:
        expected_classes = []

    row_classes = [
        match.group(1) for line in lines if (match := ROW_CLASS_RE.fullmatch(line))
    ]
    if row_classes != expected_classes:
        audit.issues.append(
            f"ROW CLASS mismatch: expected {expected_classes}, observed {row_classes}"
        )

    done_ring = [
        index for index, line in enumerate(lines) if line.strip() == f"DONE {task.ring}"
    ]
    terminal_summary = [
        index for index, line in enumerate(lines)
        if line.strip() == "===== TERMINAL SUMMARY ====="
    ]
    count_positions = [
        index for index, line in enumerate(lines) if line.startswith("COUNTS ")
    ]
    resource_matches = [
        (index, match)
        for index, line in enumerate(lines)
        if (match := RESOURCE_RE.fullmatch(line))
    ]
    marker_groups = (
        ("DONE ring", done_ring),
        ("terminal summary", terminal_summary),
        ("COUNTS", count_positions),
        ("PROCESS_RESOURCE", [index for index, _ in resource_matches]),
        ("final driver DONE", final_positions),
        (
            "TASK_DONE" if origin == "slurm" else "LOCAL_TASK_DONE",
            [index for index, _ in task_done_matches],
        ),
    )
    for label, positions in marker_groups:
        if len(positions) != 1:
            audit.issues.append(f"expected one {label}, found {len(positions)}")
    if all(len(positions) == 1 for _, positions in marker_groups):
        positions = [positions[0] for _, positions in marker_groups]
        if positions != sorted(positions):
            audit.issues.append(f"terminal markers out of order: {positions}")

    if len(task_done_matches) == 1:
        _, done = task_done_matches[0]
        done_identity, done_task, *_ = done.groups()
        if done_task != str(task.task_id):
            audit.issues.append(
                f"task-done task mismatch: expected {task.task_id}, observed {done_task}"
            )
        if origin == "slurm":
            if audit.slurm_job is not None and done_identity != audit.slurm_job:
                audit.issues.append(
                    "TASK_DONE job mismatch: "
                    f"expected {audit.slurm_job}, observed {done_identity}"
                )
        elif done_identity != filename_identity:
            audit.issues.append(
                "LOCAL_TASK_DONE run mismatch: "
                f"expected {filename_identity}, observed {done_identity}"
            )

    if len(resource_matches) == 1:
        match = resource_matches[0][1]
        elapsed, maxrss = float(match.group(1)), float(match.group(2))
        if not all(math.isfinite(value) and value >= 0 for value in (elapsed, maxrss)):
            audit.issues.append("PROCESS_RESOURCE contains invalid numeric values")
        else:
            audit.resource = Resource(elapsed, maxrss, match.group(3))
    elif any(line.startswith("PROCESS_RESOURCE") for line in lines):
        audit.issues.append("malformed PROCESS_RESOURCE line")

    if len(count_positions) == 1 and summary_class is not None:
        counts, count_error = parse_counts(lines[count_positions[0]])
        if count_error:
            audit.issues.append(count_error)
        elif tuple(counts) != COUNT_KEYS:
            audit.issues.append(
                f"COUNTS keys/order mismatch: expected {COUNT_KEYS}, observed {tuple(counts)}"
            )
        elif counts.get(summary_class) != 1 or sum(counts.values()) != 1:
            audit.issues.append(
                f"COUNTS do not encode exactly one {summary_class!r} row: {counts}"
            )

    # Validate the wrapper/driver order independently of terminal summaries.
    ordered = []
    for name, matches in (
        ("main CASE_SPEC", case_main),
        ("SOURCE_SHA256", sha_matches),
        ("SOURCE_MANIFEST_SHA256", manifest_matches),
        ("Python", python_matches),
        ("Z3", z3_matches),
        ("fiber CASE_SPEC", case_fiber),
        ("exact header", [(index, "") for index in headers]),
        ("COMMAND", command_lines),
    ):
        if len(matches) == 1:
            ordered.append((name, matches[0][0]))
    if len(ordered) == 8:
        positions = [position for _, position in ordered]
        if positions != sorted(positions):
            audit.issues.append(f"wrapper/driver banners out of order: {ordered}")
    if len(sha_matches) == 1 and len(manifest_matches) == 1:
        expected_positions = list(range(
            sha_matches[0][0] + 1,
            sha_matches[0][0] + 1 + len(expected_manifest),
        ))
        observed_positions = [index for index, _, _ in source_file_matches]
        if observed_positions != expected_positions:
            audit.issues.append(
                "SOURCE_FILE_SHA256 lines are not one contiguous sorted block "
                "immediately after SOURCE_SHA256"
            )
        if manifest_matches[0][0] != sha_matches[0][0] + 1 + len(expected_manifest):
            audit.issues.append(
                "SOURCE_MANIFEST_SHA256 is not immediately after source-file entries"
            )

    if crash_markers:
        audit.issues.append("process-error marker(s): " + ", ".join(crash_markers))

    terminal_complete = len(final_positions) == 1 and len(task_done_matches) == 1
    if not terminal_complete:
        # Absence of terminal markers is computational incompleteness, even if
        # the file is empty or stops before a later mandatory section.  It is a
        # structural error only when material already present contradicts the
        # independent task mapping/source contract, a crash is explicit, or
        # one of the two terminal claims appears without the other.
        hard_fragments = (
            "CASE_SPEC/mapping mismatch",
            "fiber CASE_SPEC mismatch",
            "driver SHA mismatch",
            "source manifest extra",
            "source manifest changed hash",
            "source-manifest aggregate mismatch",
            "does not match its individual entries",
            "does not agree with its source-manifest entry",
            "version mismatch",
            "COMMAND --",
            "COMMAND must name",
            "could not parse COMMAND",
            "unexpectedly contains",
            "direct/summary mismatch",
            "ROW CLASS mismatch",
            "task-done task mismatch",
            "TASK_DONE job mismatch",
            "LOCAL_TASK_DONE run mismatch",
            "out of order",
            "not one contiguous sorted block",
            "is not immediately after",
            "process-error marker",
        )
        hard_error = terminal_claimed or bool(crash_markers) or any(
            fragment in issue
            for issue in audit.issues
            for fragment in hard_fragments
        )
        audit.state = "error" if hard_error else "truncated"
        if not audit.issues:
            tail = "TASK_DONE" if origin == "slurm" else "LOCAL_TASK_DONE"
            audit.issues.append(f"missing complete driver/{tail} tail")
        return audit
    if audit.issues:
        audit.state = "error"
        return audit
    audit.state = "terminal"
    return audit


def combine_task(task: Task, audits: list[LogAudit]) -> EffectiveTask:
    if not audits:
        return EffectiveTask(task, "missing", None, None, None, None, None, [])
    valid = [audit for audit in audits if audit.valid_terminal]
    if not valid:
        state = "error" if any(audit.state == "error" for audit in audits) else "truncated"
        return EffectiveTask(task, state, None, None, None, None, None, audits)

    issues: list[str] = []
    conclusive = {audit.outcome for audit in valid if audit.outcome != "unknown"}
    if "H0-vacuous" in conclusive and len(conclusive) > 1:
        issues.append(f"contradictory terminal outcomes: {sorted(conclusive)}")
    if "SAT" in conclusive and "UNSAT" in conclusive:
        issues.append("contradictory terminal S2 outcomes: SAT and UNSAT")
    h0_conclusive = {audit.h0 for audit in valid if audit.h0 in ("sat", "unsat")}
    s1_conclusive = {audit.s1 for audit in valid if audit.s1 in ("sat", "unsat")}
    if len(h0_conclusive) > 1:
        issues.append(f"contradictory terminal H0 outcomes: {sorted(h0_conclusive)}")
    if len(s1_conclusive) > 1:
        issues.append(f"contradictory terminal S1 outcomes: {sorted(s1_conclusive)}")
    if issues:
        return EffectiveTask(task, "error", None, None, None, None, None, audits, issues)

    preferred = (
        "H0-vacuous" if "H0-vacuous" in conclusive else
        "SAT" if "SAT" in conclusive else
        "UNSAT" if "UNSAT" in conclusive else "unknown"
    )
    candidates = [audit for audit in valid if audit.outcome == preferred]
    selected = max(
        candidates,
        key=lambda audit: (audit.path.stat().st_mtime_ns, str(audit.path)),
    )
    if len(audits) > 1:
        issues.append(
            f"duplicate copies={len(audits)}; selected {selected.path}"
        )
    damaged = [audit for audit in audits if not audit.valid_terminal]
    if damaged:
        issues.append(
            "ignored damaged duplicate(s): "
            + ", ".join(str(audit.path) for audit in damaged)
        )
    inconclusive = [
        audit for audit in valid if audit.outcome == "unknown" and preferred != "unknown"
    ]
    if inconclusive:
        issues.append(
            "conclusive rerun supersedes unknown copy/copies: "
            + ", ".join(str(audit.path) for audit in inconclusive)
        )
    return EffectiveTask(
        task, "terminal", selected.outcome, selected.h0, selected.s1, selected.s2,
        selected.path, audits, issues,
    )


def combine_row(ring: str, row: Row, tasks: dict[int, EffectiveTask]) -> RowAudit:
    terminal = [task for task in tasks.values() if task.state == "terminal"]
    issues: list[str] = []
    h0_conclusive = {task.h0 for task in terminal if task.h0 in ("sat", "unsat")}
    s1_conclusive = {task.s1 for task in terminal if task.s1 in ("sat", "unsat")}
    if len(h0_conclusive) > 1:
        issues.append(f"contradictory H0 outcomes across coordinates: {h0_conclusive}")
    if len(s1_conclusive) > 1:
        issues.append(f"contradictory S1 outcomes across coordinates: {s1_conclusive}")
    if issues:
        return RowAudit(ring, row, "error", tasks, issues)
    if any(task.outcome == "H0-vacuous" for task in terminal):
        return RowAudit(ring, row, "H0-vacuous", tasks)
    if any(task.outcome == "SAT" for task in terminal):
        return RowAudit(ring, row, "SAT candidate", tasks)
    if all(tasks[i].outcome == "UNSAT" for i in (1, 2, 3)):
        return RowAudit(ring, row, "closed UNSAT", tasks)
    if any(task.state == "error" for task in tasks.values()):
        return RowAudit(ring, row, "error", tasks)
    if any(task.outcome == "unknown" for task in terminal):
        return RowAudit(ring, row, "unknown", tasks)
    return RowAudit(ring, row, "incomplete", tasks)


def task_cell(task: EffectiveTask) -> str:
    if task.state != "terminal":
        return task.state
    return task.outcome or "error"


def retry_reason(task: EffectiveTask) -> str:
    if task.state in ("missing", "truncated", "error"):
        return task.state
    if task.outcome == "unknown":
        return "solver-unknown"
    return "unresolved"


def compact_ranges(values: Iterable[int]) -> str:
    ordered = sorted(set(values))
    if not ordered:
        return "none"
    ranges: list[str] = []
    start = previous = ordered[0]
    for value in ordered[1:]:
        if value == previous + 1:
            previous = value
            continue
        ranges.append(str(start) if start == previous else f"{start}-{previous}")
        start = previous = value
    ranges.append(str(start) if start == previous else f"{start}-{previous}")
    return ",".join(ranges)


def audit_legacy(directory: Path) -> tuple[int, int, collections.Counter[str], list[str]]:
    """Parse only complete old driver logs; never return canonical evidence."""
    files = sorted(directory.rglob("sprime_principal_length6_*20260710.log"))
    terminal_files = 0
    rows: collections.Counter[str] = collections.Counter()
    details: list[str] = []
    summary_re = re.compile(
        r"^  (xy/[^:]+|t4/c1=[01],c4=[01]): class=(.+?); "
        r"H0=(sat|unsat|unknown); S1=(sat|unsat|unknown|not-run); S2=(.+)$"
    )
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        lines = text.splitlines()
        final = sum(line.strip() == FINAL_MARKER for line in lines)
        ring_headers = [
            line[6:-6] for line in lines
            if line.startswith("===== ") and line.endswith(" =====")
            and line[6:-6] in RINGS
        ]
        gates = [line for line in lines if "[symbolic-vs-concrete 64^2 gate]" in line]
        if final != 1 or len(ring_headers) != 1 or len(gates) != 1 or "-> PASS" not in gates[0]:
            continue
        ring = ring_headers[0]
        if sum(line.strip() == f"DONE {ring}" for line in lines) != 1:
            continue
        terminal_files += 1
        parsed = [match.groups() for line in lines if (match := summary_re.fullmatch(line))]
        for label, row_class, _, _, _ in parsed:
            rows[row_class] += 1
            details.append(f"{path}: {ring} {label} class={row_class}")
    return len(files), terminal_files, rows, details


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def build_source_manifest(
    project_root: Path, source_files: tuple[str, ...]
) -> tuple[tuple[tuple[str, str], ...], str]:
    if tuple(sorted(source_files)) != source_files:
        raise ValueError("internal source dependency list is not sorted")
    entries: list[tuple[str, str]] = []
    for source_rel in source_files:
        source_path = project_root / source_rel
        if not source_path.is_file():
            raise FileNotFoundError(f"source dependency does not exist: {source_path}")
        entries.append((source_rel, sha256_file(source_path)))
    payload = "".join(
        f"{source_rel}\t{source_sha}\n" for source_rel, source_sha in entries
    ).encode("utf-8")
    return tuple(entries), hashlib.sha256(payload).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--log-dir", action="append", type=Path,
        help="scan recursively for principal_JOB_TASK.log; repeat to combine stores",
    )
    parser.add_argument(
        "--local-log-dir", action="append", type=Path,
        help=(
            "scan recursively for principal_local_RUN_task_TASK.log; repeat to "
            "combine honest local-process evidence with Slurm evidence"
        ),
    )
    parser.add_argument(
        "--check-local-log", type=Path,
        help="validate exactly one local task log and exit 0 only if it is terminal",
    )
    parser.add_argument(
        "--expected-task", type=int,
        help="with --check-local-log, require this independently mapped task ID",
    )
    parser.add_argument(
        "--driver", type=Path,
        default=Path("scripts") / DRIVER_BASENAME,
        help="current driver used to derive the expected source SHA",
    )
    parser.add_argument(
        "--project-root", type=Path, default=Path("."),
        help="root against which the explicit source dependency manifest is resolved",
    )
    parser.add_argument(
        "--expected-driver-sha",
        help="override the SHA derived from --driver (64 lowercase hexadecimal digits)",
    )
    parser.add_argument(
        "--legacy-dir", action="append", type=Path,
        help="summarize old sprime_principal_length6 logs as noncanonical evidence",
    )
    parser.add_argument("--sbatch", default=SBATCH_DEFAULT)
    parser.add_argument("--array-percent", type=int, default=4)
    parser.add_argument("--show-all-rows", action="store_true")
    parser.add_argument("--show-retry-tasks", action="store_true")
    parser.add_argument("--no-commands", action="store_true")
    parser.add_argument(
        "--strict", action="store_true",
        help="exit nonzero unless every row is closed and canonical evidence is coherent",
    )
    args = parser.parse_args()
    if args.array_percent <= 0:
        parser.error("--array-percent must be positive")
    if (args.check_local_log is None) != (args.expected_task is None):
        parser.error("--check-local-log and --expected-task must be supplied together")
    if args.expected_task is not None and not 0 <= args.expected_task < 300:
        parser.error("--expected-task must be in 0..299")
    if args.expected_driver_sha:
        if not re.fullmatch(r"[0-9a-f]{64}", args.expected_driver_sha):
            parser.error("--expected-driver-sha must be 64 lowercase hexadecimal digits")
        expected_sha = args.expected_driver_sha
    else:
        if not args.driver.is_file():
            parser.error(f"driver does not exist: {args.driver}")
        expected_sha = sha256_file(args.driver)

    try:
        expected_manifest, expected_manifest_sha = build_source_manifest(
            args.project_root, PRINCIPAL_SOURCE_FILES,
        )
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    manifest_driver_sha = dict(expected_manifest)["scripts/" + DRIVER_BASENAME]
    if manifest_driver_sha != expected_sha:
        parser.error(
            "--driver/--expected-driver-sha disagrees with the explicit source manifest: "
            f"{expected_sha} versus {manifest_driver_sha}"
        )

    if args.check_local_log is not None:
        checked = audit_log(
            args.check_local_log.resolve(),
            expected_sha,
            expected_manifest,
            expected_manifest_sha,
            origin="local",
        )
        expected_task = Task.from_id(args.expected_task)
        if checked.task != expected_task:
            checked.issues.append(
                "requested task mismatch: "
                f"expected {expected_task.task_id}, "
                f"observed {checked.task.task_id if checked.task else 'unrecognized'}"
            )
            checked.state = "error"
        print(
            f"LOCAL LOG CHECK task={expected_task.task_id} state={checked.state} "
            f"path={checked.path}"
        )
        for issue in checked.issues:
            print(f"  issue: {issue}")
        return 0 if checked.valid_terminal else 1

    log_dirs = args.log_dir or ([] if args.local_log_dir else [Path("logs")])
    local_log_dirs = args.local_log_dir or []
    missing_dirs: list[tuple[str, Path]] = []
    candidates: list[tuple[Path, str]] = []
    for directory in log_dirs:
        if not directory.is_dir():
            missing_dirs.append(("slurm", directory))
            continue
        # Slurm's %A is numeric.  Restrict the candidate namespace accordingly
        # so unrelated launcher diagnostics such as principal_canary_*.log are
        # not misidentified as array evidence; malformed numeric task names
        # are still collected and rejected by FILENAME_RE.
        candidates.extend(
            (path, "slurm") for path in directory.rglob("principal_[0-9]*.log")
            if path.is_file()
        )
    for directory in local_log_dirs:
        if not directory.is_dir():
            missing_dirs.append(("local", directory))
            continue
        candidates.extend(
            (path, "local")
            for path in directory.rglob("principal_local_*_task_*.log")
            if path.is_file()
            and ".partial." not in path.name
            and ".rejected." not in path.name
        )
    unique_candidates = sorted({(path.resolve(), origin) for path, origin in candidates})
    audits = [
        audit_log(
            path, expected_sha, expected_manifest, expected_manifest_sha,
            origin=origin,
        )
        for path, origin in unique_candidates
    ]

    by_task: dict[Task, list[LogAudit]] = collections.defaultdict(list)
    orphans: list[LogAudit] = []
    for audit in audits:
        if audit.task is None:
            orphans.append(audit)
        else:
            by_task[audit.task].append(audit)

    effective = {
        task: combine_task(task, by_task.get(task, [])) for task in TASKS
    }
    rows: list[RowAudit] = []
    for ring in RINGS:
        for row in ROWS:
            tasks = {
                coordinate: effective[TASK_BY_ROW_COORD[(ring, row.index, coordinate)]]
                for coordinate in (1, 2, 3)
            }
            rows.append(combine_row(ring, row, tasks))

    print("PRINCIPAL COORDINATE EVIDENCE AUDIT")
    print("slurm_log_dirs=" + (",".join(str(path) for path in log_dirs) or "none"))
    print(
        "local_log_dirs="
        + (",".join(str(path) for path in local_log_dirs) or "none")
    )
    print(f"expected_driver_sha256={expected_sha}")
    print(
        f"expected_source_manifest files={len(expected_manifest)} "
        f"sha256={expected_manifest_sha}"
    )
    print("mapping=T//30:ring, (T//3)%10:row, T%3+1:i")
    print("universe rings=10 rows_per_ring=10 rows=100 coordinate_tasks=300")
    print(
        f"files matched={len(unique_candidates)} recognized={len(audits)-len(orphans)} "
        f"malformed_or_out_of_scope={len(orphans)} "
        f"duplicate_task_copies={sum(max(0, len(group)-1) for group in by_task.values())}"
    )
    if missing_dirs:
        print(
            "missing_log_dirs="
            + ",".join(f"{origin}:{path}" for origin, path in missing_dirs)
        )

    print("PER-RING ROW COUNTS")
    for ring in RINGS:
        counts = collections.Counter(row.status for row in rows if row.ring == ring)
        print(
            f"  {ring}: "
            + ", ".join(f"{status}={counts[status]}" for status in ROW_STATUSES)
        )
    global_counts = collections.Counter(row.status for row in rows)
    print(
        "GLOBAL ROW COUNTS "
        + ", ".join(f"{status}={global_counts[status]}" for status in ROW_STATUSES)
    )
    state_counts = collections.Counter(task.state for task in effective.values())
    outcome_counts = collections.Counter(
        task.outcome for task in effective.values() if task.state == "terminal"
    )
    print(
        "TASK COUNTS "
        + ", ".join(
            f"{state}={state_counts[state]}"
            for state in ("terminal", "missing", "truncated", "error")
        )
        + "; terminal_outcomes="
        + ",".join(
            f"{outcome}={outcome_counts[outcome]}"
            for outcome in ("H0-vacuous", "UNSAT", "SAT", "unknown")
        )
    )

    selected_paths = {task.source for task in effective.values() if task.source}
    selected_audits = [
        audit for audit in audits
        if audit.path in selected_paths and audit.valid_terminal
    ]
    resources = [
        audit.resource for audit in selected_audits if audit.resource
    ]
    jobs = sorted({
        audit.filename_job for audit in selected_audits
        if audit.origin == "slurm" and audit.filename_job
    })
    local_runs = sorted({
        audit.local_run for audit in selected_audits
        if audit.origin == "local" and audit.local_run
    })
    origin_counts = collections.Counter(audit.origin for audit in selected_audits)
    if resources:
        platforms = collections.Counter(resource.platform for resource in resources)
        print(
            f"PROCESS RESOURCES logs={len(resources)} "
            f"elapsed_sum_seconds={sum(resource.elapsed_seconds for resource in resources):.2f} "
            f"maxrss_max_mib={max(resource.maxrss_mib for resource in resources):.2f} "
            + "platforms="
            + ",".join(f"{key}:{value}" for key, value in sorted(platforms.items()))
        )
    else:
        print("PROCESS RESOURCES logs=0")
    print(
        "SELECTED EVIDENCE ORIGINS "
        f"slurm={origin_counts['slurm']} local={origin_counts['local']}"
    )
    print("SLURM ARRAY JOB IDS " + (",".join(jobs) if jobs else "none"))
    print("LOCAL RUN IDS " + (",".join(local_runs) if local_runs else "none"))

    displayed = [
        row for row in rows
        if args.show_all_rows or row.status not in ("closed UNSAT", "H0-vacuous")
    ]
    print(f"ROW DETAILS displayed={len(displayed)}")
    for row in displayed:
        cells = ",".join(
            f"i{coordinate}:{task_cell(row.tasks[coordinate])}"
            for coordinate in (1, 2, 3)
        )
        print(f"  {row.ring} {row.row.label}: {row.status}; {cells}")
        for issue in row.issues:
            print(f"    issue: {issue}")

    issue_lines: list[str] = []
    for audit in orphans:
        issue_lines.extend(f"{audit.path}: {issue}" for issue in audit.issues)
    for task in TASKS:
        combined = effective[task]
        for issue in combined.issues:
            issue_lines.append(f"task={task.task_id}: {issue}")
        for audit in combined.audits:
            if not audit.valid_terminal:
                issue_lines.extend(f"{audit.path}: {issue}" for issue in audit.issues)
    print(f"AUDIT ISSUES count={len(issue_lines)}")
    for issue in issue_lines:
        print(f"  {issue}")

    retry: list[tuple[Task, str]] = []
    for row in rows:
        if row.status in ("closed UNSAT", "H0-vacuous", "SAT candidate"):
            continue
        for coordinate in (1, 2, 3):
            task = row.tasks[coordinate]
            if task.outcome != "UNSAT":
                retry.append((task.task, retry_reason(task)))
    by_reason: dict[str, list[int]] = collections.defaultdict(list)
    for task, reason in retry:
        by_reason[reason].append(task.task_id)
    all_retry_ids = [task.task_id for task, _ in retry]
    ranges = compact_ranges(all_retry_ids)
    print(
        "SLURM TASKS NEEDED AFTER COMBINING ORIGINS "
        f"count={len(all_retry_ids)} ranges={ranges}"
    )
    print(f"RETRY ARRAY TASK IDS count={len(all_retry_ids)} ranges={ranges}")
    for reason in sorted(by_reason):
        print(
            f"  reason={reason} count={len(by_reason[reason])} "
            f"ranges={compact_ranges(by_reason[reason])}"
        )
    if args.show_retry_tasks:
        for task, reason in retry:
            print(
                f"  task={task.task_id} reason={reason} ring={task.ring} "
                f"row={task.row.index}:{task.row.label} i={task.coordinate}"
            )
    if not args.no_commands and all_retry_ids:
        print("RETRY COMMANDS")
        print(
            "  "
            + shlex.join([
                "sbatch", f"--array={ranges}%{args.array_percent}", args.sbatch,
            ])
        )
        for reason in sorted(by_reason):
            reason_ranges = compact_ranges(by_reason[reason])
            print(
                f"  # {reason}\n  "
                + shlex.join([
                    "sbatch", f"--array={reason_ranges}%{args.array_percent}", args.sbatch,
                ])
            )

    for directory in args.legacy_dir or []:
        if not directory.is_dir():
            print(f"LEGACY SUPPLEMENTAL directory={directory} missing (never canonical)")
            continue
        files, terminal, legacy_rows, details = audit_legacy(directory)
        print(
            f"LEGACY SUPPLEMENTAL directory={directory} files={files} "
            f"terminal_files={terminal} rows={sum(legacy_rows.values())} "
            "(never used for canonical closure)"
        )
        if legacy_rows:
            print(
                "  classes="
                + ",".join(f"{key}:{legacy_rows[key]}" for key in sorted(legacy_rows))
            )
        for detail in details:
            print("  " + detail)

    all_closed = all(
        row.status in ("closed UNSAT", "H0-vacuous") for row in rows
    )
    coherent = not orphans and not missing_dirs and not any(
        row.status == "error" for row in rows
    )
    if args.strict and (not all_closed or not coherent):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
