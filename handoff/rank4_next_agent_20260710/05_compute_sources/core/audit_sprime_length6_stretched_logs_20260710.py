#!/usr/bin/env python3
"""Audit and aggregate the split H=(1,2,1,1,1) S' sweep logs.

This program intentionally has no project or third-party dependencies.  It
does not import Z3 and never launches a solver.  Its universe is hard-coded
to the eleven stretched type-two coordinates and the ten fibre rows used by
``sprime_length6_stretched_h12111_eleven_stratified_20260710.py``.

One normal solver invocation covers one FAIL_i coordinate.  A row is closed
as follows:

* one fully audited H0=unsat log closes the row as H0-vacuous;
* one fully audited S2.i=sat log is reported as a SAT candidate;
* three fully audited S2.i=unsat logs, for i=1,2,3, close it UNSAT;
* unknown, truncated, malformed, and absent logs never count negatively.

Use repeated ``--log-dir`` options to combine, for example, banked workspace
logs with an active staging directory.  Duplicate task logs are audited
independently; a valid conclusive rerun supersedes an unknown or damaged
copy, while contradictory conclusive copies are an error.
"""

from __future__ import annotations

import argparse
import collections
import dataclasses
import math
from pathlib import Path
import re
import shlex
import sys
from typing import Iterable


DATE_TAG = "20260710"
SOLVER_BASENAME = "sprime_length6_stretched_h12111_eleven_stratified_20260710.py"
FINAL_MARKER = "DONE sprime_length6_stretched_h12111_eleven_stratified_20260710"

RINGS = (
    "s_f2", "s_z32", "s_e2_00", "s_e2_10", "s_e2_11", "s_e3",
    "s_e4", "q00", "q01", "q10", "q11",
)
XY_MODELS = (
    "a2a2", "W2F", "mu2a2", "mu2mu2",
    "mu2mu2_unipotent", "mu2mu2_irreducible",
)
T4_FORMS = ("00", "01", "10", "11")

ROW_STATUSES = (
    "closed UNSAT",
    "H0-vacuous",
    "SAT candidate",
    "unknown",
    "incomplete",
    "error",
)

RING_ALTERNATION = "|".join(
    re.escape(ring) for ring in sorted(RINGS, key=len, reverse=True)
)
FILENAME_RE = re.compile(
    rf"^sprime_length6_stretched_({RING_ALTERNATION})_(xy|t4)_(.+)_i([123])"
    rf"(?:_([A-Za-z0-9][A-Za-z0-9_.-]*))?_{DATE_TAG}\.log$"
)
RING_HEADER_RE = re.compile(
    rf"^===== STRETCHED H12111 COORDINATE ({RING_ALTERNATION}): .+ =====$"
)
H0_RE = re.compile(
    r"^\s*\[H0 axioms\+fiber2 sanity\] -> (sat|unsat|unknown)\b"
)
S1_RE = re.compile(
    r"^\s*\[S1 axioms\+fiber2\+S'-HOLDS\] -> (sat|unsat|unknown)\b"
)
S2_RE = re.compile(
    r"^\s*\[S2\.([123]) axioms\+fiber2\+S'-FAIL_i\] -> "
    r"(sat|unsat|unknown)\b"
)
UNROLL_RE = re.compile(
    r"^\s*\[exact unroll cache\] 512 combined representatives; "
    r"distinct coefficient shifts=([0-9][0-9,]*)\s*$"
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
    "Command terminated by signal",
    "z3.z3types.Z3Exception",
)


@dataclasses.dataclass(frozen=True, order=True)
class Row:
    fiber: str
    model: str

    @property
    def tag(self) -> str:
        return f"{self.fiber}_{self.model}"

    @property
    def label(self) -> str:
        if self.fiber == "xy":
            return f"xy/{self.model}"
        return f"t4/c1={self.model[0]},c4={self.model[1]}"

    @property
    def option(self) -> str:
        return "--xy-models" if self.fiber == "xy" else "--t4-forms"


ROWS = tuple(Row("xy", model) for model in XY_MODELS) + tuple(
    Row("t4", form) for form in T4_FORMS
)
ROW_LOOKUP = {(row.fiber, row.model): row for row in ROWS}


@dataclasses.dataclass(frozen=True, order=True)
class Task:
    ring: str
    row: Row
    coordinate: int

    @property
    def canonical_log_name(self) -> str:
        return (
            f"sprime_length6_stretched_{self.ring}_{self.row.tag}_"
            f"i{self.coordinate}_{DATE_TAG}.log"
        )


@dataclasses.dataclass(frozen=True)
class Resource:
    elapsed_seconds: float
    maxrss_mib: float
    platform: str


@dataclasses.dataclass
class LogAudit:
    path: Path
    task: Task | None
    state: str
    outcome: str | None = None
    h0: str | None = None
    s2: str | None = None
    resource: Resource | None = None
    issues: list[str] = dataclasses.field(default_factory=list)
    variant: str | None = None

    @property
    def valid_terminal(self) -> bool:
        return self.state == "terminal"


@dataclasses.dataclass
class EffectiveTask:
    task: Task
    state: str
    outcome: str | None
    h0: str | None
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
    """Return all values following one option up to the next long option."""
    positions = [index for index, token in enumerate(tokens) if token == option]
    if len(positions) != 1:
        return None
    start = positions[0] + 1
    end = start
    while end < len(tokens) and not tokens[end].startswith("--"):
        end += 1
    return tokens[start:end]


def exactly(lines: Iterable[str], predicate) -> list[str]:
    return [line for line in lines if predicate(line)]


def parse_filename(path: Path) -> tuple[Task | None, str | None, str | None]:
    """Return (task, variant, error); only called on task-like filenames."""
    match = FILENAME_RE.fullmatch(path.name)
    if not match:
        return None, None, "malformed stretched-H12111 task-log filename"
    ring, fiber, model, coordinate_text, variant = match.groups()
    if ring not in RINGS:
        return None, variant, f"ring tag {ring!r} is not one of the 11 targets"
    row = ROW_LOOKUP.get((fiber, model))
    if row is None:
        return None, variant, f"fibre/model tag {fiber}/{model} is not one of the ten rows"
    return Task(ring, row, int(coordinate_text)), variant, None


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
        if not value.isdigit() or key in counts:
            return {}, f"malformed COUNTS item {part!r}"
        counts[key] = int(value)
    return counts, None


def audit_log(path: Path) -> LogAudit:
    task, variant, filename_error = parse_filename(path)
    audit = LogAudit(path=path, task=task, state="error", variant=variant)
    if filename_error:
        audit.issues.append(filename_error)
        return audit
    assert task is not None

    try:
        text = path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        audit.issues.append(f"could not read log: {exc}")
        return audit
    lines = text.splitlines()

    crash_markers = [marker for marker in ERROR_MARKERS if marker in text]
    final_positions = [i for i, line in enumerate(lines) if line.strip() == FINAL_MARKER]
    if len(final_positions) == 0:
        audit.state = "error" if crash_markers else "truncated"
        if crash_markers:
            audit.issues.append("process-error marker(s): " + ", ".join(crash_markers))
        audit.issues.append("missing final DONE marker")
        return audit
    if len(final_positions) != 1:
        audit.issues.append(f"expected one final DONE marker, found {len(final_positions)}")

    # A final marker claims normal completion, so all internal structure is
    # mandatory and any crash marker is an audit error rather than truncation.
    if crash_markers:
        audit.issues.append("process-error marker(s): " + ", ".join(crash_markers))

    command_lines = [line[len("COMMAND "):] for line in lines if line.startswith("COMMAND ")]
    if len(command_lines) != 1:
        audit.issues.append(f"expected one COMMAND line, found {len(command_lines)}")
    else:
        try:
            tokens = shlex.split(command_lines[0])
        except ValueError as exc:
            audit.issues.append(f"could not parse COMMAND: {exc}")
            tokens = []
        solver_tokens = [token for token in tokens if Path(token).name == SOLVER_BASENAME]
        if len(solver_tokens) != 1:
            audit.issues.append(
                f"COMMAND must name {SOLVER_BASENAME} exactly once; found {len(solver_tokens)}"
            )
        expected_options = {
            "--rings": [task.ring],
            "--fibers": [task.row.fiber],
            task.row.option: [task.row.model],
            "--only-i": [str(task.coordinate)],
        }
        for option, expected in expected_options.items():
            observed = one_option(tokens, option)
            if observed != expected:
                audit.issues.append(
                    f"COMMAND {option} tag mismatch: expected {expected}, observed {observed}"
                )

    ring_headers = [match.group(1) for line in lines if (match := RING_HEADER_RE.fullmatch(line))]
    if ring_headers != [task.ring]:
        audit.issues.append(
            f"ring header mismatch: expected [{task.ring!r}], observed {ring_headers}"
        )
    ring_gate = exactly(
        lines,
        lambda line: "[ring/presentation/locality/Hilbert/type gate]" in line,
    )
    if len(ring_gate) != 1 or f"] {task.ring}:" not in (ring_gate[0] if ring_gate else "") \
            or "-> PASS" not in (ring_gate[0] if ring_gate else ""):
        audit.issues.append("missing, repeated, failed, or mistagged ring gate")
    syzygy_gate = exactly(
        lines,
        lambda line: "[exact full-syzygy/coset gate]" in line,
    )
    if len(syzygy_gate) != 1 or "-> PASS" not in (syzygy_gate[0] if syzygy_gate else ""):
        audit.issues.append("missing, repeated, or failed exact syzygy/coset gate")
    split_isomorphism_gate = exactly(
        lines,
        lambda line: "[split-coordinate isomorphism gate]" in line,
    )
    if len(split_isomorphism_gate) != 1 \
            or "-> PASS" not in (split_isomorphism_gate[0] if split_isomorphism_gate else ""):
        audit.issues.append(
            "missing, repeated, or failed split-coordinate isomorphism gate"
        )

    row_headers = [
        line.strip()[4:-4]
        for line in lines
        if line.strip().startswith("--- ") and line.strip().endswith(" ---")
    ]
    if row_headers != [task.row.label]:
        audit.issues.append(
            f"row header mismatch: expected [{task.row.label!r}], observed {row_headers}"
        )

    done_ring_positions = [i for i, line in enumerate(lines) if line.strip() == f"DONE {task.ring}"]
    terminal_summary_positions = [
        i for i, line in enumerate(lines)
        if line.strip() == "===== STRETCHED H12111 TERMINAL SUMMARY ====="
    ]
    count_positions = [i for i, line in enumerate(lines) if line.startswith("COUNTS ")]
    resource_matches = [
        (i, match) for i, line in enumerate(lines)
        if (match := RESOURCE_RE.fullmatch(line))
    ]
    marker_groups = (
        ("DONE ring", done_ring_positions),
        ("terminal summary", terminal_summary_positions),
        ("COUNTS", count_positions),
        ("PROCESS_RESOURCE", [i for i, _ in resource_matches]),
        ("final DONE", final_positions),
    )
    for name, positions in marker_groups:
        if len(positions) != 1:
            audit.issues.append(f"expected one {name} marker, found {len(positions)}")
    if all(len(positions) == 1 for _, positions in marker_groups):
        order = [positions[0] for _, positions in marker_groups]
        if order != sorted(order):
            audit.issues.append(f"terminal markers are out of order: line indexes {order}")

    if len(resource_matches) == 1:
        match = resource_matches[0][1]
        elapsed, maxrss = float(match.group(1)), float(match.group(2))
        if not all(math.isfinite(value) and value >= 0 for value in (elapsed, maxrss)):
            audit.issues.append("PROCESS_RESOURCE contains invalid numeric values")
        else:
            audit.resource = Resource(elapsed, maxrss, match.group(3))
    elif any(line.startswith("PROCESS_RESOURCE") for line in lines):
        audit.issues.append("malformed PROCESS_RESOURCE line")

    h0_matches = [match.group(1) for line in lines if (match := H0_RE.match(line))]
    s1_matches = [match.group(1) for line in lines if (match := S1_RE.match(line))]
    s2_matches = [
        (int(match.group(1)), match.group(2))
        for line in lines if (match := S2_RE.match(line))
    ]
    if len(h0_matches) != 1:
        audit.issues.append(f"expected one H0 result, found {len(h0_matches)}")

    summary_re = re.compile(
        rf"^\s{{2}}{re.escape(task.row.label)}: class=(.+?); "
        rf"H0=(sat|unsat|unknown); S1=(sat|unsat|unknown|not-run); S2=(.+)$"
    )
    summaries = [match.groups() for line in lines if (match := summary_re.fullmatch(line))]
    if len(summaries) != 1:
        audit.issues.append(f"expected one correctly tagged row summary, found {len(summaries)}")
        summary_class = summary_h0 = summary_s1 = None
        summary_s2: dict[int, str] = {}
    else:
        summary_class, summary_h0, summary_s1, summary_s2_text = summaries[0]
        summary_s2, summary_error = parse_s2_summary(summary_s2_text)
        if summary_error:
            audit.issues.append(summary_error)

    if len(h0_matches) == 1 and summary_h0 is not None and h0_matches[0] != summary_h0:
        audit.issues.append(
            f"H0 direct/summary mismatch: {h0_matches[0]} versus {summary_h0}"
        )
    if summary_s1 is not None:
        expected_s1_direct = [] if summary_s1 == "not-run" else [summary_s1]
        if s1_matches != expected_s1_direct:
            audit.issues.append(
                f"S1 direct/summary mismatch: {s1_matches} versus {summary_s1}"
            )
    if dict(s2_matches) != summary_s2 or len(dict(s2_matches)) != len(s2_matches):
        audit.issues.append(
            f"S2 direct/summary mismatch: {s2_matches} versus {summary_s2}"
        )

    audit.h0 = summary_h0
    if summary_h0 == "unsat":
        expected = ("H0-vacuous", "not-run", {}, [])
        vacuous_markers = [line for line in lines if "[H0-VACUOUS:" in line]
        if (summary_class, summary_s1, summary_s2, s2_matches) != expected:
            audit.issues.append("H0=unsat row does not have canonical H0-vacuous summary")
        if len(vacuous_markers) != 1:
            audit.issues.append(
                f"expected one H0-VACUOUS marker, found {len(vacuous_markers)}"
            )
        expected_row_classes: list[str] = []
        audit.outcome = "H0-vacuous"
    elif summary_h0 == "unknown":
        if summary_class != "unknown" or summary_s1 != "not-run" or summary_s2:
            audit.issues.append("H0=unknown row does not have canonical unknown summary")
        expected_row_classes = []
        audit.outcome = "unknown"
    elif summary_h0 == "sat":
        if summary_s1 != "sat":
            audit.issues.append(
                f"H0=sat split query requires the S1=sat witness gate; observed {summary_s1}"
            )
        if set(summary_s2) != {task.coordinate}:
            audit.issues.append(
                f"summary does not contain exactly S2.{task.coordinate}: {summary_s2}"
            )
        audit.s2 = summary_s2.get(task.coordinate)
        if audit.s2 == "sat":
            expected_class = "SAT S'-failure"
            audit.outcome = "SAT"
        elif audit.s2 == "unsat":
            expected_class = "partial-UNSAT"
            audit.outcome = "UNSAT"
        elif audit.s2 == "unknown":
            expected_class = "unknown"
            audit.outcome = "unknown"
        else:
            expected_class = None
            audit.issues.append("H0=sat row has no recognized S2 result")
        if expected_class is not None and summary_class != expected_class:
            audit.issues.append(
                f"row class mismatch: expected {expected_class!r}, observed {summary_class!r}"
            )
        expected_row_classes = [expected_class] if expected_class else []
    else:
        expected_row_classes = []

    row_classes = [match.group(1) for line in lines if (match := ROW_CLASS_RE.fullmatch(line))]
    if row_classes != expected_row_classes:
        audit.issues.append(
            f"ROW CLASS marker mismatch: expected {expected_row_classes}, observed {row_classes}"
        )

    unroll_matches = [
        match.group(1) for line in lines if (match := UNROLL_RE.fullmatch(line))
    ]
    expected_unroll_count = 1 if summary_h0 == "sat" and summary_s2 else 0
    if len(unroll_matches) != expected_unroll_count:
        audit.issues.append(
            "exact-unroll cache marker mismatch: expected "
            f"{expected_unroll_count}, observed {len(unroll_matches)}"
        )

    if len(count_positions) == 1 and summary_class is not None:
        counts, count_error = parse_counts(lines[count_positions[0]])
        if count_error:
            audit.issues.append(count_error)
        else:
            expected_keys = {
                "H0-vacuous", "SAT S'-failure", "UNSAT", "partial-UNSAT", "unknown"
            }
            if set(counts) != expected_keys:
                audit.issues.append(
                    f"COUNTS keys mismatch: expected {sorted(expected_keys)}, "
                    f"observed {sorted(counts)}"
                )
            elif counts.get(summary_class) != 1 or sum(counts.values()) != 1:
                audit.issues.append(
                    f"COUNTS do not encode the one row class {summary_class!r}: {counts}"
                )

    if audit.issues:
        audit.state = "error"
        return audit
    audit.state = "terminal"
    return audit


def combine_task(task: Task, audits: list[LogAudit]) -> EffectiveTask:
    if not audits:
        return EffectiveTask(task, "missing", None, None, None, None, [])

    valid = [audit for audit in audits if audit.valid_terminal]
    issues: list[str] = []
    if not valid:
        state = "error" if any(a.state == "error" for a in audits) else "truncated"
        return EffectiveTask(task, state, None, None, None, None, audits, issues)

    conclusive = {audit.outcome for audit in valid if audit.outcome != "unknown"}
    if "H0-vacuous" in conclusive and len(conclusive) > 1:
        issues.append(f"contradictory terminal outcomes: {sorted(conclusive)}")
        return EffectiveTask(task, "error", None, None, None, None, audits, issues)
    if "SAT" in conclusive and "UNSAT" in conclusive:
        issues.append("contradictory terminal S2 outcomes: SAT and UNSAT")
        return EffectiveTask(task, "error", None, None, None, None, audits, issues)

    preferred_outcome = (
        "H0-vacuous" if "H0-vacuous" in conclusive else
        "SAT" if "SAT" in conclusive else
        "UNSAT" if "UNSAT" in conclusive else
        "unknown"
    )
    candidates = [audit for audit in valid if audit.outcome == preferred_outcome]
    selected = max(candidates, key=lambda audit: audit.path.stat().st_mtime_ns)
    invalid = [audit for audit in audits if not audit.valid_terminal]
    if invalid:
        issues.append(
            "ignored damaged duplicate(s) because a valid copy exists: "
            + ", ".join(str(a.path) for a in invalid)
        )
    return EffectiveTask(
        task, "terminal", selected.outcome, selected.h0, selected.s2,
        selected.path, audits, issues,
    )


def combine_row(ring: str, row: Row, tasks: dict[int, EffectiveTask]) -> RowAudit:
    issues: list[str] = []
    terminal = [task for task in tasks.values() if task.state == "terminal"]
    h0_vacuous = [task for task in terminal if task.outcome == "H0-vacuous"]
    nonvacuous = [task for task in terminal if task.h0 == "sat"]
    if h0_vacuous and nonvacuous:
        issues.append(
            "contradictory H0 results across coordinates: H0-vacuous and H0=sat"
        )
        return RowAudit(ring, row, "error", tasks, issues)
    if h0_vacuous:
        return RowAudit(ring, row, "H0-vacuous", tasks, issues)
    if any(task.outcome == "SAT" for task in terminal):
        return RowAudit(ring, row, "SAT candidate", tasks, issues)
    if all(tasks[i].outcome == "UNSAT" for i in (1, 2, 3)):
        return RowAudit(ring, row, "closed UNSAT", tasks, issues)
    if any(task.state == "error" for task in tasks.values()):
        return RowAudit(ring, row, "error", tasks, issues)
    if any(task.outcome == "unknown" for task in terminal):
        return RowAudit(ring, row, "unknown", tasks, issues)
    return RowAudit(ring, row, "incomplete", tasks, issues)


def missing_reason(task: EffectiveTask) -> str:
    if task.state == "missing":
        return "missing"
    if task.state == "truncated":
        return "truncated"
    if task.state == "error":
        return "error"
    if task.outcome == "unknown":
        return "solver-unknown"
    return "unresolved"


def task_command(task: Task, args: argparse.Namespace) -> str:
    words = [
        args.python,
        "-u",
        args.solver,
        "--rings", task.ring,
        "--fibers", task.row.fiber,
        task.row.option, task.row.model,
        "--only-i", str(task.coordinate),
        "--timeout", str(args.timeout),
        "--memory-mb", str(args.memory_mb),
    ]
    return shlex.join(words)


def task_cell(task: EffectiveTask) -> str:
    if task.state == "missing":
        return "missing"
    if task.state == "truncated":
        return "truncated"
    if task.state == "error":
        return "error"
    return task.outcome or "error"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--log-dir",
        action="append",
        type=Path,
        help="directory to scan recursively; repeat to combine stores (default: scripts)",
    )
    parser.add_argument(
        "--solver",
        default=f"scripts/{SOLVER_BASENAME}",
        help="solver path printed in missing/retry commands",
    )
    parser.add_argument("--python", default="python3", help="Python executable in commands")
    parser.add_argument("--timeout", type=int, default=3600, help="timeout in printed commands")
    parser.add_argument(
        "--memory-mb", type=int, default=6144, help="Z3 ceiling in printed commands"
    )
    parser.add_argument("--show-all-rows", action="store_true")
    parser.add_argument("--no-commands", action="store_true")
    parser.add_argument(
        "--strict",
        action="store_true",
        help="exit nonzero unless all rows are closed UNSAT or H0-vacuous",
    )
    args = parser.parse_args()
    if args.timeout <= 0 or args.memory_mb < 0:
        parser.error("--timeout must be positive and --memory-mb nonnegative")

    log_dirs = args.log_dir or [Path("scripts")]
    candidates: list[Path] = []
    missing_dirs: list[Path] = []
    pattern = f"sprime_length6_stretched_*_i*_{DATE_TAG}.log"
    for directory in log_dirs:
        if not directory.is_dir():
            missing_dirs.append(directory)
            continue
        candidates.extend(path for path in directory.rglob(pattern) if path.is_file())
    # Resolve repeated directory aliases without collapsing genuinely distinct
    # copies from workspace and staging areas.
    unique_candidates = sorted(dict.fromkeys(path.resolve() for path in candidates))
    audits = [audit_log(path) for path in unique_candidates]

    by_task: dict[Task, list[LogAudit]] = collections.defaultdict(list)
    orphan_audits: list[LogAudit] = []
    for audit in audits:
        if audit.task is None:
            orphan_audits.append(audit)
        else:
            by_task[audit.task].append(audit)

    effective: dict[Task, EffectiveTask] = {}
    row_audits: list[RowAudit] = []
    for ring in RINGS:
        for row in ROWS:
            coordinate_tasks: dict[int, EffectiveTask] = {}
            for coordinate in (1, 2, 3):
                task = Task(ring, row, coordinate)
                combined = combine_task(task, by_task.get(task, []))
                effective[task] = combined
                coordinate_tasks[coordinate] = combined
            row_audits.append(combine_row(ring, row, coordinate_tasks))

    print("STRETCHED H12111 SPLIT-LOG AUDIT")
    print("log_dirs=" + ",".join(str(directory) for directory in log_dirs))
    print(
        f"universe rings={len(RINGS)} rows_per_ring={len(ROWS)} "
        f"rows={len(RINGS) * len(ROWS)} coordinate_tasks={len(RINGS) * len(ROWS) * 3}"
    )
    print(
        f"files matched={len(unique_candidates)} recognized={len(audits)-len(orphan_audits)} "
        f"malformed_or_out_of_scope={len(orphan_audits)} "
        f"duplicate_task_copies={sum(max(0, len(items)-1) for items in by_task.values())}"
    )
    if missing_dirs:
        print("missing_log_dirs=" + ",".join(str(directory) for directory in missing_dirs))

    print("PER-RING ROW COUNTS")
    for ring in RINGS:
        counts = collections.Counter(
            audit.status for audit in row_audits if audit.ring == ring
        )
        print(
            f"  {ring}: " + ", ".join(f"{status}={counts[status]}" for status in ROW_STATUSES)
        )
    global_counts = collections.Counter(audit.status for audit in row_audits)
    print(
        "GLOBAL ROW COUNTS "
        + ", ".join(f"{status}={global_counts[status]}" for status in ROW_STATUSES)
    )

    task_state_counts = collections.Counter(task.state for task in effective.values())
    outcome_counts = collections.Counter(
        task.outcome for task in effective.values() if task.state == "terminal"
    )
    print(
        "TASK COUNTS "
        + ", ".join(
            f"{state}={task_state_counts[state]}"
            for state in ("terminal", "missing", "truncated", "error")
        )
        + "; terminal_outcomes="
        + ",".join(
            f"{outcome}={outcome_counts[outcome]}"
            for outcome in ("H0-vacuous", "UNSAT", "SAT", "unknown")
        )
    )

    selected_paths = {
        task.source for task in effective.values() if task.source is not None
    }
    resources = [
        audit.resource for audit in audits
        if audit.path in selected_paths and audit.valid_terminal and audit.resource
    ]
    if resources:
        platforms = collections.Counter(resource.platform for resource in resources)
        print(
            f"PROCESS RESOURCES logs={len(resources)} "
            f"elapsed_sum_seconds={sum(r.elapsed_seconds for r in resources):.2f} "
            f"maxrss_max_mib={max(r.maxrss_mib for r in resources):.2f} "
            f"platforms=" + ",".join(f"{key}:{value}" for key, value in sorted(platforms.items()))
        )
    else:
        print("PROCESS RESOURCES logs=0")

    displayed_rows = [
        audit for audit in row_audits
        if args.show_all_rows or audit.status not in ("closed UNSAT", "H0-vacuous")
    ]
    print(f"ROW DETAILS displayed={len(displayed_rows)}")
    for audit in displayed_rows:
        coordinates = ",".join(
            f"i{i}:{task_cell(audit.tasks[i])}" for i in (1, 2, 3)
        )
        print(f"  {audit.ring} {audit.row.label}: {audit.status}; {coordinates}")
        for issue in audit.issues:
            print(f"    issue: {issue}")

    issue_lines: list[str] = []
    for audit in orphan_audits:
        issue_lines.extend(f"{audit.path}: {issue}" for issue in audit.issues)
    for task, combined in sorted(effective.items()):
        for issue in combined.issues:
            issue_lines.append(
                f"{task.ring}/{task.row.tag}/i{task.coordinate}: {issue}"
            )
        for audit in combined.audits:
            if not audit.valid_terminal:
                issue_lines.extend(f"{audit.path}: {issue}" for issue in audit.issues)
    print(f"AUDIT ISSUES count={len(issue_lines)}")
    for line in issue_lines:
        print(f"  {line}")

    retry_tasks: list[tuple[Task, str]] = []
    for row_audit in row_audits:
        if row_audit.status in ("closed UNSAT", "H0-vacuous", "SAT candidate"):
            continue
        for coordinate in (1, 2, 3):
            task = row_audit.tasks[coordinate]
            if task.outcome != "UNSAT":
                retry_tasks.append((task.task, missing_reason(task)))
    print(f"MISSING/RETRY TASK COMMANDS count={len(retry_tasks)}")
    if not args.no_commands:
        for task, reason in retry_tasks:
            print(f"  # reason={reason} output={task.canonical_log_name}")
            print("  " + task_command(task, args))

    all_closed = all(
        audit.status in ("closed UNSAT", "H0-vacuous") for audit in row_audits
    )
    clean = not orphan_audits and not missing_dirs and not any(
        audit.status == "error" for audit in row_audits
    )
    if args.strict and (not all_closed or not clean):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
