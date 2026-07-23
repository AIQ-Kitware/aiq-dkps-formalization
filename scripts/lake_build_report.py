#!/usr/bin/env python3
"""Run ``lake build`` quietly and render compact, deduplicated diagnostics.

The default output contains errors only. Lake progress, successful jobs,
warnings, informational diagnostics, traces, and repeated Lake failure summaries
are suppressed unless requested.

Examples
--------
Build one Lean module::

    scripts/lake_build_report.py \
        DavisKahan.Experimental.Scratch.SharedFoundations.Ideal.TwoWayFactorization

Build several targets::

    scripts/lake_build_report.py Target.One Target.Two

Include warnings, or show the unfiltered log::

    scripts/lake_build_report.py --warnings Target.One
    scripts/lake_build_report.py --raw Target.One

Pass a global option to Lake before ``build``::

    scripts/lake_build_report.py --lake-arg=-R Target.One

This script intentionally uses only the Python standard library. The build's
exit status is preserved, so it is safe to use in shell pipelines and agent
workflows.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import signal
import subprocess
import sys
import tempfile
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Sequence

SEVERITIES = ("error", "warning", "info", "trace")
SEVERITY_RANK = {"trace": 0, "info": 1, "warning": 2, "error": 3}

ANSI_RE = re.compile(
    r"(?:\x1B\][^\x07]*(?:\x07|\x1B\\))"  # OSC
    r"|(?:\x1B\[[0-?]*[ -/]*[@-~])"       # CSI
)

# Lake commonly forwards Lean messages as:
#   error: Path/File.lean:12:34: message
PREFIX_DIAG_RE = re.compile(
    r"^(?P<severity>error|warning|info|trace):\s*(?P<rest>.*)$"
)

# Direct Lean output may instead use:
#   Path/File.lean:12:34: error: message
SUFFIX_DIAG_RE = re.compile(
    r"^(?P<file>.+):(?P<line>\d+):(?P<column>\d+):\s*"
    r"(?P<severity>error|warning|info|trace):\s*(?P<message>.*)$"
)

LOCATION_RE = re.compile(
    r"^(?P<file>.+):(?P<line>\d+):(?P<column>\d+):\s*(?P<message>.*)$"
)

PROGRESS_RE = re.compile(
    r"^\s*(?:[✓✔✖✗]\s+)?\[\d+/\d+\](?:\s+|$)"
)

SYNTHETIC_ERROR_RE = re.compile(
    r"^error:\s*(?:Lean exited with code -?\d+|build failed)\s*$"
)

SUMMARY_HEADER_RE = re.compile(
    r"^(?:Some required targets logged failures:|Required targets failed:)$"
)

COLORS = {
    "red": "\x1b[31m",
    "yellow": "\x1b[33m",
    "blue": "\x1b[34m",
    "cyan": "\x1b[36m",
    "green": "\x1b[32m",
    "dim": "\x1b[2m",
    "reset": "\x1b[0m",
}

SEVERITY_COLOR = {
    "error": "red",
    "warning": "yellow",
    "info": "blue",
    "trace": "dim",
}


@dataclass
class Diagnostic:
    severity: str
    message: str
    file: str | None = None
    line: int | None = None
    column: int | None = None
    body: list[str] = field(default_factory=list)
    ordinal: int = 0
    repeats: int = 1

    def normalized_key(self) -> tuple[object, ...]:
        body = tuple(line.rstrip() for line in self.body)
        return (
            self.severity,
            self.file,
            self.line,
            self.column,
            self.message.rstrip(),
            body,
        )

    def location(self) -> str:
        if self.file is None:
            return "(no location)"
        if self.line is None:
            return self.file
        if self.column is None:
            return f"{self.file}:{self.line}"
        return f"{self.file}:{self.line}:{self.column}"

    def to_json(self) -> dict[str, object]:
        return {
            "severity": self.severity,
            "message": self.message,
            "file": self.file,
            "line": self.line,
            "column": self.column,
            "body": self.body,
            "ordinal": self.ordinal,
            "repeats": self.repeats,
        }


@dataclass
class ParseResult:
    diagnostics: list[Diagnostic]
    raw_counts: Counter[str]
    synthetic_lines: list[str]
    other_lines: list[str]


@dataclass
class Cluster:
    file: str | None
    diagnostics: list[Diagnostic]
    min_line: int | None
    max_line: int | None


def strip_control(text: str) -> str:
    """Remove terminal control sequences and carriage returns."""
    return ANSI_RE.sub("", text.replace("\r", ""))


def find_lake_root(start: Path) -> Path | None:
    """Find the nearest ancestor containing a Lake package file."""
    start = start.expanduser().resolve()
    if start.is_file():
        start = start.parent
    for path in (start, *start.parents):
        if (path / "lakefile.toml").is_file() or (path / "lakefile.lean").is_file():
            return path
    return None


def parse_diagnostic_header(line: str) -> Diagnostic | None:
    """Parse either Lake-forwarded or direct-Lean diagnostic syntax."""
    suffix = SUFFIX_DIAG_RE.match(line)
    if suffix:
        return Diagnostic(
            severity=suffix.group("severity"),
            file=suffix.group("file"),
            line=int(suffix.group("line")),
            column=int(suffix.group("column")),
            message=suffix.group("message").strip(),
        )

    prefix = PREFIX_DIAG_RE.match(line)
    if not prefix:
        return None

    severity = prefix.group("severity")
    rest = prefix.group("rest")
    location = LOCATION_RE.match(rest)
    if location:
        return Diagnostic(
            severity=severity,
            file=location.group("file"),
            line=int(location.group("line")),
            column=int(location.group("column")),
            message=location.group("message").strip(),
        )
    return Diagnostic(severity=severity, message=rest.strip())


def parse_output(lines: Iterable[str]) -> ParseResult:
    """Parse diagnostics while separating Lake progress and failure summaries."""
    diagnostics: list[Diagnostic] = []
    synthetic_lines: list[str] = []
    other_lines: list[str] = []
    raw_counts: Counter[str] = Counter()
    current: Diagnostic | None = None
    in_target_summary = False

    def flush() -> None:
        nonlocal current
        if current is not None:
            current.body = trim_blank_edges(current.body)
            current.ordinal = len(diagnostics) + 1
            diagnostics.append(current)
            raw_counts[current.severity] += 1
            current = None

    for raw_line in lines:
        line = strip_control(raw_line.rstrip("\n"))

        if SUMMARY_HEADER_RE.match(line):
            flush()
            synthetic_lines.append(line)
            in_target_summary = True
            continue
        if in_target_summary and re.match(r"^\s*-\s+", line):
            synthetic_lines.append(line)
            continue
        in_target_summary = False

        if SYNTHETIC_ERROR_RE.match(line) or PROGRESS_RE.match(line):
            flush()
            synthetic_lines.append(line)
            continue

        new_diag = parse_diagnostic_header(line)
        if new_diag is not None:
            flush()
            current = new_diag
            continue

        if current is not None:
            current.body.append(line)
        else:
            other_lines.append(line)

    flush()
    return ParseResult(diagnostics, raw_counts, synthetic_lines, other_lines)


def trim_blank_edges(lines: Sequence[str]) -> list[str]:
    start = 0
    end = len(lines)
    while start < end and not lines[start].strip():
        start += 1
    while end > start and not lines[end - 1].strip():
        end -= 1
    return list(lines[start:end])


def deduplicate(diagnostics: Sequence[Diagnostic]) -> list[Diagnostic]:
    """Collapse exact repeated diagnostics while preserving first occurrence."""
    unique: list[Diagnostic] = []
    by_key: dict[tuple[object, ...], Diagnostic] = {}
    for diagnostic in diagnostics:
        key = diagnostic.normalized_key()
        previous = by_key.get(key)
        if previous is None:
            copy = Diagnostic(
                severity=diagnostic.severity,
                message=diagnostic.message,
                file=diagnostic.file,
                line=diagnostic.line,
                column=diagnostic.column,
                body=list(diagnostic.body),
                ordinal=diagnostic.ordinal,
            )
            by_key[key] = copy
            unique.append(copy)
        else:
            previous.repeats += 1
    return unique


def cluster_diagnostics(
    diagnostics: Sequence[Diagnostic], cluster_gap: int
) -> list[Cluster]:
    """Group diagnostics whose source-context windows would overlap."""
    located: dict[str, list[Diagnostic]] = {}
    orphans: list[Diagnostic] = []
    file_order: list[str] = []

    for diagnostic in diagnostics:
        if diagnostic.file is None or diagnostic.line is None:
            orphans.append(diagnostic)
            continue
        if diagnostic.file not in located:
            located[diagnostic.file] = []
            file_order.append(diagnostic.file)
        located[diagnostic.file].append(diagnostic)

    clusters: list[Cluster] = []
    for file_name in file_order:
        file_diagnostics = sorted(
            located[file_name],
            key=lambda item: (
                item.line or 0,
                item.column or 0,
                -SEVERITY_RANK[item.severity],
                item.ordinal,
            ),
        )
        current: list[Diagnostic] = []
        min_line: int | None = None
        max_line: int | None = None
        for diagnostic in file_diagnostics:
            assert diagnostic.line is not None
            if not current or max_line is None or diagnostic.line <= max_line + cluster_gap:
                current.append(diagnostic)
                min_line = diagnostic.line if min_line is None else min(min_line, diagnostic.line)
                max_line = diagnostic.line if max_line is None else max(max_line, diagnostic.line)
            else:
                clusters.append(Cluster(file_name, current, min_line, max_line))
                current = [diagnostic]
                min_line = diagnostic.line
                max_line = diagnostic.line
        if current:
            clusters.append(Cluster(file_name, current, min_line, max_line))

    if orphans:
        clusters.append(Cluster(None, orphans, None, None))
    return clusters


def resolve_source_path(root: Path, file_name: str) -> Path | None:
    path = Path(file_name)
    candidates = [path] if path.is_absolute() else [root / path, Path.cwd() / path]
    for candidate in candidates:
        try:
            resolved = candidate.resolve()
        except OSError:
            continue
        if resolved.is_file():
            return resolved
    return None


def use_color(mode: str) -> bool:
    if mode == "always":
        return True
    if mode == "never":
        return False
    return sys.stdout.isatty() and os.environ.get("TERM") != "dumb"


def colorize(text: str, color: str | None, enabled: bool) -> str:
    if not enabled or color is None:
        return text
    return COLORS[color] + text + COLORS["reset"]


def tag(diagnostic: Diagnostic, index: int) -> str:
    letter = {"error": "E", "warning": "W", "info": "I", "trace": "T"}[
        diagnostic.severity
    ]
    return f"{letter}{index}"


def display_column(source: str, one_based_column: int, tabsize: int) -> int:
    """Convert Lean's one-based source column to a best-effort terminal column."""
    logical_prefix = source[: max(0, one_based_column - 1)]
    return len(logical_prefix.expandtabs(tabsize))


def render_source_context(
    root: Path,
    cluster: Cluster,
    context: int,
    tabsize: int,
    color_enabled: bool,
    indices: dict[int, int],
) -> list[str]:
    if cluster.file is None or cluster.min_line is None or cluster.max_line is None:
        return []
    source_path = resolve_source_path(root, cluster.file)
    if source_path is None:
        return ["  (source file unavailable)"]

    try:
        source_lines = source_path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError as ex:
        return [f"  (could not read source file: {ex})"]

    start = max(1, cluster.min_line - context)
    end = min(len(source_lines), cluster.max_line + context)
    width = len(str(max(1, end)))
    by_line: dict[int, list[Diagnostic]] = {}
    for diagnostic in cluster.diagnostics:
        if diagnostic.line is not None:
            by_line.setdefault(diagnostic.line, []).append(diagnostic)

    rendered: list[str] = []
    for line_number in range(start, end + 1):
        raw_source = source_lines[line_number - 1]
        shown_source = raw_source.expandtabs(tabsize)
        line_diagnostics = by_line.get(line_number, [])
        marker = ">" if line_diagnostics else " "
        if line_diagnostics:
            highest = max(line_diagnostics, key=lambda item: SEVERITY_RANK[item.severity])
            marker = colorize(marker, SEVERITY_COLOR[highest.severity], color_enabled)
        prefix = f"{marker}{line_number:>{width}} | "
        rendered.append(prefix + shown_source)

        for diagnostic in sorted(
            line_diagnostics,
            key=lambda item: (item.column or 0, -SEVERITY_RANK[item.severity]),
        ):
            column = display_column(raw_source, diagnostic.column or 1, tabsize)
            diagnostic_tag = tag(diagnostic, indices[id(diagnostic)])
            caret = colorize("^", SEVERITY_COLOR[diagnostic.severity], color_enabled)
            label = colorize(
                diagnostic_tag, SEVERITY_COLOR[diagnostic.severity], color_enabled
            )
            rendered.append(" " * (len(strip_control(prefix)) + column) + f"{caret} {label}")
    return rendered


def significant_tail(lines: Sequence[str], limit: int) -> list[str]:
    """Return a useful raw tail for failures the parser did not understand."""
    kept: list[str] = []
    for raw_line in lines:
        line = strip_control(raw_line.rstrip("\n"))
        if not line.strip() or PROGRESS_RE.match(line):
            continue
        kept.append(line)
    return kept[-limit:]


def run_build(command: Sequence[str], root: Path) -> tuple[int, list[str]]:
    """Run Lake without keeping an unbounded pipe buffer in memory."""
    with tempfile.TemporaryFile(mode="w+b") as stream:
        try:
            process = subprocess.Popen(
                list(command),
                cwd=root,
                stdout=stream,
                stderr=subprocess.STDOUT,
                stdin=None,
            )
        except FileNotFoundError as ex:
            raise RuntimeError(f"cannot execute {command[0]!r}: {ex}") from ex

        interrupted = False
        try:
            return_code = process.wait()
        except KeyboardInterrupt:
            interrupted = True
            if process.poll() is None:
                process.send_signal(signal.SIGINT)
            try:
                return_code = process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.terminate()
                return_code = process.wait()

        stream.seek(0)
        text = stream.read().decode("utf-8", errors="replace")
        lines = text.splitlines()
        if interrupted and return_code == 0:
            return_code = 130
        elif return_code < 0:
            return_code = 128 + abs(return_code)
        return return_code, lines


def render_text_report(
    *,
    root: Path,
    command: Sequence[str],
    return_code: int,
    parse_result: ParseResult,
    shown: Sequence[Diagnostic],
    context: int,
    cluster_gap: int,
    max_diag_lines: int,
    tabsize: int,
    color_enabled: bool,
    raw_lines: Sequence[str],
    show_raw: bool,
    fallback_tail_lines: int,
) -> None:
    duplicate_count = sum(item.repeats - 1 for item in shown)

    status_text = "SUCCEEDED" if return_code == 0 else "FAILED"
    status_color = "green" if return_code == 0 else "red"
    print(colorize(f"Lean build {status_text}", status_color, color_enabled))
    print(f"root: {root}")
    print(f"command: {shlex.join(command)}")
    print(f"exit: {return_code}")
    print(
        "diagnostics: "
        + ", ".join(
            f"{severity}={parse_result.raw_counts.get(severity, 0)}"
            for severity in SEVERITIES
        )
    )
    suppressed_count = len(parse_result.synthetic_lines)
    if duplicate_count or suppressed_count:
        print(
            f"noise removed: exact_duplicates={duplicate_count}, "
            f"lake_wrapper_lines={suppressed_count}"
        )
    print()

    if shown:
        indices = {id(diagnostic): index for index, diagnostic in enumerate(shown, 1)}
        clusters = cluster_diagnostics(shown, cluster_gap)
        for cluster_index, cluster in enumerate(clusters, 1):
            if cluster.file is None:
                heading = f"[{cluster_index}] diagnostics without source locations"
            else:
                line_range = (
                    str(cluster.min_line)
                    if cluster.min_line == cluster.max_line
                    else f"{cluster.min_line}-{cluster.max_line}"
                )
                heading = f"[{cluster_index}] {cluster.file}:{line_range}"
            print(colorize(heading, "cyan", color_enabled))

            context_lines = render_source_context(
                root,
                cluster,
                context,
                tabsize,
                color_enabled,
                indices,
            )
            if context_lines:
                print("\n".join(context_lines))
                print()

            for diagnostic in cluster.diagnostics:
                index = indices[id(diagnostic)]
                diagnostic_tag = colorize(
                    tag(diagnostic, index),
                    SEVERITY_COLOR[diagnostic.severity],
                    color_enabled,
                )
                repeat_suffix = (
                    f" (repeated {diagnostic.repeats} times)"
                    if diagnostic.repeats > 1
                    else ""
                )
                severity = colorize(
                    diagnostic.severity,
                    SEVERITY_COLOR[diagnostic.severity],
                    color_enabled,
                )
                print(
                    f"{diagnostic_tag} {severity} {diagnostic.location()}"
                    f"{repeat_suffix}"
                )
                print(diagnostic.message or "(no message)")
                body = diagnostic.body[:max_diag_lines]
                if body:
                    print("\n".join(body))
                omitted = len(diagnostic.body) - len(body)
                if omitted:
                    print(f"... {omitted} diagnostic lines omitted")
                print()
    elif return_code == 0:
        if any(parse_result.raw_counts.values()):
            hidden = ", ".join(
                f"{severity}={parse_result.raw_counts.get(severity, 0)}"
                for severity in SEVERITIES
                if parse_result.raw_counts.get(severity, 0)
            )
            print(f"No selected diagnostics. Hidden diagnostics: {hidden}.")
        else:
            print("No diagnostics.")
    else:
        print("No selected Lean diagnostic was parsed from the failed build.")
        print("Raw failure tail:")
        for line in significant_tail(raw_lines, fallback_tail_lines):
            print(line)

    if show_raw:
        print()
        print(colorize("Raw build output", "cyan", color_enabled))
        print("\n".join(strip_control(line) for line in raw_lines))


def render_json_report(
    *,
    root: Path,
    command: Sequence[str],
    return_code: int,
    parse_result: ParseResult,
    shown: Sequence[Diagnostic],
) -> None:
    payload = {
        "root": str(root),
        "command": list(command),
        "exit_code": return_code,
        "raw_counts": dict(parse_result.raw_counts),
        "synthetic_line_count": len(parse_result.synthetic_lines),
        "diagnostics": [diagnostic.to_json() for diagnostic in shown],
    }
    json.dump(payload, sys.stdout, indent=2, sort_keys=True)
    print()


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Quiet, compact, deduplicated reporter for `lake build`."
    )
    parser.add_argument("targets", nargs="+", help="Lake build target(s)")
    parser.add_argument(
        "--root",
        type=Path,
        help="Lake package root; defaults to the nearest ancestor of cwd",
    )
    parser.add_argument(
        "--lake",
        default="lake",
        help="Lake executable (default: lake)",
    )
    parser.add_argument(
        "--lake-arg",
        action="append",
        default=[],
        metavar="ARG",
        help="Global Lake argument placed before `build`; may be repeated",
    )
    parser.add_argument(
        "--no-quiet",
        action="store_true",
        help="Do not pass Lake's -q flag",
    )
    parser.add_argument("--warnings", action="store_true", help="Include warnings")
    parser.add_argument("--info", action="store_true", help="Include info diagnostics")
    parser.add_argument("--trace", action="store_true", help="Include trace diagnostics")
    parser.add_argument(
        "--all-diagnostics",
        action="store_true",
        help="Include errors, warnings, info, and trace diagnostics",
    )
    parser.add_argument(
        "--no-dedup",
        action="store_true",
        help="Do not collapse exact repeated diagnostics",
    )
    parser.add_argument(
        "--context",
        type=int,
        default=3,
        help="Source lines around a diagnostic cluster (default: 3)",
    )
    parser.add_argument(
        "--cluster-gap",
        type=int,
        help="Maximum line gap within a cluster; default: 2*context+1",
    )
    parser.add_argument(
        "--max-diag-lines",
        type=int,
        default=160,
        help="Maximum continuation lines per diagnostic (default: 160)",
    )
    parser.add_argument(
        "--tabsize",
        type=int,
        default=2,
        help="Tab width for source context (default: 2)",
    )
    parser.add_argument(
        "--color",
        choices=("auto", "always", "never"),
        default="auto",
        help="Color mode (default: auto)",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="Report format (default: text)",
    )
    parser.add_argument(
        "--raw",
        action="store_true",
        help="Append the complete unfiltered build output",
    )
    parser.add_argument(
        "--save-raw",
        type=Path,
        help="Write complete unfiltered build output to this path",
    )
    parser.add_argument(
        "--fallback-tail-lines",
        type=int,
        default=80,
        help="Raw lines shown when a failed build has no parsed error (default: 80)",
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)

    if args.context < 0 or args.max_diag_lines < 0 or args.tabsize <= 0:
        parser.error("context/max-diag-lines must be nonnegative and tabsize positive")

    root = args.root.expanduser().resolve() if args.root else find_lake_root(Path.cwd())
    if root is None:
        parser.error("could not find lakefile.toml or lakefile.lean above cwd; use --root")
    if not ((root / "lakefile.toml").is_file() or (root / "lakefile.lean").is_file()):
        parser.error(f"not a Lake package root: {root}")

    lake_global_args = list(args.lake_arg)
    if not args.no_quiet and "-q" not in lake_global_args and "--quiet" not in lake_global_args:
        lake_global_args.append("-q")
    command = [args.lake, *lake_global_args, "build", *args.targets]

    try:
        return_code, raw_lines = run_build(command, root)
    except RuntimeError as ex:
        print(f"lake_build_report.py: {ex}", file=sys.stderr)
        return 127

    if args.save_raw:
        raw_path = args.save_raw.expanduser()
        if not raw_path.is_absolute():
            raw_path = root / raw_path
        raw_path.parent.mkdir(parents=True, exist_ok=True)
        raw_path.write_text("\n".join(raw_lines) + "\n", encoding="utf-8")

    parse_result = parse_output(raw_lines)
    diagnostics = (
        list(parse_result.diagnostics)
        if args.no_dedup
        else deduplicate(parse_result.diagnostics)
    )

    selected = {"error"}
    if args.all_diagnostics:
        selected.update(SEVERITIES)
    else:
        if args.warnings:
            selected.add("warning")
        if args.info:
            selected.add("info")
        if args.trace:
            selected.add("trace")
    shown = [diagnostic for diagnostic in diagnostics if diagnostic.severity in selected]

    cluster_gap = args.cluster_gap
    if cluster_gap is None:
        cluster_gap = 2 * args.context + 1
    if cluster_gap < 0:
        parser.error("cluster-gap must be nonnegative")

    if args.format == "json":
        render_json_report(
            root=root,
            command=command,
            return_code=return_code,
            parse_result=parse_result,
            shown=shown,
        )
    else:
        render_text_report(
            root=root,
            command=command,
            return_code=return_code,
            parse_result=parse_result,
            shown=shown,
            context=args.context,
            cluster_gap=cluster_gap,
            max_diag_lines=args.max_diag_lines,
            tabsize=args.tabsize,
            color_enabled=use_color(args.color),
            raw_lines=raw_lines,
            show_raw=args.raw,
            fallback_tail_lines=args.fallback_tail_lines,
        )

    return return_code


if __name__ == "__main__":
    raise SystemExit(main())
