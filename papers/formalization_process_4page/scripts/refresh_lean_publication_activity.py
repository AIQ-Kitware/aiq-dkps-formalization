#!/usr/bin/env python3
"""Capture and audit the data candidate for the Lean-paper growth figure.

The original tracked series came from the Papers With Lean statistics chart.
Before extending it back to January 2024, this script established that grouping
``site_papers.json`` by its ``published`` field reproduced the frozen
January 2025--July 2026 chart interval.  That interval remains the validation
anchor after the tracked CSV is extended.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import shlex
import sys
import traceback
import urllib.request
from collections import Counter
from datetime import date, datetime, timezone
from pathlib import Path

from check_lean_publication_activity import load_snapshot, parse_live_series

PAPER_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CORPUS_URL = (
    "https://raw.githubusercontent.com/soonhokong/paperswithlean/main/site_papers.json"
)
DEFAULT_STATS_URL = "https://paperswithlean.com/stat/"
DEFAULT_SNAPSHOT = PAPER_ROOT / "data" / "lean_publication_activity.csv"
DEFAULT_AUDIT_ROOT = PAPER_ROOT / "generated" / "lean_publication_survey"
DEFAULT_CUTOFF = date(2026, 9, 6)
VALIDATION_START_MONTH = "2025-01"
VALIDATION_END_MONTH = "2026-07"
USER_AGENT = "aiq-dkps-formalization-lean-publication-survey/1"


def parse_date(text: str) -> date:
    try:
        return date.fromisoformat(text)
    except ValueError as ex:
        raise argparse.ArgumentTypeError(str(ex)) from ex


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    survey = commands.add_parser("survey")
    survey.add_argument("--corpus-url", default=DEFAULT_CORPUS_URL)
    survey.add_argument("--stats-url", default=DEFAULT_STATS_URL)
    survey.add_argument("--corpus-file", type=Path)
    survey.add_argument("--stats-file", type=Path)
    survey.add_argument("--snapshot", type=Path, default=DEFAULT_SNAPSHOT)
    survey.add_argument("--audit-root", type=Path, default=DEFAULT_AUDIT_ROOT)
    survey.add_argument("--cutoff", type=parse_date, default=DEFAULT_CUTOFF)
    survey.add_argument("--start-month", default="2024-01")
    survey.add_argument("--require-alignment", action="store_true")
    survey.add_argument("--write-tracked", action="store_true")
    commands.add_parser("self-test")
    return parser.parse_args()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git_blob_sha1(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def capture(url: str, local: Path | None) -> tuple[bytes, dict[str, object]]:
    if local is not None:
        path = local.expanduser().resolve()
        data = path.read_bytes()
        return data, {
            "locator": str(path),
            "mode": "local-file",
            "bytes": len(data),
            "sha256": sha256(data),
            "git_blob_sha1": git_blob_sha1(data),
        }

    request = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
    with urllib.request.urlopen(request, timeout=45) as response:
        data = response.read()
        headers = {
            key.lower(): response.headers[key]
            for key in ("Date", "ETag", "Last-Modified", "Content-Type")
            if response.headers.get(key) is not None
        }
    return data, {
        "locator": url,
        "mode": "network",
        "bytes": len(data),
        "sha256": sha256(data),
        "git_blob_sha1": git_blob_sha1(data),
        "response_headers": headers,
    }


def new_run_dir(root: Path, now: datetime) -> Path:
    root.mkdir(parents=True, exist_ok=True)
    stem = now.strftime("%Y%m%dT%H%M%SZ")
    path = root / stem
    suffix = 1
    while path.exists():
        path = root / f"{stem}-{suffix:02d}"
        suffix += 1
    path.mkdir()
    return path


def month_of(day: date) -> str:
    return day.strftime("%Y-%m")


def month_range(start: str, end: str) -> list[str]:
    match = re.fullmatch(r"(\d{4})-(\d{2})", start)
    if match is None or not 1 <= int(match.group(2)) <= 12:
        raise ValueError(f"invalid start month: {start!r}")
    year, month = int(match.group(1)), int(match.group(2))
    result = []
    while f"{year:04d}-{month:02d}" <= end:
        result.append(f"{year:04d}-{month:02d}")
        if month == 12:
            year, month = year + 1, 1
        else:
            month += 1
    return result


def parse_published(value: object) -> date | None:
    if not isinstance(value, str):
        return None
    match = re.match(r"^(\d{4}-\d{2}-\d{2})", value)
    if match is None:
        return None
    try:
        return date.fromisoformat(match.group(1))
    except ValueError:
        return None


def analyze_corpus(data: bytes, cutoff: date) -> tuple[dict[str, int], dict[str, object]]:
    payload = json.loads(data.decode("utf-8"))
    papers = payload.get("papers")
    if not isinstance(papers, list):
        raise ValueError("site_papers.json has no top-level papers list")

    counts: Counter[str] = Counter()
    missing = invalid = after_cutoff = before_2025 = 0
    days: list[date] = []
    keys: set[str] = set()
    for index, paper in enumerate(papers):
        if not isinstance(paper, dict):
            raise ValueError(f"paper record {index} is not an object")
        keys.update(map(str, paper.keys()))
        raw = paper.get("published")
        if raw in (None, ""):
            missing += 1
            continue
        published = parse_published(raw)
        if published is None:
            invalid += 1
            continue
        days.append(published)
        if published < date(2025, 1, 1):
            before_2025 += 1
        if published > cutoff:
            after_cutoff += 1
            continue
        counts[month_of(published)] += 1

    info = {
        "generated": payload.get("generated"),
        "records": len(papers),
        "parseable_published": len(days),
        "missing_published": missing,
        "invalid_published": invalid,
        "published_after_cutoff": after_cutoff,
        "published_before_2025": before_2025,
        "earliest_published": min(days).isoformat() if days else None,
        "latest_published": max(days).isoformat() if days else None,
        "record_keys": sorted(keys),
    }
    return dict(counts), info


def compare(expected: list[tuple[str, int]], actual: dict[str, int]) -> list[dict[str, object]]:
    return [
        {"month": month, "expected": count, "actual": actual.get(month)}
        for month, count in expected
        if actual.get(month) != count
    ]


def validation_overlap(rows: list[tuple[str, int]]) -> list[tuple[str, int]]:
    selected = [
        (month, count)
        for month, count in rows
        if VALIDATION_START_MONTH <= month <= VALIDATION_END_MONTH
    ]
    expected_months = month_range(VALIDATION_START_MONTH, VALIDATION_END_MONTH)
    if [month for month, _ in selected] != expected_months:
        raise ValueError(
            "tracked snapshot must contain the complete "
            f"{VALIDATION_START_MONTH}--{VALIDATION_END_MONTH} validation interval"
        )
    return selected


def write_series(path: Path, field: str, rows: list[tuple[str, int]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as file:
        writer = csv.writer(file, lineterminator="\n")
        writer.writerow(["month", field])
        writer.writerows(rows)


def write_comparison(
    path: Path,
    frozen: list[tuple[str, int]],
    live: dict[str, int],
    published: dict[str, int],
) -> None:
    with path.open("w", newline="", encoding="utf-8") as file:
        writer = csv.writer(file)
        writer.writerow(["month", "frozen_chart", "live_chart", "corpus_published"])
        for month, frozen_count in frozen:
            writer.writerow([month, frozen_count, live.get(month, ""), published.get(month, "")])


def mismatch_table(mismatches: list[dict[str, object]]) -> str:
    if not mismatches:
        return "None."
    lines = ["| Month | Expected | Actual |", "|---|---:|---:|"]
    for row in mismatches:
        actual = "missing" if row["actual"] is None else str(row["actual"])
        lines.append(f"| {row['month']} | {row['expected']} | {actual} |")
    return "\n".join(lines)


def write_tracked(
    path: Path,
    counts: dict[str, int],
    start_month: str,
    end_month: str,
) -> None:
    rows = [(month, counts.get(month, 0)) for month in month_range(start_month, end_month)]
    temp = path.with_suffix(path.suffix + ".tmp")
    write_series(temp, "papers_indexed", rows)
    temp.replace(path)


def run_survey(args: argparse.Namespace) -> int:
    now = datetime.now(timezone.utc)
    run_dir = new_run_dir(args.audit_root.expanduser().resolve(), now)
    print(f"audit directory: {run_dir}")
    try:
        corpus_data, corpus_source = capture(args.corpus_url, args.corpus_file)
        stats_data, stats_source = capture(args.stats_url, args.stats_file)
        snapshot_path = args.snapshot.expanduser().resolve()
        snapshot_data = snapshot_path.read_bytes()
        snapshot_source = {
            "locator": str(snapshot_path),
            "mode": "tracked-file",
            "bytes": len(snapshot_data),
            "sha256": sha256(snapshot_data),
            "git_blob_sha1": git_blob_sha1(snapshot_data),
        }

        (run_dir / "site_papers.json").write_bytes(corpus_data)
        (run_dir / "paperswithlean-stat.html").write_bytes(stats_data)
        (run_dir / "tracked_snapshot.csv").write_bytes(snapshot_data)

        frozen = load_snapshot(snapshot_path)
        validation = validation_overlap(frozen)
        live_rows, live_meta = parse_live_series(stats_data.decode("utf-8"))
        live = dict(live_rows)
        if len(live) != len(live_rows):
            raise ValueError("live chart contains duplicate months")
        published, corpus_info = analyze_corpus(corpus_data, args.cutoff)

        chart_mismatches = compare(validation, live)
        published_mismatches = compare(validation, published)
        validated = not chart_mismatches and not published_mismatches
        end_month = month_of(args.cutoff)
        candidate_rows = [
            (month, published.get(month, 0))
            for month in month_range(args.start_month, end_month)
        ]

        write_series(run_dir / "live_chart_series.csv", "papers_indexed", live_rows)
        write_series(
            run_dir / "corpus_published_series.csv", "papers_published", candidate_rows
        )
        write_comparison(run_dir / "overlap_comparison.csv", validation, live, published)

        wrote = False
        if args.write_tracked:
            if validated:
                write_tracked(snapshot_path, published, args.start_month, end_month)
                wrote = True
            else:
                print(
                    "refusing --write-tracked: corpus published grouping did not validate",
                    file=sys.stderr,
                )

        newer = [
            (month, count)
            for month, count in live_rows
            if month > VALIDATION_END_MONTH
        ]
        manifest = {
            "schema_version": 1,
            "run_utc": now.isoformat(),
            "command": [sys.executable, *sys.argv],
            "cutoff": args.cutoff.isoformat(),
            "candidate_definition": (
                "current site_papers.json membership grouped by record published month, "
                "with published date <= cutoff"
            ),
            "sources": {
                "corpus": corpus_source,
                "statistics_page": stats_source,
                "tracked_snapshot": snapshot_source,
            },
            "corpus": corpus_info,
            "chart": {
                "meta": live_meta,
                "months": len(live_rows),
                "sum_bars": sum(count for _, count in live_rows),
                "newer_than_snapshot": newer,
            },
            "validation": {
                "start_month": VALIDATION_START_MONTH,
                "end_month": VALIDATION_END_MONTH,
                "live_chart_matches_frozen": not chart_mismatches,
                "corpus_published_matches_frozen": not published_mismatches,
                "candidate_metric_validated": validated,
                "live_chart_mismatches": chart_mismatches,
                "corpus_published_mismatches": published_mismatches,
                "tracked_csv_written": wrote,
            },
        }
        (run_dir / "survey_manifest.json").write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

        report = f"""# Lean publication activity survey

- Run UTC: `{now.isoformat()}`
- Paper cutoff: `{args.cutoff.isoformat()}`
- Corpus SHA-256: `{corpus_source['sha256']}`
- Corpus Git-blob SHA-1: `{corpus_source['git_blob_sha1']}`
- Statistics-page SHA-256: `{stats_source['sha256']}`
- Tracked-snapshot SHA-256: `{snapshot_source['sha256']}`
- Corpus generated field: `{corpus_info['generated']}`
- Corpus records: {corpus_info['records']}
- Records published before 2025: {corpus_info['published_before_2025']}
- Parsed chart months: {len(live_rows)}
- Chart bar total: {sum(count for _, count in live_rows)}
- Chart metadata: `{live_meta}`

The candidate definition is: current `site_papers.json` membership, grouped by
its `published` calendar month, excluding records whose `published` date is
after {args.cutoff.isoformat()}. The raw corpus, raw statistics HTML, and exact
tracked snapshot are retained in this directory before comparison.

## Validation

- Live chart vs tracked {VALIDATION_START_MONTH}--{VALIDATION_END_MONTH} validation overlap: **{'PASS' if not chart_mismatches else 'FAIL'}**
- Corpus `published` grouping vs the same overlap: **{'PASS' if not published_mismatches else 'FAIL'}**
- Candidate definition safe for tracked update: **{'PASS' if validated else 'FAIL'}**

### Live chart mismatches

{mismatch_table(chart_mismatches)}

### Corpus `published` mismatches

{mismatch_table(published_mismatches)}

## Decision

{'Tracked CSV updated after both checks passed.' if wrote else 'Tracked CSV unchanged.'}
{'The candidate metric is validated, but no write was requested.' if validated and not wrote else ''}
{'The candidate metric did not reproduce the frozen chart overlap; do not splice its 2024 values into the tracked series.' if not validated else ''}

The complete candidate Jan 2024 through cutoff-month series is in
`corpus_published_series.csv`. `survey_manifest.json` contains the machine-readable
source locators, hashes, corpus schema summary, and mismatch records.
"""
        report_path = run_dir / "survey_report.md"
        report_path.write_text(report, encoding="utf-8")
        print(f"report: {report_path}")
        print(f"live chart vs frozen overlap: {'PASS' if not chart_mismatches else 'FAIL'}")
        print(
            "corpus published vs frozen overlap: "
            + ("PASS" if not published_mismatches else "FAIL")
        )

        if args.write_tracked and not wrote:
            return 2
        if args.require_alignment and not validated:
            return 2
        return 0
    except Exception as ex:
        (run_dir / "survey_error.txt").write_text(
            "command: "
            + shlex.join([sys.executable, *sys.argv])
            + "\n\n"
            + traceback.format_exc(),
            encoding="utf-8",
        )
        print(f"survey failed: {ex}", file=sys.stderr)
        print(f"error record: {run_dir / 'survey_error.txt'}", file=sys.stderr)
        return 3


def run_self_test() -> int:
    html = """
    <span class="bar-n">2</span><span class="bar-n">1</span>
    <div class="xlab">Jan 25</div><div class="xlab">Feb 25</div>
    <p class="meta-line">Fixture</p>
    """
    live, meta = parse_live_series(html)
    assert live == [("2025-01", 2), ("2025-02", 1)]
    assert meta == "Fixture"
    corpus = {
        "generated": "fixture",
        "papers": [
            {"published": "2024-12-01T00:00:00Z"},
            {"published": "2025-01-01T00:00:00Z"},
            {"published": "2025-01-02T00:00:00Z"},
            {"published": "2025-02-01T00:00:00Z"},
            {"published": "2026-09-07T00:00:00Z"},
        ],
    }
    counts, info = analyze_corpus(json.dumps(corpus).encode(), date(2026, 9, 6))
    assert compare(live, counts) == []
    assert compare([("2025-01", 3)], counts)[0]["actual"] == 2
    fixture_snapshot = [
        (month, 0)
        for month in month_range(VALIDATION_START_MONTH, VALIDATION_END_MONTH)
    ]
    assert len(validation_overlap(fixture_snapshot)) == 19
    assert info["published_before_2025"] == 1
    assert info["published_after_cutoff"] == 1
    assert month_range("2024-11", "2025-02") == [
        "2024-11",
        "2024-12",
        "2025-01",
        "2025-02",
    ]
    print("OK: publication survey self-test passed")
    return 0


def main() -> int:
    args = parse_args()
    if args.command == "self-test":
        return run_self_test()
    return run_survey(args)


if __name__ == "__main__":
    raise SystemExit(main())
