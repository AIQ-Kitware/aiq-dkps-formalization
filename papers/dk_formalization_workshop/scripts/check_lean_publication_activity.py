#!/usr/bin/env python3
"""Check the frozen Papers With Lean monthly series against the live stats page."""

from __future__ import annotations

import argparse
import csv
import html as html_lib
import re
import sys
import urllib.error
import urllib.request
from datetime import datetime
from pathlib import Path

DEFAULT_URL = "https://paperswithlean.com/stat/"
DEFAULT_SNAPSHOT = Path(__file__).resolve().parents[1] / "data" / "lean_publication_activity.csv"
PAPER_CUTOFF_MONTH = "2026-09"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--url", default=DEFAULT_URL, help="Papers With Lean statistics page")
    parser.add_argument(
        "--snapshot",
        type=Path,
        default=DEFAULT_SNAPSHOT,
        help="tracked CSV snapshot to validate",
    )
    parser.add_argument(
        "--emit-csv",
        action="store_true",
        help="also print the complete live month/count series as CSV",
    )
    return parser.parse_args()


def fetch_text(url: str) -> str:
    request = urllib.request.Request(
        url,
        headers={"User-Agent": "aiq-dkps-formalization-paper-source-check/1"},
    )
    with urllib.request.urlopen(request, timeout=30) as response:
        charset = response.headers.get_content_charset() or "utf-8"
        return response.read().decode(charset)


def month_key(label: str) -> str:
    return datetime.strptime(label.strip(), "%b %y").strftime("%Y-%m")


def parse_live_series(page: str) -> tuple[list[tuple[str, int]], str | None]:
    counts = [int(value) for value in re.findall(r'<span class="bar-n">(\d+)</span>', page)]
    labels = [
        month_key(html_lib.unescape(label))
        for label in re.findall(r'<div class="xlab">([^<]+)</div>', page)
    ]
    if not counts or len(counts) != len(labels):
        raise ValueError(
            f"could not parse Papers With Lean month series: "
            f"{len(labels)} labels, {len(counts)} counts"
        )
    meta_match = re.search(r'<p class="meta-line">([^<]+)</p>', page)
    meta = html_lib.unescape(meta_match.group(1)).strip() if meta_match else None
    return list(zip(labels, counts, strict=True)), meta


def load_snapshot(path: Path) -> list[tuple[str, int]]:
    with path.open(newline="", encoding="utf8") as file:
        reader = csv.DictReader(file)
        rows = [(row["month"], int(row["papers_indexed"])) for row in reader]
    if not rows:
        raise ValueError(f"snapshot is empty: {path}")
    return rows


def main() -> int:
    args = parse_args()
    try:
        page = fetch_text(args.url)
    except urllib.error.URLError as ex:
        print(f"could not fetch {args.url}: {ex}", file=sys.stderr)
        return 3
    live, meta = parse_live_series(page)
    frozen = load_snapshot(args.snapshot)
    live_map = dict(live)
    live_first = live[0][0]
    live_last = live[-1][0]

    comparable = [
        (month, expected)
        for month, expected in frozen
        if live_first <= month <= live_last and month < PAPER_CUTOFF_MONTH
    ]

    mismatches = [
        (month, expected, live_map.get(month))
        for month, expected in comparable
        if live_map.get(month) != expected
    ]
    missing = [month for month, _ in comparable if month not in live_map]
    if missing:
        print("live page is missing frozen months: " + ", ".join(missing), file=sys.stderr)
        return 2
    if mismatches:
        print("frozen publication snapshot differs from the live page:", file=sys.stderr)
        for month, frozen_count, live_count in mismatches:
            print(
                f"  {month}: snapshot={frozen_count}, live={live_count}",
                file=sys.stderr,
            )
        return 1

    if not comparable:
        print("no complete tracked months overlap the live statistics chart", file=sys.stderr)
        return 2
    first_month = comparable[0][0]
    last_month = comparable[-1][0]
    print(
        f"OK: {len(comparable)} complete tracked months {first_month}--{last_month} "
        "match the live Papers With Lean chart."
    )
    if meta:
        print(meta)

    newer = [(month, count) for month, count in live if month > frozen[-1][0]]
    if newer:
        print("Newer live months (not used by the frozen paper statistic):")
        for month, count in newer:
            print(f"  {month}: {count}")

    if args.emit_csv:
        print("\nmonth,papers_indexed")
        for month, count in live:
            print(f"{month},{count}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
