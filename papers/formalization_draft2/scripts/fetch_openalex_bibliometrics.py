#!/usr/bin/env python3
"""Fetch OpenAlex citation data and refresh tracked manuscript snapshots.

This is an explicit network utility, not part of the normal manuscript build.
The selected OpenAlex response is written under ``generated/`` and is therefore
ignored by Git.  Small derived artifacts used by the manuscript are written
under ``snapshots/`` and are intended to be reviewed and committed.

Authentication is read from ``OPENALEX_API_KEY`` by default.  The key is sent to
OpenAlex but is never written to either the raw response or tracked snapshots.
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import io
import json
import os
import pathlib
import sys
import tempfile
import urllib.error
import urllib.parse
import urllib.request
from typing import Any

HERE = pathlib.Path(__file__).resolve().parent
PAPER_ROOT = HERE.parent
DEFAULT_CONFIG = PAPER_ROOT / "data" / "bibliometrics" / "openalex_works.json"
DEFAULT_RAW_OUTPUT = PAPER_ROOT / "generated" / "openalex_response.json"
DEFAULT_SNAPSHOT_OUTPUT = PAPER_ROOT / "snapshots" / "openalex_bibliometrics.json"
DEFAULT_TEX_OUTPUT = PAPER_ROOT / "snapshots" / "openalex_bibliometrics_macros.tex"
DEFAULT_TREND_CSV = PAPER_ROOT / "snapshots" / "openalex_citation_trends.csv"
DEFAULT_TREND_TEX = PAPER_ROOT / "snapshots" / "openalex_citation_trend_table.tex"
DEFAULT_API_BASE = "https://api.openalex.org"
SELECT_FIELDS = (
    "id",
    "doi",
    "display_name",
    "publication_year",
    "publication_date",
    "cited_by_count",
    "counts_by_year",
    "updated_date",
)
USER_AGENT = "aiq-dkps-formalization-openalex-snapshot/1.1"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=pathlib.Path, default=DEFAULT_CONFIG)
    parser.add_argument("--raw-output", type=pathlib.Path, default=DEFAULT_RAW_OUTPUT)
    parser.add_argument("--snapshot-output", type=pathlib.Path, default=DEFAULT_SNAPSHOT_OUTPUT)
    parser.add_argument("--tex-output", type=pathlib.Path, default=DEFAULT_TEX_OUTPUT)
    parser.add_argument("--trend-csv", type=pathlib.Path, default=DEFAULT_TREND_CSV)
    parser.add_argument("--trend-tex", type=pathlib.Path, default=DEFAULT_TREND_TEX)
    parser.add_argument(
        "--api-key",
        default=os.environ.get("OPENALEX_API_KEY"),
        help="OpenAlex API key; defaults to OPENALEX_API_KEY.",
    )
    parser.add_argument("--api-base", default=DEFAULT_API_BASE, help=argparse.SUPPRESS)
    parser.add_argument("--timeout", type=float, default=30.0)
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print the DOI requests without contacting OpenAlex or writing files.",
    )
    return parser.parse_args()


def load_config(path: pathlib.Path) -> list[dict[str, str]]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("schema_version") != 1:
        raise ValueError(f"unsupported config schema in {path}")
    works = payload.get("works")
    if not isinstance(works, list) or not works:
        raise ValueError(f"expected a nonempty works list in {path}")
    required = {"key", "macro_stem", "citation_key", "doi", "expected_title"}
    seen: set[str] = set()
    for work in works:
        missing = required.difference(work)
        if missing:
            raise ValueError(f"work entry is missing {sorted(missing)}: {work!r}")
        if work["key"] in seen:
            raise ValueError(f"duplicate work key: {work['key']}")
        seen.add(work["key"])
    return works


def normalize_doi(value: str) -> str:
    doi = value.strip().lower()
    for prefix in ("https://doi.org/", "http://doi.org/", "doi:"):
        if doi.startswith(prefix):
            doi = doi[len(prefix) :]
            break
    return doi


def request_url(api_base: str, doi: str, api_key: str | None) -> str:
    external_id = urllib.parse.quote(f"doi:{normalize_doi(doi)}", safe=":/")
    query: dict[str, str] = {"select": ",".join(SELECT_FIELDS)}
    if api_key:
        query["api_key"] = api_key
    return f"{api_base.rstrip('/')}/works/{external_id}?{urllib.parse.urlencode(query)}"


def redacted_url(api_base: str, doi: str) -> str:
    external_id = urllib.parse.quote(f"doi:{normalize_doi(doi)}", safe=":/")
    query = urllib.parse.urlencode({"select": ",".join(SELECT_FIELDS)})
    return f"{api_base.rstrip('/')}/works/{external_id}?{query}"


def fetch_work(api_base: str, doi: str, api_key: str, timeout: float) -> dict[str, Any]:
    url = request_url(api_base, doi, api_key)
    request = urllib.request.Request(
        url,
        headers={"Accept": "application/json", "User-Agent": USER_AGENT},
    )
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            payload = json.load(response)
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"OpenAlex returned HTTP {exc.code} for DOI {doi}: {detail}") from exc
    except urllib.error.URLError as exc:
        raise RuntimeError(f"could not reach OpenAlex for DOI {doi}: {exc.reason}") from exc

    returned_doi = payload.get("doi")
    if not isinstance(returned_doi, str) or normalize_doi(returned_doi) != normalize_doi(doi):
        raise RuntimeError(f"OpenAlex DOI mismatch for {doi}: returned {returned_doi!r}")
    if not isinstance(payload.get("cited_by_count"), int):
        raise RuntimeError(f"OpenAlex response for {doi} has no integer cited_by_count")
    if not isinstance(payload.get("counts_by_year"), list):
        raise RuntimeError(f"OpenAlex response for {doi} has no counts_by_year list")
    return payload


def utc_now() -> dt.datetime:
    return dt.datetime.now(dt.timezone.utc).replace(microsecond=0)


def iso_z(value: dt.datetime) -> str:
    return value.isoformat().replace("+00:00", "Z")


def raw_payload(
    works: list[dict[str, str]],
    results: dict[str, dict[str, Any]],
    retrieved_at: dt.datetime,
    api_base: str,
) -> dict[str, Any]:
    records = []
    for work in works:
        records.append(
            {
                "key": work["key"],
                "macro_stem": work["macro_stem"],
                "citation_key": work["citation_key"],
                "configured_doi": normalize_doi(work["doi"]),
                "expected_title": work["expected_title"],
                "request": {
                    "method": "GET",
                    "url_without_api_key": redacted_url(api_base, work["doi"]),
                    "select_fields": list(SELECT_FIELDS),
                },
                "openalex": results[work["key"]],
            }
        )
    return {
        "schema_version": 1,
        "source": "OpenAlex",
        "retrieved_at_utc": iso_z(retrieved_at),
        "api_base": api_base,
        "authentication_secret_recorded": False,
        "works": records,
    }


def compact_snapshot(payload: dict[str, Any]) -> dict[str, Any]:
    records = []
    for record in payload["works"]:
        data = record["openalex"]
        records.append(
            {
                "key": record["key"],
                "macro_stem": record["macro_stem"],
                "citation_key": record["citation_key"],
                "doi": record["configured_doi"],
                "openalex_id": str(data["id"]).rsplit("/", 1)[-1],
                "title": data["display_name"],
                "publication_year": data["publication_year"],
                "cited_by_count": data["cited_by_count"],
                "counts_by_year": data["counts_by_year"],
                "openalex_updated_date": data.get("updated_date", ""),
            }
        )
    return {
        "schema_version": 1,
        "source": payload["source"],
        "retrieved_at_utc": payload["retrieved_at_utc"],
        "works": records,
    }


def atomic_write_text(path: pathlib.Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w", encoding="utf-8", dir=path.parent, delete=False, newline="\n"
    ) as handle:
        handle.write(text)
        temporary = pathlib.Path(handle.name)
    temporary.replace(path)


def write_json(path: pathlib.Path, payload: dict[str, Any]) -> None:
    atomic_write_text(path, json.dumps(payload, indent=2, sort_keys=True) + "\n")


def tex_escape_text(value: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "{": r"\{",
        "}": r"\}",
        "%": r"\%",
        "&": r"\&",
        "#": r"\#",
        "_": r"\_",
        "$": r"\$",
    }
    return "".join(replacements.get(ch, ch) for ch in value)


def counts_by_year(record: dict[str, Any]) -> dict[int, int]:
    return {
        int(item["year"]): int(item["cited_by_count"])
        for item in record["counts_by_year"]
    }


def render_tex(payload: dict[str, Any]) -> str:
    retrieved = dt.datetime.fromisoformat(payload["retrieved_at_utc"].replace("Z", "+00:00"))
    date_text = f"{retrieved.day} {retrieved.strftime('%B %Y')}"
    current_year = retrieved.year
    latest_complete_year = current_year - 1
    lines = [
        "% Generated by scripts/fetch_openalex_bibliometrics.py; do not edit by hand.",
        f"\\newcommand{{\\OpenAlexRetrievedAtUTC}}{{{tex_escape_text(payload['retrieved_at_utc'])}}}",
        f"\\newcommand{{\\OpenAlexRetrievedDate}}{{{date_text}}}",
        f"\\newcommand{{\\OpenAlexCurrentYear}}{{{current_year}}}",
        f"\\newcommand{{\\OpenAlexLatestCompleteYear}}{{{latest_complete_year}}}",
    ]
    for record in payload["works"]:
        stem = record["macro_stem"]
        annual = counts_by_year(record)
        lines.extend(
            [
                f"\\newcommand{{\\OpenAlex{stem}Citations}}{{{record['cited_by_count']}}}",
                f"\\newcommand{{\\OpenAlex{stem}WorkID}}{{{tex_escape_text(record['openalex_id'])}}}",
                f"\\newcommand{{\\OpenAlex{stem}UpdatedDate}}{{{tex_escape_text(str(record.get('openalex_updated_date', '')))}}}",
                f"\\newcommand{{\\OpenAlex{stem}CurrentYearCitations}}{{{annual.get(current_year, 0)}}}",
                f"\\newcommand{{\\OpenAlex{stem}LatestCompleteYearCitations}}{{{annual.get(latest_complete_year, 0)}}}",
            ]
        )
    return "\n".join(lines) + "\n"


def render_trend_csv(payload: dict[str, Any]) -> str:
    records = payload["works"]
    by_key = {record["key"]: counts_by_year(record) for record in records}
    years = sorted({year for counts in by_key.values() for year in counts}, reverse=True)
    output = io.StringIO(newline="")
    writer = csv.writer(output, lineterminator="\n")
    writer.writerow(["year", *[record["key"] for record in records]])
    for year in years:
        writer.writerow([year, *[by_key[record["key"]].get(year, 0) for record in records]])
    return output.getvalue()


def render_trend_tex(payload: dict[str, Any]) -> str:
    records = payload["works"]
    by_key = {record["key"]: counts_by_year(record) for record in records}
    years = sorted({year for counts in by_key.values() for year in counts}, reverse=True)
    retrieved_year = int(payload["retrieved_at_utc"][:4])
    headings = ["Davis--Kahan", "YWS"] if len(records) == 2 else [r["key"] for r in records]
    lines = [
        "% Generated by scripts/fetch_openalex_bibliometrics.py; do not edit by hand.",
        "\\begin{tabular}{l" + "r" * len(records) + "}",
        "\\toprule",
        "Year & " + " & ".join(headings) + r" \\",
        "\\midrule",
    ]
    for year in years:
        label = f"{year}*" if year == retrieved_year else str(year)
        counts = [str(by_key[record["key"]].get(year, 0)) for record in records]
        lines.append(label + " & " + " & ".join(counts) + r" \\")
    lines.extend(
        [
            "\\bottomrule",
            "\\end{tabular}",
            f"% * {retrieved_year} is partial through the retrieval date.",
        ]
    )
    return "\n".join(lines) + "\n"


def write_derived_outputs(
    raw: dict[str, Any],
    snapshot_path: pathlib.Path,
    tex_path: pathlib.Path,
    trend_csv_path: pathlib.Path,
    trend_tex_path: pathlib.Path,
) -> None:
    compact = compact_snapshot(raw)
    write_json(snapshot_path, compact)
    atomic_write_text(tex_path, render_tex(compact))
    atomic_write_text(trend_csv_path, render_trend_csv(compact))
    atomic_write_text(trend_tex_path, render_trend_tex(compact))


def main() -> int:
    args = parse_args()
    works = load_config(args.config)

    if args.dry_run:
        for work in works:
            print(f"{work['key']}: {redacted_url(args.api_base, work['doi'])}")
        return 0

    if not args.api_key:
        print(
            "error: OpenAlex authentication is required; set OPENALEX_API_KEY "
            "or pass --api-key",
            file=sys.stderr,
        )
        return 2

    results: dict[str, dict[str, Any]] = {}
    for work in works:
        result = fetch_work(args.api_base, work["doi"], args.api_key, args.timeout)
        results[work["key"]] = result
        print(
            f"{work['key']}: {result['cited_by_count']} OpenAlex citing works "
            f"({str(result['id']).rsplit('/', 1)[-1]})"
        )

    retrieved_at = utc_now()
    raw = raw_payload(works, results, retrieved_at, args.api_base)
    write_json(args.raw_output, raw)
    write_derived_outputs(
        raw,
        args.snapshot_output,
        args.tex_output,
        args.trend_csv,
        args.trend_tex,
    )
    print(f"wrote ignored raw response: {args.raw_output}")
    print(f"wrote tracked compact snapshot: {args.snapshot_output}")
    print(f"wrote tracked TeX macros: {args.tex_output}")
    print(f"wrote tracked annual trend CSV: {args.trend_csv}")
    print(f"wrote tracked annual trend TeX: {args.trend_tex}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
