#!/usr/bin/env python3
"""Render a compact, self-contained semantic-alignment review packet.

The full source censuses remain exhaustive.  This renderer selects an external
review surface by census `importance`.  Headline rows are intentionally curated:

* a normalized mathematical source statement;
* one or more canonical Lean declarations whose compiler-resolved types carry
  the alignment claim;
* supporting declarations used only to certify additional scope;
* a *small curated semantic dictionary* of project-local definitions that hide
  mathematical content in those types; and
* a clause-by-clause source/Lean correspondence table.

The tool deliberately does not recursively expand every `TauCeti.*` dependency.
The census author chooses the semantic closure an external reviewer needs.
"""
from __future__ import annotations

import argparse
import collections
import datetime as dt
import json
import pathlib
import re
import subprocess
import tempfile

from source_census_importance import IMPORTANCE_ORDER, selected_by_importance

ROOT = pathlib.Path(__file__).resolve().parents[1]
DK_CENSUS = ROOT / "dev/davis-kahan-1970-full-source-census.json"
YWS_CENSUS = ROOT / "dev/yu-wang-samworth-2015-full-source-census.json"
DEFAULT_OUTPUT = ROOT / "build/semantic-alignment/headline-review.md"
BEGIN = "SEMANTIC_REVIEW_BEGIN|"
END = "SEMANTIC_REVIEW_END|"

PAPER_SPECS = {
    "dk": {"label": "Davis--Kahan 1970", "census": DK_CENSUS},
    "yws": {"label": "Yu--Wang--Samworth 2015", "census": YWS_CENSUS},
}


def load(path: pathlib.Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def git_value(*args: str) -> str:
    p = subprocess.run(["git", *args], cwd=ROOT, text=True, capture_output=True)
    return p.stdout.strip() if p.returncode == 0 else "unavailable"


def fallback_review(row: dict) -> dict:
    decls = row.get("lean_declarations", [])
    return {
        "group": row["id"],
        "group_title": row["title"],
        "claim": row["summary"],
        "source_statement": {
            "setup": [],
            "hypotheses": ["See the full source census for the uncurated source hypotheses."],
            "conclusions": [row["summary"]],
            "scope": [],
        },
        "canonical_declarations": decls[:1],
        "supporting_declarations": decls[1:],
        "context_declarations": [],
        "clause_map": [{
            "source_clause": row["summary"],
            "lean_realization": "No curated headline correspondence is registered for this broader-tier row.",
            "status": "claimed_exact",
        }],
        "note": "This row is outside the curated headline surface; showing the census fallback.",
    }


def collect(papers: list[str], threshold: str) -> tuple[list[dict], list[dict]]:
    groups: collections.OrderedDict[tuple[str, str], dict] = collections.OrderedDict()
    variants: list[dict] = []
    for paper in papers:
        spec = PAPER_SPECS[paper]
        data = load(spec["census"])
        for row in selected_by_importance(data["items"], threshold):
            review = row.get("semantic_review")
            if not isinstance(review, dict):
                review = fallback_review(row)
            key = (paper, review["group"])
            if key not in groups:
                groups[key] = {
                    "paper": paper,
                    "paper_label": spec["label"],
                    "group": review["group"],
                    "title": review["group_title"],
                    "importance": row["importance"],
                    "rows": [],
                }
            group = groups[key]
            if IMPORTANCE_ORDER[row["importance"]] < IMPORTANCE_ORDER[group["importance"]]:
                group["importance"] = row["importance"]
            group["rows"].append({"row": row, "review": review})
            for variant in row.get("semantic_review_variants", []):
                variants.append({"paper": paper, "parent_row": row, **variant})
    return list(groups.values()), variants


def query_key(mode: str, name: str) -> str:
    return f"{mode}:{name}"


def probe_queries(groups: list[dict], variants: list[dict]) -> list[tuple[str, str]]:
    out: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()

    def add(mode: str, name: str) -> None:
        key = (mode, name)
        if key not in seen:
            seen.add(key)
            out.append(key)

    def add_review(review: dict) -> None:
        for name in review.get("canonical_declarations", []):
            add("check", name)
        for name in review.get("supporting_declarations", []):
            add("check", name)
        for entry in review.get("context_declarations", []):
            add("print", entry["name"])

    for group in groups:
        for entry in group["rows"]:
            add_review(entry["review"])
    for variant in variants:
        add_review(variant)
    return out


def write_probe(path: pathlib.Path, queries: list[tuple[str, str]], papers: list[str]) -> None:
    imports = ["import DavisKahan.All"]
    if "yws" in papers:
        imports.append("import FinishYuWangSamworth")
    lines = [*imports, "", "-- Generated semantic-alignment compiler probe.", ""]
    for i, (mode, name) in enumerate(queries):
        lines.append(f'#eval IO.println "{BEGIN}{i}"')
        lines.append(f"#check @{name}" if mode == "check" else f"#print {name}")
        lines.append(f'#eval IO.println "{END}{i}"')
        lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_probe(text: str, queries: list[tuple[str, str]]) -> dict[str, dict]:
    blocks: dict[int, list[str]] = {}
    current: int | None = None
    for line in text.splitlines():
        if BEGIN in line:
            try:
                current = int(line.split(BEGIN, 1)[1].split()[0])
                blocks[current] = []
            except ValueError:
                current = None
            continue
        if END in line:
            current = None
            continue
        if current is not None:
            blocks[current].append(line)

    out: dict[str, dict] = {}
    for i, (mode, name) in enumerate(queries):
        raw = "\n".join(blocks.get(i, [])).strip()
        resolved = bool(raw) and not re.search(r"(^|\n).*\berror(?:\(|:)", raw, re.I)
        out[query_key(mode, name)] = {
            "mode": mode,
            "name": name,
            "resolved": resolved,
            "text": raw if resolved else "",
            "raw": raw,
        }
    return out


def resolve(queries: list[tuple[str, str]], papers: list[str]) -> tuple[dict[str, dict], str, int]:
    (ROOT / "build").mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="semantic-review-", dir=ROOT / "build", delete=False
    ) as tmp:
        probe = pathlib.Path(tmp.name)
    try:
        write_probe(probe, queries, papers)
        p = subprocess.run(
            ["lake", "env", "lean", str(probe.relative_to(ROOT))],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        return parse_probe(p.stdout, queries), p.stdout, p.returncode
    finally:
        probe.unlink(missing_ok=True)


def lean_block(text: str) -> str:
    return "~~~~lean\n" + text.rstrip() + "\n~~~~"


def get_probe(results: dict[str, dict], mode: str, name: str) -> dict:
    return results.get(query_key(mode, name), {
        "resolved": False,
        "raw": "compiler probe not run",
        "text": "",
    })


def render_source_statement(statement: dict) -> list[str]:
    lines = ["**Normalized source statement**", ""]
    for key, label in (
        ("setup", "Setup"),
        ("hypotheses", "Hypotheses"),
        ("conclusions", "Conclusion"),
        ("scope", "Scope"),
    ):
        values = statement.get(key, [])
        if values:
            lines += [f"*{label}:*", ""]
            lines.extend(f"- {x}" for x in values)
            lines.append("")
    return lines


def md_cell(text: str) -> str:
    return text.replace("|", "\\|").replace("\n", " ")


def render_context(review: dict, results: dict[str, dict]) -> list[str]:
    entries = review.get("context_declarations", [])
    if not entries:
        return []
    lines = [
        "**Local semantic dictionary**", "",
        "These are the project-local notions in the canonical theorem type whose mathematical content is relevant to alignment. They are curated explicitly; unrelated implementation dependencies are not expanded.", "",
    ]
    for entry in entries:
        name = entry["name"]
        data = get_probe(results, "print", name)
        lines += [f"`{name}` — {entry['mathematical_role']}", ""]
        if data.get("resolved"):
            lines += [lean_block(data["text"]), ""]
        else:
            lines += [f"> **UNRESOLVED DEFINITION:** {data.get('raw') or 'no compiler output'}", ""]
    return lines


def render_clause_map(review: dict) -> list[str]:
    lines = ["**Clause-by-clause alignment claim**", "", "| Source clause | Lean realization | Status |", "|---|---|---|"]
    for entry in review.get("clause_map", []):
        lines.append(
            f"| {md_cell(entry['source_clause'])} | {md_cell(entry['lean_realization'])} | `{entry.get('status','claimed_exact')}` |"
        )
    lines.append("")
    return lines


def render_checks(title: str, names: list[str], results: dict[str, dict], *, details: bool = False) -> list[str]:
    if not names:
        return []
    lines: list[str] = []
    if details:
        lines += ["<details>", f"<summary><strong>{title}</strong></summary>", ""]
    else:
        lines += [f"**{title}**", ""]
    for name in names:
        data = get_probe(results, "check", name)
        lines += [f"`{name}`", ""]
        if data.get("resolved"):
            lines += [lean_block(data["text"]), ""]
        else:
            lines += [f"> **UNRESOLVED:** {data.get('raw') or 'no compiler output'}", ""]
    if details:
        lines += ["</details>", ""]
    return lines


def render_review_body(review: dict, results: dict[str, dict]) -> list[str]:
    lines = [review["claim"], ""]
    lines += render_source_statement(review["source_statement"])
    lines += render_checks("Canonical compiler-resolved Lean statement(s)", review.get("canonical_declarations", []), results)
    lines += render_context(review, results)
    lines += render_clause_map(review)
    lines += render_checks("Supporting scope declarations", review.get("supporting_declarations", []), results, details=True)
    if review.get("note"):
        lines += [f"**Maintainer note:** {review['note']}", ""]
    return lines


def render(groups: list[dict], variants: list[dict], results: dict[str, dict], *,
           threshold: str, papers: list[str], lean_run: bool, probe_rc: int | None) -> str:
    head = git_value("rev-parse", "HEAD")
    dirty = git_value("status", "--porcelain")
    now = dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")
    lines = [
        "# Semantic alignment review: headline mathematical statements", "",
        f"Generated: `{now}`",
        f"Repository commit: `{head}`",
        f"Working tree clean: `{'yes' if not dirty else 'no'}`",
        f"Importance threshold: `{threshold}`",
        f"Papers: {', '.join(PAPER_SPECS[p]['label'] for p in papers)}",
        f"Compiler semantic probe run: `{'yes' if lean_run else 'no'}`",
        *([f"Compiler probe exit code: `{probe_rc}`"] if lean_run else []),
        "",
        "## Review purpose", "",
        "This is a deliberately small semantic-review surface, not a full-paper census. For each selected headline claim it contains enough of both sides of the translation to let a mathematically knowledgeable reviewer decide whether the Lean theorem states the same claim under the same hypotheses and scope.", "",
        "The **normalized source statement and correspondence table are maintained claims of this project**. The Lean theorem types and local-definition bodies are obtained from the compiler on this commit. The reviewer's job is to challenge the correspondence between them.", "",
        "Project-local definitions are expanded only when they hide mathematically relevant content in a headline theorem type. The packet does not recursively dump implementation dependencies.", "",
    ]

    current_paper = None
    for group in groups:
        if group["paper"] != current_paper:
            current_paper = group["paper"]
            lines += [f"## {group['paper_label']}", ""]
        lines += [f"### {group['title']}", "", f"Review priority: `{group['importance']}`", ""]
        for entry in group["rows"]:
            row, review = entry["row"], entry["review"]
            if len(group["rows"]) > 1:
                lines += [f"#### Source clause `{row['id']}`", ""]
            lines += [f"**Source anchor:** {row['source_anchor']}", ""]
            lines += render_review_body(review, results)

        lines += [
            "**Independent reviewer verdict:** `PASS exact alignment` / `FAIL mismatch` / `UNCERTAIN`", "",
            "- Verdict: _fill in_",
            "- Hidden or stronger Lean hypothesis, if any: _fill in_",
            "- Missing or weakened conclusion, if any: _fill in_",
            "- Is every project-local notion needed to judge the theorem expanded above? _fill in_",
            "- Suggested replacement theorem/context, if needed: _fill in_",
            "", "---", "",
        ]

        parent_ids = {e["row"]["id"] for e in group["rows"]}
        for variant in [v for v in variants if v["paper"] == group["paper"] and v["parent_row"]["id"] in parent_ids]:
            lines += [
                f"### {variant['title']}", "",
                "Review priority: `headline` (derived review target)", "",
                f"**Provenance:** {variant['provenance_note']}", "",
            ]
            lines += render_review_body(variant, results)
            lines += [
                "**Independent reviewer verdict:** `PASS faithful derived form` / `FAIL` / `UNCERTAIN`", "",
                "- Verdict: _fill in_",
                "- Is the claimed derivation from the source theorem legitimate? _fill in_",
                "- Any stronger hidden hypothesis in Lean? _fill in_",
                "", "---", "",
            ]

    lines += [
        "## Scope intentionally omitted", "",
        "Rows marked `major`, `supporting`, or `technical` are excluded from the default `headline` packet. Use `--importance major` for the broader tier. The exhaustive paper censuses remain the authority for full-paper coverage.", "",
    ]
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--papers", default="dk,yws", help="comma-separated subset of dk,yws")
    ap.add_argument("--importance", choices=list(IMPORTANCE_ORDER), default="headline",
                    help="include this priority tier and all more-important tiers")
    ap.add_argument("--output", type=pathlib.Path, default=DEFAULT_OUTPUT)
    ap.add_argument("--no-lean", action="store_true", help="render without compiler probes")
    ap.add_argument("--allow-unresolved", action="store_true",
                    help="write packet and exit 0 even if a selected compiler probe fails")
    args = ap.parse_args()

    papers = [p.strip() for p in args.papers.split(",") if p.strip()]
    if not papers or any(p not in PAPER_SPECS for p in papers):
        ap.error("--papers must be a nonempty comma-separated subset of dk,yws")

    groups, variants = collect(papers, args.importance)
    queries = probe_queries(groups, variants)
    if args.no_lean:
        results = {
            query_key(mode, name): {"resolved": False, "raw": "compiler probe not run (--no-lean)", "text": ""}
            for mode, name in queries
        }
        probe_output = ""
        probe_rc = None
    else:
        results, probe_output, probe_rc = resolve(queries, papers)

    output = args.output if args.output.is_absolute() else ROOT / args.output
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(render(groups, variants, results, threshold=args.importance, papers=papers,
                             lean_run=not args.no_lean, probe_rc=probe_rc), encoding="utf-8")

    unresolved = [(mode, name) for mode, name in queries if not get_probe(results, mode, name).get("resolved")]
    print(f"semantic alignment review: {output.relative_to(ROOT)}")
    print(f"  groups: {len(groups)}; derived variants: {len(variants)}; compiler probes: {len(queries)}")
    if args.no_lean:
        print("  compiler probes: not run (--no-lean preview)")
    else:
        print(f"  compiler probes: {len(queries)-len(unresolved)}/{len(queries)} resolved")
        if unresolved:
            print("  unresolved:")
            for mode, name in unresolved:
                print(f"    {mode}: {name}")
            if probe_output:
                log = output.with_suffix(output.suffix + ".lean.log")
                log.write_text(probe_output, encoding="utf-8")
                print(f"  probe log: {log.relative_to(ROOT)}")
    return 1 if unresolved and not args.allow_unresolved and not args.no_lean else 0


if __name__ == "__main__":
    raise SystemExit(main())
