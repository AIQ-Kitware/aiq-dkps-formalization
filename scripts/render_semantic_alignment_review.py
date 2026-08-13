#!/usr/bin/env python3
"""Render a concise, compiler-resolved semantic-alignment review packet.

The full source censuses stay exhaustive.  This renderer selects only rows at or
above an `importance` threshold, groups rows that are clauses of the same paper
theorem, and pairs the maintained source-aligned prose with compiler-printed
Lean theorem types.

Default external packet:

    python3 scripts/render_semantic_alignment_review.py

Expanded important-result packet:

    python3 scripts/render_semantic_alignment_review.py --importance major

Static preview without invoking Lean:

    python3 scripts/render_semantic_alignment_review.py --no-lean
"""
from __future__ import annotations

import argparse
import collections
import datetime as dt
import json
import pathlib
import re
import subprocess
import sys
import tempfile

from source_census_importance import IMPORTANCE_ORDER, selected_by_importance

ROOT = pathlib.Path(__file__).resolve().parents[1]
DK_CENSUS = ROOT / "dev/davis-kahan-1970-full-source-census.json"
DK_RESULTS = ROOT / "dev/davis-kahan-1970-formalization-result-inventory.json"
YWS_CENSUS = ROOT / "dev/yu-wang-samworth-2015-full-source-census.json"
DEFAULT_OUTPUT = ROOT / "build/semantic-alignment/headline-review.md"
BEGIN = "SEMANTIC_REVIEW_BEGIN|"
END = "SEMANTIC_REVIEW_END|"

PAPER_SPECS = {
    "dk": {
        "label": "Davis--Kahan 1970",
        "census": DK_CENSUS,
    },
    "yws": {
        "label": "Yu--Wang--Samworth 2015",
        "census": YWS_CENSUS,
    },
}


def load(path: pathlib.Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def git_value(*args: str) -> str:
    p = subprocess.run(["git", *args], cwd=ROOT, text=True, capture_output=True)
    return p.stdout.strip() if p.returncode == 0 else "unavailable"


def collect(papers: list[str], threshold: str) -> tuple[list[dict], list[dict]]:
    groups: collections.OrderedDict[tuple[str, str], dict] = collections.OrderedDict()
    variants: list[dict] = []
    for paper in papers:
        spec = PAPER_SPECS[paper]
        data = load(spec["census"])
        rows = selected_by_importance(data["items"], threshold)
        for row in rows:
            review = row.get("semantic_review")
            # Supporting/technical rows may become selected only with a very broad
            # threshold and intentionally fall back to the census summary + all
            # declarations. Headline rows are schema-checked to be curated.
            if not isinstance(review, dict):
                curated = None
                if paper == "dk" and DK_RESULTS.exists():
                    inv = load(DK_RESULTS)
                    curated = next((r for r in inv.get("results", []) if r.get("id") == row["id"]), None)
                review = {
                    "group": row["id"],
                    "group_title": row["title"],
                    "claim": row["summary"],
                    "declarations": (curated or {}).get("lean_declarations", row.get("lean_declarations", [])),
                    "note": ((curated or {}).get("review_note")
                             or "No curated semantic-review surface is registered; showing the census row directly."),
                }
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
                variants.append({
                    "paper": paper,
                    "paper_label": spec["label"],
                    "parent_row": row,
                    **variant,
                })
    return list(groups.values()), variants


def declarations(groups: list[dict], variants: list[dict]) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for group in groups:
        for entry in group["rows"]:
            for decl in entry["review"].get("declarations", []):
                if decl not in seen:
                    out.append(decl); seen.add(decl)
    for variant in variants:
        for decl in variant.get("declarations", []):
            if decl not in seen:
                out.append(decl); seen.add(decl)
    return out


def write_probe(path: pathlib.Path, decls: list[str], papers: list[str]) -> None:
    imports = ["import DavisKahan.All"]
    if "yws" in papers:
        imports.append("import FinishYuWangSamworth")
    lines = [*imports, "", "-- Generated semantic-alignment signature probe.", ""]
    for i, decl in enumerate(decls):
        lines += [
            f'#eval IO.println "{BEGIN}{i}"',
            f"#check @{decl}",
            f'#eval IO.println "{END}{i}"',
            "",
        ]
    path.write_text("\n".join(lines), encoding="utf-8")


def parse_probe(text: str, decls: list[str]) -> dict[str, dict]:
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
    out = {}
    for i, decl in enumerate(decls):
        raw = "\n".join(blocks.get(i, [])).strip()
        resolved = bool(raw) and not re.search(r"(^|\n).*\berror(?:\(|:)", raw, re.I)
        out[decl] = {"resolved": resolved, "type": raw if resolved else "", "raw": raw}
    return out


def resolve(decls: list[str], papers: list[str]) -> tuple[dict[str, dict], str, int]:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="semantic-review-", dir=ROOT / "build", delete=False
    ) as tmp:
        probe = pathlib.Path(tmp.name)
    try:
        write_probe(probe, decls, papers)
        p = subprocess.run(
            ["lake", "env", "lean", str(probe.relative_to(ROOT))],
            cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        parsed = parse_probe(p.stdout, decls)
        return parsed, p.stdout, p.returncode
    finally:
        probe.unlink(missing_ok=True)


def dk_atom_summaries(result_id: str) -> list[tuple[str, str]]:
    if not DK_RESULTS.exists():
        return []
    results = load(DK_RESULTS)
    result = next((r for r in results.get("results", []) if r.get("id") == result_id), None)
    if result is None:
        return []
    fidelity = ROOT / results["source_fidelity_inventory"]
    atoms = {a["id"]: a for a in load(fidelity).get("atoms", [])}
    out = []
    for atom_id in result.get("source_atom_ids", []):
        atom = atoms.get(atom_id)
        if atom is not None:
            out.append((atom_id, atom["summary"]))
    return out


def code(text: str) -> str:
    return "~~~~lean\n" + text.rstrip() + "\n~~~~"


def render(groups: list[dict], variants: list[dict], sigs: dict[str, dict], *,
           threshold: str, papers: list[str], lean_run: bool, probe_rc: int | None) -> str:
    head = git_value("rev-parse", "HEAD")
    dirty = git_value("status", "--porcelain")
    now = dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds")
    lines = [
        "# Semantic alignment review: headline mathematical statements",
        "",
        f"Generated: `{now}`",
        f"Repository commit: `{head}`",
        f"Working tree clean: `{'yes' if not dirty else 'no'}`",
        f"Importance threshold: `{threshold}` (includes equally or more important rows)",
        f"Papers: {', '.join(PAPER_SPECS[p]['label'] for p in papers)}",
        f"Compiler signature probe run: `{'yes' if lean_run else 'no'}`",
        *( [f"Compiler probe exit code: `{probe_rc}`"] if lean_run else [] ),
        "",
        "## Review purpose",
        "",
        "This packet is intentionally **not** a full-paper census. It is a small external-review surface selected by the `importance` field in each paper's source census. For every selected claim it presents the project-maintained prose statement that is claimed to match the source and the compiler-resolved Lean theorem type(s) chosen to realize that claim.",
        "",
        "The review question is semantic, not proof-theoretic: **does the Lean type state the same mathematical claim, under the same hypotheses and scope, without weakening the conclusion?** Proof bodies and supporting lemmas are deliberately omitted.",
        "",
    ]
    current_paper = None
    for group in groups:
        if group["paper"] != current_paper:
            current_paper = group["paper"]
            lines += [f"## {group['paper_label']}", ""]
        lines += [
            f"### {group['title']}", "",
            f"Review priority: `{group['importance']}`", "",
        ]
        for entry in group["rows"]:
            row, review = entry["row"], entry["review"]
            lines += [
                f"#### Claimed source-aligned prose — `{row['id']}`", "",
                f"**Source anchor:** {row['source_anchor']}", "",
                review["claim"], "",
            ]
            if review.get("note"):
                lines += [f"**Maintainer note:** {review['note']}", ""]
            if group["paper"] == "dk":
                atoms = dk_atom_summaries(row["id"])
                if atoms:
                    lines += ["**Registered source-fidelity clauses counted for this result:**", ""]
                    for atom_id, summary in atoms:
                        lines.append(f"- `{atom_id}` — {summary}")
                    lines.append("")
            lines += ["**Resolved Lean statement(s):**", ""]
            for decl in review.get("declarations", []):
                data = sigs.get(decl, {"resolved": False, "raw": "signature probe not run"})
                lines += [f"`{decl}`", ""]
                if data.get("resolved"):
                    lines += [code(data["type"]), ""]
                else:
                    lines += [f"> **UNRESOLVED:** {data.get('raw') or 'no compiler output'}", ""]
        lines += [
            "**Independent reviewer verdict:** `PASS exact alignment` / `FAIL mismatch` / `UNCERTAIN`", "",
            "- Verdict: _fill in_",
            "- Hypothesis/scope mismatch, if any: _fill in_",
            "- Conclusion mismatch, if any: _fill in_",
            "- Suggested replacement Lean statement, if needed: _fill in_",
            "", "---", "",
        ]

        # Variants attached to a selected row in this group are rendered as their
        # own review target immediately after the source theorem that motivates them.
        for variant in [v for v in variants if v["paper"] == group["paper"] and
                        any(e["row"]["id"] == v["parent_row"]["id"] for e in group["rows"])]:
            lines += [
                f"### {variant['title']}", "",
                "Review priority: `headline` (derived review target)", "",
                f"**Provenance:** {variant['provenance_note']}", "",
                "#### Claimed mathematical statement", "",
                variant["claim"], "",
                "**Resolved Lean statement(s):**", "",
            ]
            for decl in variant["declarations"]:
                data = sigs.get(decl, {"resolved": False, "raw": "signature probe not run"})
                lines += [f"`{decl}`", ""]
                if data.get("resolved"):
                    lines += [code(data["type"]), ""]
                else:
                    lines += [f"> **UNRESOLVED:** {data.get('raw') or 'no compiler output'}", ""]
            lines += [
                "**Independent reviewer verdict:** `PASS mathematically faithful derived form` / `FAIL` / `UNCERTAIN`", "",
                "- Verdict: _fill in_",
                "- Is the stated provenance from the source theorem to this projector form legitimate? _fill in_",
                "- Any stronger hidden hypothesis in Lean? _fill in_",
                "", "---", "",
            ]
    lines += [
        "## Scope intentionally omitted",
        "",
        "Rows marked `major`, `supporting`, or `technical` are excluded from the default `headline` packet. Increase the threshold with `--importance major` when a broader expert audit is desired. The exhaustive source censuses remain the authority for full-paper coverage and are not replaced by this packet.",
        "",
    ]
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--papers", default="dk,yws",
                    help="comma-separated subset of: dk,yws (default: dk,yws)")
    ap.add_argument("--importance", choices=list(IMPORTANCE_ORDER), default="headline",
                    help="include this review-priority tier and all more-important tiers")
    ap.add_argument("--output", type=pathlib.Path, default=DEFAULT_OUTPUT)
    ap.add_argument("--no-lean", action="store_true",
                    help="render a static preview without compiler-resolving theorem types")
    ap.add_argument("--allow-unresolved", action="store_true",
                    help="write the packet and exit 0 even if a selected declaration does not resolve")
    args = ap.parse_args()

    papers = [p.strip() for p in args.papers.split(",") if p.strip()]
    bad = [p for p in papers if p not in PAPER_SPECS]
    if bad or not papers:
        ap.error("--papers must be a nonempty comma-separated subset of dk,yws")

    groups, variants = collect(papers, args.importance)
    decls = declarations(groups, variants)
    sigs: dict[str, dict]
    probe_output = ""
    probe_rc: int | None = None
    if args.no_lean:
        sigs = {d: {"resolved": False, "raw": "signature probe not run (--no-lean)"} for d in decls}
    else:
        (ROOT / "build").mkdir(exist_ok=True)
        sigs, probe_output, probe_rc = resolve(decls, papers)

    args.output = args.output if args.output.is_absolute() else ROOT / args.output
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        render(groups, variants, sigs, threshold=args.importance, papers=papers,
               lean_run=not args.no_lean, probe_rc=probe_rc),
        encoding="utf-8",
    )

    unresolved = [d for d in decls if not sigs.get(d, {}).get("resolved")]
    print(f"semantic alignment review: {args.output.relative_to(ROOT)}")
    print(f"  groups: {len(groups)}; derived variants: {len(variants)}; declarations: {len(decls)}")
    if args.no_lean:
        print("  Lean signatures: not resolved (--no-lean preview)")
    else:
        print(f"  Lean signatures: {len(decls)-len(unresolved)}/{len(decls)} resolved")
        if unresolved:
            print("  unresolved:")
            for d in unresolved:
                print(f"    {d}")
            if probe_output:
                log = args.output.with_suffix(args.output.suffix + ".lean.log")
                log.write_text(probe_output, encoding="utf-8")
                print(f"  probe log: {log.relative_to(ROOT)}")
    if unresolved and not args.allow_unresolved and not args.no_lean:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
