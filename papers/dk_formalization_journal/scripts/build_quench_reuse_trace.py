#!/usr/bin/env python3
"""Measure the narrow YWS/Davis-Kahan foundation slice reused by Quench.

The Quench analysis is intentionally ancillary to the paper.  It first invokes the
compiler-backed prerequisite tracer on every top-level theorem in
``DkpsQuench2026/Geometry/AlignedCMDS.lean`` and then intersects that conservative
named-declaration closure with the checked-in whole-formalization inventory.

Outputs preserve exact Lean declaration names, source-result overlap, mathematical
theory classifications, and witness paths from Quench roots.  As with the underlying
compiler trace, imported opaque theorem bodies can hide proof-internal helpers, so all
reuse counts are conservative lower bounds rather than complete proof-body counts.
"""
from __future__ import annotations

import argparse
import csv
import json
import pathlib
import subprocess
import sys
import zipfile
from collections import defaultdict, deque
from typing import Any

HERE = pathlib.Path(__file__).resolve().parent
PAPER = HERE.parent
REPO = PAPER.parent.parent
DATA = PAPER / "data"
OUT = PAPER / "generated"
CONFIG = DATA / "quench_reuse_roots_20260817.json"
TRACE_SCRIPT = HERE / "build_formalization_prerequisite_trace.py"
TRACE_STEM = "quench_reuse_dependency"
INVENTORY_NODES = DATA / "formalization_dependency_nodes_20260817.csv"
THEORY_LINKS = DATA / "formalization_theory_evidence_links_20260817.csv"
TAXONOMY = DATA / "formalization_theory_taxonomy_20260817.json"
SOURCE_REACH = DATA / "formalization_result_reachability_20260817.csv"
SOURCE_ROOTS = DATA / "formalization_result_roots_20260817.csv"
OUT_STEM = "quench_reuse"


def run(cmd: list[str]) -> None:
    print("+", " ".join(cmd), file=sys.stderr)
    subprocess.run(cmd, cwd=REPO, check=True)


def rows(path: pathlib.Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: pathlib.Path, fieldnames: list[str], data: list[dict[str, Any]]) -> None:
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(data)


def load_theory_map() -> tuple[dict[str, str], dict[str, dict[str, Any]]]:
    taxonomy = json.loads(TAXONOMY.read_text(encoding="utf-8"))
    theories = {str(t["id"]): t for t in taxonomy["theories"]}
    decl_to_theories: dict[str, set[str]] = defaultdict(set)
    for row in rows(THEORY_LINKS):
        decl_to_theories[row["declaration"]].add(row["theory_id"])
    bad = {d: ts for d, ts in decl_to_theories.items() if len(ts) != 1}
    if bad:
        sample = list(sorted(bad.items()))[:10]
        raise SystemExit(f"formalization declarations have non-unique theory classifications: {sample}")
    return {d: next(iter(ts)) for d, ts in decl_to_theories.items()}, theories


def path_witness(root: str, target: str, deps: dict[str, list[str]]) -> list[str]:
    if root == target:
        return [root]
    q: deque[str] = deque([root])
    parent: dict[str, str | None] = {root: None}
    while q:
        cur = q.popleft()
        for nxt in deps.get(cur, []):
            if nxt in parent:
                continue
            parent[nxt] = cur
            if nxt == target:
                out = [target]
                while out[-1] != root:
                    prev = parent[out[-1]]
                    if prev is None:
                        break
                    out.append(prev)
                return list(reversed(out))
            q.append(nxt)
    return []


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--skip-build", action="store_true", help="reuse an already-built AlignedCMDS target")
    ap.add_argument("--skip-trace", action="store_true", help="only postprocess an existing generated quench_reuse_dependency_graph.json")
    args = ap.parse_args()

    OUT.mkdir(parents=True, exist_ok=True)
    if not args.skip_trace:
        cmd = [
            sys.executable,
            str(TRACE_SCRIPT.relative_to(REPO)),
            "--config", str(CONFIG.relative_to(REPO)),
            "--output-stem", TRACE_STEM,
        ]
        if args.skip_build:
            cmd.append("--skip-build")
        run(cmd)

    graph_path = OUT / f"{TRACE_STEM}_graph.json"
    if not graph_path.exists():
        raise SystemExit(f"missing compiler trace: {graph_path.relative_to(REPO)}")
    graph = json.loads(graph_path.read_text(encoding="utf-8"))

    inventory = {r["declaration"] for r in rows(INVENTORY_NODES)}
    theory_of, theories = load_theory_map()
    source_roots = rows(SOURCE_ROOTS)
    source_root_names = {r["root_declaration"] for r in source_roots}

    source_units_for_decl: dict[str, set[tuple[str, str]]] = defaultdict(set)
    for r in rows(SOURCE_REACH):
        source_units_for_decl[r["declaration"]].add((r["corpus"], r["source_id"]))

    node_by_name = {n["name"]: n for n in graph["nodes"]}
    deps: dict[str, list[str]] = defaultdict(list)
    for e in graph["local_edges"]:
        deps[e["dependent"]].append(e["prerequisite"])

    root_groups: dict[str, dict[str, Any]] = {g["id"]: g for g in graph["root_groups"]}
    root_of_group = {gid: str(g["declarations"][0]) for gid, g in root_groups.items()}

    reused = sorted(set(node_by_name) & inventory)
    reused_by_theory: dict[str, list[str]] = defaultdict(list)
    for decl in reused:
        tid = theory_of.get(decl)
        if tid is not None and bool(theories[tid].get("basic_theory")):
            reused_by_theory[tid].append(decl)

    link_rows: list[dict[str, Any]] = []
    for decl in reused:
        node = node_by_name[decl]
        tid = theory_of.get(decl, "")
        theory = theories.get(tid, {})
        source_units = sorted(source_units_for_decl.get(decl, set()))
        for gid in sorted(node.get("reached_by_groups", [])):
            root = root_of_group[gid]
            witness = path_witness(root, decl, deps)
            link_rows.append({
                "quench_root_group": gid,
                "quench_root_label": root_groups[gid].get("label", gid),
                "quench_root_declaration": root,
                "reused_declaration": decl,
                "reused_module": node.get("module", ""),
                "distance": node.get("minimum_distance_from_group_root", {}).get(gid, ""),
                "theory_id": tid,
                "theory_label": theory.get("label", ""),
                "basic_theory": int(bool(theory.get("basic_theory"))) if theory else "",
                "is_yws_dk_source_root": int(decl in source_root_names),
                "shared_source_units": ";".join(f"{c}:{s}" for c, s in source_units),
                "witness_path": " -> ".join(witness),
            })
    write_csv(
        OUT / f"{OUT_STEM}_declaration_links.csv",
        ["quench_root_group", "quench_root_label", "quench_root_declaration", "reused_declaration",
         "reused_module", "distance", "theory_id", "theory_label", "basic_theory",
         "is_yws_dk_source_root", "shared_source_units", "witness_path"],
        link_rows,
    )

    theory_rows: list[dict[str, Any]] = []
    for tid, decls in sorted(reused_by_theory.items(), key=lambda kv: theories[kv[0]]["label"]):
        groups = sorted({gid for d in decls for gid in node_by_name[d].get("reached_by_groups", [])})
        yws = sorted({sid for d in decls for corpus, sid in source_units_for_decl.get(d, set()) if corpus == "YWS2015"})
        dk = sorted({sid for d in decls for corpus, sid in source_units_for_decl.get(d, set()) if corpus == "DK1970"})
        theory_rows.append({
            "theory_id": tid,
            "theory_label": theories[tid]["label"],
            "coverage_level_in_formalization": theories[tid]["coverage_level"],
            "reused_declarations": len(decls),
            "quench_root_groups": ";".join(groups),
            "shared_yws_source_units": len(yws),
            "shared_dk_source_units": len(dk),
            "representative_declarations": ";".join(sorted(decls)[:8]),
        })
    write_csv(
        OUT / f"{OUT_STEM}_theory_summary.csv",
        ["theory_id", "theory_label", "coverage_level_in_formalization", "reused_declarations",
         "quench_root_groups", "shared_yws_source_units", "shared_dk_source_units",
         "representative_declarations"],
        theory_rows,
    )

    overlap: dict[tuple[str, str], set[str]] = defaultdict(set)
    for decl in reused:
        for key in source_units_for_decl.get(decl, set()):
            overlap[key].add(decl)
    source_rows: list[dict[str, Any]] = []
    for (corpus, sid), decls in sorted(overlap.items()):
        tids = sorted({theory_of[d] for d in decls if d in theory_of and theories[theory_of[d]].get("basic_theory")})
        source_rows.append({
            "corpus": corpus,
            "source_id": sid,
            "shared_declarations": len(decls),
            "basic_theories": ";".join(tids),
            "representative_declarations": ";".join(sorted(decls)[:8]),
        })
    write_csv(
        OUT / f"{OUT_STEM}_source_overlap.csv",
        ["corpus", "source_id", "shared_declarations", "basic_theories", "representative_declarations"],
        source_rows,
    )

    direct_source_roots = sorted(set(reused) & source_root_names)
    local_nodes = set(node_by_name)
    basic_theories = sorted(reused_by_theory)
    summary = {
        "schema": "formalization-draft2/quench-reuse-summary/v1",
        "interpretation": "Conservative lower bound from environment-visible named declaration dependencies; not a complete proof-body trace.",
        "quench_root_groups": len(root_groups),
        "quench_local_closure_declarations": len(local_nodes),
        "whole_formalization_inventory_declarations": len(inventory),
        "reused_formalization_declarations": len(reused),
        "reused_basic_theories": len(basic_theories),
        "reused_basic_theory_ids": basic_theories,
        "direct_yws_dk_source_root_declarations": direct_source_roots,
        "shared_yws_source_units": len({sid for (c, sid) in overlap if c == "YWS2015"}),
        "shared_dk_source_units": len({sid for (c, sid) in overlap if c == "DK1970"}),
    }
    (OUT / f"{OUT_STEM}_summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    md = [
        "# Quench reuse audit",
        "",
        "This is an ancillary reuse audit, not part of the YWS/Davis--Kahan source-completeness claim.",
        "The counts are conservative lower bounds because imported opaque theorem bodies can hide proof-internal helpers.",
        "",
        f"- Quench roots: {summary['quench_root_groups']}",
        f"- Project-local declarations in Quench closure: {summary['quench_local_closure_declarations']}",
        f"- Declarations overlapping the whole YWS/DK formalization inventory: {summary['reused_formalization_declarations']} / {summary['whole_formalization_inventory_declarations']}",
        f"- Basic theory areas reached in that overlap: {summary['reused_basic_theories']}",
        f"- Direct YWS/DK source-facing root declarations reused: {len(direct_source_roots)}",
        "",
        "## Reused basic theories",
        "",
    ]
    for r in theory_rows:
        md.append(f"- **{r['theory_label']}**: {r['reused_declarations']} reached declarations")
    if not theory_rows:
        md.append("- None visible in the conservative trace.")
    md += ["", "## Direct source-facing roots", ""]
    md += [f"- `{d}`" for d in direct_source_roots] or ["- None visible in the conservative trace."]
    (OUT / f"{OUT_STEM}_summary.md").write_text("\n".join(md) + "\n", encoding="utf-8")

    bundle = OUT / f"{OUT_STEM}_artifacts.zip"
    members = [
        graph_path,
        OUT / f"{TRACE_STEM}_reachability.csv",
        OUT / f"{TRACE_STEM}_edges.csv",
        OUT / f"{TRACE_STEM}_run_manifest.json",
        OUT / f"{OUT_STEM}_declaration_links.csv",
        OUT / f"{OUT_STEM}_theory_summary.csv",
        OUT / f"{OUT_STEM}_source_overlap.csv",
        OUT / f"{OUT_STEM}_summary.json",
        OUT / f"{OUT_STEM}_summary.md",
        CONFIG,
    ]
    with zipfile.ZipFile(bundle, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for path in members:
            if path.exists():
                zf.write(path, (path.relative_to(REPO)).as_posix())

    print(
        f"Quench reuse: {len(reused)} / {len(inventory)} formalization declarations; "
        f"{len(basic_theories)} basic theories; {len(direct_source_roots)} direct source roots.",
        file=sys.stderr,
    )
    print(f"Upload {bundle.relative_to(REPO)} for analysis.", file=sys.stderr)


if __name__ == "__main__":
    main()
