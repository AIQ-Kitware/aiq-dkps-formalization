#!/usr/bin/env python3
"""Audit the recursive Davis--Kahan 1970 formalization frontier.

The audit has two modes.

Static mode validates the manifest, dependency graph, source-census coverage,
module paths, and textual declaration presence.  Lean mode additionally imports
the frontier aggregate, checks every declaration, and runs `#print axioms` so a
node is counted as grounded only when its entire Lean dependency closure is
free of `sorryAx`.
"""
from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import shutil
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "dev/davis-kahan-1970-frontier.json"
CENSUS = ROOT / "dev/davis-kahan-1970-full-source-census.json"
PROBE = ROOT / "dev/.davis-kahan-frontier-probe.lean"
REPORT = ROOT / "dev/davis-kahan-1970-frontier-status.md"


def load_json(path: pathlib.Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf8"))


def module_path(module: str) -> pathlib.Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def validate_manifest(data: dict[str, Any]) -> list[str]:
    problems: list[str] = []
    nodes = data.get("nodes")
    if not isinstance(nodes, list):
        return ["manifest.nodes must be a list"]
    by_id: dict[str, dict[str, Any]] = {}
    by_decl: dict[str, str] = {}
    for index, node in enumerate(nodes):
        where = f"nodes[{index}]"
        for key in ("id", "title", "kind", "module", "declaration", "dependencies"):
            if key not in node:
                problems.append(f"{where}: missing {key}")
        node_id = node.get("id")
        if not isinstance(node_id, str) or not node_id:
            problems.append(f"{where}: id must be a nonempty string")
            continue
        if node_id in by_id:
            problems.append(f"duplicate node id {node_id!r}")
        by_id[node_id] = node
        decl = node.get("declaration")
        if isinstance(decl, str):
            if decl in by_decl:
                problems.append(
                    f"declaration {decl!r} is assigned to both {by_decl[decl]!r} and {node_id!r}")
            by_decl[decl] = node_id
        if not isinstance(node.get("dependencies", []), list):
            problems.append(f"{node_id}: dependencies must be a list")
        if not isinstance(node.get("source_census_ids", []), list):
            problems.append(f"{node_id}: source_census_ids must be a list")
    for node_id, node in by_id.items():
        for dep in node.get("dependencies", []):
            if dep not in by_id:
                problems.append(f"{node_id}: unknown dependency {dep!r}")
        path = module_path(node.get("module", ""))
        if not path.exists():
            problems.append(f"{node_id}: module file does not exist: {path.relative_to(ROOT)}")
    # Cycle detection gives a useful failure rather than recursive status loops.
    visiting: set[str] = set()
    visited: set[str] = set()
    stack: list[str] = []

    def visit(node_id: str) -> None:
        if node_id in visited:
            return
        if node_id in visiting:
            start = stack.index(node_id)
            problems.append("dependency cycle: " + " -> ".join(stack[start:] + [node_id]))
            return
        visiting.add(node_id)
        stack.append(node_id)
        for dep in by_id[node_id].get("dependencies", []):
            if dep in by_id:
                visit(dep)
        stack.pop()
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in by_id:
        visit(node_id)
    return problems


def textual_presence(node: dict[str, Any]) -> bool:
    path = module_path(node["module"])
    if not path.exists():
        return False
    text = path.read_text(encoding="utf8")
    short = node["declaration"].split(".")[-1]
    pattern = re.compile(
        rf"(?m)^\s*(?:noncomputable\s+)?(?:private\s+)?"
        rf"(?:def|abbrev|structure|class|theorem|lemma|opaque|alias)\s+{re.escape(short)}\b"
    )
    return bool(pattern.search(text))


def required_census_ids(manifest: dict[str, Any], census: dict[str, Any]) -> set[str]:
    terminal = set(manifest.get("coverage_policy", {}).get("census_terminal_statuses", []))
    required: set[str] = set()
    for item in census.get("items", []):
        if item.get("status") not in terminal:
            required.add(item["id"])
    return required


def mapped_census_ids(manifest: dict[str, Any]) -> set[str]:
    return {
        item
        for node in manifest.get("nodes", [])
        for item in node.get("source_census_ids", [])
    }


def write_probe(manifest: dict[str, Any]) -> None:
    root_import = manifest["root_import"]
    lines = [f"import {root_import}\n\n"]
    for node in manifest["nodes"]:
        node_id = node["id"]
        decl = node["declaration"]
        lines.extend([
            f'#eval IO.println "FRONTIER_BEGIN:{node_id}"\n',
            f"#check @{decl}\n",
            f"#print axioms {decl}\n",
            f'#eval IO.println "FRONTIER_END:{node_id}"\n\n',
        ])
    # Canary ensures an output parser change cannot silently classify all names as resolved.
    lines.extend([
        '#eval IO.println "FRONTIER_BEGIN:__canary__"\n',
        "#check @ForMathlib.DavisKahan.Experimental.Frontier.ThisNameMustNeverResolve\n",
        '#eval IO.println "FRONTIER_END:__canary__"\n',
    ])
    PROBE.write_text("".join(lines), encoding="utf8")


def run_lean_probe(manifest: dict[str, Any]) -> tuple[dict[str, dict[str, Any]], str]:
    write_probe(manifest)
    result = subprocess.run(
        ["lake", "env", "lean", str(PROBE.relative_to(ROOT))],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    output = result.stdout
    # Markers are printed even when the command between them reports an error.
    sections: dict[str, list[str]] = collections.defaultdict(list)
    current: str | None = None
    begin = re.compile(r"FRONTIER_BEGIN:([^\s]+)")
    end = re.compile(r"FRONTIER_END:([^\s]+)")
    for line in output.splitlines():
        mb = begin.search(line)
        if mb:
            current = mb.group(1)
            continue
        me = end.search(line)
        if me:
            current = None
            continue
        if current is not None:
            sections[current].append(line)
    status: dict[str, dict[str, Any]] = {}
    marker = manifest.get("coverage_policy", {}).get("admission_marker", "sorryAx")
    error_re = re.compile(r"\berror(?:\(|:)", re.I)
    unknown_re = re.compile(r"unknown identifier|invalid field|unknown constant", re.I)
    for node in manifest["nodes"] + [{"id": "__canary__"}]:
        node_id = node["id"]
        chunk = "\n".join(sections.get(node_id, []))
        has_error = bool(error_re.search(chunk) or unknown_re.search(chunk))
        resolved = bool(chunk) and not has_error
        admitted = marker in chunk if resolved else None
        status[node_id] = {
            "resolved": resolved,
            "admitted": admitted,
            "output": chunk,
        }
    if status["__canary__"]["resolved"]:
        raise RuntimeError(
            "frontier probe parser is broken: the deliberately unknown canary resolved")
    status.pop("__canary__", None)
    return status, output


def compute_recursive_status(
    manifest: dict[str, Any], lean: dict[str, dict[str, Any]] | None
) -> dict[str, dict[str, Any]]:
    by_id = {n["id"]: n for n in manifest["nodes"]}
    result: dict[str, dict[str, Any]] = {}

    def one(node_id: str) -> dict[str, Any]:
        if node_id in result:
            return result[node_id]
        node = by_id[node_id]
        text_present = textual_presence(node)
        if lean is None:
            resolved: bool | None = None
            admitted: bool | None = None
            local_grounded: bool | None = None
        else:
            resolved = bool(lean[node_id]["resolved"])
            admitted = lean[node_id]["admitted"]
            local_grounded = resolved and admitted is False
        dependencies = [one(dep) for dep in node.get("dependencies", [])]
        if lean is None:
            recursive_grounded: bool | None = None
        else:
            recursive_grounded = bool(local_grounded) and all(
                dep["recursive_grounded"] for dep in dependencies)
        info = {
            "text_present": text_present,
            "resolved": resolved,
            "admitted": admitted,
            "local_grounded": local_grounded,
            "recursive_grounded": recursive_grounded,
            "dependencies_resolved": (
                None if lean is None else all(dep["resolved"] for dep in dependencies)
            ),
        }
        result[node_id] = info
        return info

    for node_id in by_id:
        one(node_id)
    return result


def summary(
    manifest: dict[str, Any], census: dict[str, Any],
    status: dict[str, dict[str, Any]], lean_used: bool
) -> dict[str, Any]:
    required = required_census_ids(manifest, census)
    mapped = mapped_census_ids(manifest)
    source_nodes = [n for n in manifest["nodes"] if n["kind"] == "source"]
    all_nodes = manifest["nodes"]
    return {
        "lean_used": lean_used,
        "nodes_total": len(all_nodes),
        "nodes_textually_present": sum(status[n["id"]]["text_present"] for n in all_nodes),
        "nodes_resolved": (
            sum(bool(status[n["id"]]["resolved"]) for n in all_nodes) if lean_used else None
        ),
        "nodes_admission_free": (
            sum(status[n["id"]]["admitted"] is False for n in all_nodes) if lean_used else None
        ),
        "nodes_recursively_grounded": (
            sum(bool(status[n["id"]]["recursive_grounded"]) for n in all_nodes)
            if lean_used else None
        ),
        "source_nodes_total": len(source_nodes),
        "source_nodes_resolved": (
            sum(bool(status[n["id"]]["resolved"]) for n in source_nodes)
            if lean_used else None
        ),
        "source_nodes_recursively_grounded": (
            sum(bool(status[n["id"]]["recursive_grounded"]) for n in source_nodes)
            if lean_used else None
        ),
        "census_rows_requiring_frontier": len(required),
        "census_rows_mapped": len(required & mapped),
        "census_rows_unmapped": sorted(required - mapped),
        "manifest_census_ids_unknown": sorted(mapped - {i["id"] for i in census.get("items", [])}),
    }


def render_report(
    manifest: dict[str, Any], census: dict[str, Any],
    status: dict[str, dict[str, Any]], totals: dict[str, Any]
) -> str:
    lines = [
        "# Davis--Kahan 1970 frontier status",
        "",
        "Generated by `scripts/check_davis_kahan_frontier.py`.",
        "",
        "## Summary",
        "",
        f"- Manifest nodes: **{totals['nodes_total']}**",
        f"- Textually present: **{totals['nodes_textually_present']}**",
        f"- Census rows requiring frontier coverage: **{totals['census_rows_requiring_frontier']}**",
        f"- Census rows mapped: **{totals['census_rows_mapped']}**",
    ]
    if totals["lean_used"]:
        lines.extend([
            f"- Declarations resolving in Lean: **{totals['nodes_resolved']}**",
            f"- Declarations with admission-free Lean closure: **{totals['nodes_admission_free']}**",
            f"- Recursively grounded manifest nodes: **{totals['nodes_recursively_grounded']}**",
            f"- Source endpoints resolving: **{totals['source_nodes_resolved']} / {totals['source_nodes_total']}**",
            f"- Source endpoints recursively grounded: **{totals['source_nodes_recursively_grounded']} / {totals['source_nodes_total']}**",
        ])
    else:
        lines.append("- Lean probe: **not run**")
    if totals["census_rows_unmapped"]:
        lines.extend(["", "Unmapped census rows:"])
        lines.extend(f"- `{x}`" for x in totals["census_rows_unmapped"])
    lines.extend([
        "",
        "## Nodes",
        "",
        "| Node | Kind | Priority | Text | Resolves | Admission-free | Recursive |",
        "|---|---|---:|:---:|:---:|:---:|:---:|",
    ])
    def mark(value: Any) -> str:
        if value is True:
            return "yes"
        if value is False:
            return "no"
        return "?"
    for node in manifest["nodes"]:
        st = status[node["id"]]
        admission_free = None if st["admitted"] is None else not st["admitted"]
        lines.append(
            f"| `{node['id']}` | {node['kind']} | {node.get('priority','')} | "
            f"{mark(st['text_present'])} | {mark(st['resolved'])} | "
            f"{mark(admission_free)} | {mark(st['recursive_grounded'])} |"
        )
    lines.extend(["", "## Dependency edges", ""])
    for node in manifest["nodes"]:
        deps = node.get("dependencies", [])
        if deps:
            lines.append(f"- `{node['id']}` <- " + ", ".join(f"`{d}`" for d in deps))
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--check", action="store_true",
                        help="fail if coverage is incomplete, a declaration is unresolved, or a source endpoint is not recursively grounded")
    parser.add_argument("--no-lean", action="store_true",
                        help="run only manifest and textual checks")
    parser.add_argument("--keep-probe", action="store_true")
    parser.add_argument("--write-report", action="store_true")
    args = parser.parse_args()

    manifest = load_json(MANIFEST)
    census = load_json(CENSUS)
    problems = validate_manifest(manifest)
    lean_available = shutil.which("lake") is not None and not args.no_lean
    lean_status: dict[str, dict[str, Any]] | None = None
    raw_output = ""
    if not problems and lean_available:
        try:
            lean_status, raw_output = run_lean_probe(manifest)
        except Exception as ex:
            problems.append(f"Lean probe failed: {ex}")
        finally:
            if not args.keep_probe and PROBE.exists():
                PROBE.unlink()
    status = compute_recursive_status(manifest, lean_status)
    totals = summary(manifest, census, status, lean_status is not None)
    if totals["census_rows_unmapped"]:
        problems.append(
            "unmapped source-census rows: " + ", ".join(totals["census_rows_unmapped"]))
    if totals["manifest_census_ids_unknown"]:
        problems.append(
            "manifest references unknown census rows: " +
            ", ".join(totals["manifest_census_ids_unknown"]))
    missing_text = [n["id"] for n in manifest["nodes"] if not status[n["id"]]["text_present"]]
    if missing_text:
        problems.append("declarations not found textually: " + ", ".join(missing_text))
    if lean_status is not None:
        unresolved = [n["id"] for n in manifest["nodes"] if not status[n["id"]]["resolved"]]
        if unresolved:
            problems.append("declarations unresolved in Lean: " + ", ".join(unresolved))

    report = render_report(manifest, census, status, totals)
    if args.write_report:
        REPORT.write_text(report, encoding="utf8")

    payload = {
        "summary": totals,
        "problems": problems,
        "nodes": {n["id"]: status[n["id"]] for n in manifest["nodes"]},
    }
    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        print(
            f"Frontier: {totals['nodes_textually_present']}/{totals['nodes_total']} declarations textually present; "
            f"{totals['census_rows_mapped']}/{totals['census_rows_requiring_frontier']} required census rows mapped")
        if lean_status is not None:
            print(
                f"Lean: {totals['nodes_resolved']}/{totals['nodes_total']} resolve; "
                f"{totals['nodes_recursively_grounded']}/{totals['nodes_total']} recursively grounded; "
                f"{totals['source_nodes_recursively_grounded']}/{totals['source_nodes_total']} source endpoints grounded")
        else:
            print("Lean: not available; recursive proof-closure status is unknown")
        if problems:
            print("Problems:")
            for problem in problems:
                print(f"  - {problem}")
        if args.write_report:
            print(f"Wrote {REPORT.relative_to(ROOT)}")

    if args.check:
        if problems:
            return 1
        if lean_status is None:
            print("--check requires a Lean probe unless --no-lean is used only for diagnostics", file=sys.stderr)
            return 2
        ungrounded_sources = [
            n["id"] for n in manifest["nodes"]
            if n["kind"] == "source" and not status[n["id"]]["recursive_grounded"]
        ]
        return 1 if ungrounded_sources else 0
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main())
