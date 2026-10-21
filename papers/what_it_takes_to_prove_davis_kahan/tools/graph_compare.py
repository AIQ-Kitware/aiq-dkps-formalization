#!/usr/bin/env python3
"""Compare Lean elaboration-backed proof dependencies at two historical revisions.

Reads two saved `leanq graph-index` or `graph-slice` files, never source-text
regexes. Exposes observed graph changes, not mathematical necessity or theorem
identity. Supports explicit, audited old->new declaration-name correspondences.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import sys
from collections import Counter, defaultdict, deque
from pathlib import Path


class CompareError(Exception):
    pass


def read_json(path: Path) -> dict:
    result = json.loads(path.read_text(encoding="utf-8"))
    if result.get("payloadKind") not in ("graph-slice", "semantic-index"):
        raise CompareError(f"{path}: expected leanq graph-slice or semantic-index")
    if result.get("edgeDirection") != "dependency-to-consumer":
        raise CompareError(f"{path}: graph direction must be dependency-to-consumer")
    if not isinstance(result.get("nodes"), list) or not isinstance(result.get("edges"), list):
        raise CompareError(f"{path}: malformed nodes/edges")
    return result


def alias_map(path: Path | None, args: list[str]) -> dict[str, str]:
    result = {}
    if path:
        with path.open(newline="", encoding="utf-8") as stream:
            for row in csv.DictReader(stream):
                if not row.get("old") or not row.get("new"):
                    raise CompareError(f"{path}: alias row requires old and new names")
                if row.get("review_status") != "reviewed" or not row.get("evidence_id"):
                    raise CompareError(f"{path}: alias requires reviewed status and immutable evidence_id")
                result[row["old"]] = row["new"]
    for spec in args:
        old, sep, new = spec.partition("=")
        if not sep or not old or not new:
            raise CompareError(f"invalid --alias {spec!r}; expected OLD=NEW")
        result[old] = new
    if len(set(result.values())) != len(result):
        raise CompareError("two old names map to the same new declaration; review aliases")
    return result


def select_graph(obj: dict, root: str | None) -> tuple[dict[str, dict], set[tuple[str, str]], str]:
    nodes = {}
    for item in obj["nodes"]:
        name = item.get("id", item.get("name"))
        if not isinstance(name, str):
            raise CompareError("graph node missing declaration name")
        if name in nodes:
            raise CompareError(f"duplicate graph node {name}")
        nodes[name] = item
    edges = set()
    for row in obj["edges"]:
        src, dst = row.get("source"), row.get("target")
        if src in nodes and dst in nodes:
            edges.add((src, dst))
    candidate_roots = obj.get("targets", [])
    if root is None and len(candidate_roots) == 1:
        root = candidate_roots[0]
    if not root:
        raise CompareError("explicit --old-root/--new-root required for whole-project or multi-root graphs")
    if root not in nodes:
        raise CompareError(f"graph does not contain chosen declaration {root!r}")
    parents = defaultdict(set)
    for dep, consumer in edges:
        parents[consumer].add(dep)
    selected = {root}
    queue = deque([root])
    while queue:
        for dep in parents[queue.popleft()]:
            if dep not in selected:
                selected.add(dep)
                queue.append(dep)
    return ({name: nodes[name] for name in selected},
            {(a, b) for a, b in edges if a in selected and b in selected}, root)


def renamed_graph(nodes: dict[str, dict], edges: set[tuple[str, str]],
                  renames: dict[str, str]) -> tuple[dict[str, dict], set[tuple[str, str]]]:
    translated = {}
    for old, node in nodes.items():
        name = renames.get(old, old)
        if name in translated:
            raise CompareError(f"renamed graph collides at {name}; review declared correspondences")
        copy = dict(node)
        copy["_original_id"] = old
        if isinstance(copy.get("typeDeps"), list):
            copy["typeDeps"] = [renames.get(dep, dep) for dep in copy["typeDeps"]]
        translated[name] = copy
    return translated, {(renames.get(src, src), renames.get(dst, dst)) for src, dst in edges}


def edge_role(nodes: dict[str, dict], edge: tuple[str, str]) -> str:
    dep, consumer = edge
    row = nodes[consumer]
    typed = row.get("typeDeps")
    if typed is None:
        return "unknown"
    return "type" if dep in typed else "proof"


def group(name: str, item: dict) -> str:
    module = item.get("module") or name
    if module.startswith("ForTauCeti"):
        return "ForTauCeti"
    if module.startswith("DavisKahan"):
        return "DavisKahan"
    if module.startswith("Mathlib"):
        return "Mathlib"
    if module.startswith("TauCeti"):
        return "TauCeti library"
    return "Other"


def compare(old_obj: dict, new_obj: dict, old_root: str | None,
            new_root: str | None, renames: dict[str, str]) -> dict:
    a, ae, aroot = select_graph(old_obj, old_root)
    b, be, broot = select_graph(new_obj, new_root)
    a, ae = renamed_graph(a, ae, renames)
    if renames.get(aroot, aroot) != broot:
        raise CompareError("root declarations do not match; provide an explicit --alias OLD=NEW only after semantic review")
    shared_nodes = set(a) & set(b)
    removed_nodes = sorted(set(a) - set(b))
    added_nodes = sorted(set(b) - set(a))
    removed_edges = sorted(ae - be)
    added_edges = sorted(be - ae)
    role_changes = []
    for edge in sorted(ae & be):
        old_role, new_role = edge_role(a, edge), edge_role(b, edge)
        if old_role != new_role:
            role_changes.append({"dependency": edge[0], "consumer": edge[1],
                                 "old_role": old_role, "new_role": new_role})
    metadata_changes = []
    for name in sorted(shared_nodes):
        keys = ("kind", "module", "library", "sorried", "axioms")
        diff = {key: {"old": a[name].get(key), "new": b[name].get(key)} for key in keys
                if a[name].get(key) != b[name].get(key)}
        if diff:
            metadata_changes.append({"name": name, "fields": diff})
    return {
        "schema": "dk-proof-archaeology/graph-comparison/v1",
        "old_root": aroot, "new_root": broot,
        "investigator_supplied_alias_mapping": renames,
        "old_node_count": len(a), "new_node_count": len(b),
        "old_direct_edge_count": len(ae), "new_direct_edge_count": len(be),
        "added_nodes": added_nodes, "removed_nodes": removed_nodes,
        "added_node_groups": dict(sorted(Counter(group(name, b[name]) for name in added_nodes).items())),
        "removed_node_groups": dict(sorted(Counter(group(name, a[name]) for name in removed_nodes).items())),
        "added_direct_edges": [{"dependency": x, "consumer": y, "role": edge_role(b, (x, y))}
                               for x, y in added_edges],
        "removed_direct_edges": [{"dependency": x, "consumer": y, "role": edge_role(a, (x, y))}
                                 for x, y in removed_edges],
        "direct_edge_role_changes": role_changes,
        "declaration_metadata_changes": metadata_changes,
        "old_unresolved_prefixes": old_obj.get("unresolvedDependencyPrefixes"),
        "new_unresolved_prefixes": new_obj.get("unresolvedDependencyPrefixes"),
        "caveats": [
            "Comparison is only valid if each graph was actually indexed at its claimed revision; the JSON file alone does not attest that.",
            "Name-preserving changes to theorem statements or proof terms need statement hashes or independent source inspection.",
            "Type/proof roles are 'unknown' when the index predates typeDeps; role transitions from unknown are not mathematical changes.",
            "Renames are investigator-proposed correspondence, not proof of theorem equivalence.",
            "One compiler-derived proof closure is not a minimal mathematical premise set."
        ]
    }


def statement_delta(old_path: Path, new_path: Path, old_name: str, new_name: str,
                    renames: dict[str, str]) -> dict:
    """Compare the existing leanq statement-sidecar records, not source text."""
    def load(path: Path) -> dict[str, dict]:
        payload = json.loads(path.read_text(encoding="utf-8"))
        if payload.get("payloadKind") != "statement-closure":
            raise CompareError(f"{path}: expected a leanq statement-closure payload")
        records = {r["name"]: r for r in payload.get("records", [])}
        if len(records) != len(payload.get("records", [])):
            raise CompareError(f"{path}: duplicate statement records")
        return records

    left, right = load(old_path), load(new_path)
    if old_name not in left or new_name not in right:
        raise CompareError("selected root missing from one statement closure")
    a, b = left[old_name], right[new_name]
    if a.get("missing") or b.get("missing"):
        raise CompareError("selected root has a missing statement record")

    def status(x, y):
        if not x or not y:
            return "unavailable"
        return "unchanged" if x == y else "changed"

    mapped = {renames.get(k, k): v for k, v in left.items()}
    common = set(mapped) & set(right)
    altered = []
    for name in sorted(common):
        x, y = mapped[name], right[name]
        before = x.get("typeExprHash")
        after = y.get("typeExprHash")
        if before and after and before != after:
            altered.append({"name": name, "old_typeExprHash": before,
                            "new_typeExprHash": after})

    return {
        "old_sidecar_sha256": hashlib.sha256(old_path.read_bytes()).hexdigest(),
        "new_sidecar_sha256": hashlib.sha256(new_path.read_bytes()).hexdigest(),
        "old_root": old_name, "new_root": new_name,
        "structural_type_hash": status(a.get("typeExprHash"), b.get("typeExprHash")),
        "printed_type_hash": status(a.get("typeTextSha256"), b.get("typeTextSha256")),
        "old_structural_hash": a.get("typeExprHash"),
        "new_structural_hash": b.get("typeExprHash"),
        "old_signature": a.get("signature", ""),
        "new_signature": b.get("signature", ""),
        "old_binders": a.get("binders", []),
        "new_binders": b.get("binders", []),
        "removed_closure_names": sorted(set(mapped) - set(right)),
        "added_closure_names": sorted(set(right) - set(mapped)),
        "changed_named_definition_types": altered,
        "caveat": "Lean type hashes refer to the elaborated term in the corresponding indexed environment. An unchanged hash is not evidence that unfolded definitions or imports retained the same meaning; a changed signature needs mathematical review."
    }


def write_markdown(obj: dict, path: Path) -> None:
    def listed(items: list, key: str | None = None, cap: int = 50) -> list[str]:
        shown = items[:cap]
        out = ["- " + (str(x[key]) if key else str(x)) for x in shown]
        if len(items) > cap:
            out.append(f"- ... {len(items) - cap} more in JSON")
        return out or ["- none"]
    lines = ["# Revision-to-revision Lean proof graph comparison", "",
             f"Old root: `{obj['old_root']}`", f"New root: `{obj['new_root']}`", "",
             "These are declaration-level proof observations, not proofs of mathematical independence or necessity.",
             f"Claimed commits (not verified by this tool): `{obj.get('old_claimed_git_commit') or 'not provided'}` / `{obj.get('new_claimed_git_commit') or 'not provided'}`.",
             f"Input SHA256: `{obj.get('old_graph_sha256') or 'not attached'}` / `{obj.get('new_graph_sha256') or 'not attached'}`.", "",
             "| Measure | Old | New |", "| --- | ---: | ---: |",
             f"| Named declarations | {obj['old_node_count']} | {obj['new_node_count']} |",
             f"| Direct edges | {obj['old_direct_edge_count']} | {obj['new_direct_edge_count']} |",
             "", "## Dependencies added", *listed(obj["added_nodes"]),
             "", "## Dependencies removed", *listed(obj["removed_nodes"]),
             "", "## Direct proof-edge additions", *listed(obj["added_direct_edges"], cap=80),
             "", "## Direct proof-edge removals", *listed(obj["removed_direct_edges"], cap=80),
             "", "## Edge role changes", *listed(obj["direct_edge_role_changes"]),
             "", "## Source and interpretation checks still needed",
             "1. Verify the two graph files were generated from distinct pinned commits and compatible Lean/Mathlib environments.",
             "2. Compare elaborated statement hashes and the mathematical hypotheses/conclusions, especially for renamed declarations.",
             "3. Classify significant edge changes as mathematical restructuring, abstraction/implementation change, or indeterminate.",
             "4. Find the primary mathematical and historical sources before assigning ancestry.",
             "", "## Limitations", *["- " + s for s in obj["caveats"]], ""]
    stmt = obj.get("statement_comparison")
    if stmt:
        lines.extend(["", "## Elaborated theorem statement comparison", "",
                      f"Structural type hash: **{stmt['structural_type_hash']}**; "
                      f"printed type hash: **{stmt['printed_type_hash']}**.",
                      f"Statement-closure names added: {len(stmt['added_closure_names'])}; removed: {len(stmt['removed_closure_names'])}.",
                      "", "**Before:**", "", "```lean", stmt["old_signature"], "```",
                      "", "**After:**", "", "```lean", stmt["new_signature"], "```",
                      "", "These hashes are evidence about indexed elaborated terms; neither equality nor inequality automatically determines mathematical equivalence.", ""])
    path.write_text("\n".join(lines), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--old", type=Path, required=True, help="old leanq semantic-index or graph-slice JSON")
    p.add_argument("--new", type=Path, required=True, help="new leanq semantic-index or graph-slice JSON")
    p.add_argument("--old-root", help="exact old declaration")
    p.add_argument("--new-root", help="exact new declaration")
    p.add_argument("--alias", action="append", default=[], help="investigator-reviewed OLD=NEW declaration correspondence")
    p.add_argument("--alias-file", type=Path, help="CSV of reviewed old/new aliases with evidence identifiers")
    p.add_argument("--old-statement", type=Path, help="optional old leanq statement-closure JSON")
    p.add_argument("--new-statement", type=Path, help="optional new leanq statement-closure JSON")
    p.add_argument("--old-commit", help="optional claimed historical SHA; NOT checked against graph contents")
    p.add_argument("--new-commit", help="optional claimed historical SHA; NOT checked against graph contents")
    p.add_argument("--out", type=Path, required=True, help="output JSON; Markdown report alongside")
    args = p.parse_args(argv)
    try:
        if bool(args.old_statement) != bool(args.new_statement):
            raise CompareError("provide both --old-statement and --new-statement, or neither")
        a, b = read_json(args.old), read_json(args.new)
        result = compare(a, b, args.old_root, args.new_root,
                         alias_map(args.alias_file, args.alias))
        if args.old_statement and args.new_statement:
            result["statement_comparison"] = statement_delta(
                args.old_statement, args.new_statement,
                result["old_root"], result["new_root"],
                result["investigator_supplied_alias_mapping"])
        result["old_graph_path"] = str(args.old)
        result["new_graph_path"] = str(args.new)
        result["old_graph_sha256"] = hashlib.sha256(args.old.read_bytes()).hexdigest()
        result["new_graph_sha256"] = hashlib.sha256(args.new.read_bytes()).hexdigest()
        result["old_claimed_git_commit"] = args.old_commit
        result["new_claimed_git_commit"] = args.new_commit
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        md_path = args.out.with_suffix(".md")
        write_markdown(result, md_path)
        print(args.out)
        print(md_path)
        return 0
    except (CompareError, OSError, ValueError, KeyError) as exc:
        print(f"graph-compare: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
