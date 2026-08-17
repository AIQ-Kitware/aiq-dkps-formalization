#!/usr/bin/env python3
"""Build auditable whole-formalization prerequisite/theory summaries.

The checked-in data has two deliberately separate layers:

1. Compiler facts: source-unit roots, project-local declaration nodes/edges, and
   source-unit reachability. These are rebuildable from Lean's elaborated environment.
2. Human classification: an exact module -> theory map plus qualitative, explicitly
   scoped coverage labels. These are scientific annotations, not compiler facts.

The generated paper-facing summaries are joins/aggregations of those layers.  A future
trace that reaches an unclassified module is an error: we do not silently guess a
mathematical theory from a pathname.
"""
from __future__ import annotations

import argparse
import collections
import csv
import hashlib
import json
import pathlib
import subprocess
import sys
import tempfile
import zipfile
from collections import deque
from typing import Any, Iterable

HERE = pathlib.Path(__file__).resolve().parent
PAPER = HERE.parent
REPO = PAPER.parent.parent
DATA = PAPER / "data"
GENERATED = PAPER / "generated"
SCOPE_PATH = DATA / "formalization_scope_20260817.json"
TAXONOMY_PATH = DATA / "formalization_theory_taxonomy_20260817.json"
ROOTS_PATH = DATA / "formalization_result_roots_20260817.csv"
NODES_PATH = DATA / "formalization_dependency_nodes_20260817.csv"
EDGES_PATH = DATA / "formalization_dependency_edges_20260817.csv"
REACH_PATH = DATA / "formalization_result_reachability_20260817.csv"
MODULE_MAP_PATH = DATA / "formalization_module_theory_map_20260817.csv"
DECL_OVERRIDE_PATH = DATA / "formalization_declaration_theory_overrides_20260817.csv"
MODULE_INVENTORY_PATH = DATA / "formalization_module_inventory_20260817.csv"
EVIDENCE_PATH = DATA / "formalization_theory_evidence_links_20260817.csv"
MANIFEST_PATH = DATA / "formalization_trace_manifest_20260817.json"
DECL_INDEX = REPO / "tools" / "leanq" / "src" / "leanq" / "lean" / "decl_index.lean"


def read_csv(path: pathlib.Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: pathlib.Path, rows: Iterable[dict[str, Any]], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def run(cmd: list[str], *, capture: bool = False) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(cmd), file=sys.stderr)
    return subprocess.run(
        cmd,
        cwd=REPO,
        check=True,
        text=True,
        stdout=subprocess.PIPE if capture else None,
    )


def git_value(*args: str) -> str | None:
    try:
        return subprocess.check_output(["git", *args], cwd=REPO, text=True, stderr=subprocess.DEVNULL).strip()
    except subprocess.CalledProcessError:
        return None


def project_source_fingerprint() -> tuple[str, int]:
    skip_top = {".git", ".lake", "external", "retired"}
    paths = []
    for path in REPO.rglob("*.lean"):
        rel = path.relative_to(REPO)
        if rel.parts and rel.parts[0] in skip_top:
            continue
        if ".lake" in rel.parts:
            continue
        paths.append(path)
    h = hashlib.sha256()
    for path in sorted(paths, key=lambda p: p.relative_to(REPO).as_posix()):
        rel = path.relative_to(REPO).as_posix().encode()
        data = path.read_bytes()
        h.update(len(rel).to_bytes(8, "big")); h.update(rel)
        h.update(len(data).to_bytes(8, "big")); h.update(data)
    return h.hexdigest(), len(paths)


def _semantic_index_signature(row: dict[str, Any]) -> tuple[str, tuple[str, ...]]:
    return str(row.get("kind", "")), tuple(sorted({str(x) for x in row.get("deps", [])}))


def _module_candidates(row: dict[str, Any]) -> list[str]:
    c = row.get("module_candidates")
    if isinstance(c, list):
        return sorted({str(x) for x in c if str(x)})
    m = str(row.get("module", ""))
    return [m] if m else []


def compiler_index(scope: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Run the existing leanq indexer and merge benign duplicate module claims."""
    if not DECL_INDEX.exists():
        raise SystemExit(f"missing compiler indexer: {DECL_INDEX.relative_to(REPO)}")
    with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".modules", delete=False) as f:
        modules_path = pathlib.Path(f.name)
        for module in scope["import_modules"]:
            f.write(str(module) + "\n")
    try:
        by_name: dict[str, dict[str, Any]] = {}
        for prefix in scope["project_module_prefixes"]:
            p = run([
                "lake", "env", "lean", "--run", str(DECL_INDEX),
                str(prefix), str(modules_path), "deps",
            ], capture=True)
            rows = []
            for raw in p.stdout.splitlines():
                if raw.strip():
                    rows.append(json.loads(raw))
            print(f"indexed {len(rows)} declarations under module prefix {prefix}", file=sys.stderr)
            for incoming in rows:
                row = dict(incoming)
                name = str(row["name"])
                module = str(row.get("module", ""))
                old = by_name.get(name)
                if old is None:
                    row["module_candidates"] = [module] if module else []
                    by_name[name] = row
                    continue
                if _semantic_index_signature(old) != _semantic_index_signature(row):
                    raise SystemExit(f"conflicting compiler index payload for {name}")
                candidates = set(_module_candidates(old))
                if module:
                    candidates.add(module)
                old["module_candidates"] = sorted(candidates)
        return by_name
    finally:
        modules_path.unlink(missing_ok=True)


def expected_root_rows(scope: dict[str, Any]) -> list[dict[str, str]]:
    """Derive the complete source-facing root set from canonical repo registries."""
    rows: list[dict[str, str]] = []
    for corpus in scope["corpora"]:
        cid = str(corpus["id"])
        rel = pathlib.Path(str(corpus["registry_path"]))
        payload = json.loads((REPO / rel).read_text(encoding="utf-8"))
        items = payload[str(corpus["items_key"])]
        result_kinds = set(map(str, corpus.get("result_source_kinds", [])))
        extension_ids = set(map(str, corpus.get("extension_ids", [])))
        for item in items:
            sid = str(item["id"])
            if cid == "YWS2015":
                source_kind = str(item.get("source_kind", ""))
                source_relation = "extension" if sid in extension_ids else "published_source"
                unit_role = "result" if source_kind in result_kinds else "supporting_source_surface"
                disposition = str(item.get("status", ""))
            elif cid == "DK1970":
                source_kind = str(item.get("result_kind", ""))
                source_relation = "published_result"
                unit_role = "result"
                disposition = str(item.get("disposition", ""))
            else:
                raise SystemExit(f"unsupported corpus in scope file: {cid}")
            for decl in item.get("lean_declarations", []):
                rows.append({
                    "corpus": cid,
                    "source_id": sid,
                    "source_anchor": str(item.get("source_anchor", "")),
                    "title": str(item.get("title", "")),
                    "source_kind": source_kind,
                    "source_relation": source_relation,
                    "source_unit_role": unit_role,
                    "verification": str(item.get("verification", "")),
                    "disposition": disposition,
                    "root_declaration": str(decl),
                    "registry_path": rel.as_posix(),
                })
    return rows


def trace_source_units(
    roots: list[dict[str, str]], index: dict[str, dict[str, Any]]
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[dict[str, Any]]]:
    missing = sorted({r["root_declaration"] for r in roots if r["root_declaration"] not in index})
    if missing:
        raise SystemExit("registered source declarations absent from compiler index:\n  " + "\n  ".join(missing))
    grouped: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
    for r in roots:
        grouped[(r["corpus"], r["source_id"])].add(r["root_declaration"])
    reached_all: set[str] = set()
    edge_all: set[tuple[str, str]] = set()
    reach_rows: list[dict[str, Any]] = []
    for (corpus, source_id), group_roots in sorted(grouped.items()):
        dist: dict[str, int] = {}
        q: deque[tuple[str, int]] = deque((n, 0) for n in sorted(group_roots))
        while q:
            name, d = q.popleft()
            if name in dist and dist[name] <= d:
                continue
            dist[name] = d
            reached_all.add(name)
            for dep in index[name].get("deps", []):
                dep = str(dep)
                if dep in index:
                    edge_all.add((name, dep))
                    q.append((dep, d + 1))
        for name, d in sorted(dist.items()):
            reach_rows.append({
                "corpus": corpus,
                "source_id": source_id,
                "declaration": name,
                "min_distance": d,
                "is_root": int(name in group_roots),
            })
    any_roots = {r["root_declaration"] for r in roots}
    node_rows: list[dict[str, Any]] = []
    for name in sorted(reached_all):
        row = index[name]
        candidates = _module_candidates(row)
        if len(candidates) != 1:
            raise SystemExit(
                f"reached declaration {name} has ambiguous module attribution: {candidates}; "
                "classify this explicitly before refreshing the checked-in snapshot"
            )
        node_rows.append({
            "declaration": name,
            "module": candidates[0],
            "kind": str(row.get("kind", "")),
            "is_any_root": int(name in any_roots),
        })
    edge_rows = [
        {"dependent": a, "prerequisite": b}
        for a, b in sorted(edge_all)
        if a in reached_all and b in reached_all
    ]
    return node_rows, edge_rows, reach_rows


def validate_declaration_overrides(
    nodes: list[dict[str, str]], module_map: dict[str, str], theories: dict[str, Any]
) -> dict[str, str]:
    rows = read_csv(DECL_OVERRIDE_PATH)
    by_decl = {r["declaration"]: r for r in nodes}
    mapping: dict[str, str] = {}
    for row in rows:
        decl = row["declaration"]
        tid = row["theory_id"]
        if decl in mapping:
            raise SystemExit(f"duplicate declaration theory override: {decl}")
        if decl not in by_decl:
            raise SystemExit(f"declaration theory override is stale or outside the trace: {decl}")
        if tid not in theories:
            raise SystemExit(f"declaration theory override references unknown theory {tid}: {decl}")
        default_tid = module_map[by_decl[decl]["module"]]
        if tid == default_tid:
            raise SystemExit(f"redundant declaration theory override agrees with module default: {decl}")
        mapping[decl] = tid
    return mapping


def declaration_theory(
    declaration: str, node_by_decl: dict[str, dict[str, str]],
    module_map: dict[str, str], declaration_overrides: dict[str, str],
) -> str:
    return declaration_overrides.get(declaration, module_map[node_by_decl[declaration]["module"]])


def joined_evidence(
    nodes: list[dict[str, str]], reach: list[dict[str, str]],
    module_map: dict[str, str], declaration_overrides: dict[str, str],
) -> list[dict[str, str]]:
    by_decl = {r["declaration"]: r for r in nodes}
    rows = []
    for r in reach:
        n = by_decl[r["declaration"]]
        rows.append({
            "corpus": r["corpus"],
            "source_id": r["source_id"],
            "theory_id": declaration_theory(r["declaration"], by_decl, module_map, declaration_overrides),
            "declaration": r["declaration"],
            "module": n["module"],
            "min_distance": r["min_distance"],
            "is_root": r["is_root"],
        })
    return rows


def validate_exact_module_map(nodes: list[dict[str, str]], module_rows: list[dict[str, str]]) -> dict[str, str]:
    mapping = {r["module"]: r["theory_id"] for r in module_rows}
    if len(mapping) != len(module_rows):
        raise SystemExit("duplicate module rows in exact theory map")
    reached = {r["module"] for r in nodes}
    missing = sorted(reached - mapping.keys())
    if missing:
        GENERATED.mkdir(parents=True, exist_ok=True)
        write_csv(
            GENERATED / "formalization_theory_unclassified_modules.csv",
            [{"module": m} for m in missing], ["module"],
        )
        raise SystemExit(
            "compiler trace reached unclassified project modules; inspect generated/"
            "formalization_theory_unclassified_modules.csv and update the exact module map"
        )
    return mapping


def refresh_snapshot(scope: dict[str, Any], *, skip_build: bool) -> None:
    """Rebuild compact checked-in compiler facts, only after classification validates."""
    roots = expected_root_rows(scope)
    if not skip_build:
        run(["lake", "build", *map(str, scope["build_targets"])])
    index = compiler_index(scope)
    nodes, edges, reach = trace_source_units(roots, index)
    module_rows = read_csv(MODULE_MAP_PATH)
    taxonomy = json.loads(TAXONOMY_PATH.read_text(encoding="utf-8"))
    theories = {t["id"]: t for t in taxonomy["theories"]}
    string_nodes = [{k: str(v) for k, v in r.items()} for r in nodes]
    mapping = validate_exact_module_map(string_nodes, module_rows)
    declaration_overrides = validate_declaration_overrides(string_nodes, mapping, theories)
    evidence = joined_evidence(
        string_nodes,
        [{k: str(v) for k, v in r.items()} for r in reach], mapping, declaration_overrides,
    )
    reached_per_module = collections.Counter(str(r["module"]) for r in nodes)
    indexed_per_module: collections.Counter[str] = collections.Counter()
    for row in index.values():
        for module in set(_module_candidates(row)):
            indexed_per_module[module] += 1
    module_inventory = [
        {
            "module": module,
            "theory_id": mapping[module],
            "reached_declarations": reached_per_module[module],
            "indexed_declarations_in_module": indexed_per_module[module],
        }
        for module in sorted(reached_per_module)
    ]
    # Only now overwrite tracked snapshot files.
    write_csv(ROOTS_PATH, roots, list(roots[0]))
    write_csv(NODES_PATH, nodes, ["declaration", "module", "kind", "is_any_root"])
    write_csv(EDGES_PATH, edges, ["dependent", "prerequisite"])
    write_csv(REACH_PATH, reach, ["corpus", "source_id", "declaration", "min_distance", "is_root"])
    write_csv(EVIDENCE_PATH, evidence, ["corpus", "source_id", "theory_id", "declaration", "module", "min_distance", "is_root"])
    write_csv(MODULE_INVENTORY_PATH, module_inventory, ["module", "theory_id", "reached_declarations", "indexed_declarations_in_module"])
    registry_hashes = {
        str(c["registry_path"]): sha256_file(REPO / str(c["registry_path"]))
        for c in scope["corpora"]
    }
    source_sha, source_count = project_source_fingerprint()
    try:
        lean_toolchain = (REPO / "lean-toolchain").read_text(encoding="utf-8").strip()
    except FileNotFoundError:
        lean_toolchain = ""
    manifest = {
        "schema": "formalization-draft2/formalization-trace-snapshot/v1",
        "snapshot_date": scope["snapshot_date"],
        "source": "Compiler-backed declaration dependencies from tools/leanq decl_index.lean.",
        "counts": {
            "source_units": len({(r["corpus"], r["source_id"]) for r in roots}),
            "yws_source_units": len({r["source_id"] for r in roots if r["corpus"] == "YWS2015"}),
            "dk_results": len({r["source_id"] for r in roots if r["corpus"] == "DK1970"}),
            "root_rows": len(roots),
            "unique_root_declarations": len({r["root_declaration"] for r in roots}),
            "reached_declarations": len(nodes),
            "dependency_edges": len(edges),
            "reachability_rows": len(reach),
            "reached_modules": len({r["module"] for r in nodes}),
        },
        "hashes": {"registries": registry_hashes},
        "compiler_provenance": {
            "git_head": git_value("rev-parse", "HEAD"),
            "lean_toolchain": lean_toolchain,
            "decl_index_path": DECL_INDEX.relative_to(REPO).as_posix(),
            "decl_index_sha256": sha256_file(DECL_INDEX),
            "project_lean_source_files_hashed": source_count,
            "project_lean_source_sha256": source_sha,
            "indexed_project_declarations": len(index),
        },
        "semantics": {
            "dependency_edge": "dependent -> prerequisite, from constants in elaborated declaration type/value expressions",
            "reachability": "minimum project-local declaration distance from any declaration registered to the source unit",
            "scope": "All maintained YWS census units and all maintained DK formalization-result entries.",
        },
    }
    MANIFEST_PATH.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


def latex_escape(s: str) -> str:
    repl = {"&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}"}
    return "".join(repl.get(c, c) for c in s)


def generate() -> None:
    scope = json.loads(SCOPE_PATH.read_text(encoding="utf-8"))
    taxonomy = json.loads(TAXONOMY_PATH.read_text(encoding="utf-8"))
    theories = {t["id"]: t for t in taxonomy["theories"]}
    module_rows = read_csv(MODULE_MAP_PATH)
    module_inventory = read_csv(MODULE_INVENTORY_PATH)
    for r in module_rows:
        if r["theory_id"] not in theories:
            raise SystemExit(f"module map references unknown theory {r['theory_id']}: {r['module']}")
    roots = read_csv(ROOTS_PATH)
    nodes = read_csv(NODES_PATH)
    edges = read_csv(EDGES_PATH)
    reach = read_csv(REACH_PATH)
    mapping = validate_exact_module_map(nodes, module_rows)
    declaration_overrides = validate_declaration_overrides(nodes, mapping, theories)
    inv_by_module = {r["module"]: r for r in module_inventory}
    if set(inv_by_module) != {r["module"] for r in nodes}:
        raise SystemExit("checked-in module inventory is stale relative to dependency nodes")
    for module, row in inv_by_module.items():
        if row["theory_id"] != mapping[module]:
            raise SystemExit(f"module inventory classification stale for {module}")

    # Root registry drift is deliberate and loud: source coverage changed, so refresh the trace.
    expected = expected_root_rows(scope)
    key_fields = list(expected[0])
    canon = lambda rows: sorted(tuple(str(r.get(k, "")) for k in key_fields) for r in rows)
    if canon(expected) != canon(roots):
        raise SystemExit("checked-in source root snapshot differs from canonical registries; run with --refresh-trace")

    computed_evidence = joined_evidence(nodes, reach, mapping, declaration_overrides)
    checked_evidence = read_csv(EVIDENCE_PATH)
    ev_fields = ["corpus", "source_id", "theory_id", "declaration", "module", "min_distance", "is_root"]
    if sorted(tuple(r[k] for k in ev_fields) for r in computed_evidence) != sorted(tuple(r[k] for k in ev_fields) for r in checked_evidence):
        raise SystemExit("checked-in theory evidence join is stale relative to nodes/reachability/module map")

    GENERATED.mkdir(parents=True, exist_ok=True)
    node_by_decl = {r["declaration"]: r for r in nodes}
    unit_meta: dict[tuple[str, str], dict[str, str]] = {}
    for r in roots:
        unit_meta[(r["corpus"], r["source_id"])] = r

    theory_to_decls: dict[str, set[str]] = collections.defaultdict(set)
    theory_to_modules: dict[str, set[str]] = collections.defaultdict(set)
    theory_to_units: dict[str, set[tuple[str, str]]] = collections.defaultdict(set)
    result_theory: dict[tuple[str, str, str], list[dict[str, str]]] = collections.defaultdict(list)
    for r in computed_evidence:
        tid = r["theory_id"]
        theory_to_decls[tid].add(r["declaration"])
        theory_to_modules[tid].add(r["module"])
        theory_to_units[tid].add((r["corpus"], r["source_id"]))
        result_theory[(r["corpus"], r["source_id"], tid)].append(r)

    summary_rows = []
    for t in taxonomy["theories"]:
        tid = t["id"]
        units = theory_to_units[tid]
        summary_rows.append({
            "theory_id": tid,
            "theory": t["label"],
            "basic_theory": int(bool(t["basic_theory"])),
            "coverage_level": t["coverage_level"],
            "reached_declarations": len(theory_to_decls[tid]),
            "reached_modules": len(theory_to_modules[tid]),
            "indexed_declarations_in_reached_modules": sum(int(inv_by_module[m]["indexed_declarations_in_module"]) for m in theory_to_modules[tid]),
            "source_units": len(units),
            "yws_units": sum(c == "YWS2015" for c, _ in units),
            "dk_results": sum(c == "DK1970" for c, _ in units),
            "scope_note": t["scope_note"],
        })
    write_csv(
        GENERATED / "formalization_theory_summary.csv", summary_rows,
        ["theory_id", "theory", "basic_theory", "coverage_level", "reached_declarations", "reached_modules", "indexed_declarations_in_reached_modules", "source_units", "yws_units", "dk_results", "scope_note"],
    )

    result_rows = []
    for (corpus, sid, tid), rs in sorted(result_theory.items()):
        meta = unit_meta[(corpus, sid)]
        result_rows.append({
            "corpus": corpus,
            "source_id": sid,
            "title": meta["title"],
            "source_anchor": meta["source_anchor"],
            "source_unit_role": meta["source_unit_role"],
            "source_relation": meta["source_relation"],
            "theory_id": tid,
            "theory": theories[tid]["label"],
            "basic_theory": int(bool(theories[tid]["basic_theory"])),
            "reached_declarations": len({r["declaration"] for r in rs}),
            "min_distance": min(int(r["min_distance"]) for r in rs),
            "root_declarations": sum(int(r["is_root"]) for r in rs),
        })
    write_csv(
        GENERATED / "formalization_result_theory_links.csv", result_rows,
        ["corpus", "source_id", "title", "source_anchor", "source_unit_role", "source_relation", "theory_id", "theory", "basic_theory", "reached_declarations", "min_distance", "root_declarations"],
    )

    # Compact source-surface coverage.  This describes what corpus units are in scope;
    # it is separate from prerequisite-theory breadth.
    units = list(unit_meta.values())
    coverage_rows = []
    disposition_rows = []
    for corpus in sorted({r["corpus"] for r in units}):
        us = [r for r in units if r["corpus"] == corpus]
        coverage_rows.append({
            "corpus": corpus,
            "source_units": len(us),
            "published_units": sum(r["source_relation"] != "extension" for r in us),
            "extension_units": sum(r["source_relation"] == "extension" for r in us),
            "result_units": sum(r["source_unit_role"] == "result" for r in us),
            "supporting_source_surface_units": sum(r["source_unit_role"] == "supporting_source_surface" for r in us),
            "verified_in_build_units": sum(r["verification"] == "proved_in_build" for r in us),
            "corrected_printed_units": sum("corrected" in r["disposition"] for r in us),
            "refuted_as_transcribed_units": sum("refuted_as_transcribed" in r["disposition"] for r in us),
        })
        counts = collections.Counter(r["disposition"] for r in us)
        for disposition, count in sorted(counts.items()):
            disposition_rows.append({"corpus": corpus, "disposition": disposition, "source_units": count})
    write_csv(
        GENERATED / "formalization_source_coverage.csv", coverage_rows,
        ["corpus", "source_units", "published_units", "extension_units", "result_units",
         "supporting_source_surface_units", "verified_in_build_units",
         "corrected_printed_units", "refuted_as_transcribed_units"],
    )
    write_csv(
        GENERATED / "formalization_source_dispositions.csv", disposition_rows,
        ["corpus", "disposition", "source_units"],
    )

    edge_counts: collections.Counter[tuple[str, str]] = collections.Counter()
    edge_examples: dict[tuple[str, str], tuple[str, str]] = {}
    for e in edges:
        a = node_by_decl[e["dependent"]]
        b = node_by_decl[e["prerequisite"]]
        ta = declaration_theory(e["dependent"], node_by_decl, mapping, declaration_overrides)
        tb = declaration_theory(e["prerequisite"], node_by_decl, mapping, declaration_overrides)
        if ta != tb:
            edge_counts[(ta, tb)] += 1
            edge_examples.setdefault((ta, tb), (e["dependent"], e["prerequisite"]))
    theory_edge_rows = []
    for (a, b), n in sorted(edge_counts.items()):
        exa, exb = edge_examples[(a, b)]
        theory_edge_rows.append({
            "dependent_theory_id": a,
            "prerequisite_theory_id": b,
            "declaration_edges": n,
            "example_dependent": exa,
            "example_prerequisite": exb,
        })
    write_csv(
        GENERATED / "formalization_theory_edges.csv", theory_edge_rows,
        ["dependent_theory_id", "prerequisite_theory_id", "declaration_edges", "example_dependent", "example_prerequisite"],
    )

    basic = [r for r in summary_rows if r["basic_theory"]]
    basic.sort(key=lambda r: next(i for i, t in enumerate(taxonomy["theories"]) if t["id"] == r["theory_id"]))
    write_csv(
        GENERATED / "formalization_basic_theories.csv", basic,
        ["theory_id", "theory", "coverage_level", "reached_declarations", "reached_modules", "indexed_declarations_in_reached_modules", "source_units", "yws_units", "dk_results", "scope_note"],
    )

    paper_groups = {g["id"]: g for g in taxonomy.get("paper_groups", [])}
    group_decls: dict[str, set[str]] = collections.defaultdict(set)
    group_modules: dict[str, set[str]] = collections.defaultdict(set)
    group_units: dict[str, set[tuple[str, str]]] = collections.defaultdict(set)
    group_theories: dict[str, set[str]] = collections.defaultdict(set)
    for t in taxonomy["theories"]:
        gid = t.get("paper_group_id")
        if not gid:
            continue
        if gid not in paper_groups:
            raise SystemExit(f"theory {t['id']} references unknown paper group {gid}")
        group_theories[gid].add(t["id"])
        group_decls[gid].update(theory_to_decls[t["id"]])
        group_modules[gid].update(theory_to_modules[t["id"]])
        group_units[gid].update(theory_to_units[t["id"]])
    group_rows = []
    for g in taxonomy.get("paper_groups", []):
        gid = g["id"]; units = group_units[gid]
        group_rows.append({
            "paper_group_id": gid,
            "paper_group": g["label"],
            "theory_count": len(group_theories[gid]),
            "reached_declarations": len(group_decls[gid]),
            "reached_modules": len(group_modules[gid]),
            "indexed_declarations_in_reached_modules": sum(int(inv_by_module[m]["indexed_declarations_in_module"]) for m in group_modules[gid]),
            "source_units": len(units),
            "yws_units": sum(c == "YWS2015" for c, _ in units),
            "dk_results": sum(c == "DK1970" for c, _ in units),
            "description": g["description"],
        })
    write_csv(
        GENERATED / "formalization_paper_groups.csv", group_rows,
        ["paper_group_id", "paper_group", "theory_count", "reached_declarations", "reached_modules", "indexed_declarations_in_reached_modules", "source_units", "yws_units", "dk_results", "description"],
    )
    group_tex = ["% Generated by scripts/build_formalization_theory_graph.py; do not edit.", "\\begin{itemize}"]
    for r in group_rows:
        group_tex.append(f"  \\item \\textbf{{{latex_escape(r['paper_group'])}}}.")
    group_tex.append("\\end{itemize}")
    (GENERATED / "formalization_paper_group_list.tex").write_text("\n".join(group_tex) + "\n", encoding="utf-8")

    tex = ["% Generated by scripts/build_formalization_theory_graph.py; do not edit.", "\\begin{itemize}"]
    for r in basic:
        tex.append(
            f"  \\item \\textbf{{{latex_escape(r['theory'])}}} "
            f"({latex_escape(r['coverage_level'].replace('_', ' '))})."
        )
    tex.append("\\end{itemize}")
    (GENERATED / "formalization_basic_theory_list.tex").write_text("\n".join(tex) + "\n", encoding="utf-8")

    # Theory graph retains non-foundation layers for provenance, while paper can choose basic nodes only.
    dot = ["digraph formalization_theories {", "  rankdir=LR;", "  node [shape=box];"]
    for t in taxonomy["theories"]:
        label = t["label"].replace('"', r'\"')
        shape = "box" if t["basic_theory"] else "ellipse"
        dot.append(f'  "{t["id"]}" [label="{label}", shape={shape}];')
    for r in theory_edge_rows:
        dot.append(f'  "{r["dependent_theory_id"]}" -> "{r["prerequisite_theory_id"]}" [label="{r["declaration_edges"]}"];')
    dot.append("}")
    (GENERATED / "formalization_theory_graph.dot").write_text("\n".join(dot) + "\n", encoding="utf-8")

    # Compact corpus -> basic-theory graph measures how many source units actually reach each theory.
    dot2 = ["digraph corpus_theories {", "  rankdir=LR;", "  node [shape=box];", '  "YWS2015" [label="Yu--Wang--Samworth (2015)", shape=ellipse];', '  "DK1970" [label="Davis--Kahan (1970)", shape=ellipse];']
    for r in basic:
        tid = r["theory_id"]
        label = r["theory"].replace('"', r'\"')
        dot2.append(f'  "{tid}" [label="{label}"];')
        if int(r["yws_units"]):
            dot2.append(f'  "YWS2015" -> "{tid}" [label="{r["yws_units"]} units"];')
        if int(r["dk_results"]):
            dot2.append(f'  "DK1970" -> "{tid}" [label="{r["dk_results"]} results"];')
    dot2.append("}")
    (GENERATED / "formalization_corpus_theory_graph.dot").write_text("\n".join(dot2) + "\n", encoding="utf-8")

    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    report = [
        "# Whole-formalization prerequisite theory report",
        "",
        f"Compiler snapshot: **{manifest['counts']['reached_declarations']}** project-local declarations, "
        f"**{manifest['counts']['dependency_edges']}** declaration edges, "
        f"**{manifest['counts']['reached_modules']}** modules.",
        "",
        "Scope: all maintained YWS census units and all maintained DK counted results. "
        "The exact declaration-level evidence is checked in under `data/`; this report is only a summary.",
        "",
        "## Paper-level groups",
        "",
    ]
    for r in group_rows:
        report.append(
            f"- **{r['paper_group']}** — {r['theory_count']} basic theories; "
            f"{r['reached_declarations']} reached declarations in {r['reached_modules']} modules; "
            f"reached by {r['yws_units']} YWS units and {r['dk_results']} DK results."
        )
    report += ["", "## Basic theory names", ""]
    for r in basic:
        report.append(
            f"- **{r['theory']}** — `{r['coverage_level']}`; "
            f"{r['reached_declarations']} reached declarations in {r['reached_modules']} modules "
            f"({r['indexed_declarations_in_reached_modules']} declarations present in those modules at the snapshot); "
            f"reached by {r['yws_units']} YWS units and {r['dk_results']} DK results."
        )
    report += [
        "",
        "## Interpretation",
        "",
        "`coverage_level` is a qualitative assessment of the repository subsystem, not a percentage of a mathematical field. "
        "Declaration/module counts are evidence about the local development and proof graph, not an automatic completeness score.",
        "",
        "Every generated theory link is recoverable from exact source IDs, exact Lean declaration names, compiler-derived declaration dependencies, explicit module defaults, and any exact declaration-level classification overrides.",
    ]
    (GENERATED / "FORMALIZATION_THEORY_REPORT.md").write_text("\n".join(report) + "\n", encoding="utf-8")

    input_paths = [SCOPE_PATH, TAXONOMY_PATH, ROOTS_PATH, NODES_PATH, EDGES_PATH, REACH_PATH, MODULE_MAP_PATH, DECL_OVERRIDE_PATH, MODULE_INVENTORY_PATH, EVIDENCE_PATH, MANIFEST_PATH]
    generation_manifest = {
        "schema": "formalization-draft2/theory-generation/v1",
        "inputs_sha256": {p.relative_to(REPO).as_posix(): sha256_file(p) for p in input_paths},
        "counts": {
            "source_units": len(unit_meta),
            "declarations": len(nodes),
            "dependency_edges": len(edges),
            "modules": len({r["module"] for r in nodes}),
            "basic_theories": len(basic),
            "paper_groups": len(group_rows),
        },
    }
    (GENERATED / "formalization_theory_generation_manifest.json").write_text(json.dumps(generation_manifest, indent=2) + "\n", encoding="utf-8")

    bundle = GENERATED / "formalization_theory_artifacts.zip"
    generated_names = [
        "formalization_theory_summary.csv",
        "formalization_result_theory_links.csv",
        "formalization_theory_edges.csv",
        "formalization_source_coverage.csv",
        "formalization_source_dispositions.csv",
        "formalization_basic_theories.csv",
        "formalization_basic_theory_list.tex",
        "formalization_paper_groups.csv",
        "formalization_paper_group_list.tex",
        "formalization_theory_graph.dot",
        "formalization_corpus_theory_graph.dot",
        "FORMALIZATION_THEORY_REPORT.md",
        "formalization_theory_generation_manifest.json",
    ]
    raw_paths = [SCOPE_PATH, TAXONOMY_PATH, ROOTS_PATH, NODES_PATH, EDGES_PATH, REACH_PATH, MODULE_MAP_PATH, DECL_OVERRIDE_PATH, MODULE_INVENTORY_PATH, EVIDENCE_PATH, MANIFEST_PATH]
    with zipfile.ZipFile(bundle, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for name in generated_names:
            path = GENERATED / name
            zf.write(path, path.relative_to(REPO).as_posix())
        for path in raw_paths:
            zf.write(path, path.relative_to(REPO).as_posix())

    print(
        f"formalization theory graph: {len(nodes)} declarations, {len(edges)} edges, "
        f"{len({r['module'] for r in nodes})} modules, {len(basic)} basic theories"
    )
    print(f"artifact bundle: {bundle.relative_to(REPO)}")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--refresh-trace", action="store_true", help="rebuild checked-in compiler snapshot from canonical YWS/DK registries")
    ap.add_argument("--skip-build", action="store_true", help="with --refresh-trace, skip lake build if the configured targets already build")
    args = ap.parse_args()
    scope = json.loads(SCOPE_PATH.read_text(encoding="utf-8"))
    if args.refresh_trace:
        refresh_snapshot(scope, skip_build=args.skip_build)
    generate()


if __name__ == "__main__":
    main()
