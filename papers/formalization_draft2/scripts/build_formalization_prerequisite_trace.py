#!/usr/bin/env python3
"""Trace environment-visible project-local prerequisites of selected declarations.

This tool is intentionally downstream of Lean elaboration. It reuses the repository's
``leanq``'s ``decl_index.lean`` indexer, which records constants exposed by
imported declaration types and retained values. This is substantially more specific than
import closure, but imported theorem proof terms can be opaque or otherwise omit named
proof-internal helpers. The resulting reachability graph is therefore a conservative
lower bound on named declaration dependence, not a complete proof-body trace.

The tool does *not* infer that a reached declaration constitutes a whole mathematical
"theory", and it does not turn declaration counts into a completeness percentage. It
emits an annotation template so those scientific judgments can be made explicitly from
compiler-backed evidence after inspecting the graph.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import zipfile
from collections import Counter, defaultdict, deque
from datetime import datetime, timezone
from typing import Any, Iterable

HERE = pathlib.Path(__file__).resolve().parent
PAPER_DIR = HERE.parent
REPO = PAPER_DIR.parent.parent
DEFAULT_CONFIG = PAPER_DIR / "data" / "formalization_prerequisite_roots_20260817.json"
def _decl_index_path() -> pathlib.Path:
    """The Lean declaration exporter, from the installed `leanq` package.

    It used to be vendored at `tools/leanq/src/leanq/lean/decl_index.lean`; that
    copy was removed when the tooling moved to
    `aiq-lean-formalization-tools`.  The provenance block below hashes whatever
    this resolves to, so a manuscript rebuild still records exactly which
    exporter produced its numbers.
    """
    try:
        from importlib.resources import files

        return pathlib.Path(str(files("leanq") / "lean" / "decl_index.lean"))
    except Exception as exc:  # pragma: no cover - environment guidance
        raise SystemExit(
            "the leanq declaration exporter is unavailable; install the tooling with\n"
            "  python3 -m pip install -e submodules/aiq-lean-formalization-tools\n"
            f"({exc})"
        )


DECL_INDEX = _decl_index_path()


def _decl_index_provenance() -> str:
    """How to name the exporter in a provenance block."""
    try:
        return DECL_INDEX.relative_to(REPO).as_posix()
    except ValueError:
        return "leanq/lean/decl_index.lean (installed aiq-lean-formalization-tools)"
OUT = PAPER_DIR / "generated"
DEFAULT_OUTPUT_STEM = "formalization_prerequisite"


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def source_fingerprint() -> tuple[str, int]:
    """Hash project Lean sources by relative path and bytes.

    Excludes vendored/build/history trees.  This makes an artifact auditable even when the
    working tree contains uncommitted formalization changes.
    """
    skip_top = {".git", ".lake", "external", "retired"}
    paths: list[pathlib.Path] = []
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
        h.update(len(rel).to_bytes(8, "big"))
        h.update(rel)
        data = path.read_bytes()
        h.update(len(data).to_bytes(8, "big"))
        h.update(data)
    return h.hexdigest(), len(paths)


def run(cmd: list[str], *, capture: bool = False) -> subprocess.CompletedProcess[str]:
    print("+", " ".join(cmd), file=sys.stderr)
    return subprocess.run(
        cmd,
        cwd=REPO,
        check=True,
        text=True,
        stdout=subprocess.PIPE if capture else None,
        stderr=None,
    )


def git_value(*args: str) -> str | None:
    try:
        p = subprocess.run(
            ["git", *args], cwd=REPO, check=True, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
        )
        return p.stdout.strip()
    except subprocess.CalledProcessError:
        return None


def load_config(path: pathlib.Path) -> dict[str, Any]:
    data = json.loads(path.read_text(encoding="utf-8"))
    required = {"build_targets", "import_modules", "project_module_prefixes", "root_groups"}
    missing = sorted(required - data.keys())
    if missing:
        raise SystemExit(f"config missing fields: {', '.join(missing)}")
    return data


def parse_jsonl(text: str, prefix: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for lineno, raw in enumerate(text.splitlines(), 1):
        line = raw.strip()
        if not line:
            continue
        try:
            row = json.loads(line)
        except json.JSONDecodeError as ex:
            raise SystemExit(
                f"leanq declaration index emitted non-JSON for prefix {prefix} at line {lineno}: {line[:240]}"
            ) from ex
        rows.append(row)
    return rows


def _semantic_index_signature(row: dict[str, Any]) -> tuple[str, tuple[str, ...]]:
    """Fields that must agree when Lean module metadata lists a declaration twice.

    ``env.header.moduleData[*].constNames`` can legitimately associate the same global
    declaration name with more than one imported module.  The module claim is provenance,
    not part of the declaration's kernel payload.  We therefore merge duplicate names only
    when their declaration kind and direct constant dependencies agree exactly (up to order).
    """
    return str(row.get("kind", "")), tuple(sorted({str(x) for x in row.get("deps", [])}))


def _module_candidates(row: dict[str, Any]) -> list[str]:
    candidates = row.get("module_candidates")
    if isinstance(candidates, list):
        return sorted({str(x) for x in candidates if str(x)})
    module = str(row.get("module", ""))
    return [module] if module else []


def _module_label(row: dict[str, Any]) -> str:
    """Auditable module label for aggregation and pictures.

    A multi-claim declaration is deliberately *not* silently assigned to one claimant.
    """
    candidates = _module_candidates(row)
    if len(candidates) <= 1:
        return candidates[0] if candidates else "unknown"
    return "AMBIGUOUS{" + " | ".join(candidates) + "}"


def index_project_declarations(config: dict[str, Any]) -> dict[str, dict[str, Any]]:
    if not DECL_INDEX.exists():
        raise SystemExit(f"missing compiler indexer: {DECL_INDEX}")

    with tempfile.NamedTemporaryFile("w", encoding="utf-8", suffix=".modules", delete=False) as f:
        modules_path = pathlib.Path(f.name)
        for module in config["import_modules"]:
            f.write(str(module) + "\n")
    try:
        by_name: dict[str, dict[str, Any]] = {}
        for prefix in config["project_module_prefixes"]:
            p = run(
                [
                    "lake", "env", "lean", "--run", str(DECL_INDEX),
                    str(prefix), str(modules_path), "deps",
                ],
                capture=True,
            )
            rows = parse_jsonl(p.stdout, str(prefix))
            print(f"indexed {len(rows)} declarations under module prefix {prefix}", file=sys.stderr)
            for raw_row in rows:
                row = dict(raw_row)
                name = str(row["name"])
                module = str(row.get("module", ""))
                old = by_name.get(name)
                if old is None:
                    row["module_candidates"] = [module] if module else []
                    row["index_prefixes"] = [str(prefix)]
                    row["module_attribution_ambiguous"] = False
                    by_name[name] = row
                    continue

                if _semantic_index_signature(old) != _semantic_index_signature(row):
                    raise SystemExit(
                        "conflicting declaration kernel payload for " + name + "\n"
                        + "  existing kind/deps: " + repr(_semantic_index_signature(old)) + "\n"
                        + "  new kind/deps:      " + repr(_semantic_index_signature(row))
                    )

                candidates = set(_module_candidates(old))
                if module:
                    candidates.add(module)
                old["module_candidates"] = sorted(candidates)
                prefixes = {str(x) for x in old.get("index_prefixes", [])}
                prefixes.add(str(prefix))
                old["index_prefixes"] = sorted(prefixes)
                old["module_attribution_ambiguous"] = len(candidates) > 1
                # Retain ``module`` only as a deterministic compatibility field.  Every
                # aggregate emitted by this script uses _module_label(), and the ambiguity
                # is explicit in module_candidates/module_attribution_ambiguous.
                if candidates:
                    old["module"] = sorted(candidates)[0]

        ambiguous = sum(bool(row.get("module_attribution_ambiguous")) for row in by_name.values())
        if ambiguous:
            print(
                f"coalesced {ambiguous} declarations with multiple Lean module claimants; "
                "see the generated module-ambiguities artifact",
                file=sys.stderr,
            )
        return by_name
    finally:
        try:
            modules_path.unlink()
        except FileNotFoundError:
            pass


def normalize_roots(config: dict[str, Any]) -> tuple[dict[str, list[str]], dict[str, str]]:
    groups: dict[str, list[str]] = {}
    labels: dict[str, str] = {}
    for group in config["root_groups"]:
        gid = str(group["id"])
        if gid in groups:
            raise SystemExit(f"duplicate root group id: {gid}")
        decls = [str(x) for x in group["declarations"]]
        if not decls:
            raise SystemExit(f"root group {gid} has no declarations")
        groups[gid] = decls
        labels[gid] = str(group.get("label", gid))
    return groups, labels


def trace_group(
    roots: list[str], index: dict[str, dict[str, Any]]
) -> tuple[set[str], dict[str, int], set[tuple[str, str]], set[tuple[str, str]]]:
    """Return reached locals, minimum distance, local edges, and external boundary edges.

    Edges are stored as (dependent, prerequisite), matching the raw Lean dependency direction.
    """
    missing = [root for root in roots if root not in index]
    if missing:
        formatted = "\n  ".join(missing)
        raise SystemExit(
            "configured root declarations were not found in the compiled local index:\n  " + formatted
        )

    reached: set[str] = set()
    distance: dict[str, int] = {}
    local_edges: set[tuple[str, str]] = set()
    boundary_edges: set[tuple[str, str]] = set()
    queue: deque[tuple[str, int]] = deque((root, 0) for root in roots)
    while queue:
        name, dist = queue.popleft()
        old = distance.get(name)
        if old is not None and old <= dist:
            continue
        distance[name] = dist
        reached.add(name)
        for dep in index[name].get("deps", []):
            dep = str(dep)
            if dep in index:
                local_edges.add((name, dep))
                queue.append((dep, dist + 1))
            else:
                boundary_edges.add((name, dep))
    return reached, distance, local_edges, boundary_edges


def family(module: str) -> str:
    return module.split(".", 1)[0] if module else "unknown"


def write_csv(path: pathlib.Path, rows: Iterable[dict[str, Any]], fields: list[str]) -> None:
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)


def dot_quote(text: str) -> str:
    return '"' + text.replace("\\", "\\\\").replace('"', '\\"') + '"'


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=pathlib.Path, default=DEFAULT_CONFIG)
    parser.add_argument(
        "--skip-build", action="store_true",
        help="do not run lake build first; use only after the configured targets already build",
    )
    parser.add_argument(
        "--output-stem", default=DEFAULT_OUTPUT_STEM,
        help="basename for generated artifacts (default: formalization_prerequisite)",
    )
    args = parser.parse_args()
    output_stem = args.output_stem.strip()
    if not output_stem or any(c not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_-" for c in output_stem):
        raise SystemExit("--output-stem must contain only letters, digits, underscore, or hyphen")

    config_path = args.config.resolve()
    config = load_config(config_path)
    OUT.mkdir(parents=True, exist_ok=True)

    if not args.skip_build:
        run(["lake", "build", *map(str, config["build_targets"])])

    preexisting_dirty = bool(git_value("status", "--porcelain"))
    source_hash, source_count = source_fingerprint()
    index = index_project_declarations(config)
    groups, labels = normalize_roots(config)

    reached_by_group: dict[str, set[str]] = {}
    distance_by_group: dict[str, dict[str, int]] = {}
    edges_by_group: dict[str, set[tuple[str, str]]] = {}
    boundary_by_group: dict[str, set[tuple[str, str]]] = {}
    for gid, roots in groups.items():
        reached, distances, edges, boundary = trace_group(roots, index)
        reached_by_group[gid] = reached
        distance_by_group[gid] = distances
        edges_by_group[gid] = edges
        boundary_by_group[gid] = boundary

    reached_all = set().union(*reached_by_group.values())
    roots_all = {d for roots in groups.values() for d in roots}
    local_edges_all = set().union(*edges_by_group.values())
    boundary_edges_all = set().union(*boundary_by_group.values())

    reached_groups_for: dict[str, list[str]] = defaultdict(list)
    for gid, reached in reached_by_group.items():
        for name in reached:
            reached_groups_for[name].append(gid)

    nodes = []
    for name in sorted(reached_all):
        row = index[name]
        distances = {gid: distance_by_group[gid][name] for gid in groups if name in distance_by_group[gid]}
        nodes.append(
            {
                "name": name,
                "module": _module_label(row),
                "module_candidates": _module_candidates(row),
                "module_attribution_ambiguous": bool(row.get("module_attribution_ambiguous")),
                "family": family(_module_label(row)),
                "kind": row.get("kind"),
                "is_root": name in roots_all,
                "reached_by_groups": sorted(reached_groups_for[name]),
                "minimum_distance_from_group_root": distances,
                "direct_local_prerequisites": sorted(
                    dep for dependent, dep in local_edges_all if dependent == name
                ),
                "direct_external_prerequisites": sorted(
                    dep for dependent, dep in boundary_edges_all if dependent == name
                ),
            }
        )

    graph = {
        "schema": "formalization-draft2/prerequisite-declaration-graph/v1",
        "semantics": {
            "node": "A project-local Lean declaration reached from at least one configured headline root.",
            "edge": "dependent -> prerequisite, where the prerequisite constant is exposed by the imported elaborated declaration type or retained value of the dependent declaration.",
            "external_boundary": "A direct prerequisite constant not defined in one of the configured project module prefixes; external dependencies are recorded but not traversed.",
            "warning": "Reachability is a compiler-backed conservative lower bound on named declaration dependence, not a complete proof-body trace: imported theorem bodies can hide named helpers. Mathematical theory labels and completeness judgments require separate human annotation and are not inferred from declaration counts. Lean module metadata can associate one global declaration with multiple modules; such cases are retained explicitly as module_candidates and are never silently assigned for aggregation."
        },
        "root_groups": config["root_groups"],
        "nodes": nodes,
        "local_edges": [
            {"dependent": a, "prerequisite": b} for a, b in sorted(local_edges_all)
        ],
        "external_boundary_edges": [
            {"dependent": a, "prerequisite": b} for a, b in sorted(boundary_edges_all)
        ],
    }
    graph_path = OUT / f"{output_stem}_graph.json"
    graph_path.write_text(json.dumps(graph, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    # Preserve the local compiler index as an audit artifact.  This includes unreachable
    # project declarations, allowing later questions about reached-vs-available scope.
    index_path = OUT / f"{output_stem}_local_decl_index.jsonl"
    with index_path.open("w", encoding="utf-8") as f:
        for name in sorted(index):
            f.write(json.dumps(index[name], sort_keys=True) + "\n")

    ambiguity_rows = []
    for name in sorted(index):
        row = index[name]
        candidates = _module_candidates(row)
        if len(candidates) <= 1:
            continue
        ambiguity_rows.append(
            {
                "declaration": name,
                "kind": row.get("kind"),
                "module_candidates": ";".join(candidates),
                "index_prefixes": ";".join(str(x) for x in row.get("index_prefixes", [])),
                "reached_from_headline_roots": name in reached_all,
            }
        )
    write_csv(
        OUT / f"{output_stem}_module_ambiguities.csv",
        ambiguity_rows,
        ["declaration", "kind", "module_candidates", "index_prefixes", "reached_from_headline_roots"],
    )

    edge_rows = []
    for dependent, prerequisite in sorted(local_edges_all):
        dep_groups = sorted(gid for gid, edges in edges_by_group.items() if (dependent, prerequisite) in edges)
        edge_rows.append(
            {
                "dependent": dependent,
                "dependent_module": _module_label(index[dependent]),
                "prerequisite": prerequisite,
                "prerequisite_module": _module_label(index[prerequisite]),
                "root_groups": ";".join(dep_groups),
            }
        )
    write_csv(
        OUT / f"{output_stem}_edges.csv", edge_rows,
        ["dependent", "dependent_module", "prerequisite", "prerequisite_module", "root_groups"],
    )

    boundary_rows = []
    for dependent, prerequisite in sorted(boundary_edges_all):
        dep_groups = sorted(gid for gid, edges in boundary_by_group.items() if (dependent, prerequisite) in edges)
        boundary_rows.append(
            {
                "dependent": dependent,
                "dependent_module": _module_label(index[dependent]),
                "external_prerequisite": prerequisite,
                "root_groups": ";".join(dep_groups),
            }
        )
    write_csv(
        OUT / f"{output_stem}_external_boundary.csv", boundary_rows,
        ["dependent", "dependent_module", "external_prerequisite", "root_groups"],
    )

    # Declaration reachability per root group, useful for intersections and attribution.
    reach_rows = []
    for gid in groups:
        for name in sorted(reached_by_group[gid]):
            reach_rows.append(
                {
                    "root_group": gid,
                    "root_group_label": labels[gid],
                    "declaration": name,
                    "module": _module_label(index[name]),
                    "kind": index[name]["kind"],
                    "distance": distance_by_group[gid][name],
                    "is_group_root": name in groups[gid],
                }
            )
    write_csv(
        OUT / f"{output_stem}_reachability.csv", reach_rows,
        ["root_group", "root_group_label", "declaration", "module", "kind", "distance", "is_group_root"],
    )

    indexed_by_module: dict[str, list[str]] = defaultdict(list)
    reached_by_module: dict[str, list[str]] = defaultdict(list)
    for name, row in index.items():
        indexed_by_module[_module_label(row)].append(name)
    for name in reached_all:
        reached_by_module[_module_label(index[name])].append(name)

    module_rows = []
    for module in sorted(reached_by_module):
        reached_names = reached_by_module[module]
        all_names = indexed_by_module[module]
        kinds = Counter(str(index[name]["kind"]) for name in reached_names)
        group_ids = sorted({gid for name in reached_names for gid in reached_groups_for[name]})
        module_rows.append(
            {
                "module": module,
                "family": family(module),
                "reached_declarations": len(reached_names),
                "indexed_declarations_in_module": len(all_names),
                "reached_theorems": kinds["theorem"],
                "reached_defs": kinds["def"],
                "reached_opaque": kinds["opaque"],
                "root_groups": ";".join(group_ids),
            }
        )
    write_csv(
        OUT / f"{output_stem}_modules.csv", module_rows,
        ["module", "family", "reached_declarations", "indexed_declarations_in_module", "reached_theorems", "reached_defs", "reached_opaque", "root_groups"],
    )

    # This is intentionally a blank scientific-annotation surface.  Counts are evidence about
    # the implemented API, not a percentage-complete score for a mathematical subject.
    theory_rows = [
        {
            **row,
            "theory_label": "",
            "formalized_scope": "",
            "known_unformalized_scope": "",
            "coverage_level": "",
            "coverage_rationale": "",
        }
        for row in module_rows
    ]
    write_csv(
        OUT / f"{output_stem}_theory_annotation_template.csv", theory_rows,
        [
            "module", "family", "reached_declarations", "indexed_declarations_in_module",
            "reached_theorems", "reached_defs", "reached_opaque", "root_groups",
            "theory_label", "formalized_scope", "known_unformalized_scope",
            "coverage_level", "coverage_rationale",
        ],
    )

    module_edges = Counter()
    for dependent, prerequisite in local_edges_all:
        dm = _module_label(index[dependent])
        pm = _module_label(index[prerequisite])
        if dm != pm:
            module_edges[(pm, dm)] += 1  # prerequisite -> dependent for the picture
    module_edge_rows = [
        {"prerequisite_module": p, "dependent_module": d, "declaration_edges": count}
        for (p, d), count in sorted(module_edges.items())
    ]
    write_csv(
        OUT / f"{output_stem}_module_edges.csv", module_edge_rows,
        ["prerequisite_module", "dependent_module", "declaration_edges"],
    )

    dot_path = OUT / f"{output_stem}_module_graph.dot"
    with dot_path.open("w", encoding="utf-8") as f:
        f.write("digraph FormalizationPrerequisites {\n")
        f.write("  rankdir=LR;\n")
        f.write("  graph [label=\"Compiler-traced project-local prerequisite modules\", labelloc=t];\n")
        f.write("  node [shape=box];\n")
        for row in module_rows:
            label = f"{row['module']}\\n{row['reached_declarations']} reached declarations"
            f.write(f"  {dot_quote(row['module'])} [label={dot_quote(label)}];\n")
        for row in module_edge_rows:
            f.write(
                f"  {dot_quote(row['prerequisite_module'])} -> {dot_quote(row['dependent_module'])} "
                f"[label={dot_quote(str(row['declaration_edges']))}];\n"
            )
        f.write("}\n")

    group_summary = []
    for gid in groups:
        mods = {_module_label(index[n]) for n in reached_by_group[gid]}
        fams = Counter(family(m) for m in mods)
        group_summary.append(
            {
                "id": gid,
                "label": labels[gid],
                "configured_roots": len(groups[gid]),
                "reached_local_declarations": len(reached_by_group[gid]),
                "reached_local_modules": len(mods),
                "external_boundary_edges": len(boundary_by_group[gid]),
                "module_families": dict(sorted(fams.items())),
            }
        )

    manifest = {
        "schema": "formalization-draft2/prerequisite-trace-run/v1",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "git_head": git_value("rev-parse", "HEAD"),
        "working_tree_was_dirty_before_generation": preexisting_dirty,
        "lean_toolchain": (REPO / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "config_path": config_path.relative_to(REPO).as_posix(),
        "config_sha256": sha256_file(config_path),
        "decl_index_path": _decl_index_provenance(),
        "decl_index_sha256": sha256_file(DECL_INDEX),
        "project_lean_source_sha256": source_hash,
        "project_lean_source_files_hashed": source_count,
        "indexed_project_declarations": len(index),
        "module_ambiguous_indexed_declarations": len(ambiguity_rows),
        "module_ambiguous_reached_declarations": sum(1 for row in ambiguity_rows if row["reached_from_headline_roots"]),
        "reached_project_declarations": len(reached_all),
        "local_dependency_edges": len(local_edges_all),
        "external_boundary_edges": len(boundary_edges_all),
        "root_group_summary": group_summary,
        "outputs": [
            f"generated/{output_stem}_graph.json",
            f"generated/{output_stem}_local_decl_index.jsonl",
            f"generated/{output_stem}_module_ambiguities.csv",
            f"generated/{output_stem}_edges.csv",
            f"generated/{output_stem}_external_boundary.csv",
            f"generated/{output_stem}_reachability.csv",
            f"generated/{output_stem}_modules.csv",
            f"generated/{output_stem}_module_edges.csv",
            f"generated/{output_stem}_module_graph.dot",
            f"generated/{output_stem}_theory_annotation_template.csv",
            f"generated/{output_stem}_run_manifest.json",
            f"generated/{output_stem}_summary.md",
            f"generated/{output_stem}_artifacts.zip",
        ],
    }
    (OUT / f"{output_stem}_run_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    summary = [
        "# Compiler-traced formalization prerequisites",
        "",
        "This report follows constants exposed by imported elaborated Lean declaration types and retained values. It is substantially more specific than import availability, but it is a conservative lower bound on named declaration dependence because imported theorem proof bodies can hide proof-internal helpers.",
        "",
        "External constants are retained as boundary edges but are not traversed. The project-local closure is restricted to the module prefixes named in the root configuration.",
        "",
        "## Root groups",
        "",
    ]
    for row in group_summary:
        summary.append(
            f"- **{row['label']}**: {row['configured_roots']} root declarations; "
            f"{row['reached_local_declarations']} project-local declarations across "
            f"{row['reached_local_modules']} modules; {row['external_boundary_edges']} direct external-boundary edges."
        )
    summary += [
        "",
        "## Interpretation guardrail",
        "",
        "The graph can support conservative claims of the form 'the imported declaration environment exposes dependence on formalized declarations in these areas.' It does not establish that every proof-internal helper was recovered, that an entire mathematical theory was formalized, or that reached/available declaration count defines a meaningful completeness percentage. The generated theory-annotation template is intentionally blank in those fields so scope and omissions can be reviewed explicitly.",
        "",
        f"Project-local union: {len(reached_all)} declarations, {len(local_edges_all)} local dependency edges, {len(boundary_edges_all)} external-boundary edges.",
        f"Lean module-attribution ambiguities: {len(ambiguity_rows)} indexed declarations, of which {sum(1 for row in ambiguity_rows if row['reached_from_headline_roots'])} are in the headline-root closure. These are preserved explicitly rather than silently assigned to a module.",
        "",
        "Return the generated files with prefix `formalization_prerequisite_` for theory-level classification and paper-graph construction.",
        "",
    ]
    summary_path = OUT / f"{output_stem}_summary.md"
    summary_path.write_text("\n".join(summary), encoding="utf-8")

    bundle_path = OUT / f"{output_stem}_artifacts.zip"
    bundle_members = [
        OUT / f"{output_stem}_graph.json",
        OUT / f"{output_stem}_local_decl_index.jsonl",
        OUT / f"{output_stem}_module_ambiguities.csv",
        OUT / f"{output_stem}_edges.csv",
        OUT / f"{output_stem}_external_boundary.csv",
        OUT / f"{output_stem}_reachability.csv",
        OUT / f"{output_stem}_modules.csv",
        OUT / f"{output_stem}_module_edges.csv",
        OUT / f"{output_stem}_module_graph.dot",
        OUT / f"{output_stem}_theory_annotation_template.csv",
        OUT / f"{output_stem}_run_manifest.json",
        summary_path,
        config_path,
    ]
    with zipfile.ZipFile(bundle_path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        for path in bundle_members:
            if path.is_relative_to(PAPER_DIR):
                arcname = pathlib.PurePosixPath("papers/formalization_draft2") / path.relative_to(PAPER_DIR)
            else:
                arcname = pathlib.PurePosixPath(path.name)
            zf.write(path, arcname.as_posix())

    print("\nCompiler-traced prerequisite artifacts written:", file=sys.stderr)
    for output in manifest["outputs"]:
        print(f"  papers/formalization_draft2/{output}", file=sys.stderr)


if __name__ == "__main__":
    main()
