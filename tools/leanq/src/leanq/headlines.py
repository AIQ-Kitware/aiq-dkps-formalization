"""Census-aware headline consumption analysis over saved semantic graphs.

This module is deliberately Lean-free.  It consumes the broad semantic index
written by ``leanq graph-index`` and paper census JSON files, then answers:

* which headline claims are on the dependency path to a chosen target;
* which declaration from a census claim is actually consumed;
* the nearest Acharyya and Quench integration declarations;
* the nearest downstream Quench headline claim; and
* exact witness paths for every collapsed visual edge.

The census is treated as claim metadata, while all reachability facts come from
the elaborated declaration graph.
"""

from __future__ import annotations

import json
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping, Sequence

from .graph import DependencyGraph, declarations_from_graph_payload, target_dependency_graph
from .index import Decl
from .project import ProjectError


@dataclass(frozen=True)
class CensusClaim:
    census: str
    family: str
    id: str
    title: str
    importance: str
    status: str | None
    declarations: tuple[str, ...]
    canonical_declarations: tuple[str, ...]
    supporting_declarations: tuple[str, ...]
    has_explicit_realizations: bool
    source_path: str


def _family_from_path(path: Path) -> str:
    stem = path.stem
    for suffix in ("-full-source-census", "-source-census", "-census"):
        if stem.endswith(suffix):
            stem = stem[: -len(suffix)]
            break
    low = stem.lower()
    if "davis-kahan" in low:
        return "Davis–Kahan"
    if "yu-wang-samworth" in low:
        return "Yu–Wang–Samworth"
    if "quench" in low:
        return "Quench"
    return stem.replace("-", " ").strip().title()


def load_census_claims(
    paths: Sequence[Path], *, importances: Iterable[str] = ("headline",)
) -> list[CensusClaim]:
    """Load selected claim rows from the repository's paper census schema."""
    wanted = set(importances)
    result: list[CensusClaim] = []
    for path in paths:
        try:
            obj = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as ex:
            raise ProjectError(f"cannot read census {path}: {ex}") from ex
        items = obj.get("items") if isinstance(obj, dict) else None
        if not isinstance(items, list):
            raise ProjectError(f"census {path} has no items list")
        family = _family_from_path(path)
        for row in items:
            if not isinstance(row, dict):
                continue
            importance = str(row.get("importance") or "")
            if wanted and importance not in wanted:
                continue
            declarations = row.get("lean_declarations", [])
            if declarations is None:
                declarations = []
            if not isinstance(declarations, list):
                raise ProjectError(
                    f"census {path} item {row.get('id')!r} has non-list lean_declarations"
                )
            semantic_review = row.get("semantic_review")
            canonical: list[str] = []
            supporting: list[str] = []
            if isinstance(semantic_review, dict):
                raw_canonical = semantic_review.get("canonical_declarations", [])
                raw_supporting = semantic_review.get("supporting_declarations", [])
                if isinstance(raw_canonical, list):
                    canonical = [str(name) for name in raw_canonical if name]
                if isinstance(raw_supporting, list):
                    supporting = [str(name) for name in raw_supporting if name]
            result.append(
                CensusClaim(
                    census=path.name,
                    family=family,
                    id=str(row.get("id") or ""),
                    title=str(row.get("title") or row.get("id") or "Untitled claim"),
                    importance=importance,
                    status=(None if row.get("status") is None else str(row.get("status"))),
                    declarations=tuple(str(name) for name in declarations if name),
                canonical_declarations=tuple(canonical),
                supporting_declarations=tuple(supporting),
                has_explicit_realizations=bool(canonical or supporting),
                source_path=str(path),
                )
            )
    return result


def _resolve_census_name(table: Mapping[str, Decl], query: str) -> tuple[str | None, str | None]:
    """Resolve an exact or uniquely short census declaration name."""
    if query in table:
        return query, None
    short = query.rsplit(".", 1)[-1]
    hits = sorted(name for name, decl in table.items() if decl.short_name == short)
    if len(hits) == 1:
        return hits[0], None
    if not hits:
        return None, "not present in imported semantic index"
    return None, f"ambiguous short name ({len(hits)} matches)"


def _adjacency(graph: DependencyGraph) -> tuple[dict[str, list[str]], dict[str, list[str]]]:
    adj = {name: [] for name in graph.nodes}
    rev = {name: [] for name in graph.nodes}
    for source, target in graph.edges:
        if source in adj and target in adj:
            adj[source].append(target)
            rev[target].append(source)
    for values in adj.values():
        values.sort()
    for values in rev.values():
        values.sort()
    return adj, rev


def _distance_to_targets(graph: DependencyGraph) -> tuple[dict[str, int], dict[str, str | None]]:
    """Shortest downstream distance and next hop from every target ancestor."""
    _, rev = _adjacency(graph)
    distance: dict[str, int] = {}
    next_hop: dict[str, str | None] = {}
    queue: deque[str] = deque()
    for target in sorted(graph.targets):
        distance[target] = 0
        next_hop[target] = None
        queue.append(target)
    while queue:
        consumer = queue.popleft()
        for dependency in rev.get(consumer, ()):
            candidate = distance[consumer] + 1
            if dependency not in distance:
                distance[dependency] = candidate
                next_hop[dependency] = consumer
                queue.append(dependency)
    return distance, next_hop


def _path_to_target(source: str, next_hop: Mapping[str, str | None]) -> list[str] | None:
    if source not in next_hop:
        return None
    result = [source]
    seen = {source}
    while next_hop.get(result[-1]) is not None:
        nxt = next_hop[result[-1]]
        assert nxt is not None
        if nxt in seen:
            return None
        result.append(nxt)
        seen.add(nxt)
    return result


def _shortest_path_to_predicate(
    graph: DependencyGraph,
    source: str,
    predicate,
    *,
    allow_source: bool = False,
) -> list[str] | None:
    """Deterministic BFS downstream inside one target ancestor closure."""
    adj, _ = _adjacency(graph)
    queue: deque[str] = deque([source])
    previous: dict[str, str | None] = {source: None}
    while queue:
        node = queue.popleft()
        if (allow_source or node != source) and predicate(node):
            path: list[str] = []
            cur: str | None = node
            while cur is not None:
                path.append(cur)
                cur = previous[cur]
            return list(reversed(path))
        for nxt in adj.get(node, ()):
            if nxt not in previous:
                previous[nxt] = node
                queue.append(nxt)
    return None


def _library_is(
    graph: DependencyGraph, library: str, *, public_only: bool = True
):
    """Predicate for presentation-level integration seams.

    Private/internal helpers remain in witness paths, but the named nearest
    package integration node defaults to the first public declaration so the
    visual does not elevate an implementation detail into a paper-facing seam.
    """
    return lambda name: (
        graph.nodes[name].library == library
        and (not public_only or not graph.nodes[name].internal)
    )


def _claim_node_id(claim: CensusClaim) -> str:
    safe_family = claim.family.replace(" ", "-").replace("–", "-").replace("—", "-")
    return f"claim:{safe_family}:{claim.id}"


def _short_label(name: str) -> str:
    return name.rsplit(".", 1)[-1]


def analyze_headlines(
    semantic_payload: Mapping,
    *,
    targets: Sequence[str],
    census_paths: Sequence[Path],
    importances: Iterable[str] = ("headline",),
) -> dict:
    """Build a compact, census-aware Quench headline consumption graph."""
    if len(targets) != 1:
        raise ProjectError("headline consumption analysis currently requires exactly one target")
    decls = declarations_from_graph_payload(semantic_payload)
    table = {decl.name: decl for decl in decls}
    closure = target_dependency_graph(decls, targets)
    distance, next_hop = _distance_to_targets(closure)
    claims = load_census_claims(census_paths, importances=importances)

    resolved_by_claim: dict[tuple[str, str], list[str]] = {}
    resolution_warnings: list[dict] = []
    quench_decl_to_claims: dict[str, list[CensusClaim]] = {}
    for claim in claims:
        resolved: list[str] = []
        for raw in claim.declarations:
            name, warning = _resolve_census_name(table, raw)
            if name is not None:
                if name not in resolved:
                    resolved.append(name)
            elif warning is not None and warning.startswith("ambiguous"):
                resolution_warnings.append(
                    {
                        "claim": claim.id,
                        "family": claim.family,
                        "declaration": raw,
                        "warning": warning,
                    }
                )
        resolved_by_claim[(claim.census, claim.id)] = resolved
        if claim.family == "Quench":
            for name in resolved:
                quench_decl_to_claims.setdefault(name, []).append(claim)

    claim_rows: list[dict] = []
    selected_real_nodes: set[str] = set(closure.targets)
    route_parts: dict[str, dict[str, list[str] | None]] = {}

    for claim in claims:
        key = (claim.census, claim.id)
        resolved = resolved_by_claim[key]
        observed = [name for name in resolved if name in closure.nodes]
        observed.sort(key=lambda name: (distance.get(name, 10**9), resolved.index(name)))

        def resolved_subset(raw_names):
            out = []
            for raw in raw_names:
                name, _ = _resolve_census_name(table, raw)
                if name is not None and name not in out:
                    out.append(name)
            return out

        canonical_resolved = resolved_subset(claim.canonical_declarations)
        supporting_resolved = resolved_subset(claim.supporting_declarations)
        canonical_consumed = [name for name in canonical_resolved if name in closure.nodes]
        supporting_consumed = [name for name in supporting_resolved if name in closure.nodes]
        other_observed = [
            name for name in observed
            if name not in set(canonical_consumed) | set(supporting_consumed)
        ]
        # A semantic review that names canonical/supporting declarations is an
        # explicit claim boundary.  Do not let an incidental setup/helper from
        # the broad historical ``lean_declarations`` list make that reviewed
        # claim look consumed.  Older rows with no such distinction retain the
        # registered-realization fallback for backwards-compatible censuses.
        other_consumed = [] if claim.has_explicit_realizations else other_observed
        consumed = canonical_consumed + supporting_consumed + other_consumed
        preferred = canonical_consumed or supporting_consumed or other_consumed
        preferred.sort(key=lambda name: (distance.get(name, 10**9), resolved.index(name)))
        if preferred:
            representative = preferred[0]
        else:
            preferred_present = canonical_resolved or supporting_resolved or resolved
            representative = preferred_present[0] if preferred_present else None
        if canonical_consumed:
            consumption_class = "canonical"
        elif supporting_consumed:
            consumption_class = "supporting"
        elif other_consumed:
            consumption_class = "registered-support"
        else:
            consumption_class = "none"
        witness = _path_to_target(representative, next_hop) if representative in closure.nodes else None
        unclassified_witnesses = [
            {
                "declaration": name,
                "distanceToTarget": distance.get(name),
                "witnessToTarget": _path_to_target(name, next_hop),
            }
            for name in other_observed
        ] if claim.has_explicit_realizations else []

        nearest_yws = None
        nearest_acharyya = None
        nearest_quench = None
        nearest_quench_claim = None
        path_yws = None
        path_acharyya = None
        path_quench = None
        path_quench_claim = None
        first_consumer = None
        first_consumer_path = None

        if representative in closure.nodes:
            first_consumer_path = _shortest_path_to_predicate(
                closure, representative, lambda _name: True
            )
            if first_consumer_path and len(first_consumer_path) > 1:
                first_consumer = first_consumer_path[-1]

            if claim.family != "Yu–Wang–Samworth":
                path_yws = _shortest_path_to_predicate(
                    closure,
                    representative,
                    _library_is(closure, "YuWangSamworth2015"),
                )
                if path_yws:
                    nearest_yws = path_yws[-1]
                    selected_real_nodes.add(nearest_yws)

            path_acharyya = _shortest_path_to_predicate(
                closure, representative, _library_is(closure, "Acharyya2025")
            )
            if path_acharyya:
                nearest_acharyya = path_acharyya[-1]
                selected_real_nodes.add(nearest_acharyya)

            path_quench = _shortest_path_to_predicate(
                closure, representative, _library_is(closure, "DkpsQuench2026")
            )
            if path_quench:
                nearest_quench = path_quench[-1]
                selected_real_nodes.add(nearest_quench)

            path_quench_claim = _shortest_path_to_predicate(
                closure,
                representative,
                lambda name: name in quench_decl_to_claims,
                allow_source=claim.family == "Quench",
            )
            if path_quench_claim:
                hit = path_quench_claim[-1]
                choices = sorted(
                    quench_decl_to_claims[hit], key=lambda row: (row.id, row.title)
                )
                nearest_quench_claim = choices[0]

        claim_rows.append(
            {
                "nodeId": _claim_node_id(claim),
                "census": claim.census,
                "family": claim.family,
                "id": claim.id,
                "title": claim.title,
                "importance": claim.importance,
                "status": claim.status,
                "declaredDeclarations": list(claim.declarations),
                "canonicalDeclarations": list(claim.canonical_declarations),
                "supportingDeclarations": list(claim.supporting_declarations),
                "resolvedDeclarations": resolved,
                "observedRegisteredDeclarations": observed,
                "consumed": bool(consumed),
                "consumptionClass": consumption_class,
                "consumedDeclarations": consumed,
                "canonicalConsumedDeclarations": canonical_consumed,
                "supportingConsumedDeclarations": supporting_consumed,
                "otherConsumedDeclarations": other_consumed,
                "unclassifiedObservedDeclarations": (
                    other_observed if claim.has_explicit_realizations else []
                ),
                "unclassifiedObservedWitnesses": unclassified_witnesses,
                "representativeDeclaration": representative,
                "canonicalConsumed": bool(canonical_consumed),
                "distanceToTarget": distance.get(representative) if representative else None,
                "firstConsumer": first_consumer,
                "nearestYWS": nearest_yws,
                "nearestAcharyya": nearest_acharyya,
                "nearestQuench": nearest_quench,
                "nearestQuenchHeadline": (
                    None
                    if nearest_quench_claim is None
                    else {
                        "id": nearest_quench_claim.id,
                        "title": nearest_quench_claim.title,
                        "nodeId": _claim_node_id(nearest_quench_claim),
                        "viaDeclaration": path_quench_claim[-1],
                    }
                ),
                "witnessToTarget": witness,
            }
        )
        route_parts[_claim_node_id(claim)] = {
            "yws": path_yws,
            "acharyya": path_acharyya,
            "quench": path_quench,
            "quenchClaim": path_quench_claim,
            "target": witness,
        }

    # Standard node records let the existing declaration metadata/search surface
    # remain useful, while synthetic claim nodes keep unused census headlines visible.
    nodes: list[dict] = []
    claim_by_node = {row["nodeId"]: row for row in claim_rows}
    for row in claim_rows:
        if row["family"] == "Quench":
            stage = 4
        elif row["family"] == "Yu–Wang–Samworth":
            stage = 1
        else:
            stage = 0
        nodes.append(
            {
                "id": row["nodeId"],
                "name": row["title"],
                "module": row["family"],
                "kind": "claim",
                "library": row["family"],
                "internal": False,
                "target": False,
                "stage": stage,
                "claim": True,
                "consumed": row["consumed"],
                "consumptionClass": row["consumptionClass"],
                "claimId": row["id"],
                "claimTitle": row["title"],
                "representativeDeclaration": row["representativeDeclaration"],
            }
        )

    for name in sorted(selected_real_nodes):
        if name not in closure.nodes:
            continue
        decl = closure.nodes[name]
        if name in closure.targets:
            stage = 5
        elif decl.library == "YuWangSamworth2015":
            stage = 1
        elif decl.library == "Acharyya2025":
            stage = 2
        elif decl.library == "DkpsQuench2026":
            stage = 3
        else:
            stage = 1
        nodes.append(
            {
                "id": name,
                **decl.to_json(),
                "target": name in closure.targets,
                "stage": stage,
                "claim": False,
                "consumed": True,
            }
        )

    edges: list[dict] = []
    edge_keys: set[tuple[str, str, str]] = set()

    def add_edge(
        source: str,
        target: str,
        witness: list[str] | None,
        role: str,
        *,
        origin_claim: str,
    ) -> None:
        if source == target or not witness:
            return
        key = (source, target, role)
        if key in edge_keys:
            return
        edge_keys.add(key)
        edges.append(
            {
                "source": source,
                "target": target,
                "role": role,
                "originClaim": origin_claim,
                "witness": witness,
                "collapsedNodeCount": max(0, len(witness) - 2),
            }
        )

    # Quench claim nodes feed the selected target directly when their census
    # realization is in the target closure.
    for row in claim_rows:
        claim_node = row["nodeId"]
        rep = row["representativeDeclaration"]
        if not row["consumed"] or rep is None:
            continue
        parts = route_parts[claim_node]
        if row["family"] == "Quench":
            add_edge(
                claim_node, closure.targets[0], parts["target"], "headline-to-target",
                origin_claim=claim_node,
            )
            continue

        current_node = claim_node
        current_decl = rep
        if row["family"] != "Yu–Wang–Samworth":
            path_y = _shortest_path_to_predicate(
                closure, current_decl, _library_is(closure, "YuWangSamworth2015")
            )
            if path_y:
                y = path_y[-1]
                add_edge(
                    current_node, y, path_y, "nearest-yws", origin_claim=claim_node
                )
                current_node, current_decl = y, y

        path_a = _shortest_path_to_predicate(
            closure, current_decl, _library_is(closure, "Acharyya2025")
        )
        if path_a:
            a = path_a[-1]
            add_edge(
                current_node, a, path_a, "nearest-acharyya", origin_claim=claim_node
            )
            current_node, current_decl = a, a

        path_to_qclaim = _shortest_path_to_predicate(
            closure,
            current_decl,
            lambda name: name in quench_decl_to_claims,
            allow_source=True,
        )
        if path_to_qclaim:
            qdecl = path_to_qclaim[-1]
            qclaim = sorted(
                quench_decl_to_claims[qdecl], key=lambda item: (item.id, item.title)
            )[0]
            qnode = _claim_node_id(qclaim)
            add_edge(
                current_node, qnode, path_to_qclaim, "nearest-quench-headline",
                origin_claim=claim_node,
            )
        else:
            path_q = _shortest_path_to_predicate(
                closure, current_decl, _library_is(closure, "DkpsQuench2026")
            )
            if path_q:
                q = path_q[-1]
                add_edge(
                    current_node, q, path_q, "nearest-quench", origin_claim=claim_node
                )
                tail = _path_to_target(q, next_hop)
                add_edge(
                    q, closure.targets[0], tail, "to-target", origin_claim=claim_node
                )
            else:
                tail = _path_to_target(current_decl, next_hop)
                add_edge(
                    current_node, closure.targets[0], tail, "to-target",
                    origin_claim=claim_node,
                )

    family_counts: dict[str, dict[str, int]] = {}
    for row in claim_rows:
        bucket = family_counts.setdefault(
            row["family"],
            {"claims": 0, "consumed": 0, "canonical": 0, "supporting": 0},
        )
        bucket["claims"] += 1
        bucket["consumed"] += int(row["consumed"])
        bucket["canonical"] += int(row["consumptionClass"] == "canonical")
        bucket["supporting"] += int(row["consumptionClass"] == "supporting")

    return {
        "schemaVersion": 1,
        "payloadKind": "headline-consumption",
        "edgeDirection": "dependency-to-consumer",
        "targets": list(closure.targets),
        "nodeCount": len(nodes),
        "edgeCount": len(edges),
        "nodes": nodes,
        "edges": edges,
        "headlineAnalysis": {
            "importances": sorted(set(importances)),
            "censuses": [str(path) for path in census_paths],
            "claims": claim_rows,
            "familyCounts": family_counts,
            "resolutionWarnings": resolution_warnings,
            "targetClosureNodeCount": len(closure.nodes),
            "targetClosureEdgeCount": len(closure.edges),
        },
        "sourceSemanticIndex": {
            "project": semantic_payload.get("project"),
            "libraries": semantic_payload.get("libraries", []),
            "importRoots": semantic_payload.get("importRoots", []),
            "nodeCount": semantic_payload.get("nodeCount"),
            "edgeCount": semantic_payload.get("edgeCount"),
        },
    }
