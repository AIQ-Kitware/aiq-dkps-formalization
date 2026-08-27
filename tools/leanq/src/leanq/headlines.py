"""Census-aware headline analyses over saved semantic graphs.

This module is deliberately Lean-free.  It consumes the broad semantic index
written by ``leanq graph-index`` and paper census JSON files, then answers:

* which headline claims are on the dependency path to a chosen target;
* which declaration from a census claim is actually consumed;
* the nearest Acharyya and Quench integration declarations;
* the nearest downstream Quench headline claim; and
* exact witness paths for every collapsed visual edge.

The primary dependency view keeps the real declaration DAG: every canonical
headline declaration is a seed, every indexed dependency in their union closure
is retained, and census data is attached as metadata.  The older compact
target-consumption analysis remains available as an explicitly selected view.

The census is treated as claim metadata, while all reachability facts come from
the elaborated declaration graph.  This module is intentionally Lean-free.
"""

from __future__ import annotations

import json
from collections import Counter, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping, Sequence

from .graph import (
    DependencyGraph,
    declarations_from_graph_payload,
    environment_dependency_graph,
    strongly_connected_components,
    target_dependency_graph,
)
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
    source_kind: str | None
    source_anchor: str | None
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
                    source_kind=(
                        None if row.get("source_kind") is None else str(row.get("source_kind"))
                    ),
                    source_anchor=(
                        None if row.get("source_anchor") is None else str(row.get("source_anchor"))
                    ),
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


#: Census ``source_kind`` values that a paper's headline *theorems* use.  Davis--Kahan
#: states its four Section 2 headline results without numbers, so both spellings count;
#: a census definition or standing assumption is a landmark but not a headline theorem.
DEFAULT_CLAIM_SOURCE_KINDS: tuple[str, ...] = ("theorem", "unnumbered_theorem")


def _default_claim_selection(
    claim_rows: Sequence[Mapping], explicit: Sequence[str] = ()
) -> list[str]:
    """Claim node ids the viewer selects on load.

    Without an explicit request this is every headline *theorem* row: the four
    Davis--Kahan Section 2 theorems, both Yu--Wang--Samworth Theorem 2 conclusions,
    and both Quench Theorem 2 conclusions.  Estimator definitions and standing
    assumptions stay available in the sidebar but start unselected.
    """
    if explicit:
        wanted = set(explicit)
        chosen = [
            str(row["nodeId"])
            for row in claim_rows
            if row.get("id") in wanted or row.get("nodeId") in wanted
        ]
        missing = sorted(
            wanted
            - {str(row.get("id")) for row in claim_rows}
            - {str(row.get("nodeId")) for row in claim_rows}
        )
        if missing:
            raise ProjectError(
                "requested default claim(s) absent from the loaded censuses: "
                + ", ".join(missing)
            )
        return chosen
    chosen = [
        str(row["nodeId"])
        for row in claim_rows
        if str(row.get("sourceKind") or "") in DEFAULT_CLAIM_SOURCE_KINDS
    ]
    return chosen or [str(row["nodeId"]) for row in claim_rows]


def analyze_consumption_headlines(
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
        # Preserve the semantic review distinction without discarding exact
        # registered uses.  Canonical/supporting consumption remains stronger;
        # any other declaration explicitly listed by the census is reported as
        # registered support rather than silently turning a real YWS/DK use into
        # "not consumed".
        other_consumed = other_observed
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
                "sourceKind": claim.source_kind,
                "sourceAnchor": claim.source_anchor,
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
            "targetClosureLibraryCounts": dict(
                sorted(
                    Counter(
                        decl.library or "Other" for decl in closure.nodes.values()
                    ).items()
                )
            ),
        },
        "sourceSemanticIndex": {
            "project": semantic_payload.get("project"),
            "libraries": semantic_payload.get("libraries", []),
            "importRoots": semantic_payload.get("importRoots", []),
            "nodeCount": semantic_payload.get("nodeCount"),
            "edgeCount": semantic_payload.get("edgeCount"),
        },
    }


def _resolved_realizations(
    claim: CensusClaim, table: Mapping[str, Decl]
) -> tuple[list[str], list[str], list[dict]]:
    """Resolve canonical/supporting declarations without fuzzy namespace guesses."""
    warnings: list[dict] = []

    def resolve_many(raw_names: Iterable[str]) -> list[str]:
        result: list[str] = []
        for raw in raw_names:
            name, warning = _resolve_census_name(table, raw)
            if name is not None:
                if name not in result:
                    result.append(name)
            else:
                warnings.append(
                    {
                        "claim": claim.id,
                        "family": claim.family,
                        "declaration": raw,
                        "warning": warning or "could not resolve",
                    }
                )
        return result

    # A reviewed canonical list is authoritative.  Older censuses deliberately
    # used lean_declarations as their realization list, so retain that exact,
    # documented fallback rather than inventing a representative.
    canonical_raw = (
        claim.canonical_declarations
        if claim.canonical_declarations
        else claim.declarations
    )
    canonical = resolve_many(canonical_raw)
    supporting = resolve_many(claim.supporting_declarations)
    supporting = [name for name in supporting if name not in canonical]
    return canonical, supporting, warnings


def _dependency_walk(
    headline: str, incoming: Mapping[str, Sequence[str]]
) -> tuple[dict[str, int], dict[str, str | None]]:
    """Shortest distances from a headline to its dependencies (reverse edges)."""
    distance = {headline: 0}
    previous: dict[str, str | None] = {headline: None}
    queue: deque[str] = deque([headline])
    while queue:
        consumer = queue.popleft()
        for dependency in incoming.get(consumer, ()):
            if dependency not in distance:
                distance[dependency] = distance[consumer] + 1
                previous[dependency] = consumer
                queue.append(dependency)
    return distance, previous


def _dependency_path(
    headline: str, dependency: str, previous: Mapping[str, str | None]
) -> list[str]:
    """Return headline -> ... -> dependency despite stored edges pointing back."""
    result = [dependency]
    while result[-1] != headline:
        parent = previous.get(result[-1])
        if parent is None:
            return []
        result.append(parent)
    result.reverse()
    return result


def _topological_depths(graph: DependencyGraph) -> dict[str, int]:
    """Longest dependency-to-consumer layer on the exact SCC condensation DAG."""
    components = strongly_connected_components(graph.nodes, graph.edges)
    component_of = {
        name: index for index, component in enumerate(components) for name in component
    }
    outgoing = {index: set() for index in range(len(components))}
    indegree = {index: 0 for index in range(len(components))}
    for source, target in graph.edges:
        left, right = component_of[source], component_of[target]
        if left != right and right not in outgoing[left]:
            outgoing[left].add(right)
            indegree[right] += 1
    depth = {index: 0 for index in range(len(components))}
    queue: deque[int] = deque(sorted(index for index, value in indegree.items() if value == 0))
    while queue:
        source = queue.popleft()
        for target in sorted(outgoing[source]):
            depth[target] = max(depth[target], depth[source] + 1)
            indegree[target] -= 1
            if indegree[target] == 0:
                queue.append(target)
    return {name: depth[component_of[name]] for name in graph.nodes}


def _structural_projection(
    graph: DependencyGraph,
    *,
    headline_nodes: set[str],
    supporting_nodes: set[str],
    shared_nodes: set[str],
    frontier_nodes: set[str],
    target_nodes: set[str],
) -> tuple[set[str], list[dict]]:
    """Collapse only private linear chains, preserving topology and witnesses."""
    outgoing, incoming = _adjacency(graph)
    keep = set(headline_nodes) | set(supporting_nodes) | set(shared_nodes)
    keep |= set(frontier_nodes) | set(target_nodes)
    for name in graph.nodes:
        if len(incoming[name]) != 1 or len(outgoing[name]) != 1:
            keep.add(name)
    for source, target in graph.edges:
        if graph.nodes[source].library != graph.nodes[target].library:
            keep.add(source)
            keep.add(target)

    edges: list[dict] = []
    seen: set[tuple[str, str, tuple[str, ...]]] = set()
    for source in sorted(keep):
        for first in outgoing.get(source, ()):
            witness = [source, first]
            current = first
            local_seen = {source}
            while current not in keep:
                if current in local_seen or len(outgoing[current]) != 1:
                    break
                local_seen.add(current)
                current = outgoing[current][0]
                witness.append(current)
            if current not in keep or current == source:
                continue
            key = (source, current, tuple(witness))
            if key in seen:
                continue
            seen.add(key)
            edges.append(
                {
                    "source": source,
                    "target": current,
                    "direct": len(witness) == 2,
                    "witness": witness,
                    "collapsedNodeCount": max(0, len(witness) - 2),
                }
            )
    return keep, edges


def analyze_dependency_headlines(
    semantic_payload: Mapping,
    *,
    targets: Sequence[str] = (),
    census_paths: Sequence[Path],
    importances: Iterable[str] = ("headline",),
    include_supporting: bool = False,
    default_claims: Sequence[str] = (),
) -> dict:
    """Build the exact union of real headline declaration dependency closures."""
    decls = declarations_from_graph_payload(semantic_payload)
    table = {decl.name: decl for decl in decls}
    claims = load_census_claims(census_paths, importances=importances)
    warnings: list[dict] = []
    claim_rows: list[dict] = []
    headline_claims: dict[str, list[dict]] = {}
    support_claims: dict[str, list[dict]] = {}
    canonical_seeds: list[str] = []
    supporting_seeds: list[str] = []

    for claim in claims:
        canonical, supporting, claim_warnings = _resolved_realizations(claim, table)
        warnings.extend(claim_warnings)
        metadata = {
            "nodeId": _claim_node_id(claim),
            "claimId": claim.id,
            "claimTitle": claim.title,
            "headlineFamily": claim.family,
            "census": claim.census,
            "realizationRole": (
                "canonical" if claim.canonical_declarations else "registered-fallback"
            ),
        }
        for name in canonical:
            headline_claims.setdefault(name, []).append(metadata)
            if name not in canonical_seeds:
                canonical_seeds.append(name)
        for name in supporting:
            support_claims.setdefault(name, []).append(metadata)
            if name not in supporting_seeds:
                supporting_seeds.append(name)
        claim_rows.append(
            {
                "nodeId": _claim_node_id(claim),
                "census": claim.census,
                "family": claim.family,
                "id": claim.id,
                "title": claim.title,
                "importance": claim.importance,
                "status": claim.status,
                "sourceKind": claim.source_kind,
                "sourceAnchor": claim.source_anchor,
                "declaredDeclarations": list(claim.declarations),
                "canonicalDeclarations": canonical,
                "canonicalSource": (
                    "semantic-review"
                    if claim.canonical_declarations
                    else "lean-declarations-fallback"
                ),
                "supportingDeclarations": supporting,
            }
        )

    if not canonical_seeds:
        raise ProjectError("no canonical headline declarations resolved in the semantic index")
    union_seeds = canonical_seeds + ([x for x in supporting_seeds if x not in canonical_seeds] if include_supporting else [])
    graph = target_dependency_graph(decls, union_seeds)
    outgoing, incoming = _adjacency(graph)
    coverage: dict[str, set[str]] = {name: set() for name in graph.nodes}
    walks: dict[str, tuple[dict[str, int], dict[str, str | None]]] = {}
    for headline in canonical_seeds:
        distances, previous = _dependency_walk(headline, incoming)
        walks[headline] = (distances, previous)
        for name in distances:
            coverage[name].add(headline)

    # A claim often registers several canonical realizations of one printed
    # theorem: a general form, a specialization, a packaged corollary.  The
    # leafmost ones are those no *other* realization of the same claim consumes,
    # so selecting them alone still covers the claim's whole dependency closure.
    for row in claim_rows:
        realizations = [name for name in row["canonicalDeclarations"] if name in graph.nodes]
        leaves = []
        for name in realizations:
            downstream = _dependency_walk(name, outgoing)[0]
            if not any(other != name and other in downstream for other in realizations):
                leaves.append(name)
        row["leafDeclarations"] = leaves or realizations
        # Which packages each realization actually reaches.  A claim whose
        # realizations never leave their own library is a visible signal that the
        # census registered the abstract form of the theorem rather than the
        # instantiation that consumes the shared mathematics.
        reach: dict[str, dict[str, int]] = {}
        for name in realizations:
            distances, _ = _dependency_walk(name, incoming)
            counts = Counter(graph.nodes[dep].library or "Other" for dep in distances)
            reach[name] = dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))
        row["realizationClosureLibraries"] = reach

    shared = {name for name, ids in coverage.items() if len(ids) >= 2}
    frontier = {
        name
        for name in shared
        if any(coverage[target] != coverage[name] for target in outgoing.get(name, ()))
    }
    depths = _topological_depths(graph)

    resolved_targets: tuple[str, ...] = ()
    target_closure: DependencyGraph | None = None
    target_distance: dict[str, int] = {}
    if targets:
        target_closure = target_dependency_graph(decls, targets)
        resolved_targets = target_closure.targets
        target_distance, _ = _distance_to_targets(target_closure)

    headline_rows: list[dict] = []
    for headline in canonical_seeds:
        distances, previous = walks[headline]
        candidates = [name for name in distances if name != headline and name in shared]
        nearest = min(candidates, key=lambda name: (distances[name], name)) if candidates else None
        dependency_names = set(distances) - {headline}
        exclusive = {name for name in dependency_names if coverage[name] == {headline}}
        shared_for_headline = dependency_names & shared
        headline_rows.append(
            {
                "declaration": headline,
                "claimIds": [row["claimId"] for row in headline_claims[headline]],
                "claims": headline_claims[headline],
                "dependencyCount": len(dependency_names),
                "directDependencyCount": len(incoming.get(headline, ())),
                "directConsumerCount": len(outgoing.get(headline, ())),
                "maximumDependencyDepth": depths[headline],
                "dependencyLibraryCount": len({graph.nodes[name].library for name in distances}),
                "dependencyModuleCount": len({graph.nodes[name].module for name in distances}),
                "exclusiveDependencyCount": len(exclusive),
                "sharedDependencyCount": len(shared_for_headline),
                "nearestSharedDependency": nearest,
                "distanceToNearestSharedDependency": None if nearest is None else distances[nearest],
                "pathToNearestSharedDependency": [] if nearest is None else _dependency_path(headline, nearest, previous),
                "consumedByTarget": headline in target_distance,
                "distanceToTarget": target_distance.get(headline),
            }
        )

    pair_rows: list[dict] = []
    for index, left in enumerate(canonical_seeds):
        left_dist, left_previous = walks[left]
        for right in canonical_seeds[index + 1 :]:
            right_dist, right_previous = walks[right]
            common = (set(left_dist) & set(right_dist)) - {left, right}
            if not common:
                continue
            nearest = min(
                common,
                key=lambda name: (
                    max(left_dist[name], right_dist[name]),
                    left_dist[name] + right_dist[name],
                    name,
                ),
            )
            pair_rows.append(
                {
                    "headlines": [left, right],
                    "nearestSharedDependency": nearest,
                    "distances": [left_dist[nearest], right_dist[nearest]],
                    "exclusivePathNodesBeforeOverlap": [
                        max(0, left_dist[nearest] - 1),
                        max(0, right_dist[nearest] - 1),
                    ],
                    "paths": [
                        _dependency_path(left, nearest, left_previous),
                        _dependency_path(right, nearest, right_previous),
                    ],
                    "commonDependencyCount": len(common),
                }
            )

    target_nodes = set(resolved_targets) & set(graph.nodes)
    structural_nodes, structural_edges = _structural_projection(
        graph,
        headline_nodes=set(canonical_seeds),
        supporting_nodes=set(supporting_seeds) & set(graph.nodes),
        shared_nodes=shared,
        frontier_nodes=frontier,
        target_nodes=target_nodes,
    )

    nodes: list[dict] = []
    for name in sorted(graph.nodes):
        decl = graph.nodes[name]
        claims_here = headline_claims.get(name, [])
        supports_here = support_claims.get(name, [])
        coverage_ids = sorted(coverage[name])
        row = decl.to_json()
        row.pop("deps", None)
        row.pop("name", None)
        nodes.append(
            {
                "id": name,
                **row,
                "target": name in target_nodes,
                "headline": bool(claims_here),
                "headlineRole": (
                    (
                        "canonical"
                        if any(row["realizationRole"] == "canonical" for row in claims_here)
                        else "registered-fallback"
                    )
                    if claims_here
                    else ("supporting" if supports_here else None)
                ),
                "headlineClaims": claims_here,
                "supportingClaims": supports_here,
                "headlineCoverageCount": len(coverage_ids),
                "headlineCoverageIds": coverage_ids,
                "exclusiveToHeadline": coverage_ids[0] if len(coverage_ids) == 1 else None,
                "sharedDependency": name in shared,
                "sharedFrontier": name in frontier,
                "dependencyDepth": depths[name],
                "consumedByTarget": name in target_distance,
                "distanceToTarget": target_distance.get(name),
            }
        )

    family_counts: dict[str, dict[str, int]] = {}
    for claim in claim_rows:
        bucket = family_counts.setdefault(claim["family"], {"claims": 0, "canonicalDeclarations": 0, "supportingDeclarations": 0})
        bucket["claims"] += 1
        bucket["canonicalDeclarations"] += len(claim["canonicalDeclarations"])
        bucket["supportingDeclarations"] += len(claim["supportingDeclarations"])

    return {
        "schemaVersion": 2,
        "payloadKind": "headline-dependencies",
        "edgeDirection": "dependency-to-consumer",
        "targets": list(resolved_targets),
        "nodeCount": len(nodes),
        "edgeCount": len(graph.edges),
        "nodes": nodes,
        "edges": [
            {"source": source, "target": target, "direct": True}
            for source, target in sorted(graph.edges)
        ],
        "structuralNodeCount": len(structural_nodes),
        "structuralEdgeCount": len(structural_edges),
        "structuralNodeIds": sorted(structural_nodes),
        "structuralEdges": structural_edges,
        "headlineAnalysis": {
            "view": "dependencies",
            "importances": sorted(set(importances)),
            "censuses": [str(path) for path in census_paths],
            "claims": claim_rows,
            "defaultClaimSelection": _default_claim_selection(claim_rows, default_claims),
            "headlines": headline_rows,
            "headlinePairs": pair_rows,
            "familyCounts": family_counts,
            "resolutionWarnings": warnings,
            "headlineDeclarationCount": len(canonical_seeds),
            "supportingDeclarationCount": len(supporting_seeds),
            "sharedDependencyCount": len(shared),
            "sharedFrontierCount": len(frontier),
            "includeSupportingAsSeeds": include_supporting,
            "targetAnnotation": None if not resolved_targets else {
                "targets": list(resolved_targets),
                "closureNodeCount": len(target_closure.nodes) if target_closure else 0,
                "closureEdgeCount": len(target_closure.edges) if target_closure else 0,
            },
        },
        "sourceSemanticIndex": {
            "project": semantic_payload.get("project"),
            "libraries": semantic_payload.get("libraries", []),
            "importRoots": semantic_payload.get("importRoots", []),
            "nodeCount": semantic_payload.get("nodeCount"),
            "edgeCount": semantic_payload.get("edgeCount"),
        },
    }


def analyze_headlines(
    semantic_payload: Mapping,
    *,
    targets: Sequence[str] = (),
    census_paths: Sequence[Path],
    importances: Iterable[str] = ("headline",),
    view: str = "dependencies",
    include_supporting: bool = False,
    default_claims: Sequence[str] = (),
) -> dict:
    """Dispatch to the exact dependency view or legacy compact consumption view."""
    if view == "dependencies":
        return analyze_dependency_headlines(
            semantic_payload,
            targets=targets,
            census_paths=census_paths,
            importances=importances,
            include_supporting=include_supporting,
            default_claims=default_claims,
        )
    if view == "consumption":
        return analyze_consumption_headlines(
            semantic_payload,
            targets=targets,
            census_paths=census_paths,
            importances=importances,
        )
    raise ProjectError(f"unknown headline view {view!r}")


def prepare_project_explorer(
    semantic_payload: Mapping,
    *,
    census_paths: Sequence[Path] = (),
    importances: Iterable[str] = ("headline",),
    targets: Sequence[str] = (),
    default_claims: Sequence[str] = (),
) -> dict:
    """Annotate a complete semantic index for the whole-project HTML explorer.

    No declaration or direct edge is removed.  Headline dependency analysis is
    merged back as landmark metadata; the browser derives changing visible
    projections from this one complete payload.
    """
    if semantic_payload.get("payloadKind") != "semantic-index":
        raise ProjectError("project explorer input must be a reusable semantic index")
    decls = declarations_from_graph_payload(semantic_payload)
    graph = environment_dependency_graph(decls)
    depths = _topological_depths(graph)
    outgoing, incoming = _adjacency(graph)
    dependency_result = None
    annotated: dict[str, dict] = {}
    analysis: dict = {
        "view": "whole-project",
        "claims": [],
        "defaultClaimSelection": [],
        "headlines": [],
        "headlinePairs": [],
        "familyCounts": {},
        "resolutionWarnings": [],
        "headlineDeclarationCount": 0,
        "supportingDeclarationCount": 0,
        "sharedDependencyCount": 0,
        "sharedFrontierCount": 0,
    }
    if census_paths:
        dependency_result = analyze_dependency_headlines(
            semantic_payload,
            targets=targets,
            census_paths=census_paths,
            importances=importances,
            default_claims=default_claims,
        )
        annotated = {row["id"]: row for row in dependency_result["nodes"]}
        analysis = dict(dependency_result["headlineAnalysis"])
        analysis["view"] = "whole-project"
        # Supporting realizations are landmarks even when they are downstream
        # of, rather than dependencies of, every canonical headline seed.
        for claim in analysis["claims"]:
            metadata = {
                "nodeId": claim["nodeId"],
                "claimId": claim["id"],
                "claimTitle": claim["title"],
                "headlineFamily": claim["family"],
                "census": claim["census"],
            }
            for name in claim["supportingDeclarations"]:
                row = annotated.setdefault(name, {"id": name})
                support_rows = row.setdefault("supportingClaims", [])
                if metadata not in support_rows:
                    support_rows.append(metadata)
                row.setdefault("headlineRole", "supporting")

    resolved_target_set = set(dependency_result.get("targets", ())) if dependency_result else set()

    nodes: list[dict] = []
    for name in sorted(graph.nodes):
        decl = graph.nodes[name]
        landmark = annotated.get(name, {})
        row = decl.to_json()
        row.pop("deps", None)
        row.pop("name", None)
        nodes.append(
            {
                "id": name,
                **row,
                "target": name in resolved_target_set,
                "dependencyDepth": depths[name],
                "directDependencyCount": len(incoming[name]),
                "directConsumerCount": len(outgoing[name]),
                "headline": bool(landmark.get("headline")),
                "headlineRole": landmark.get("headlineRole"),
                "headlineClaims": landmark.get("headlineClaims", []),
                "supportingClaims": landmark.get("supportingClaims", []),
                "headlineCoverageCount": landmark.get("headlineCoverageCount", 0),
                "headlineCoverageIds": landmark.get("headlineCoverageIds", []),
                "exclusiveToHeadline": landmark.get("exclusiveToHeadline"),
                "sharedDependency": bool(landmark.get("sharedDependency")),
                "sharedFrontier": bool(landmark.get("sharedFrontier")),
                "consumedByTarget": bool(landmark.get("consumedByTarget")),
                "distanceToTarget": landmark.get("distanceToTarget"),
            }
        )

    cluster_stats: dict[str, dict[str, dict]] = {"libraries": {}, "modules": {}}
    for level, key_fn in (
        ("libraries", lambda d: d.library or "Other"),
        ("modules", lambda d: d.module or "Other"),
    ):
        for decl in graph.nodes.values():
            key = key_fn(decl)
            bucket = cluster_stats[level].setdefault(
                key,
                {
                    "declarationCount": 0,
                    "internalEdgeCount": 0,
                    "maximumDependencyDepth": 0,
                    "headlineCount": 0,
                    "sharedDependencyCount": 0,
                    "libraries": set(),
                    "modules": set(),
                },
            )
            bucket["declarationCount"] += 1
            bucket["maximumDependencyDepth"] = max(bucket["maximumDependencyDepth"], depths[decl.name])
            bucket["headlineCount"] += int(bool(annotated.get(decl.name, {}).get("headline")))
            bucket["sharedDependencyCount"] += int(bool(annotated.get(decl.name, {}).get("sharedDependency")))
            bucket["libraries"].add(decl.library or "Other")
            bucket["modules"].add(decl.module or "Other")
        for source, target in graph.edges:
            source_key = key_fn(graph.nodes[source])
            if source_key == key_fn(graph.nodes[target]):
                cluster_stats[level][source_key]["internalEdgeCount"] += 1
        for bucket in cluster_stats[level].values():
            bucket["libraryCount"] = len(bucket.pop("libraries"))
            bucket["moduleCount"] = len(bucket.pop("modules"))

    result = dict(semantic_payload)
    result.update(
        {
            "schemaVersion": 3,
            "payloadKind": "project-explorer",
            "targets": sorted(resolved_target_set),
            "nodeCount": len(nodes),
            "edgeCount": len(graph.edges),
            "nodes": nodes,
            "edges": [
                {"source": source, "target": target, "direct": True}
                for source, target in sorted(graph.edges)
            ],
            "headlineAnalysis": analysis,
            "clusterStats": cluster_stats,
            "explorer": {
                "completeGraphEmbedded": True,
                "projectionComputedInBrowser": True,
                "defaultPreset": "overview",
                "sourcePayloadKind": "semantic-index",
            },
        }
    )
    return result
