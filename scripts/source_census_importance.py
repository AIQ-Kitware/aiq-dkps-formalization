#!/usr/bin/env python3
"""Shared external-review priority and semantic-review schema.

`importance` is deliberately orthogonal to proof status and source completeness.
It controls which claims appear in the compact semantic-alignment packet.

Headline rows additionally carry an *intentional audit surface*: a normalized
source statement, compiler-resolved canonical Lean declarations, a curated set
of local definitions whose meanings are needed to read those declarations, and
a clause-by-clause source/Lean correspondence map.  The renderer never tries to
recursively expand every project-local name.
"""
from __future__ import annotations

IMPORTANCE_ORDER = {
    "headline": 0,
    "major": 1,
    "supporting": 2,
    "technical": 3,
}

IMPORTANCE_DEFINITIONS = {
    "headline": (
        "Default external semantic-alignment surface: the small set of central "
        "paper claims a reviewer should inspect first."
    ),
    "major": (
        "Important named theorem or major consequence, included when requesting "
        "a broader review than the default headline surface."
    ),
    "supporting": (
        "Mathematically substantive supporting result, example, corollary, or "
        "structural statement, normally omitted from the concise external packet."
    ),
    "technical": (
        "Definition, proof ingredient, numerical working, appendix machinery, or "
        "other source item retained for full-paper completeness rather than the "
        "concise semantic-alignment packet."
    ),
}


def _nonempty_string(value) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _validate_source_statement(item_id: str, statement: object, fail) -> None:
    if not isinstance(statement, dict):
        fail(f"{item_id}.semantic_review.source_statement must be an object")
    for key in ("setup", "hypotheses", "conclusions", "scope"):
        value = statement.get(key)
        if not isinstance(value, list):
            fail(f"{item_id}.semantic_review.source_statement.{key} must be a list")
        if any(not _nonempty_string(x) for x in value):
            fail(f"{item_id}.semantic_review.source_statement.{key} must contain strings")
    if not statement.get("hypotheses") or not statement.get("conclusions"):
        fail(f"{item_id}.semantic_review.source_statement needs hypotheses and conclusions")


def _validate_context(item_id: str, context: object, fail) -> None:
    if not isinstance(context, list):
        fail(f"{item_id}.semantic_review.context_declarations must be a list")
    for index, entry in enumerate(context):
        if not isinstance(entry, dict):
            fail(f"{item_id}.semantic_review.context_declarations[{index}] must be an object")
        if not _nonempty_string(entry.get("name")):
            fail(f"{item_id}.semantic_review.context_declarations[{index}].name must be nonempty")
        if not _nonempty_string(entry.get("mathematical_role")):
            fail(f"{item_id}.semantic_review.context_declarations[{index}].mathematical_role must be nonempty")


def _validate_clause_map(item_id: str, mapping: object, fail) -> None:
    if not isinstance(mapping, list) or not mapping:
        fail(f"{item_id}.semantic_review.clause_map must be a nonempty list")
    for index, entry in enumerate(mapping):
        if not isinstance(entry, dict):
            fail(f"{item_id}.semantic_review.clause_map[{index}] must be an object")
        for key in ("source_clause", "lean_realization"):
            if not _nonempty_string(entry.get(key)):
                fail(f"{item_id}.semantic_review.clause_map[{index}].{key} must be nonempty")
        status = entry.get("status", "claimed_exact")
        if status not in {"claimed_exact", "derived", "scope_companion"}:
            fail(f"{item_id}.semantic_review.clause_map[{index}] has invalid status {status!r}")


def _validate_review(item_id: str, review: object, census_decls: list[str], fail) -> None:
    if not isinstance(review, dict):
        fail(f"{item_id} is headline but has no semantic_review object")
    for key in ("group", "group_title", "claim"):
        if not _nonempty_string(review.get(key)):
            fail(f"{item_id}.semantic_review.{key} must be nonempty")

    _validate_source_statement(item_id, review.get("source_statement"), fail)

    canonical = review.get("canonical_declarations")
    supporting = review.get("supporting_declarations", [])
    if not isinstance(canonical, list) or not canonical or any(not _nonempty_string(x) for x in canonical):
        fail(f"{item_id}.semantic_review.canonical_declarations must be a nonempty string list")
    if not isinstance(supporting, list) or any(not _nonempty_string(x) for x in supporting):
        fail(f"{item_id}.semantic_review.supporting_declarations must be a string list")
    # Keep every reviewed theorem anchored to the maintained census declaration list.
    missing = [d for d in canonical + supporting if d not in census_decls]
    if missing:
        fail(
            f"{item_id} semantic-review declarations must be census declarations; "
            f"missing from lean_declarations: {', '.join(missing)}"
        )

    _validate_context(item_id, review.get("context_declarations", []), fail)
    _validate_clause_map(item_id, review.get("clause_map"), fail)


def validate_importance_schema(data: dict, items: list[dict], fail) -> None:
    defs = data.get("importance_definitions")
    if not isinstance(defs, dict):
        fail("importance_definitions is required")
    if set(defs) != set(IMPORTANCE_ORDER):
        fail("importance_definitions must contain exactly: " + ", ".join(IMPORTANCE_ORDER))
    for key in IMPORTANCE_DEFINITIONS:
        if not _nonempty_string(defs.get(key)):
            fail(f"importance_definitions.{key} must be a nonempty string")

    for item in items:
        item_id = item.get("id", "<missing-id>")
        importance = item.get("importance")
        if importance not in IMPORTANCE_ORDER:
            fail(f"{item_id} has invalid importance: {importance!r}")
        if importance == "headline":
            _validate_review(item_id, item.get("semantic_review"), item.get("lean_declarations", []), fail)

        variants = item.get("semantic_review_variants", [])
        if not isinstance(variants, list):
            fail(f"{item_id}.semantic_review_variants must be a list")
        for index, variant in enumerate(variants):
            prefix = f"{item_id}.semantic_review_variants[{index}]"
            if not isinstance(variant, dict):
                fail(f"{prefix} must be an object")
            for key in ("id", "title", "claim", "provenance_note"):
                if not _nonempty_string(variant.get(key)):
                    fail(f"{prefix}.{key} must be nonempty")
            # Variants use the same audit-surface vocabulary as headline rows.
            _validate_source_statement(prefix, variant.get("source_statement"), fail)
            canonical = variant.get("canonical_declarations")
            supporting = variant.get("supporting_declarations", [])
            if not isinstance(canonical, list) or not canonical:
                fail(f"{prefix}.canonical_declarations must be nonempty")
            if not isinstance(supporting, list):
                fail(f"{prefix}.supporting_declarations must be a list")
            missing = [d for d in canonical + supporting if d not in item.get("lean_declarations", [])]
            # Derived variants are allowed to point outside the parent's source-row declaration
            # list, because they are explicitly labelled derived review targets.
            _validate_context(prefix, variant.get("context_declarations", []), fail)
            _validate_clause_map(prefix, variant.get("clause_map"), fail)


def selected_by_importance(items: list[dict], threshold: str) -> list[dict]:
    if threshold not in IMPORTANCE_ORDER:
        raise ValueError(f"unknown importance threshold: {threshold}")
    cutoff = IMPORTANCE_ORDER[threshold]
    return [item for item in items if IMPORTANCE_ORDER[item["importance"]] <= cutoff]
