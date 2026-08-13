#!/usr/bin/env python3
"""Shared review-priority schema for source-census rows.

`importance` is deliberately about *external semantic review priority*, not proof
status or mathematical truth.  It lets review renderers select a small auditable
surface without changing either paper's full source census.
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


def validate_importance_schema(data: dict, items: list[dict], fail) -> None:
    defs = data.get("importance_definitions")
    if not isinstance(defs, dict):
        fail("importance_definitions is required")
    if set(defs) != set(IMPORTANCE_ORDER):
        fail(
            "importance_definitions must contain exactly: "
            + ", ".join(IMPORTANCE_ORDER)
        )
    for key, expected in IMPORTANCE_DEFINITIONS.items():
        if not isinstance(defs.get(key), str) or not defs[key].strip():
            fail(f"importance_definitions.{key} must be a nonempty string")

    for item in items:
        item_id = item.get("id", "<missing-id>")
        importance = item.get("importance")
        if importance not in IMPORTANCE_ORDER:
            fail(f"{item_id} has invalid importance: {importance!r}")
        review = item.get("semantic_review")
        if importance == "headline":
            if not isinstance(review, dict):
                fail(f"{item_id} is headline but has no semantic_review object")
            for key in ("group", "group_title", "claim", "declarations"):
                if key not in review:
                    fail(f"{item_id}.semantic_review is missing {key}")
            if not isinstance(review["group"], str) or not review["group"].strip():
                fail(f"{item_id}.semantic_review.group must be nonempty")
            if not isinstance(review["group_title"], str) or not review["group_title"].strip():
                fail(f"{item_id}.semantic_review.group_title must be nonempty")
            if not isinstance(review["claim"], str) or not review["claim"].strip():
                fail(f"{item_id}.semantic_review.claim must be nonempty")
            if not isinstance(review["declarations"], list) or not review["declarations"]:
                fail(f"{item_id}.semantic_review.declarations must be a nonempty list")
            missing = [d for d in review["declarations"] if d not in item.get("lean_declarations", [])]
            if missing:
                fail(
                    f"{item_id}.semantic_review.declarations must be census declarations; "
                    f"missing from lean_declarations: {', '.join(missing)}"
                )
        variants = item.get("semantic_review_variants", [])
        if not isinstance(variants, list):
            fail(f"{item_id}.semantic_review_variants must be a list")
        for index, variant in enumerate(variants):
            if not isinstance(variant, dict):
                fail(f"{item_id}.semantic_review_variants[{index}] must be an object")
            for key in ("id", "title", "claim", "declarations", "provenance_note"):
                if key not in variant:
                    fail(f"{item_id}.semantic_review_variants[{index}] is missing {key}")
            if not isinstance(variant["declarations"], list) or not variant["declarations"]:
                fail(f"{item_id}.semantic_review_variants[{index}].declarations must be nonempty")


def selected_by_importance(items: list[dict], threshold: str) -> list[dict]:
    if threshold not in IMPORTANCE_ORDER:
        raise ValueError(f"unknown importance threshold: {threshold}")
    cutoff = IMPORTANCE_ORDER[threshold]
    return [item for item in items if IMPORTANCE_ORDER[item["importance"]] <= cutoff]
