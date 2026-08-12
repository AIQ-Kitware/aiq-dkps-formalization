#!/usr/bin/env python3
"""Validate the result-level denominator for the Davis--Kahan 1970 100% claim.

This checker deliberately separates two different questions:

* source fidelity: did the distributable TeX preserve the mathematical content
  of the paper?  The fine-grained source-atom inventory answers that question.
* formalization completion: did Lean exactly represent every result that
  Davis--Kahan actually establish in this paper (the named
  theorem/proposition/lemma/corollary environments plus the four Section 2
  headline theorems)?  This result inventory is the only denominator for the
  project's "100% formalized" claim.

Intermediate proof identities, proof equations, derivations, historical remarks,
and numerical working may be source-fidelity atoms without becoming Lean proof
obligations.

The compact result inventory is now the maintained completion contract.
Terminality is computed only from its 29 result entries, never from the
fine-grained source atoms or the 49 organizational statement-map rows.  The
source atoms remain a total reviewer-facing accounting surface: each one must
say which counted result it supports, or why it is intentionally outside the
completion denominator.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
STATEMENT_MAP_PATH = ROOT / "dev/davis-kahan-1970-statement-map.json"
CENSUS_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.json"
TEX_PATH = ROOT / "prose/distilled_literature/DavisKahan1970_part_III.tex"
DEFAULT_CANDIDATES = (
    ROOT / "dev/davis-kahan-1970-formalization-result-inventory.json",
    ROOT / "dev/davis-kahan-1970-result-inventory.json",
)

TERMINAL_RESULT_DISPOSITIONS = {
    "proved_exact",
    "compiled_exact",
    "refuted_as_transcribed",
}
TERMINAL_VERIFICATIONS = {"proved_in_build"}
TERMINAL_SEMANTIC_CERTIFICATIONS = {"accepted"}
TERMINAL_REPAIR_STATUSES = {"proved", "documented_no_satisfactory_repair"}
COUNTED_RESULT_KINDS = {"unnumbered_theorem", "theorem", "proposition", "lemma", "corollary"}
RESULT_SUPPORT_ROLES = {
    "result", "stated_result", "result_support", "result_hypothesis", "result_scope"
}
NON_RESULT_ROLES = {
    "definition", "definition_only", "proof_only", "intermediate_proof",
    "derivation", "derivation_only", "historical", "historical_comment",
    "numerical_working", "expository", "open_question", "non_result",
}
BOUNDARY_REASON_CODES = {
    "counted_result_statement",
    "counted_result_hypothesis",
    "counted_result_scope",
    "definition_not_result",
    "proof_or_derivation_not_result",
    "introductory_background_not_designated_result",
    "section_setup_not_result",
    "expository_commentary_not_result",
    "sharpness_commentary_not_designated_result",
    "pre_result_setup_not_in_printed_statement",
    "proof_detail_not_in_printed_statement",
    "post_result_consequence_not_in_printed_statement",
    "post_result_scope_remark_not_in_printed_statement",
    "remark_or_example_not_result",
    "background_theory_not_designated_result",
    "restatement_of_counted_result",
    "pre_result_motivation_not_result",
    "post_result_interpretation_not_result",
    "section9_worked_example_not_result",
    "external_result_not_dk_result",
    "historical_knowledge_state",
    "deferred_unproved_claim",
    "open_question",
    "section10_motivation_not_result",
}


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _first(mapping: dict[str, Any], names: tuple[str, ...], default: Any = None) -> Any:
    for name in names:
        if name in mapping:
            return mapping[name]
    return default


def discover_inventory(explicit: Path | None = None) -> Path | None:
    if explicit is not None:
        path = explicit if explicit.is_absolute() else ROOT / explicit
        return path

    if STATEMENT_MAP_PATH.exists():
        statement_map = json.loads(STATEMENT_MAP_PATH.read_text(encoding="utf-8"))
        rel = _first(
            statement_map,
            (
                "formalization_result_inventory",
                "result_inventory",
                "completion_result_inventory",
            ),
        )
        if isinstance(rel, str) and rel.strip():
            return ROOT / rel

    for path in DEFAULT_CANDIDATES:
        if path.exists():
            return path
    return None


def _load_source_atoms() -> tuple[Path, dict[str, dict[str, Any]]]:
    statement_map = json.loads(STATEMENT_MAP_PATH.read_text(encoding="utf-8"))
    rel = statement_map.get("source_atom_inventory")
    if not isinstance(rel, str) or not rel.strip():
        fail("statement map does not declare source_atom_inventory")
    path = ROOT / rel
    if not path.exists():
        fail(f"source-fidelity inventory does not exist: {rel}")
    data = json.loads(path.read_text(encoding="utf-8"))
    atoms = data.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        fail("source-fidelity inventory must contain a nonempty atoms list")
    by_id: dict[str, dict[str, Any]] = {}
    for atom in atoms:
        atom_id = atom.get("id")
        if not isinstance(atom_id, str) or not atom_id or atom_id in by_id:
            fail(f"source-fidelity inventory has missing/duplicate atom id: {atom_id!r}")
        by_id[atom_id] = atom
    return path, by_id


def _registered_census_declarations() -> set[str]:
    data = json.loads(CENSUS_PATH.read_text(encoding="utf-8"))
    out: set[str] = set()
    for item in data.get("items", []):
        for key in ("lean_declarations", "review_declarations"):
            for declaration in item.get(key, []) or []:
                if isinstance(declaration, str):
                    out.add(declaration)
    return out


def _review_block(data: dict[str, Any]) -> dict[str, Any] | None:
    review = _first(
        data,
        (
            "result_inventory_review",
            "selection_review",
            "coverage_review",
        ),
    )
    return review if isinstance(review, dict) else None


def _result_items(data: dict[str, Any]) -> list[dict[str, Any]]:
    items = _first(data, ("results", "items"))
    if not isinstance(items, list) or not items:
        fail("formalization-result inventory must contain a nonempty results/items list")
    if not all(isinstance(item, dict) for item in items):
        fail("formalization-result inventory entries must be objects")
    return items


def _result_kind(item: dict[str, Any]) -> str | None:
    value = _first(item, ("result_kind", "source_kind", "kind"))
    return value if isinstance(value, str) else None


def _result_disposition(item: dict[str, Any]) -> str | None:
    value = _first(item, ("disposition", "status"))
    return value if isinstance(value, str) else None


def _semantic_certification(item: dict[str, Any]) -> str | None:
    value = _first(item, ("semantic_certification", "completion_certification"))
    return value if isinstance(value, str) else None


def _declarations(item: dict[str, Any]) -> list[str]:
    value = _first(item, ("lean_declarations", "review_declarations"), [])
    if value is None:
        return []
    if not isinstance(value, list) or not all(isinstance(x, str) for x in value):
        fail(f"{item.get('id', '<unknown>')}: Lean declarations must be a list of strings")
    return value


def _source_atom_ids(item: dict[str, Any]) -> list[str]:
    value = _first(item, ("source_atom_ids", "source_fidelity_atom_ids"), [])
    if not isinstance(value, list) or not value or not all(isinstance(x, str) for x in value):
        fail(f"{item.get('id', '<unknown>')}: source_atom_ids must be a nonempty list of strings")
    if len(value) != len(set(value)):
        fail(f"{item.get('id', '<unknown>')}: duplicate source_atom_ids")
    return value



def _classification_table(data: dict[str, Any], source_atoms: dict[str, dict[str, Any]]) -> dict[str, str]:
    """Return a total source-atom -> formalization-role classification when available."""
    external = _first(
        data,
        ("source_atom_classification", "source_atom_classifications", "formalization_classification"),
        {},
    )
    parsed: dict[str, str] = {}
    if isinstance(external, dict):
        for atom_id, value in external.items():
            if isinstance(value, str):
                parsed[atom_id] = value
            elif isinstance(value, dict):
                role = _first(value, ("role", "classification", "formalization_role"))
                if isinstance(role, str):
                    parsed[atom_id] = role
    elif isinstance(external, list):
        for item in external:
            if not isinstance(item, dict):
                continue
            atom_id = item.get("source_atom_id", item.get("id"))
            role = _first(item, ("role", "classification", "formalization_role"))
            if isinstance(atom_id, str) and isinstance(role, str):
                parsed[atom_id] = role

    for atom_id, atom in source_atoms.items():
        inline = _first(
            atom,
            ("formalization_role", "formalization_result_role", "completion_role"),
        )
        if isinstance(inline, str):
            if atom_id in parsed and parsed[atom_id] != inline:
                fail(
                    f"{atom_id}: source-fidelity inline formalization role {inline!r} disagrees with "
                    f"result-inventory classification {parsed[atom_id]!r}"
                )
            parsed[atom_id] = inline
    return parsed


def _validate_total_source_classification(
    data: dict[str, Any],
    source_atoms: dict[str, dict[str, Any]],
    obligation_atom_ids: set[str],
    *,
    require_terminal: bool,
) -> tuple[bool, str | None]:
    classification = _classification_table(data, source_atoms)
    missing = sorted(set(source_atoms) - set(classification))
    extra = sorted(set(classification) - set(source_atoms))
    if extra:
        fail("formalization classification references unknown source atoms: " + ", ".join(extra))
    if missing:
        message = (
            f"{len(missing)} source-fidelity atoms have no stated-result/non-result classification; "
            "a real stated result could still disappear between the fidelity and completion inventories"
        )
        if require_terminal:
            fail(message + f"; first missing: {missing[0]}")
        return False, message

    for atom_id, role in classification.items():
        if role not in RESULT_SUPPORT_ROLES | NON_RESULT_ROLES:
            fail(f"{atom_id}: unsupported formalization role {role!r}")
        if atom_id in obligation_atom_ids:
            if role not in RESULT_SUPPORT_ROLES:
                fail(
                    f"{atom_id}: selected by a formalization obligation but classified as non-result role {role!r}"
                )
            continue
        if role not in NON_RESULT_ROLES:
            fail(
                f"{atom_id}: classified as result-support role {role!r} but no formalization result selects it"
            )
    return True, None


def _validate_boundary_accounting(
    source_atoms: dict[str, dict[str, Any]],
    items: list[dict[str, Any]],
) -> None:
    """Check the explicit reviewer-facing boundary between fidelity and completion.

    The fine-grained source inventory is intentionally larger than the 29-result
    denominator.  This check makes that limitation visible rather than implicit:
    every source atom has a specific reason code, every result-support atom names
    the result(s) it supports, and every counted result partitions its primary
    source block into statement atoms versus adjacent fidelity-only material.
    """
    expected_links: dict[str, list[str]] = {atom_id: [] for atom_id in source_atoms}
    for item in items:
        result_id = item["id"]
        for atom_id in _source_atom_ids(item):
            expected_links[atom_id].append(result_id)

    role_to_reason = {
        "result": "counted_result_statement",
        "stated_result": "counted_result_statement",
        "result_support": "counted_result_statement",
        "result_hypothesis": "counted_result_hypothesis",
        "result_scope": "counted_result_scope",
    }
    for atom_id, atom in source_atoms.items():
        role = _first(atom, ("formalization_role", "formalization_result_role", "completion_role"))
        reason_code = atom.get("formalization_role_reason_code")
        reason = atom.get("formalization_role_reason")
        result_ids = atom.get("formalization_result_ids")
        if reason_code not in BOUNDARY_REASON_CODES:
            fail(f"{atom_id}: missing/unsupported formalization_role_reason_code {reason_code!r}")
        if not isinstance(reason, str) or not reason.strip():
            fail(f"{atom_id}: formalization_role_reason must explain the inclusion/exclusion decision")
        if not isinstance(result_ids, list) or not all(isinstance(x, str) for x in result_ids):
            fail(f"{atom_id}: formalization_result_ids must be a list of result ids")
        if result_ids != expected_links[atom_id]:
            fail(
                f"{atom_id}: formalization_result_ids disagree with the compact result inventory; "
                f"expected {expected_links[atom_id]!r}, got {result_ids!r}"
            )
        if role in RESULT_SUPPORT_ROLES:
            expected_reason = role_to_reason[role]
            if reason_code != expected_reason:
                fail(
                    f"{atom_id}: result-support role {role!r} must use reason code {expected_reason!r}, "
                    f"got {reason_code!r}"
                )
            if not result_ids:
                fail(f"{atom_id}: result-support atom is linked to no counted result")
        else:
            if result_ids:
                fail(f"{atom_id}: fidelity-only atom unexpectedly supports counted results {result_ids!r}")
            if reason_code.startswith("counted_result_"):
                fail(f"{atom_id}: fidelity-only role {role!r} uses counted-result reason {reason_code!r}")

    atoms_by_parent: dict[str, list[str]] = {}
    for atom_id, atom in source_atoms.items():
        atoms_by_parent.setdefault(atom.get("parent_claim_id"), []).append(atom_id)

    for item in items:
        result_id = item["id"]
        boundary = item.get("boundary_review")
        if not isinstance(boundary, dict) or boundary.get("status") != "accepted":
            fail(f"{result_id}: missing accepted boundary_review")
        if boundary.get("primary_source_block") != result_id:
            fail(
                f"{result_id}: boundary_review.primary_source_block must be the result's source block {result_id!r}"
            )
        selected = _source_atom_ids(item)
        same_block = atoms_by_parent.get(result_id, [])
        expected_included = [atom_id for atom_id in same_block if atom_id in selected]
        expected_excluded = [atom_id for atom_id in same_block if atom_id not in selected]
        expected_cross = [atom_id for atom_id in selected if atom_id not in same_block]
        for key, expected in (
            ("included_same_block_atom_ids", expected_included),
            ("excluded_same_block_atom_ids", expected_excluded),
            ("cross_block_scope_atom_ids", expected_cross),
        ):
            value = boundary.get(key)
            if value != expected:
                fail(f"{result_id}: boundary_review.{key} must be {expected!r}, got {value!r}")
        for atom_id in expected_excluded:
            atom = source_atoms[atom_id]
            if atom.get("formalization_role") in RESULT_SUPPORT_ROLES:
                fail(f"{result_id}: excluded same-block atom {atom_id} is still classified as result support")
        for key in ("method", "note"):
            value = boundary.get(key)
            if not isinstance(value, str) or not value.strip():
                fail(f"{result_id}: boundary_review.{key} must explain the boundary audit")

def _repair_terminal(item: dict[str, Any], census_declarations: set[str]) -> tuple[bool, str | None]:
    repair = item.get("repair")
    if not isinstance(repair, dict):
        return False, "refuted source result has no separate best-effort repair record"
    status = repair.get("status")
    notes = repair.get("notes")
    if status not in TERMINAL_REPAIR_STATUSES:
        return False, f"repair status is not terminal: {status!r}"
    if not isinstance(notes, str) or not notes.strip():
        return False, "terminal repair record has no explanatory notes"
    declarations = repair.get("lean_declarations", repair.get("declarations", []))
    if not isinstance(declarations, list) or not all(isinstance(x, str) for x in declarations):
        return False, "repair declarations must be a list of strings"
    if status == "proved" and not declarations:
        return False, "proved repair has no Lean declaration"
    unknown = sorted(set(declarations) - census_declarations)
    if unknown:
        return False, "repair declarations are not registered in the census: " + ", ".join(unknown)
    return True, None


def _validate_selection_review(
    data: dict[str, Any],
    source_inventory_path: Path,
    *,
    require_terminal: bool,
) -> tuple[bool, str | None]:
    review = _review_block(data)
    if review is None:
        message = "formalization-result inventory has no source-selection review"
        if require_terminal:
            fail(message)
        return False, message

    status = review.get("status")
    if status != "accepted":
        message = f"formalization-result source-selection review is not accepted: {status!r}"
        if require_terminal:
            fail(message)
        return False, message

    policy = review.get("policy", review.get("completion_policy"))
    if policy != "dk_established_results_only":
        fail(
            "accepted source-selection review must use policy='dk_established_results_only'; "
            "the denominator is only results Davis--Kahan actually establish in this paper, while proof equations, "
            "examples, open/deferred claims, and other source mathematics remain source-fidelity material"
        )
    if review.get("boundary_review_status") != "accepted":
        fail("accepted source-selection review must record boundary_review_status='accepted'")

    expected_source_hash = review.get("source_fidelity_inventory_sha256")
    actual_source_hash = sha256_file(source_inventory_path)
    if expected_source_hash != actual_source_hash:
        fail(
            "accepted source-selection review is stale: source-fidelity inventory hash differs; "
            f"expected {expected_source_hash!r}, got {actual_source_hash}"
        )

    expected_tex_hash = review.get("distributable_specification_sha256")
    actual_tex_hash = sha256_file(TEX_PATH)
    if expected_tex_hash != actual_tex_hash:
        fail(
            "accepted source-selection review is stale: distributable TeX hash differs; "
            f"expected {expected_tex_hash!r}, got {actual_tex_hash}"
        )

    method = review.get("method")
    if not isinstance(method, str) or not method.strip():
        fail("accepted source-selection review must record its review method")
    return True, None



def _validate_semantic_audit_surface(
    data: dict[str, Any],
    items: list[dict[str, Any]],
    *,
    terminal: int,
    nonterminal: list[dict[str, Any]],
) -> dict[str, Any]:
    """Require reviewer-visible static evidence for every semantic promotion.

    The result inventory is the semantic ledger, but a hostile reviewer should not
    need to trust declaration strings inside JSON.  The maintained audit surface
    imports `DavisKahan.All` and `#check`s every selected declaration, while the
    companion Markdown report records the source-vs-Lean judgement and the exact
    residual gap for nonterminal results.
    """
    sweep = data.get("semantic_review_sweep")
    if not isinstance(sweep, dict):
        fail("formalization-result inventory must record semantic_review_sweep")

    audit_rel = sweep.get("compiler_audit_surface")
    report_rel = sweep.get("human_report")
    if not isinstance(audit_rel, str) or not audit_rel.strip():
        fail("semantic_review_sweep.compiler_audit_surface must name the maintained Lean audit file")
    if not isinstance(report_rel, str) or not report_rel.strip():
        fail("semantic_review_sweep.human_report must name the maintained semantic-review report")
    audit_path = ROOT / audit_rel
    report_path = ROOT / report_rel
    if not audit_path.exists():
        fail(f"semantic compiler audit surface does not exist: {audit_rel}")
    if not report_path.exists():
        fail(f"semantic review report does not exist: {report_rel}")

    if sweep.get("terminal_results") != terminal:
        fail(
            "semantic_review_sweep.terminal_results is stale: "
            f"expected {terminal}, got {sweep.get('terminal_results')!r}"
        )
    expected_remaining = [item["id"] for item in nonterminal]
    if sweep.get("remaining_results") != expected_remaining:
        fail(
            "semantic_review_sweep.remaining_results is stale: "
            f"expected {expected_remaining!r}, got {sweep.get('remaining_results')!r}"
        )

    audit_text = audit_path.read_text(encoding="utf-8")
    report_text = report_path.read_text(encoding="utf-8")
    for item in items:
        result_id = item["id"]
        review_note = item.get("review_note")
        if not isinstance(review_note, str) or not review_note.strip():
            fail(f"{result_id}: semantic result entry must record a nonempty review_note")
        for declaration in _declarations(item):
            if f"#check @{declaration}" not in audit_text and f"#check {declaration}" not in audit_text:
                fail(
                    f"{result_id}: selected semantic evidence {declaration} is missing from "
                    f"{audit_rel}"
                )
        repair = item.get("repair")
        if isinstance(repair, dict):
            for declaration in repair.get("lean_declarations", []) or []:
                if f"#check @{declaration}" not in audit_text and f"#check {declaration}" not in audit_text:
                    fail(
                        f"{result_id}: repair evidence {declaration} is missing from {audit_rel}"
                    )

        is_terminal = (
            _result_disposition(item) in TERMINAL_RESULT_DISPOSITIONS
            and item.get("verification") in TERMINAL_VERIFICATIONS
            and _semantic_certification(item) in TERMINAL_SEMANTIC_CERTIFICATIONS
        )
        gap = item.get("remaining_gap")
        if is_terminal:
            if gap is not None:
                fail(f"{result_id}: terminal result must not retain remaining_gap")
        else:
            if not isinstance(gap, dict):
                fail(f"{result_id}: nonterminal result must carry a structured remaining_gap")
            for key in ("category", "missing_surface", "next_action"):
                value = gap.get(key)
                if not isinstance(value, str) or not value.strip():
                    fail(f"{result_id}: remaining_gap.{key} must be nonempty")
            strongest = gap.get("strongest_existing_evidence")
            if not isinstance(strongest, list) or not strongest or not all(isinstance(x, str) for x in strongest):
                fail(f"{result_id}: remaining_gap.strongest_existing_evidence must be a nonempty list")
            for declaration in strongest:
                if f"#check @{declaration}" not in audit_text and f"#check {declaration}" not in audit_text:
                    fail(
                        f"{result_id}: strongest gap evidence {declaration} is missing from {audit_rel}"
                    )
        if f"`{result_id}`" not in report_text:
            fail(f"{result_id}: semantic review report {report_rel} does not mention this counted result")

    return {
        "compiler_audit_surface": audit_rel,
        "human_report": report_rel,
        "compiler_audit_surface_sha256": sha256_file(audit_path),
        "human_report_sha256": sha256_file(report_path),
    }

def completion_summary(
    inventory_path: Path | None = None,
    *,
    require_terminal: bool = False,
) -> dict[str, Any]:
    source_inventory_path, source_atoms = _load_source_atoms()
    path = discover_inventory(inventory_path)
    if path is None or not path.exists():
        message = (
            "formalization-result inventory is not checked in yet; source fidelity can be audited, "
            "but the stated-result denominator for the 100% formalization claim is unavailable"
        )
        if require_terminal:
            fail(message)
        return {
            "inventory_available": False,
            "inventory_path": str(path.relative_to(ROOT)) if path is not None and path.is_relative_to(ROOT) else None,
            "selection_review_accepted": False,
            "result_count": 0,
            "completion_obligations": 0,
            "terminal_completion_obligations": 0,
            "source_coverage_terminal": False,
            "nonterminal_results": [],
            "note": message,
        }

    data = json.loads(path.read_text(encoding="utf-8"))
    if data.get("schema_version") not in {1, 2}:
        fail(f"unsupported formalization-result inventory schema: {data.get('schema_version')!r}")

    declared_source = _first(data, ("source_fidelity_inventory", "source_atom_inventory"))
    if isinstance(declared_source, str) and (ROOT / declared_source).resolve() != source_inventory_path.resolve():
        fail(
            "formalization-result inventory points at a different source-fidelity inventory: "
            f"{declared_source!r}"
        )

    selection_review_accepted, selection_note = _validate_selection_review(
        data, source_inventory_path, require_terminal=require_terminal
    )

    census_declarations = _registered_census_declarations()
    items = _result_items(data)
    if data.get("result_count") != len(items):
        fail(
            f"formalization-result inventory result_count={data.get('result_count')!r} "
            f"but contains {len(items)} results"
        )
    if len(items) != 29:
        fail(
            f"current DK1970 established-result denominator must contain 29 results, got {len(items)}; "
            "change this only after a fresh original-paper result-selection audit"
        )
    seen: set[str] = set()
    obligation_source_atoms: set[str] = set()
    obligations = 0
    terminal = 0
    nonterminal: list[dict[str, Any]] = []

    for item in items:
        result_id = item.get("id")
        if not isinstance(result_id, str) or not result_id or result_id in seen:
            fail(f"formalization-result inventory has missing/duplicate id: {result_id!r}")
        seen.add(result_id)

        source_ids = _source_atom_ids(item)
        unknown_atoms = sorted(set(source_ids) - set(source_atoms))
        if unknown_atoms:
            fail(f"{result_id}: references unknown source-fidelity atoms: " + ", ".join(unknown_atoms))

        parent = item.get("parent_claim_id")
        if isinstance(parent, str):
            wrong_parent = sorted(
                atom_id for atom_id in source_ids
                if source_atoms[atom_id].get("parent_claim_id") != parent
            )
            if wrong_parent:
                fail(
                    f"{result_id}: source atoms do not belong to parent_claim_id={parent!r}: "
                    + ", ".join(wrong_parent)
                )

        kind = _result_kind(item)
        if kind not in COUNTED_RESULT_KINDS:
            fail(f"{result_id}: unsupported counted result_kind/source_kind {kind!r}")
        obligation = item.get("completion_obligation")
        if not isinstance(obligation, bool):
            fail(f"{result_id}: completion_obligation must be an explicit boolean")
        disposition = _result_disposition(item)
        verification = item.get("verification")
        semantic = _semantic_certification(item)
        declarations = _declarations(item)

        if not obligation:
            fail(
                f"{result_id}: the compact formalization-result inventory contains only counted results; "
                "open questions and other exclusions belong in the source-fidelity inventory"
            )

        obligation_source_atoms.update(source_ids)
        obligations += 1
        reasons: list[str] = []
        if disposition not in TERMINAL_RESULT_DISPOSITIONS:
            reasons.append(f"disposition={disposition!r}")
        if verification not in TERMINAL_VERIFICATIONS:
            reasons.append(f"verification={verification!r}")
        if semantic not in TERMINAL_SEMANTIC_CERTIFICATIONS:
            reasons.append(f"semantic_certification={semantic!r}")
        if not declarations:
            reasons.append("no source-facing Lean declarations")
        unknown_decls = sorted(set(declarations) - census_declarations)
        if unknown_decls:
            fail(f"{result_id}: result declarations are not registered in the source census: " + ", ".join(unknown_decls))

        if disposition == "refuted_as_transcribed":
            repair_ok, repair_reason = _repair_terminal(item, census_declarations)
            if not repair_ok:
                reasons.append(repair_reason or "repair obligation is nonterminal")

        if reasons:
            nonterminal.append({
                "id": result_id,
                "result_kind": kind,
                "disposition": disposition,
                "verification": verification,
                "semantic_certification": semantic,
                "reasons": reasons,
            })
        else:
            terminal += 1

    semantic_audit = _validate_semantic_audit_surface(
        data, items, terminal=terminal, nonterminal=nonterminal
    )
    _validate_boundary_accounting(source_atoms, items)
    classification_complete, classification_note = _validate_total_source_classification(
        data, source_atoms, obligation_source_atoms, require_terminal=require_terminal
    )
    source_coverage_terminal = (
        selection_review_accepted and classification_complete and terminal == obligations
    )
    if require_terminal and not source_coverage_terminal:
        first = nonterminal[0] if nonterminal else None
        if first:
            fail(
                "formalization-result inventory is nonterminal: "
                f"{terminal}/{obligations} obligations complete; first open result {first['id']}: "
                + "; ".join(first["reasons"])
            )
        fail(
            "formalization-result inventory is nonterminal because its source-selection review is not accepted"
        )

    return {
        "inventory_available": True,
        "inventory_path": str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path),
        "inventory_sha256": sha256_file(path),
        "selection_review_accepted": selection_review_accepted,
        "selection_review_note": selection_note,
        "source_classification_complete": classification_complete,
        "source_classification_note": classification_note,
        "source_fidelity_inventory": str(source_inventory_path.relative_to(ROOT)),
        "source_fidelity_inventory_sha256": sha256_file(source_inventory_path),
        "result_count": len(items),
        "completion_obligations": obligations,
        "terminal_completion_obligations": terminal,
        "source_coverage_terminal": source_coverage_terminal,
        "semantic_audit": semantic_audit,
        "nonterminal_results": nonterminal,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inventory", type=Path, help="override formalization-result inventory path")
    parser.add_argument(
        "--require-terminal",
        action="store_true",
        help="require an accepted stated-result selection review and terminal exact/refuted evidence for every result obligation",
    )
    parser.add_argument("--json", action="store_true", help="emit the completion summary as JSON")
    args = parser.parse_args()

    summary = completion_summary(args.inventory, require_terminal=args.require_terminal)
    if args.json:
        print(json.dumps(summary, indent=2, ensure_ascii=False))
        return 0

    if not summary["inventory_available"]:
        print("Davis--Kahan formalization-result inventory: PENDING")
        print("  " + summary["note"])
        return 0

    print(
        "Davis--Kahan formalization-result inventory: CLEAN "
        f"({summary['terminal_completion_obligations']}/{summary['completion_obligations']} stated-result "
        "obligations terminal; "
        f"selection review accepted={summary['selection_review_accepted']}; "
        f"source classification complete={summary['source_classification_complete']})"
    )
    print(f"  inventory: {summary['inventory_path']}")
    print(f"  source fidelity: {summary['source_fidelity_inventory']}")
    print(f"  semantic audit surface: {summary['semantic_audit']['compiler_audit_surface']}")
    print(f"  semantic review report: {summary['semantic_audit']['human_report']}")
    if summary["nonterminal_results"]:
        print("  first nonterminal results:")
        for item in summary["nonterminal_results"][:10]:
            print(f"    - {item['id']}: " + "; ".join(item["reasons"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
