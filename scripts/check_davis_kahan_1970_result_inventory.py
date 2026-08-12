#!/usr/bin/env python3
"""Validate the result-level denominator for the Davis--Kahan 1970 100% claim.

This checker deliberately separates two different questions:

* source fidelity: did the distributable TeX preserve the mathematical content
  of the paper?  The fine-grained source-atom inventory answers that question.
* formalization completion: did Lean exactly represent every *stated result*
  (theorem/proposition/lemma/corollary, the four Section 2 headline theorems,
  and any other standalone theorem-like result)?  This result inventory is the
  only denominator for the project's "100% formalized" claim.

Intermediate proof identities, proof equations, derivations, historical remarks,
and numerical working may be source-fidelity atoms without becoming Lean proof
obligations.

The script is migration-friendly: before Agent 3's compact result inventory is
checked in, ordinary validation succeeds with an explicit NOTE while
`--require-terminal` fails closed.  Once the inventory exists, terminality is
computed only from its result entries, never from the fine-grained source atoms
or the 49 organizational statement-map rows.
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
OPEN_RESULT_DISPOSITIONS = {"source_open_question", "open_question"}
TERMINAL_VERIFICATIONS = {"proved_in_build"}
TERMINAL_SEMANTIC_CERTIFICATIONS = {"accepted"}
TERMINAL_REPAIR_STATUSES = {"proved", "documented_no_satisfactory_repair"}
OPEN_KINDS = {"open_question"}
RESULT_SUPPORT_ROLES = {
    "result", "stated_result", "result_support", "result_hypothesis", "result_scope"
}
NON_RESULT_ROLES = {
    "definition", "definition_only", "proof_only", "intermediate_proof",
    "derivation", "derivation_only", "historical", "historical_comment",
    "numerical_working", "expository", "open_question", "non_result",
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
    open_question_atom_ids: set[str],
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
        if atom_id in open_question_atom_ids:
            if role not in RESULT_SUPPORT_ROLES | {"open_question"}:
                fail(
                    f"{atom_id}: selected by an open-question record but has incompatible role {role!r}"
                )
            continue
        if role not in NON_RESULT_ROLES:
            fail(
                f"{atom_id}: classified as result-support role {role!r} but no formalization result selects it"
            )
    return True, None

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
    if policy not in {"stated_results_only", "stated-results-only"}:
        fail(
            "accepted source-selection review must use policy='stated_results_only'; "
            "proof equations and intermediate mathematical facts are source-fidelity material, not completion obligations"
        )

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
    seen: set[str] = set()
    obligation_source_atoms: set[str] = set()
    open_question_source_atoms: set[str] = set()
    obligations = 0
    terminal = 0
    open_questions = 0
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
        if not isinstance(kind, str) or not kind:
            fail(f"{result_id}: missing result_kind/source_kind")
        obligation = item.get("completion_obligation")
        if not isinstance(obligation, bool):
            fail(f"{result_id}: completion_obligation must be an explicit boolean")
        disposition = _result_disposition(item)
        verification = item.get("verification")
        semantic = _semantic_certification(item)
        declarations = _declarations(item)

        if not obligation:
            if kind not in OPEN_KINDS:
                fail(
                    f"{result_id}: only an explicit open_question may be excluded from the formalization denominator; "
                    f"result_kind={kind!r}"
                )
            if disposition not in OPEN_RESULT_DISPOSITIONS:
                fail(f"{result_id}: open question must have an open-question disposition")
            if declarations:
                fail(f"{result_id}: open question must not use proof declarations to manufacture completion")
            open_question_source_atoms.update(source_ids)
            open_questions += 1
            continue

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

    classification_complete, classification_note = _validate_total_source_classification(
        data, source_atoms, obligation_source_atoms, open_question_source_atoms,
        require_terminal=require_terminal
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
        "open_questions": open_questions,
        "source_coverage_terminal": source_coverage_terminal,
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
        f"obligations terminal; {summary['open_questions']} open questions; "
        f"selection review accepted={summary['selection_review_accepted']}; "
        f"source classification complete={summary['source_classification_complete']})"
    )
    print(f"  inventory: {summary['inventory_path']}")
    print(f"  source fidelity: {summary['source_fidelity_inventory']}")
    if summary["nonterminal_results"]:
        print("  first nonterminal results:")
        for item in summary["nonterminal_results"][:10]:
            print(f"    - {item['id']}: " + "; ".join(item["reasons"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
