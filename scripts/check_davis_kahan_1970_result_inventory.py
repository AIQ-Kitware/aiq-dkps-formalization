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
import re
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
CANONICAL_EVIDENCE_ROLES = {"primary_source_witness", "exact_refutation"}
CANONICAL_EVIDENCE_KINDS = {"proof", "refutation"}
CANONICAL_SCALAR_SCOPES = {
    "complex", "real", "rclike", "scalar_generic", "mixed", "not_visible_in_type",
}
PROBE_IMPORT = "DavisKahan.All"
# Instance binders that are proof *capabilities* rather than printed source
# hypotheses.  Each has instances for both scalar fields of the paper, so a
# declaration carrying one still proves the printed result at `ℝ` and at `ℂ`;
# but `RCLike` is an open class, so the binder is a real hypothesis at any other
# field, and it is not something Davis and Kahan print.  Canonical evidence must
# therefore declare which of these it carries.
CAPABILITY_CLASSES = {
    "ContinuousLinearMap.HasMinMaxLowerBoundEverywhere",
    "TauCeti.DavisKahan.ExactSinTheta.HasUnboundedSylvesterKyFan",
    "TauCeti.DavisKahan.ExactSinTheta.HasApproximationNumberStrongCutoff",
}
SUPPORTING_EVIDENCE_ROLES = {
    "public_alias", "specialization", "alternative_route", "generalization",
    "presentation_wrapper", "implementation_structure", "transport_lemma",
    "scalar_generic_facade", "supporting_theorem",
}
REFUTATION_RESULT_IDS = {"DK-4.4-prop"}
SCOPE_CLASSIFICATION_CATEGORIES = {
    # the atom states scope of one or more counted results, and must be covered
    "counted_result_scope",
    # the source mentions an extension, variant, consequence or further case around
    # a counted result WITHOUT introducing and proving it as a result of its own.
    # Under `selection_definition.statement_boundary` such a passage does not
    # enlarge the counted result; it is fidelity material, and any Lean coverage of
    # it is supporting evidence rather than a canonical obligation.
    "result_adjacent_extension",
    # ambient setting or convention governing the whole paper
    "source_wide_setup",
    # tells a reader how to READ a statement (automaticity, vacuity conventions)
    "reading_interpretation",
    # sits inside a proof and describes the argument
    "proof_context",
    # commentary, motivation, negative remarks, worked-example choices
    "non_extending_commentary",
}
# Reason codes whose ONLY grounds are "this occurs outside the printed theorem
# environment".  That is exactly the condition the inventory's statement_boundary
# policy says does not exclude an explicit scope extension, so for a scope atom
# stating a mathematical assertion they are not an answer.  Four atoms were
# excluded from the denominator on these codes while explicitly extending a
# counted result.
GENERIC_SCOPE_REASON_CODES = {
    "post_result_scope_remark_not_in_printed_statement",
    "expository_commentary_not_result",
    "introductory_background_not_designated_result",
}
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
    "paper_wide_semantic_convention_not_result",
}

# Reviewer-facing source-alignment taxonomy.  It is deliberately three-valued:
# a locally self-contained exact match, a true result whose exact formalization
# depends on nonlocal source semantics, and a meaningful printed statement that
# is mathematically false.  The middle category must never be used to soften the
# third one.
SEMANTIC_ALIGNMENTS = {
    "locally_exact",
    "paper_faithful_nonlocal_source_interpretation",
    "refuted_as_transcribed",
}
NONLOCAL_INTERPRETATION_STATUSES = {"accepted", "pending", "rejected"}
NONLOCAL_INTERPRETATION_ROLES = {
    "printed_statement_clause",
    "paper_wide_convention",
    "later_standing_assumption",
    "omitted_qualification",
    "related_dimension_condition",
    "scope_separating_example",
    "automatic_case",
    "proof_context_dependency",
    "related_unqualified_claim",
}
NONLOCAL_INTERPRETATION_PROSE_FIELDS = (
    "reviewer_issue",
    "awkwardness",
    "accepted_reading",
    "alternative_literal_reading",
    "why_not_refutation",
    "semantic_conclusion",
)


try:
    from aiq_lean_tools.coverage import load_coverage_bundle
except ImportError:  # pragma: no cover - environment guidance, not logic
    raise SystemExit(
        "aiq_lean_tools is not installed. Run:\n"
        "  python3 -m pip install -e submodules/aiq-lean-formalization-tools"
    )


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


CLAUSE_STATUSES = {"established", "open"}

# The atom kinds that carry a counted result's PRINTED STATEMENT, as opposed to
# its hypotheses (`hypothesis`, `numbered-equation`) or its scope (`scope`).
#
# This was `{"theorem"}` until 2026-08-31, and that was a hole: five counted
# results state their conclusion under a different kind -- the four Section 6
# lemmas under `lemma`, and Proposition 4.4 under `source-assertion`, because it
# is false as printed.  For those five the "every printed conclusion has an
# established clause" check was vacuous, so a clause could name no conclusion at
# all and the row still counted as terminal.  Found by the 2026-08-31 hostile
# re-review, which is exactly the kind of gap it was looking for.
CONCLUSION_ATOM_KINDS = {"theorem", "lemma", "source-assertion"}


def _validate_source_clauses(
    items: list[dict[str, Any]],
    source_atoms: dict[str, dict[str, Any]],
    census_declarations: set[str],
    audit_text: str,
    audit_rel: str,
    probed_types: dict[str, str] | None,
) -> dict[str, list[str]]:
    """Require every printed source clause to have ONE coherent witness.

    The defect this replaces: canonical evidence recorded, per declaration, a set
    of source atoms it covered, and a result was terminal when the **union** over
    all its declarations covered the row.  That accepts a certificate assembled
    from pieces no theorem proves together.  It really happened, in
    `S2-sin-two-theta`:

        directed theorems  ->  unbounded scope, gap scope, bounded residual
        bounded ambient    ->  the ambient conclusion
        union              ->  "ambient conclusion at unbounded scope"

    No theorem and no proof chain establishes that conjunction.

    The model here is: a result declares `result_wide_scope_atoms` -- scope and
    hypothesis atoms that hold of the printed result as a whole -- and one
    `source_clauses` entry per printed clause per scalar field.  Each clause names
    ONE primary theorem, optionally with compiled correspondence lemmas, and must
    satisfy the type requirements of **its own conclusion atoms and every
    result-wide scope atom**.  Scope can no longer be donated by a sibling.

    This is deliberately not the crude rule "every canonical theorem must contain
    every atom on the row".  Clause conclusions stay clause-local, fixed-field
    siblings are separate clauses, and a clause may carry
    `clause_hypothesis_atoms` that belong to it alone.  What is result-wide is
    what the source states about the result as a whole.

    Returns the per-result list of open clause ids.
    """
    open_by_result: dict[str, list[str]] = {}
    for item in items:
        result_id = item["id"]
        atoms = set(_source_atom_ids(item))
        wide = item.get("result_wide_scope_atoms")
        if not isinstance(wide, list) or not all(isinstance(x, str) for x in wide):
            fail(f"{result_id}: must record result_wide_scope_atoms (possibly empty)")
        stray = sorted(set(wide) - atoms)
        if stray:
            fail(
                f"{result_id}: result_wide_scope_atoms names atoms not assigned to this result: "
                + ", ".join(stray)
            )
        clauses = item.get("source_clauses")
        if not isinstance(clauses, list) or not clauses:
            fail(f"{result_id}: must record a nonempty source_clauses list")

        seen_ids: set[str] = set()
        covered_conclusions: set[str] = set()
        clause_local: set[str] = set()
        scalar_by_conclusion: dict[str, set[str]] = {}
        refuted_conclusions: set[str] = set()
        opens: list[str] = []
        for clause in clauses:
            if not isinstance(clause, dict):
                fail(f"{result_id}: source_clauses entries must be objects")
            cid = clause.get("id")
            if not isinstance(cid, str) or not cid.strip():
                fail(f"{result_id}: every source clause needs an id")
            if cid in seen_ids:
                fail(f"{result_id}: duplicate source clause id {cid!r}")
            seen_ids.add(cid)
            where = f"{result_id}/{cid}"

            status = clause.get("status")
            if status not in CLAUSE_STATUSES:
                fail(f"{where}: status is {status!r}; expected one of {sorted(CLAUSE_STATUSES)}")
            justification = clause.get("justification")
            if not isinstance(justification, str) or len(justification.strip()) < 40:
                fail(f"{where}: justification must state which printed clause this discharges")

            conclusions = clause.get("conclusion_atoms")
            if not isinstance(conclusions, list) or not all(isinstance(x, str) for x in conclusions):
                fail(f"{where}: conclusion_atoms must be a list of atom ids")
            stray = sorted(set(conclusions) - atoms)
            if stray:
                fail(f"{where}: conclusion_atoms names atoms outside this result: " + ", ".join(stray))
            local = clause.get("clause_hypothesis_atoms", [])
            if not isinstance(local, list) or not all(isinstance(x, str) for x in local):
                fail(f"{where}: clause_hypothesis_atoms must be a list of atom ids")
            stray = sorted(set(local) - atoms)
            if stray:
                fail(f"{where}: clause_hypothesis_atoms names atoms outside this result: " + ", ".join(stray))
            clause_local.update(local)

            evidence = clause.get("evidence")
            if not isinstance(evidence, dict):
                fail(f"{where}: must record evidence")
            primary = evidence.get("primary")
            if not isinstance(primary, str) or not primary.strip():
                fail(f"{where}: evidence.primary must name ONE theorem")
            correspondence = evidence.get("correspondence", [])
            if not isinstance(correspondence, list) or not all(isinstance(x, str) for x in correspondence):
                fail(f"{where}: evidence.correspondence must be a list of declaration names")
            # A clause's primary IS this result's canonical evidence for that clause.
            # Without this, a primary could be a `supporting_evidence` declaration --
            # a specialization, a presentation wrapper, an alternative route -- and the
            # coherence check below would then have no compiler-printed type to work
            # with.  Stated as its own rule so the failure names the real problem.
            canonical_scopes = {
                entry.get("declaration"): entry.get("scalar_scope")
                for entry in item.get("canonical_evidence", []) or []
                if isinstance(entry, dict)
            }
            if primary not in canonical_scopes:
                fail(
                    f"{where}: evidence.primary {primary} is not canonical evidence of this result; "
                    "a clause's primary witness is by definition canonical evidence, not supporting "
                    "evidence"
                )
            # The clause's own scalar field must be the primary's, and the primary's is
            # compiler-derived.  Otherwise a row could claim both of the paper's scalar
            # fields while both clauses are witnessed over the same one.
            if clause.get("scalar_scope") != canonical_scopes[primary]:
                fail(
                    f"{where}: clause scalar_scope {clause.get('scalar_scope')!r} disagrees with the "
                    f"compiler-derived scalar scope {canonical_scopes[primary]!r} of its primary {primary}"
                )
            for declaration in [primary, *correspondence]:
                if declaration not in _declarations(item):
                    fail(f"{where}: {declaration} is not registered in the result's lean_declarations")
                if declaration not in census_declarations:
                    fail(f"{where}: {declaration} is not registered in the source census")
                if (
                    f"#check @{declaration}" not in audit_text
                    and f"#check {declaration}" not in audit_text
                ):
                    fail(f"{where}: {declaration} is not #checked by {audit_rel}")

            if status == "open":
                reason = clause.get("open_reason")
                if not isinstance(reason, str) or len(reason.strip()) < 80:
                    fail(
                        f"{where}: an open clause must say exactly what is missing, in open_reason"
                    )
                opens.append(cid)
                continue

            covered_conclusions.update(conclusions)
            is_refutation = any(
                entry.get("declaration") == primary and entry.get("role") == "exact_refutation"
                for entry in item.get("canonical_evidence", []) or []
                if isinstance(entry, dict)
            )
            for atom_id in conclusions:
                scalar_by_conclusion.setdefault(atom_id, set()).add(clause.get("scalar_scope"))
                if is_refutation:
                    refuted_conclusions.add(atom_id)

            # THE COHERENCE CHECK: the clause's own primary must satisfy the type
            # requirements of its conclusions AND of every result-wide scope atom.
            if probed_types is not None:
                printed = probed_types.get(primary)
                if printed is None:
                    fail(f"{where}: no compiler-printed type was probed for {primary}")
                for atom_id in [*conclusions, *local, *wide]:
                    requirement = source_atoms[atom_id].get("type_requirements")
                    if not requirement:
                        continue
                    missing = [t for t in requirement.get("must_contain", []) if t not in printed]
                    forbidden = [t for t in requirement.get("must_not_contain", []) if t in printed]
                    if missing or forbidden:
                        fail(
                            f"{where}: the clause's primary {primary} does not establish its conclusion at "
                            f"the scope of {atom_id}: "
                            + (f"its printed type lacks {missing!r}; " if missing else "")
                            + (f"its printed type contains the disqualifying {forbidden!r}; " if forbidden else "")
                            + "a sibling declaration may not donate this scope"
                        )
            for atom_id in wide:
                mode = source_atoms[atom_id].get("scope_assertion_mode")
                if isinstance(mode, dict) and mode.get("mode") == "clause_justified":
                    key = "gap_scope_justification"
                    value = clause.get(key)
                    if not isinstance(value, str) or len(value.strip()) < 60:
                        fail(
                            f"{where}: {atom_id} cannot be decided from a printed type, so this clause must "
                            f"record {key} naming the hypotheses in {primary} that realize it"
                        )
                    # Prose alone is an escape hatch, so the clause must also NAME the
                    # hypotheses, and every name must actually occur in the primary's
                    # printed type.  A justification may then still be wrong about what
                    # those hypotheses mean, but it can no longer claim a scope realized
                    # by hypotheses the theorem does not have.
                    tokens = clause.get("gap_scope_hypothesis_tokens")
                    if not isinstance(tokens, list) or not tokens or not all(
                        isinstance(t, str) and t.strip() for t in tokens
                    ):
                        fail(
                            f"{where}: {atom_id} is clause-justified, so this clause must list the "
                            "hypothesis tokens realizing it, in gap_scope_hypothesis_tokens"
                        )
                    if probed_types is not None:
                        printed = probed_types.get(primary)
                        absent = [t for t in tokens if t not in (printed or "")]
                        if absent:
                            fail(
                                f"{where}: gap_scope_hypothesis_tokens {absent!r} do not occur in the "
                                f"compiler-printed type of {primary}, so the recorded justification for "
                                f"{atom_id} describes hypotheses this theorem does not have"
                            )

        result_conclusions = {
            atom_id for atom_id in atoms
            if source_atoms[atom_id].get("kind") in CONCLUSION_ATOM_KINDS
        }
        uncovered = sorted(result_conclusions - covered_conclusions)
        is_terminal = (
            _result_disposition(item) in TERMINAL_RESULT_DISPOSITIONS
            and item.get("verification") in TERMINAL_VERIFICATIONS
            and _semantic_certification(item) in TERMINAL_SEMANTIC_CERTIFICATIONS
        )
        if is_terminal and (uncovered or opens):
            fail(
                f"{result_id}: recorded as terminal, but "
                + (f"printed conclusions with no established clause: {uncovered}; " if uncovered else "")
                + (f"open clauses: {opens}" if opens else "")
            )
        if not is_terminal and not uncovered and not opens:
            fail(
                f"{result_id}: every printed clause is established, so the result should not be "
                "recorded as nonterminal"
            )
        # both of the paper's scalar fields must be reached for each conclusion
        for atom_id, scopes in scalar_by_conclusion.items():
            if scopes & {"rclike", "scalar_generic"}:
                continue
            # A refutation is discharged by ONE counterexample.  The paper asserts the
            # printed statement over a real or complex space, so a counterexample in
            # either field already refutes it; demanding both would be demanding two
            # counterexamples for one false claim.
            if atom_id in refuted_conclusions:
                continue
            if not {"complex", "real"} <= scopes:
                fail(
                    f"{result_id}: conclusion {atom_id} is established only at {sorted(scopes)}; the source "
                    "states its results for a real OR complex Hilbert space, so both fields are needed "
                    "unless a single scalar-generic clause covers them"
                )
        partition = covered_conclusions | clause_local | set(wide)
        for clause in clauses:
            partition.update(clause.get("conclusion_atoms", []))
        leftover = sorted(atoms - partition)
        if leftover:
            fail(
                f"{result_id}: source atoms belong to no clause and are not result-wide scope: "
                + ", ".join(leftover)
            )
        open_by_result[result_id] = opens
    return open_by_result


def _validate_scope_atom_classification(source_atoms: dict[str, dict[str, Any]]) -> None:
    """Every scope atom must say WHICH kind of scope it is, and quote the source.

    `dev/davis-kahan-1970-formalization-result-inventory.json` states that a later
    source passage which explicitly extends the proved scope of a counted result
    is part of that result's scope and must be covered.  Four scope atoms were
    nevertheless excluded from the denominator with reason codes whose grounds
    were that they occur after the theorem environment -- the exact condition the
    policy says does not exclude an extension.  The inconsistency was visible in
    the source: the Appendix's unbounded *tangent* sentence was `result_scope`
    while the adjacent *sine* sentence was expository commentary.

    A generic code is therefore no longer sufficient for a scope atom.  Each must
    carry a `scope_classification` naming one of six categories, the results it
    extends (exactly when the category says it extends any), a substantive
    rationale, and a verbatim quotation from the distributable specification that
    a reviewer can check against the source.
    """
    for atom_id, atom in sorted(source_atoms.items()):
        if atom.get("kind") != "scope" or atom.get("source_role") != "mathematical_assertion":
            continue
        classification = atom.get("scope_classification")
        if not isinstance(classification, dict):
            fail(
                f"{atom_id}: a scope atom stating a mathematical assertion must carry a "
                "scope_classification"
            )
        category = classification.get("category")
        if category not in SCOPE_CLASSIFICATION_CATEGORIES:
            fail(
                f"{atom_id}: scope_classification.category is {category!r}; expected one of "
                f"{sorted(SCOPE_CLASSIFICATION_CATEGORIES)}"
            )
        extends = classification.get("extends_results")
        if not isinstance(extends, list) or not all(isinstance(x, str) for x in extends):
            fail(f"{atom_id}: scope_classification.extends_results must be a list of result ids")
        linked = atom.get("formalization_result_ids") or []
        if category == "counted_result_scope":
            if not extends:
                fail(
                    f"{atom_id}: classified as counted_result_scope but names no result it extends"
                )
            if atom.get("formalization_role") != "result_scope":
                fail(
                    f"{atom_id}: classified as counted_result_scope but formalization_role is "
                    f"{atom.get('formalization_role')!r}"
                )
        else:
            if extends:
                fail(
                    f"{atom_id}: category {category!r} must not name results it extends, got {extends!r}"
                )
            if atom.get("formalization_role") in RESULT_SUPPORT_ROLES:
                fail(
                    f"{atom_id}: category {category!r} is incompatible with the result-support role "
                    f"{atom.get('formalization_role')!r}"
                )
        if sorted(extends) != sorted(linked):
            fail(
                f"{atom_id}: scope_classification.extends_results {sorted(extends)!r} disagrees with "
                f"formalization_result_ids {sorted(linked)!r}"
            )
        rationale = classification.get("rationale")
        if not isinstance(rationale, str) or len(rationale.strip()) < 120:
            fail(
                f"{atom_id}: scope_classification.rationale must substantively justify the category "
                "(at least a couple of sentences)"
            )
        quote = classification.get("source_quote")
        if not isinstance(quote, str) or not quote.strip():
            fail(
                f"{atom_id}: scope_classification.source_quote must quote the source passage being "
                "classified, so a reviewer can check the reading"
            )
        code = atom.get("formalization_role_reason_code")
        if code in GENERIC_SCOPE_REASON_CODES:
            fail(
                f"{atom_id}: reason code {code!r} is not sufficient for a scope atom -- its grounds are "
                "that the passage lies outside the printed statement, which the statement_boundary policy "
                "says does not exclude an explicit scope extension. Give the substantive reason."
            )


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
            # An atom may be excluded from THIS result's statement and still be
            # scope of a DIFFERENT counted result: the source states the sin 2 Theta
            # unequal-dimension extension inside the Theorem 8.2 block, and textual
            # location is not semantic ownership.  What must not happen is an atom
            # excluded here while still claiming to support this result.
            if result_id in (atom.get("formalization_result_ids") or []):
                fail(
                    f"{result_id}: excluded same-block atom {atom_id} still claims to support this result"
                )
            if (
                atom.get("formalization_role") in RESULT_SUPPORT_ROLES
                and atom.get("formalization_role") != "result_scope"
            ):
                fail(
                    f"{result_id}: excluded same-block atom {atom_id} is classified as result support for "
                    f"{atom.get('formalization_result_ids')!r}; only scope atoms may belong to another result"
                )
        for key in ("method", "note"):
            value = boundary.get(key)
            if not isinstance(value, str) or not value.strip():
                fail(f"{result_id}: boundary_review.{key} must explain the boundary audit")

def _supporting_atom_digest(atom_ids: list[str], source_atoms: dict[str, dict[str, Any]]) -> str:
    """Digest the exact interpretation evidence an accepted reading was built on.

    The whole-inventory hash already fails closed on any atom edit; this narrower
    digest names *which* evidence moved, so a stale accepted reading points the
    reviewer at the passage that changed rather than at the file.
    """
    payload = [
        {
            "id": atom_id,
            "summary": source_atoms[atom_id]["summary"],
            "reason_code": source_atoms[atom_id]["formalization_role_reason_code"],
            "role": (source_atoms[atom_id].get("interpretation_support") or {}).get("role"),
        }
        for atom_id in atom_ids
    ]
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, ensure_ascii=False).encode("utf-8")
    ).hexdigest()


def _validate_nonlocal_interpretation(
    items: list[dict[str, Any]],
    source_atoms: dict[str, dict[str, Any]],
    source_inventory_path: Path,
    census_declarations: set[str],
    audit_text: str,
) -> dict[str, Any]:
    """Check the first-class record of results that are not locally self-contained.

    Most counted results are locally exact: the printed statement carries its own
    hypotheses and Lean matches it directly.  A few are not, because the paper
    imposes semantics elsewhere -- a global existence/vacuity convention, a later
    standing assumption, an inherited proof context.  For those, Lean necessarily
    says something the printed display does not literally say, and the repository
    must expose that to a hostile reviewer instead of letting them discover it.

    This validation exists so the record cannot decay into decorative prose: the
    reading must be explicit, its evidence must be real source atoms that link
    back, its Lean explicitation must be registered and compiler-visible, and any
    edit to the source specification or to the cited evidence makes the accepted
    reading stale.
    """
    exceptional: list[str] = []
    linked_back: dict[str, set[str]] = {}

    for item in items:
        result_id = item["id"]
        alignment = item.get("semantic_alignment")
        if alignment not in SEMANTIC_ALIGNMENTS:
            fail(
                f"{result_id}: semantic_alignment must be one of "
                + ", ".join(sorted(SEMANTIC_ALIGNMENTS))
                + f"; got {alignment!r}"
            )
        self_contained = item.get("local_statement_self_contained")
        if not isinstance(self_contained, bool):
            fail(f"{result_id}: local_statement_self_contained must be an explicit boolean")
        block = item.get("nonlocal_source_interpretation")

        if alignment == "refuted_as_transcribed" and _result_disposition(item) != "refuted_as_transcribed":
            fail(
                f"{result_id}: semantic_alignment='refuted_as_transcribed' requires the refuted disposition; "
                "a nonlocal-interpretation result must not be recorded as a refutation"
            )
        if _result_disposition(item) == "refuted_as_transcribed" and alignment != "refuted_as_transcribed":
            fail(f"{result_id}: refuted disposition requires semantic_alignment='refuted_as_transcribed'")

        if self_contained:
            if block is not None:
                fail(
                    f"{result_id}: locally self-contained result must not carry nonlocal_source_interpretation"
                )
            if alignment == "paper_faithful_nonlocal_source_interpretation":
                fail(
                    f"{result_id}: nonlocal-interpretation alignment requires "
                    "local_statement_self_contained=false"
                )
            continue

        exceptional.append(result_id)
        if alignment != "paper_faithful_nonlocal_source_interpretation":
            fail(
                f"{result_id}: local_statement_self_contained=false requires "
                "semantic_alignment='paper_faithful_nonlocal_source_interpretation'"
            )
        if not isinstance(block, dict):
            fail(
                f"{result_id}: a result whose printed statement is not locally self-contained must carry a "
                "structured nonlocal_source_interpretation record"
            )
        status = block.get("status")
        if status not in NONLOCAL_INTERPRETATION_STATUSES:
            fail(f"{result_id}: nonlocal_source_interpretation.status must be one of "
                 + ", ".join(sorted(NONLOCAL_INTERPRETATION_STATUSES)) + f"; got {status!r}")
        if block.get("classification") != "paper_faithful_nonlocal_source_interpretation":
            fail(
                f"{result_id}: nonlocal_source_interpretation.classification must be "
                "'paper_faithful_nonlocal_source_interpretation'"
            )
        if block.get("local_statement_self_contained") is not False:
            fail(
                f"{result_id}: nonlocal_source_interpretation.local_statement_self_contained must be false "
                "and agree with the result entry"
            )
        for field in NONLOCAL_INTERPRETATION_PROSE_FIELDS:
            value = block.get(field)
            if not isinstance(value, str) or len(value.split()) < 12:
                fail(
                    f"{result_id}: nonlocal_source_interpretation.{field} must be a substantive "
                    "reviewer-facing explanation"
                )
        dependencies = block.get("nonlocal_dependencies")
        if not isinstance(dependencies, list) or not dependencies or not all(
            isinstance(x, str) and x.strip() for x in dependencies
        ):
            fail(f"{result_id}: nonlocal_source_interpretation.nonlocal_dependencies must be a nonempty list")
        if block.get("distinct_from_refutation") not in {item["id"] for item in items}:
            fail(
                f"{result_id}: nonlocal_source_interpretation.distinct_from_refutation must name the counted "
                "result that is the repository's canonical refutation, so the two categories stay separable"
            )

        atom_ids = block.get("supporting_atom_ids")
        if not isinstance(atom_ids, list) or not atom_ids or not all(isinstance(x, str) for x in atom_ids):
            fail(f"{result_id}: nonlocal_source_interpretation.supporting_atom_ids must be a nonempty list")
        if len(atom_ids) != len(set(atom_ids)):
            fail(f"{result_id}: duplicate nonlocal_source_interpretation.supporting_atom_ids")
        for atom_id in atom_ids:
            atom = source_atoms.get(atom_id)
            if atom is None:
                fail(f"{result_id}: nonlocal interpretation cites unknown source atom {atom_id!r}")
            support = atom.get("interpretation_support")
            if not isinstance(support, dict):
                fail(
                    f"{result_id}: source atom {atom_id} is cited as interpretation evidence but carries no "
                    "interpretation_support link back to the counted result"
                )
            if result_id not in (support.get("result_ids") or []):
                fail(
                    f"{result_id}: source atom {atom_id} does not link back to this result in "
                    "interpretation_support.result_ids"
                )
            linked_back.setdefault(atom_id, set()).add(result_id)

        explicitation = block.get("lean_explicitation")
        if not isinstance(explicitation, list) or not explicitation:
            fail(
                f"{result_id}: nonlocal_source_interpretation.lean_explicitation must name the declarations that "
                "make the implicit source semantics explicit"
            )
        for entry in explicitation:
            if not isinstance(entry, dict):
                fail(f"{result_id}: lean_explicitation entries must be objects")
            declaration = entry.get("declaration")
            mechanism = entry.get("mechanism")
            if not isinstance(declaration, str) or declaration not in census_declarations:
                fail(
                    f"{result_id}: lean_explicitation declaration {declaration!r} is not registered in the "
                    "source census"
                )
            if not isinstance(mechanism, str) or len(mechanism.split()) < 8:
                fail(
                    f"{result_id}: lean_explicitation for {declaration} must say exactly which hypothesis or "
                    "conclusion carries the implicit source semantics"
                )
            if f"#check @{declaration}" not in audit_text and f"#check {declaration}" not in audit_text:
                fail(
                    f"{result_id}: lean_explicitation declaration {declaration} is missing from the compiler "
                    "audit surface"
                )

        expected_tex = sha256_file(TEX_PATH)
        expected_atoms = sha256_file(source_inventory_path)
        expected_digest = _supporting_atom_digest(atom_ids, source_atoms)
        for field, expected in (
            ("distributable_specification_sha256", expected_tex),
            ("source_fidelity_inventory_sha256", expected_atoms),
            ("supporting_atom_digest_sha256", expected_digest),
        ):
            actual = block.get(field)
            if actual != expected:
                fail(
                    f"{result_id}: accepted nonlocal source interpretation is stale ({field} differs); "
                    f"expected {expected}, got {actual!r}. Re-audit the reading against the changed source "
                    "material before re-accepting it."
                )
        if not isinstance(block.get("reviewed_on"), str) or not block["reviewed_on"].strip():
            fail(f"{result_id}: nonlocal_source_interpretation.reviewed_on must record the review date")

    # Reverse direction: no atom may claim to support a reading that does not cite it.
    for atom_id, atom in source_atoms.items():
        support = atom.get("interpretation_support")
        if support is None:
            continue
        if not isinstance(support, dict):
            fail(f"{atom_id}: interpretation_support must be an object")
        role = support.get("role")
        if role not in NONLOCAL_INTERPRETATION_ROLES:
            fail(
                f"{atom_id}: interpretation_support.role must be one of "
                + ", ".join(sorted(NONLOCAL_INTERPRETATION_ROLES))
                + f"; got {role!r}"
            )
        note = support.get("note")
        if not isinstance(note, str) or len(note.split()) < 8:
            fail(f"{atom_id}: interpretation_support.note must explain what the atom contributes to the reading")
        result_ids = support.get("result_ids")
        if not isinstance(result_ids, list) or not result_ids or not all(isinstance(x, str) for x in result_ids):
            fail(f"{atom_id}: interpretation_support.result_ids must be a nonempty list of counted result ids")
        if set(result_ids) != linked_back.get(atom_id, set()):
            fail(
                f"{atom_id}: interpretation_support.result_ids {sorted(result_ids)!r} disagree with the results "
                f"that actually cite this atom {sorted(linked_back.get(atom_id, set()))!r}"
            )

    return {
        "exceptional_results": exceptional,
        "interpretation_support_atoms": sorted(linked_back),
    }


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



_SCOPE_IDENT = r"[^\s\(\)\[\],:]+"


def _derive_scalar_scope(type_text: str) -> str:
    """Read a declaration's scalar scope off its compiler-printed type.

    The scalar a theorem is stated over is visible in its type, so it does not
    have to be asserted by hand -- and asserting it by hand went wrong: nine
    canonical entries claimed `complex` for declarations whose types quantify
    over `[RCLike 𝕜]`.

    The field position is read from `InnerProductSpace`/`NormedSpace`, which is
    where the scalar of the spaces the theorem is about actually appears; `δ : ℝ`
    and similar real parameters occur in every statement and say nothing about
    scalar scope.  `not_visible_in_type` is returned rather than guessed when the
    scalar is hidden inside a predicate, which is a fact about the type and is
    itself checkable.
    """
    rclike = set(re.findall(r"RCLike\s+(" + _SCOPE_IDENT + r")", type_text))
    generic = set(re.findall(r"NontriviallyNormedField\s+(" + _SCOPE_IDENT + r")", type_text))
    fields: set[str] = set()
    for pattern in (
        r"InnerProductSpace\s+(" + _SCOPE_IDENT + r")",
        r"NormedSpace\s+(" + _SCOPE_IDENT + r")",
    ):
        fields |= set(re.findall(pattern, type_text))
    if fields & rclike:
        return "rclike"
    if fields & (generic - rclike):
        return "scalar_generic"
    concrete = fields & {"\u2102", "\u211d"}
    if concrete == {"\u2102"}:
        return "complex"
    if concrete == {"\u211d"}:
        return "real"
    if concrete == {"\u2102", "\u211d"}:
        return "mixed"
    if rclike:
        return "rclike"
    if generic:
        return "scalar_generic"
    return "not_visible_in_type"


def _derive_capability_classes(type_text: str) -> list[str]:
    """Which proof-capability instance binders a printed type carries.

    The vocabulary is policy and lives above.  Anything else that *looks* like a
    capability class -- an instance binder whose head is `…Has<Something>` -- is
    reported rather than silently ignored, so a new one cannot appear in a
    canonical signature unclassified.
    """
    found = sorted(name for name in CAPABILITY_CLASSES if f"[{name} " in type_text)
    for match in re.findall(r"\[([A-Za-z_][A-Za-z0-9_.]*Has[A-Z][A-Za-z0-9_]*)\s", type_text):
        if match not in CAPABILITY_CLASSES:
            fail(
                f"unclassified capability-like instance binder {match!r} in a canonical "
                "signature; add it to CAPABILITY_CLASSES or explain why it is an ordinary "
                "mathematical hypothesis"
            )
    return found


def _probe_canonical_types(names: list[str]) -> dict[str, str]:
    """`#check` every canonical declaration and return its printed type.

    Uses the same compiler probe the source census uses, so a stale snapshot
    cannot drift: the types are read from the build at check time.
    """
    try:
        from aiq_lean_tools.lean_backend import SubprocessLeanBackend
    except ModuleNotFoundError:  # pragma: no cover - environment problem, not a data problem
        fail(
            "aiq_lean_tools is not installed, so canonical scalar scopes cannot be verified. "
            "Run `python3 -m pip install -e submodules/aiq-lean-formalization-tools`, or pass "
            "--no-lean-probe and accept that scalar_scope is unverified."
        )
    backend = SubprocessLeanBackend()
    rows = backend.probe_queries(
        ROOT, [("check", name) for name in names], [PROBE_IMPORT]
    )
    unresolved = sorted(row.name for row in rows if not row.resolved)
    if unresolved:
        fail(
            "canonical evidence did not resolve against "
            f"{PROBE_IMPORT}: " + ", ".join(unresolved)
        )
    return {row.name: row.output for row in rows}


def _canonical_evidence_digest(items: list[dict[str, Any]]) -> str:
    """Digest of every result's canonical evidence, in inventory order.

    Changing which declaration is a result's canonical witness -- or which source
    atoms it is claimed to cover -- changes this digest, which makes the accepted
    semantic sweep stale.  That is the point: canonical evidence is the answer to
    "what proves this result", so an edit to it must be re-reviewed rather than
    inherited.
    """
    payload = [
        {
            "id": item["id"],
            "canonical_evidence": [
                {
                    "declaration": entry.get("declaration"),
                    "role": entry.get("role"),
                    "scalar_scope": entry.get("scalar_scope"),
                    "evidence_kind": entry.get("evidence_kind"),
                    "covers_source_atoms": entry.get("covers_source_atoms"),
                    "capability_classes": entry.get("capability_classes"),
                }
                for entry in item.get("canonical_evidence", []) or []
            ],
        }
        for item in items
    ]
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _validate_markdown_view(items: list[dict[str, Any]], terminal: int) -> None:
    """Gate the hand-maintained Markdown view against the JSON it restates.

    `dev/davis-kahan-1970-formalization-result-inventory.md` is the file the
    READMEs point reviewers at, and its header counts and status table are a copy
    of this inventory.  A copy of a moving fact goes stale silently, so the copy
    is checked rather than trusted.  (The same failure has already happened in
    the census notes, which asserted for weeks that all four short `SectionTwo.*`
    names were unbound after one of them was bound.)
    """
    view_path = ROOT / "dev/davis-kahan-1970-formalization-result-inventory.md"
    if not view_path.exists():
        fail("dev/davis-kahan-1970-formalization-result-inventory.md is missing")
    text = view_path.read_text(encoding="utf-8")

    obligations = sum(1 for item in items if item.get("completion_obligation") is not False)
    nonlocal_count = sum(
        1
        for item in items
        if item.get("semantic_alignment") == "paper_faithful_nonlocal_source_interpretation"
    )
    for label, value in (
        ("Counted results", len(items)),
        ("Result-boundary reviews accepted", f"{obligations}/{obligations}"),
        ("Currently hostile-certified terminal", terminal),
        ("Awaiting closure", obligations - terminal),
        ("Printed statements that are NOT locally self-contained", nonlocal_count),
    ):
        line = f"- {label}: **{value}**"
        if line not in text:
            fail(
                "dev/davis-kahan-1970-formalization-result-inventory.md is stale: expected the "
                f"header line {line!r}"
            )

    for item in items:
        result_id = item["id"]
        cells = [
            f"`{result_id}`",
            str(_result_kind(item)),
            f"`{item.get('semantic_alignment')}`",
            "yes" if item.get("semantic_alignment") != "paper_faithful_nonlocal_source_interpretation" else "**no**",
            f"`{_result_disposition(item)}`",
            f"`{item.get('verification')}`",
            f"`{_semantic_certification(item)}`",
        ]
        row = "| " + " | ".join(cells)
        if row not in text:
            fail(
                "dev/davis-kahan-1970-formalization-result-inventory.md is stale: the status row "
                f"for {result_id} does not match the inventory; expected a row beginning {row!r}"
            )


SECTION_TWO_SHORT_NAMES = ("sinTheta", "tanTheta", "sinTwoTheta", "tanTwoTheta")


def _validate_section_two_short_names(data: dict[str, Any]) -> None:
    """One owner for "which short Section 2 names are bound".

    Four census rows and four inventory notes each asserted that all four were
    unbound, and stayed that way after `SectionTwo.sinTheta` was bound.  The
    prose is gone; the fact now lives here and is compared against
    `SectionTwo.lean`'s own `alias` lines.
    """
    record = data.get("section_two_short_names")
    if not isinstance(record, dict):
        fail("formalization-result inventory must record section_two_short_names")
    rel = record.get("source_file")
    if not isinstance(rel, str) or not rel.strip():
        fail("section_two_short_names.source_file must name the Lean inventory module")
    path = ROOT / rel
    if not path.exists():
        fail(f"section_two_short_names.source_file does not exist: {rel}")
    aliases = dict(
        re.findall(
            r"^alias\s+([A-Za-z_][A-Za-z0-9_]*)\s*:=\s*(\S+)\s*$",
            path.read_text(encoding="utf-8"),
            re.M,
        )
    )
    bindings = record.get("bindings")
    if not isinstance(bindings, dict):
        fail("section_two_short_names.bindings must be an object")
    if sorted(bindings) != sorted(SECTION_TWO_SHORT_NAMES):
        fail(
            "section_two_short_names.bindings must name exactly "
            f"{sorted(SECTION_TWO_SHORT_NAMES)}, got {sorted(bindings)}"
        )
    for name in SECTION_TWO_SHORT_NAMES:
        recorded = bindings[name]
        actual = aliases.get(name)
        if recorded != actual:
            fail(
                f"section_two_short_names.bindings[{name!r}] is stale: {rel} says "
                f"{actual!r}, the inventory says {recorded!r}"
            )


def _validate_census_canonical_agreement(items: list[dict[str, Any]]) -> None:
    """The census reviewer packet must not name a different canonical theorem.

    Each census item carries a `semantic_review` packet with its own
    `canonical_declarations` list.  When that item is one of the 29 counted
    results, the two lists are answering the same question, and they have
    disagreed: the packets for three of the four Section 2 results named a
    *finite-dimensional* facade as canonical while the inventory certified the
    result at unbounded infinite-dimensional scope.  The inventory's
    `canonical_evidence` is the single owner of that answer.
    """
    if not CENSUS_PATH.exists():
        return
    census = json.loads(CENSUS_PATH.read_text(encoding="utf-8"))
    canonical_by_id = {
        item["id"]: {
            entry.get("declaration") for entry in item.get("canonical_evidence", []) or []
        }
        for item in items
    }
    for census_item in census.get("items", []):
        result_id = census_item.get("id")
        if result_id not in canonical_by_id:
            continue
        review = census_item.get("semantic_review")
        if not isinstance(review, dict):
            continue
        declared = review.get("canonical_declarations")
        if not isinstance(declared, list):
            continue
        stray = sorted(set(declared) - canonical_by_id[result_id])
        if stray:
            fail(
                f"{result_id}: the census semantic-review packet names canonical declarations "
                "that the result inventory does not treat as canonical evidence: "
                + ", ".join(stray)
            )


def _validate_canonical_evidence(
    items: list[dict[str, Any]],
    census_declarations: set[str],
    audit_text: str,
    audit_rel: str,
    probed_types: dict[str, str] | None,
) -> None:
    """Separate what *proves* a counted result from what merely accompanies it.

    `lean_declarations` mixes primary witnesses, fixed-field companions,
    presentation wrappers, stronger generalizations, specializations, and
    implementation structures.  Agents have repeatedly selected the wrong
    theorem out of that list by name or by ordering.  `canonical_evidence`
    names the declarations that carry the printed statement, together with the
    exact source atoms each one covers; `supporting_evidence` holds the rest.
    """
    for item in items:
        result_id = item["id"]
        canonical = item.get("canonical_evidence")
        supporting = item.get("supporting_evidence")
        if not isinstance(canonical, list) or not canonical:
            fail(f"{result_id}: must record a nonempty canonical_evidence list")
        if not isinstance(supporting, list):
            fail(f"{result_id}: must record a supporting_evidence list (possibly empty)")

        declared = set(_declarations(item))
        atom_ids = set(_source_atom_ids(item))
        covered: set[str] = set()
        seen: set[str] = set()
        for entry in canonical:
            if not isinstance(entry, dict):
                fail(f"{result_id}: canonical_evidence entries must be objects")
            declaration = entry.get("declaration")
            if not isinstance(declaration, str) or not declaration.strip():
                fail(f"{result_id}: canonical_evidence entry must name a declaration")
            if declaration in seen:
                fail(f"{result_id}: canonical_evidence names {declaration} twice")
            seen.add(declaration)
            if declaration not in declared:
                fail(
                    f"{result_id}: canonical evidence {declaration} is not registered in "
                    "the result's lean_declarations"
                )
            if declaration not in census_declarations:
                fail(
                    f"{result_id}: canonical evidence {declaration} is not registered in "
                    "the source census"
                )
            if (
                f"#check @{declaration}" not in audit_text
                and f"#check {declaration}" not in audit_text
            ):
                fail(
                    f"{result_id}: canonical evidence {declaration} is not #checked by "
                    f"{audit_rel}; canonical evidence must carry compiler evidence"
                )
            role = entry.get("role")
            if role not in CANONICAL_EVIDENCE_ROLES:
                fail(
                    f"{result_id}: canonical evidence {declaration} has role {role!r}; "
                    f"expected one of {sorted(CANONICAL_EVIDENCE_ROLES)}"
                )
            kind = entry.get("evidence_kind")
            if kind not in CANONICAL_EVIDENCE_KINDS:
                fail(
                    f"{result_id}: canonical evidence {declaration} has evidence_kind "
                    f"{kind!r}; expected one of {sorted(CANONICAL_EVIDENCE_KINDS)}"
                )
            if (role == "exact_refutation") != (kind == "refutation"):
                fail(
                    f"{result_id}: canonical evidence {declaration} must pair role "
                    "'exact_refutation' with evidence_kind 'refutation'"
                )
            scope = entry.get("scalar_scope")
            if scope not in CANONICAL_SCALAR_SCOPES:
                fail(
                    f"{result_id}: canonical evidence {declaration} has scalar_scope "
                    f"{scope!r}; expected one of {sorted(CANONICAL_SCALAR_SCOPES)}"
                )
            if scope == "not_visible_in_type":
                note = entry.get("scalar_scope_note")
                if not isinstance(note, str) or not note.strip():
                    fail(
                        f"{result_id}: canonical evidence {declaration} records "
                        "scalar_scope 'not_visible_in_type' and must say where the scalar "
                        "actually lives, in scalar_scope_note"
                    )
            recorded_caps = entry.get("capability_classes")
            if not isinstance(recorded_caps, list) or not all(
                isinstance(x, str) for x in recorded_caps
            ):
                fail(
                    f"{result_id}: canonical evidence {declaration} must record "
                    "capability_classes (an empty list when it carries none)"
                )
            if probed_types is not None:
                derived = _derive_scalar_scope(probed_types[declaration])
                if derived != scope:
                    fail(
                        f"{result_id}: canonical evidence {declaration} records scalar_scope "
                        f"{scope!r}, but its compiler-printed type says {derived!r}"
                    )
                derived_caps = _derive_capability_classes(probed_types[declaration])
                if sorted(recorded_caps) != derived_caps:
                    fail(
                        f"{result_id}: canonical evidence {declaration} records "
                        f"capability_classes {sorted(recorded_caps)!r}, but its "
                        f"compiler-printed type carries {derived_caps!r}"
                    )
            atoms = entry.get("covers_source_atoms")
            if not isinstance(atoms, list) or not all(isinstance(a, str) for a in atoms):
                fail(
                    f"{result_id}: canonical evidence {declaration} must list the source "
                    "atoms it covers"
                )
            stray = sorted(set(atoms) - atom_ids)
            if stray:
                fail(
                    f"{result_id}: canonical evidence {declaration} claims source atoms "
                    "that are not assigned to this result: " + ", ".join(stray)
                )
            # `covers_source_atoms` is DERIVED from the source clauses, never authored.
            # Hand-authored unions are how a certificate was assembled from pieces no
            # theorem proves together; a declaration covers exactly what the ESTABLISHED
            # clauses it is the primary of establish.
            wide = set(item.get("result_wide_scope_atoms") or [])
            derived: set[str] = set()
            for clause in item.get("source_clauses") or []:
                if clause.get("status") != "established":
                    continue
                if (clause.get("evidence") or {}).get("primary") != declaration:
                    continue
                derived |= set(clause.get("conclusion_atoms") or [])
                derived |= set(clause.get("clause_hypothesis_atoms") or [])
                derived |= wide
            if set(atoms) != derived:
                fail(
                    f"{result_id}: canonical evidence {declaration} records covers_source_atoms "
                    f"{sorted(atoms)!r}, but its established source clauses establish {sorted(derived)!r}. "
                    "This field is derived from the clauses and must not be authored."
                )
            covered.update(atoms)

        refuting = {e.get("declaration") for e in canonical if e.get("role") == "exact_refutation"}
        if result_id in REFUTATION_RESULT_IDS:
            if not refuting:
                fail(
                    f"{result_id}: the printed statement is false, so its canonical evidence "
                    "must be an exact refutation, not a proof"
                )
            if _result_disposition(item) != "refuted_as_transcribed":
                fail(f"{result_id}: refutation evidence requires disposition 'refuted_as_transcribed'")
        elif refuting:
            fail(
                f"{result_id}: canonical evidence claims an exact refutation, but this "
                "result is not recorded as false as printed"
            )

        support_seen: set[str] = set()
        for entry in supporting:
            if not isinstance(entry, dict):
                fail(f"{result_id}: supporting_evidence entries must be objects")
            declaration = entry.get("declaration")
            if not isinstance(declaration, str) or declaration not in declared:
                fail(
                    f"{result_id}: supporting evidence {declaration!r} is not registered in "
                    "the result's lean_declarations"
                )
            if declaration in seen:
                fail(
                    f"{result_id}: {declaration} is listed as both canonical and supporting "
                    "evidence"
                )
            support_seen.add(declaration)
            if entry.get("role") not in SUPPORTING_EVIDENCE_ROLES:
                fail(
                    f"{result_id}: supporting evidence {declaration} has role "
                    f"{entry.get('role')!r}; expected one of {sorted(SUPPORTING_EVIDENCE_ROLES)}"
                )
        unpartitioned = sorted(declared - seen - support_seen)
        if unpartitioned:
            fail(
                f"{result_id}: registered declarations are neither canonical nor supporting "
                "evidence: " + ", ".join(unpartitioned)
            )

        is_terminal = (
            _result_disposition(item) in TERMINAL_RESULT_DISPOSITIONS
            and item.get("verification") in TERMINAL_VERIFICATIONS
            and _semantic_certification(item) in TERMINAL_SEMANTIC_CERTIFICATIONS
        )
        uncovered = sorted(atom_ids - covered)
        if is_terminal and uncovered:
            fail(
                f"{result_id}: terminal result has source atoms covered by no canonical "
                "evidence: " + ", ".join(uncovered)
            )
        if not is_terminal and not uncovered:
            fail(
                f"{result_id}: nonterminal result claims complete canonical atom coverage; "
                "either the coverage or the status is wrong"
            )


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
    expected_evidence_digest = _canonical_evidence_digest(items)
    recorded_evidence_digest = sweep.get("canonical_evidence_sha256")
    if recorded_evidence_digest != expected_evidence_digest:
        fail(
            "semantic_review_sweep.canonical_evidence_sha256 is stale: canonical evidence "
            f"changed; expected {expected_evidence_digest!r}, got {recorded_evidence_digest!r}"
        )
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
        "canonical_evidence_sha256": expected_evidence_digest,
    }

def unique_in_order(values: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for value in values:
        if value not in seen:
            seen.add(value)
            out.append(value)
    return out


def completion_summary(
    inventory_path: Path | None = None,
    *,
    require_terminal: bool = False,
    lean_probe: bool = True,
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
            # Cross-block SCOPE atoms are legitimate: the source often states a
            # result's scope extension in a later block, and the boundary review
            # lists them under `cross_block_scope_atom_ids`.  Anything else from
            # another block is a mis-attachment.
            wrong_parent = sorted(
                atom_id for atom_id in source_ids
                if source_atoms[atom_id].get("parent_claim_id") != parent
                and source_atoms[atom_id].get("formalization_role") != "result_scope"
            )
            if wrong_parent:
                fail(
                    f"{result_id}: source atoms from another block are not scope atoms, so they do not "
                    f"belong to parent_claim_id={parent!r}: " + ", ".join(wrong_parent)
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
    audit_text = (ROOT / semantic_audit["compiler_audit_surface"]).read_text(encoding="utf-8")
    canonical_names = unique_in_order([
        entry["declaration"]
        for item in items
        for entry in item.get("canonical_evidence", []) or []
        if isinstance(entry, dict) and isinstance(entry.get("declaration"), str)
    ])
    probed_types = _probe_canonical_types(canonical_names) if lean_probe else None
    _validate_canonical_evidence(
        items, census_declarations, audit_text, semantic_audit["compiler_audit_surface"],
        probed_types,
    )
    clause_opens = _validate_source_clauses(
        items, source_atoms, census_declarations, audit_text,
        semantic_audit["compiler_audit_surface"], probed_types,
    )
    _validate_census_canonical_agreement(items)
    _validate_section_two_short_names(data)
    _validate_markdown_view(items, terminal)
    nonlocal_interpretation = _validate_nonlocal_interpretation(
        items, source_atoms, source_inventory_path, census_declarations, audit_text
    )
    _validate_scope_atom_classification(source_atoms)
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
        "nonlocal_source_interpretation": nonlocal_interpretation,
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
    parser.add_argument(
        "--no-lean-probe", action="store_true",
        help="skip the compiler probe; canonical scalar scopes are then NOT verified",
    )
    args = parser.parse_args()

    # The generic layer -- ids, cross-links between counted results and source
    # atoms, and the structural shape of cited declaration names -- is the
    # package's; everything below it in this file is Davis--Kahan completion
    # policy, which is deliberately not generic.
    inventory = discover_inventory(args.inventory)
    if inventory is not None:
        findings = load_coverage_bundle(inventory, root=ROOT).validate()
        for finding in findings:
            print(f"{finding.level.upper():8s}{finding.location}: [{finding.code}] {finding.message}")
        if any(f.level == "error" for f in findings):
            return 1

    summary = completion_summary(
        args.inventory, require_terminal=args.require_terminal,
        lean_probe=not args.no_lean_probe,
    )
    if args.no_lean_probe:
        print("NOTE: --no-lean-probe given; canonical scalar_scope was NOT verified "
              "against the compiler-printed types")
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
    exceptional = summary["nonlocal_source_interpretation"]["exceptional_results"]
    if exceptional:
        print(
            "  results accepted under a nonlocal source interpretation (printed statement not locally "
            "self-contained): " + ", ".join(exceptional)
        )
    if summary["nonterminal_results"]:
        print("  first nonterminal results:")
        for item in summary["nonterminal_results"][:10]:
            print(f"    - {item['id']}: " + "; ".join(item["reasons"]))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
