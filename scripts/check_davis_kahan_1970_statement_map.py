#!/usr/bin/env python3
"""Check the distributable Davis--Kahan 1970 source-to-Lean statement map.

This gate is deliberately compiler-free.  The checked-in transformative
reconstruction `DavisKahan1970_part_III.tex` is the semantic source
specification used by the static audit.  The checker verifies that its marked
claim passages, the machine-readable statement map, and the maintained source
census agree on identity, source order, passage hashes, expected status, and
review declarations.

No private transcription, publisher PDF, or copied source register is required
or accepted as an input to this check. Those may be used separately to audit
the quality of the distributable reconstruction itself.

The 49 statement-map rows are organizational groups. The fine-grained source
atom inventory is checked here for source-fidelity coverage, but those atoms are
not the denominator for "100% formalized". The hard completion gate delegates to
`check_davis_kahan_1970_result_inventory.py`, whose compact stated-result
inventory is the only formalization denominator.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
MAP_PATH = ROOT / "dev/davis-kahan-1970-statement-map.json"
CENSUS_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.json"
EXPECTED_AUDIT_TEX = pathlib.Path("prose/distilled_literature/DavisKahan1970_part_III.tex")
LEGACY_REGISTER = ROOT / "prose/distilled_literature/DavisKahan1970_exact_source_register.tex"

CLAIM_BEGIN = re.compile(r"^% DK-CERT-CLAIM-BEGIN ([A-Za-z0-9_.-]+)\s*$")
CLAIM_END = re.compile(r"^% DK-CERT-CLAIM-END ([A-Za-z0-9_.-]+)\s*$")
SOURCE_BEGIN = "% DK-CERT-SOURCE-BEGIN"
SOURCE_END = "% DK-CERT-SOURCE-END"

TERMINAL_COMPLETION_STATUSES = {"compiled_exact", "refuted_as_transcribed"}
TERMINAL_COMPLETION_VERIFICATIONS = {"proved_in_build"}
TERMINAL_COMPLETION_CERTIFICATIONS = {"accepted"}
NUMBERED_EQUATION_RE = re.compile(r"\\tag\{([^}]+)\}")


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def check_no_unregistered_source_prose(tex_path: pathlib.Path) -> None:
    """Reject substantive prose between registered claims in the source-order body.

    Section headings are structural navigation.  Every other source-derived sentence in
    the audited body must live inside a DK-CERT claim so the statement map cannot
    silently omit it from the generated audit packet.
    """
    lines = tex_path.read_text(encoding="utf-8").splitlines()
    claim_starts = [i for i, line in enumerate(lines) if CLAIM_BEGIN.match(line)]
    claim_ends = [i for i, line in enumerate(lines) if CLAIM_END.match(line)]
    if not claim_starts or not claim_ends:
        fail("source specification has no registered claim body")
    lo, hi = claim_starts[0], claim_ends[-1]
    in_claim = False
    for i in range(lo, hi + 1):
        line = lines[i]
        if CLAIM_BEGIN.match(line):
            in_claim = True
            continue
        if CLAIM_END.match(line):
            in_claim = False
            continue
        if in_claim or not line.strip() or line.lstrip().startswith("%"):
            continue
        stripped = line.strip()
        if stripped.startswith(r"\section{") or stripped.startswith(r"\subsection*{"):
            continue
        fail(
            f"unregistered source prose at {tex_path.relative_to(ROOT)}:{i + 1}: "
            f"{stripped!r}; move source mathematics/prose into a DK-CERT claim block"
        )


def extract_claims(tex_path: pathlib.Path) -> dict[str, str]:
    """Extract source-specification passages in their TeX presentation order."""
    lines = tex_path.read_text(encoding="utf-8").splitlines()
    claims: dict[str, str] = {}
    i = 0
    while i < len(lines):
        match = CLAIM_BEGIN.match(lines[i])
        if not match:
            i += 1
            continue
        claim_id = match.group(1)
        if claim_id in claims:
            fail(f"duplicate TeX claim marker: {claim_id}")
        i += 1
        while i < len(lines) and lines[i] != SOURCE_BEGIN:
            if CLAIM_BEGIN.match(lines[i]):
                fail(f"nested claim before source block for {claim_id}")
            if CLAIM_END.match(lines[i]):
                fail(f"{claim_id}: claim ended before source block")
            i += 1
        if i >= len(lines):
            fail(f"missing source-begin marker for {claim_id}")
        i += 1

        source_lines: list[str] = []
        while i < len(lines) and lines[i] != SOURCE_END:
            if CLAIM_BEGIN.match(lines[i]) or CLAIM_END.match(lines[i]):
                fail(f"{claim_id}: malformed nested/end marker inside source passage")
            source_lines.append(lines[i])
            i += 1
        if i >= len(lines):
            fail(f"{claim_id}: missing source-end marker")
        source = "\n".join(source_lines).strip() + "\n"
        if not source.strip():
            fail(f"{claim_id}: empty source-specification passage")
        if r"\begin{verbatim}" in source or r"\end{verbatim}" in source:
            fail(
                f"{claim_id}: source passage uses a verbatim environment; "
                "the distributable audit source must be a transformative mathematical reconstruction"
            )
        claims[claim_id] = source

        i += 1
        while i < len(lines):
            end = CLAIM_END.match(lines[i])
            if end:
                if end.group(1) != claim_id:
                    fail(f"claim end {end.group(1)} does not match {claim_id}")
                break
            if CLAIM_BEGIN.match(lines[i]):
                fail(f"{claim_id}: missing claim-end marker")
            i += 1
        if i >= len(lines):
            fail(f"{claim_id}: missing claim-end marker")
        i += 1
    return claims



def validate_source_fidelity_inventory(
    statement_map: dict,
    map_items: list[dict],
    tex_path: pathlib.Path,
) -> dict:
    """Validate Agent 3's fine-grained source inventory without making it proof debt."""
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

    row_ids = [item["id"] for item in map_items]
    row_set = set(row_ids)
    atom_ids: list[str] = []
    by_id: dict[str, dict] = {}
    orders: list[int] = []
    for atom in atoms:
        atom_id = atom.get("id")
        if not isinstance(atom_id, str) or not atom_id or atom_id in by_id:
            fail(f"source-fidelity inventory has missing/duplicate atom id: {atom_id!r}")
        parent = atom.get("parent_claim_id")
        if parent not in row_set:
            fail(f"{atom_id}: parent_claim_id is not a statement-map group: {parent!r}")
        order = atom.get("order")
        if not isinstance(order, int) or order <= 0:
            fail(f"{atom_id}: order must be a positive integer")
        if atom.get("present_in_distributable_spec") is not True:
            fail(f"{atom_id}: source-fidelity atom is not present in the distributable specification")
        role = atom.get("source_role")
        if role not in {"mathematical_assertion", "definition", "open_question", "historical_knowledge_state"}:
            fail(f"{atom_id}: unsupported source_role {role!r}")
        atom_ids.append(atom_id)
        by_id[atom_id] = atom
        orders.append(order)

    if orders != list(range(1, len(atoms) + 1)):
        fail("source-fidelity atom order must be exactly 1..N in paper order")

    flattened: list[str] = []
    for row in map_items:
        ids = row.get("source_atom_ids")
        if not isinstance(ids, list) or not ids or not all(isinstance(x, str) for x in ids):
            fail(f"{row['id']}: source_atom_ids must be a nonempty list of strings")
        if len(ids) != len(set(ids)):
            fail(f"{row['id']}: duplicate source_atom_ids")
        for atom_id in ids:
            atom = by_id.get(atom_id)
            if atom is None:
                fail(f"{row['id']}: references unknown source-fidelity atom {atom_id!r}")
            if atom.get("parent_claim_id") != row["id"]:
                fail(
                    f"{row['id']}: atom {atom_id} belongs to parent {atom.get('parent_claim_id')!r}"
                )
        flattened.extend(ids)

    if flattened != atom_ids:
        missing = sorted(set(atom_ids) - set(flattened))
        duplicated = sorted({x for x in flattened if flattened.count(x) > 1})
        extra = sorted(set(flattened) - set(atom_ids))
        fail(
            "statement-map source_atom_ids are not a source-order bijection onto the source-fidelity inventory; "
            f"missing={missing}, duplicated={duplicated}, extra={extra}"
        )

    summary = data.get("coverage_summary", {})
    if summary.get("source_blocks") != len(map_items):
        fail("source-fidelity coverage_summary.source_blocks disagrees with statement-map group count")
    if summary.get("total_atoms") != len(atoms):
        fail("source-fidelity coverage_summary.total_atoms disagrees with atoms list")

    numbered = [atom for atom in atoms if atom.get("kind") == "numbered-equation"]
    if summary.get("numbered_equation_atoms") != len(numbered):
        fail("source-fidelity numbered-equation summary disagrees with atoms list")
    tex_tags = NUMBERED_EQUATION_RE.findall(tex_path.read_text(encoding="utf-8"))
    if len(tex_tags) != len(numbered):
        fail(
            "distributable TeX numbered-equation count differs from source-fidelity inventory: "
            f"TeX={len(tex_tags)}, inventory={len(numbered)}"
        )

    return {
        "path": rel,
        "atoms": len(atoms),
        "numbered_equations": len(numbered),
    }

def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--require-terminal",
        action="store_true",
        help="require the compact stated-result inventory (not source-fidelity atoms or row labels) to be terminal",
    )
    args = parser.parse_args()

    statement_map = json.loads(MAP_PATH.read_text(encoding="utf-8"))
    census = json.loads(CENSUS_PATH.read_text(encoding="utf-8"))

    if statement_map.get("schema_version") != 1:
        fail(f"unsupported statement-map schema: {statement_map.get('schema_version')!r}")
    tex_rel = statement_map.get("source", {}).get("audit_tex")
    if tex_rel != str(EXPECTED_AUDIT_TEX):
        fail(
            "statement map must use the distributable Part III reconstruction as source.audit_tex; "
            f"expected {EXPECTED_AUDIT_TEX}, got {tex_rel!r}"
        )
    tex_path = ROOT / EXPECTED_AUDIT_TEX
    if not tex_path.exists():
        fail(f"audit TeX does not exist: {EXPECTED_AUDIT_TEX}")
    if LEGACY_REGISTER.exists():
        fail(
            f"legacy copied source register still exists: {LEGACY_REGISTER.relative_to(ROOT)}; "
            "remove it so the repository has one unambiguous distributable audit specification"
        )
    if statement_map.get("census") != str(CENSUS_PATH.relative_to(ROOT)):
        fail("statement map does not point at the maintained source census")

    map_items = statement_map.get("items")
    census_items = census.get("items")
    if not isinstance(map_items, list) or not isinstance(census_items, list):
        fail("statement map and census must both contain item lists")

    def by_id(items: list[dict], label: str) -> dict[str, dict]:
        out: dict[str, dict] = {}
        for item in items:
            item_id = item.get("id")
            if not item_id or item_id in out:
                fail(f"{label}: missing or duplicate id {item_id!r}")
            out[item_id] = item
        return out

    mapped = by_id(map_items, "statement map")
    censused = by_id(census_items, "census")
    check_no_unregistered_source_prose(tex_path)
    claims = extract_claims(tex_path)
    fidelity = validate_source_fidelity_inventory(statement_map, map_items, tex_path)

    census_order = [item["id"] for item in census_items]
    map_order = [item["id"] for item in map_items]
    tex_order = list(claims)
    if map_order != census_order:
        fail("statement-map row order differs from the maintained source census")
    if tex_order != census_order:
        fail(
            "TeX claim-marker order differs from the source/census order; "
            "the distributable reconstruction must preserve the paper presentation order"
        )

    expected_ids = set(censused)
    if set(mapped) != expected_ids:
        fail(
            "statement-map IDs differ from census IDs; missing="
            f"{sorted(expected_ids - set(mapped))}, extra={sorted(set(mapped) - expected_ids)}"
        )
    if set(claims) != expected_ids:
        fail(
            "TeX claim-marker IDs differ from census IDs; missing="
            f"{sorted(expected_ids - set(claims))}, extra={sorted(set(claims) - expected_ids)}"
        )

    completion_count = 0
    exact_count = 0
    refuted_count = 0
    questions = 0
    reopened_count = 0
    nonobligation_count = 0
    review_count = 0

    for item_id in census_order:
        m = mapped[item_id]
        c = censused[item_id]

        for field, census_field in (
            ("section", "section"),
            ("title", "title"),
            ("source_kind", "source_kind"),
            ("source_anchor", "source_anchor"),
        ):
            if m.get(field) != c.get(census_field):
                fail(
                    f"{item_id}: statement-map {field}={m.get(field)!r} differs from "
                    f"census {census_field}={c.get(census_field)!r}"
                )
        if m.get("expected_status") != c.get("status"):
            fail(f"{item_id}: expected_status disagrees with census status")
        if m.get("expected_verification") != c.get("verification"):
            fail(f"{item_id}: expected_verification disagrees with census verification")
        if m.get("expected_completion_certification") != c.get("completion_certification"):
            fail(f"{item_id}: expected_completion_certification disagrees with census completion_certification")
        if m.get("known_completion_holes", []) != c.get("completion_holes", []):
            fail(f"{item_id}: statement-map known_completion_holes disagree with census completion_holes")
        if m.get("tex_marker") != item_id:
            fail(f"{item_id}: tex_marker must equal the census id")

        passage = claims[item_id]
        actual_hash = sha256_text(passage)
        expected_hash = m.get("source_specification_sha256")
        if not isinstance(expected_hash, str) or len(expected_hash) != 64:
            fail(f"{item_id}: missing source_specification_sha256")
        if actual_hash != expected_hash:
            fail(
                f"{item_id}: source-specification passage hash changed: "
                f"expected {expected_hash}, got {actual_hash}"
            )
        forbidden_provenance_fields = {
            "source_excerpt_sha256",
            "source_line_ranges_in_modernized_transcription",
        }
        stale = sorted(forbidden_provenance_fields.intersection(m))
        if stale:
            fail(
                f"{item_id}: obsolete private-transcription/register fields remain in statement map: "
                + ", ".join(stale)
            )

        obligation = m.get("completion_obligation")
        if not isinstance(obligation, bool):
            fail(f"{item_id}: completion_obligation must be an explicit boolean")
        source_kind = c.get("source_kind")
        if source_kind == "open_question" and obligation:
            fail(f"{item_id}: a pure open_question row cannot be a completion obligation; use mixed_open_question for mixed blocks")
        if not obligation and source_kind != "open_question":
            fail(
                f"{item_id}: only a pure open_question row may be excluded from completion obligations; "
                f"source_kind={source_kind!r}"
            )
        cert = c.get("completion_certification")
        if obligation and cert == "not_applicable":
            fail(f"{item_id}: a completion obligation cannot have completion_certification='not_applicable'")
        if not obligation and cert != "not_applicable":
            fail(f"{item_id}: a pure non-obligation must have completion_certification='not_applicable'")
        if item_id.startswith("DK-10."):
            questions += 1
        if obligation:
            completion_count += 1
            is_compiler_terminal = (
                c.get("status") in TERMINAL_COMPLETION_STATUSES
                and c.get("verification") in TERMINAL_COMPLETION_VERIFICATIONS
            )
            is_semantically_terminal = cert in TERMINAL_COMPLETION_CERTIFICATIONS
            if is_compiler_terminal and is_semantically_terminal:
                if c.get("status") == "compiled_exact":
                    exact_count += 1
                else:
                    refuted_count += 1
            else:
                reopened_count += 1
        else:
            nonobligation_count += 1

        full_decls = c.get("lean_declarations") or []
        review_decls = m.get("review_declarations") or []
        if not isinstance(review_decls, list) or not all(isinstance(x, str) for x in review_decls):
            fail(f"{item_id}: review_declarations must be a list of strings")
        if obligation and not review_decls:
            fail(f"{item_id}: completion obligation has no primary review declarations")
        missing = [d for d in review_decls if d not in full_decls]
        if missing:
            fail(f"{item_id}: review declarations are not registered in the census: " + ", ".join(missing))
        if len(review_decls) != len(set(review_decls)):
            fail(f"{item_id}: duplicate review declarations")
        review_count += len(review_decls)

        clauses = m.get("audit_clauses")
        if not isinstance(clauses, list) or not clauses:
            fail(f"{item_id}: audit_clauses must be a nonempty list")
        clause_ids: set[str] = set()
        for clause in clauses:
            clause_id = clause.get("id")
            if not isinstance(clause_id, str) or not clause_id.startswith(item_id + "."):
                fail(f"{item_id}: invalid audit clause id {clause_id!r}")
            if clause_id in clause_ids:
                fail(f"{item_id}: duplicate audit clause id {clause_id}")
            clause_ids.add(clause_id)
            description = clause.get("description")
            if not isinstance(description, str) or not description.strip():
                fail(f"{clause_id}: missing clause description")
            clause_decls = clause.get("review_declarations")
            if not isinstance(clause_decls, list) or not all(isinstance(x, str) for x in clause_decls):
                fail(f"{clause_id}: review_declarations must be a list of strings")
            missing_clause = [d for d in clause_decls if d not in full_decls]
            if missing_clause:
                fail(
                    f"{clause_id}: clause review declarations are not registered in the census: "
                    + ", ".join(missing_clause)
                )

    result_checker = ROOT / "scripts/check_davis_kahan_1970_result_inventory.py"
    result_command = [sys.executable, str(result_checker)]
    if args.require_terminal:
        result_command.append("--require-terminal")
    result_check = subprocess.run(result_command, cwd=ROOT)
    if result_check.returncode:
        return result_check.returncode

    renderer = ROOT / "scripts/render_davis_kahan_1970_audit_packet.py"
    if renderer.exists():
        rendered = subprocess.run([sys.executable, str(renderer), "--check"], cwd=ROOT)
        if rendered.returncode:
            return rendered.returncode

    print(
        "Davis--Kahan statement map: CLEAN "
        f"({len(mapped)} organizational rows; legacy row triage: "
        f"{exact_count} accepted exact + {refuted_count} accepted refuted, "
        f"{reopened_count} reopened; {questions} Section 10 rows; {review_count} primary review links)"
    )
    print(
        f"  source fidelity: {fidelity['atoms']} atoms, {fidelity['numbered_equations']} numbered equations "
        f"({fidelity['path']}); these are NOT the formalization denominator"
    )
    print(f"  distributable source specification: {tex_path.relative_to(ROOT)}")
    print(f"  statement map: {MAP_PATH.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
