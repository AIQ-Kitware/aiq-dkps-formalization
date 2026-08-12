#!/usr/bin/env python3
"""Check the distributable Davis--Kahan 1970 source-to-Lean statement map.

This gate is deliberately compiler-free.  The checked-in transformative
reconstruction `DavisKahan1970_part_III.tex` is the semantic source
specification used by the static audit.  The checker verifies that its marked
claim passages, the machine-readable statement map, and the maintained source
census agree on identity, source order, passage hashes, expected status, and
review declarations.

No private transcription, publisher PDF, or copied source register is required
or accepted as an input to this check.  Those may be used separately to audit
the quality of the distributable reconstruction itself.
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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--require-terminal",
        action="store_true",
        help="require every registered completion obligation to have terminal source status, proved_in_build verification, and hostile semantic certification=accepted",
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
                if args.require_terminal:
                    if c.get("status") not in TERMINAL_COMPLETION_STATUSES:
                        fail(f"{item_id}: completion obligation is not source-terminal: status={c.get('status')!r}")
                    if c.get("verification") not in TERMINAL_COMPLETION_VERIFICATIONS:
                        fail(
                            f"{item_id}: terminal completion obligation is not compiler-certified: "
                            f"verification={c.get('verification')!r}"
                        )
                    if cert not in TERMINAL_COMPLETION_CERTIFICATIONS:
                        fail(
                            f"{item_id}: hostile semantic certification is not accepted: "
                            f"completion_certification={cert!r}"
                        )
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

    renderer = ROOT / "scripts/render_davis_kahan_1970_audit_packet.py"
    if renderer.exists():
        rendered = subprocess.run([sys.executable, str(renderer), "--check"], cwd=ROOT)
        if rendered.returncode:
            return rendered.returncode

    print(
        "Davis--Kahan statement map: CLEAN "
        f"({len(mapped)} rows; {completion_count} completion obligations; "
        f"{exact_count} hostile-certified exact + {refuted_count} hostile-certified refuted; "
        f"{reopened_count} reopened obligations; {nonobligation_count} non-obligations; "
        f"{questions} Section 10 rows; {review_count} primary review links)"
    )
    print(f"  distributable source specification: {tex_path.relative_to(ROOT)}")
    print(f"  statement map: {MAP_PATH.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
