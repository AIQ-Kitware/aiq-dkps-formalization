#!/usr/bin/env python3
"""Check the Davis--Kahan 1970 exact-statement audit register.

This gate is deliberately compiler-free.  It verifies that the distributable
TeX claim register, the machine-readable statement map, and the maintained
source census agree exactly on row identity, source excerpts, expected status,
and the declarations selected for independent review.

The compiler-backed half of the certificate is produced separately by
`scripts/certify_davis_kahan_1970.py`.
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

CLAIM_BEGIN = re.compile(r"^% DK-CERT-CLAIM-BEGIN ([A-Za-z0-9_.-]+)\s*$")
CLAIM_END = re.compile(r"^% DK-CERT-CLAIM-END ([A-Za-z0-9_.-]+)\s*$")
SOURCE_BEGIN = "% DK-CERT-SOURCE-BEGIN"
SOURCE_END = "% DK-CERT-SOURCE-END"
VERBATIM_BEGIN = r"\begin{verbatim}"
VERBATIM_END = r"\end{verbatim}"

TERMINAL_COMPLETION_STATUSES = {"compiled_exact", "refuted_as_transcribed"}
TERMINAL_COMPLETION_VERIFICATIONS = {"proved_in_build"}


def fail(message: str) -> None:
    print(f"ERROR: {message}", file=sys.stderr)
    raise SystemExit(1)


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def extract_claims(tex_path: pathlib.Path) -> dict[str, str]:
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
            i += 1
        if i >= len(lines):
            fail(f"missing source-begin marker for {claim_id}")
        i += 1
        if i >= len(lines) or lines[i] != VERBATIM_BEGIN:
            fail(f"{claim_id}: source block must begin with {VERBATIM_BEGIN}")
        i += 1
        source_lines: list[str] = []
        while i < len(lines) and lines[i] != VERBATIM_END:
            source_lines.append(lines[i])
            i += 1
        if i >= len(lines):
            fail(f"{claim_id}: unterminated verbatim source block")
        i += 1
        if i >= len(lines) or lines[i] != SOURCE_END:
            fail(f"{claim_id}: missing source-end marker")
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
        # The register generator canonicalizes every excerpt to exactly one
        # trailing newline.  Hash that representation, not TeX surrounding it.
        claims[claim_id] = "\n".join(source_lines).strip() + "\n"
        i += 1
    return claims


def excerpt_from_private_transcription(path: pathlib.Path, ranges: list[list[int]]) -> str:
    lines = path.read_text(encoding="utf-8").splitlines()
    parts: list[str] = []
    for start, end in ranges:
        if end > len(lines):
            fail(f"private transcription line range {start}-{end} exceeds {len(lines)} lines")
        parts.append("\n".join(lines[start - 1:end]))
    return "\n\n".join(parts).strip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--transcription",
        type=pathlib.Path,
        help="optional private modernized transcription; verifies its full SHA-256 and every registered line-range excerpt without copying it into the repository",
    )
    parser.add_argument(
        "--require-terminal",
        action="store_true",
        help="add the completion-certificate requirement that every mathematical obligation be compiled_exact or refuted_as_transcribed and proved_in_build",
    )
    args = parser.parse_args()

    statement_map = json.loads(MAP_PATH.read_text(encoding="utf-8"))
    census = json.loads(CENSUS_PATH.read_text(encoding="utf-8"))

    if statement_map.get("schema_version") != 1:
        fail(f"unsupported statement-map schema: {statement_map.get('schema_version')!r}")
    tex_rel = statement_map.get("source", {}).get("audit_tex")
    if not tex_rel:
        fail("statement map has no source.audit_tex")
    tex_path = ROOT / tex_rel
    if not tex_path.exists():
        fail(f"audit TeX does not exist: {tex_rel}")
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
    claims = extract_claims(tex_path)

    private_transcription: pathlib.Path | None = None
    if args.transcription is not None:
        private_transcription = args.transcription.expanduser().resolve()
        if not private_transcription.exists():
            fail(f"private transcription does not exist: {private_transcription}")
        expected_full_hash = statement_map.get("source", {}).get("modernized_transcription_sha256")
        actual_full_hash = hashlib.sha256(private_transcription.read_bytes()).hexdigest()
        if actual_full_hash != expected_full_hash:
            fail(
                "private transcription SHA-256 differs from the provenance recorded in the statement map: "
                f"expected {expected_full_hash}, got {actual_full_hash}"
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
    review_count = 0

    for item_id in [item["id"] for item in census_items]:
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
        if m.get("tex_marker") != item_id:
            fail(f"{item_id}: tex_marker must equal the census id")

        excerpt = claims[item_id]
        actual_hash = sha256_text(excerpt)
        if actual_hash != m.get("source_excerpt_sha256"):
            fail(
                f"{item_id}: exact TeX excerpt hash changed: expected "
                f"{m.get('source_excerpt_sha256')}, got {actual_hash}"
            )
        ranges = m.get("source_line_ranges_in_modernized_transcription")
        if not isinstance(ranges, list) or not ranges:
            fail(f"{item_id}: missing source-line provenance")
        for value in ranges:
            if (
                not isinstance(value, list)
                or len(value) != 2
                or not all(isinstance(n, int) and n > 0 for n in value)
                or value[0] > value[1]
            ):
                fail(f"{item_id}: invalid source line range {value!r}")
        if private_transcription is not None:
            private_excerpt = excerpt_from_private_transcription(private_transcription, ranges)
            if private_excerpt != excerpt:
                fail(
                    f"{item_id}: TeX source block differs from the registered lines in the private transcription"
                )

        is_question = item_id.startswith("DK-10.")
        if bool(m.get("completion_obligation")) == is_question:
            fail(
                f"{item_id}: completion_obligation must be false exactly for Section 10 questions"
            )
        if is_question:
            questions += 1
        else:
            completion_count += 1
            if c.get("status") == "compiled_exact" and c.get("verification") == "proved_in_build":
                exact_count += 1
            elif c.get("status") == "refuted_as_transcribed" and c.get("verification") == "proved_in_build":
                refuted_count += 1
            elif args.require_terminal:
                if c.get("status") not in TERMINAL_COMPLETION_STATUSES:
                    fail(
                        f"{item_id}: completion obligation is not terminal: status={c.get('status')!r}"
                    )
                fail(
                    f"{item_id}: terminal completion obligation is not compiler-certified: "
                    f"verification={c.get('verification')!r}"
                )

        full_decls = c.get("lean_declarations") or []
        review_decls = m.get("review_declarations") or []
        if not isinstance(review_decls, list) or not all(isinstance(x, str) for x in review_decls):
            fail(f"{item_id}: review_declarations must be a list of strings")
        if not is_question and not review_decls:
            fail(f"{item_id}: completion obligation has no primary review declarations")
        missing = [d for d in review_decls if d not in full_decls]
        if missing:
            fail(
                f"{item_id}: review declarations are not registered in the census: "
                + ", ".join(missing)
            )
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
                fail(f"{clause_id}: clause review declarations are not registered in the census: " + ", ".join(missing_clause))

    renderer = ROOT / "scripts/render_davis_kahan_1970_audit_packet.py"
    if renderer.exists():
        rendered = subprocess.run([sys.executable, str(renderer), "--check"], cwd=ROOT)
        if rendered.returncode:
            return rendered.returncode

    print(
        "Davis--Kahan statement register: CLEAN "
        f"({len(mapped)} rows; {completion_count} completion obligations; "
        f"{exact_count} compiled exact + {refuted_count} compiled refuted; {questions} Section 10 questions; "
        f"{review_count} primary review links)"
    )
    print(f"  exact source register: {tex_path.relative_to(ROOT)}")
    print(f"  statement map: {MAP_PATH.relative_to(ROOT)}")
    if private_transcription is not None:
        print(f"  private transcription provenance: VERIFIED ({private_transcription})")
    else:
        print("  private transcription provenance: not rechecked (pass --transcription PATH to verify)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
