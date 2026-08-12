#!/usr/bin/env python3
"""Render a one-row-at-a-time Davis--Kahan 1970 statement audit packet.

Without a compiler certificate this produces a static review template containing
the registered passages from the checked-in transformative source specification,
plus mapped Lean declaration names and best-effort source locations.  With
`--certificate`, it also inserts theorem types printed by the pinned Lean compiler.
"""
from __future__ import annotations

import argparse
import json
import pathlib
import re
import tempfile
from typing import Iterable

from check_davis_kahan_1970_statement_map import extract_claims

ROOT = pathlib.Path(__file__).resolve().parents[1]
MAP_PATH = ROOT / "dev/davis-kahan-1970-statement-map.json"
CENSUS_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.json"
DEFAULT_OUTPUT = ROOT / "dev/davis-kahan-1970-independent-audit-template.md"

DECL_LINE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|alias)\s+([A-Za-z0-9_']+)\b"
)

CHECKLIST = [
    "The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.",
    "The Lean conclusion matches every mathematical clause in the registered source excerpt.",
    "Real/complex scalar scope matches the source, including any source statement that is field-independent.",
    "Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.",
    "Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.",
    "Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.",
    "Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.",
    "Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.",
    "Finite sums, infinite sums, extended-real divergence, and ideal-membership conclusions match the source where relevant.",
    "Any claimed equivalent formulation is actually connected to the paper's notation by compiled dictionary theorems.",
    "If this row is a refutation, the formal counterexample satisfies all printed hypotheses and falsifies the printed conclusion.",
]


def load_json(path: pathlib.Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def production_lean_files() -> Iterable[pathlib.Path]:
    for path in ROOT.rglob("*.lean"):
        rel = path.relative_to(ROOT)
        if any(part.startswith(".") for part in rel.parts):
            continue
        if rel.parts and rel.parts[0] in {"build"}:
            continue
        yield path


def declaration_locations(declarations: set[str]) -> dict[str, list[str]]:
    by_short: dict[str, list[str]] = {}
    wanted_short: dict[str, set[str]] = {}
    for decl in declarations:
        wanted_short.setdefault(decl.rsplit(".", 1)[-1], set()).add(decl)
    for path in production_lean_files():
        rel = path.relative_to(ROOT)
        try:
            lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
        except OSError:
            continue
        for lineno, line in enumerate(lines, start=1):
            match = DECL_LINE.match(line)
            if not match:
                continue
            short = match.group(1)
            if short not in wanted_short:
                continue
            location = f"{rel}:{lineno}"
            by_short.setdefault(short, []).append(location)
    out: dict[str, list[str]] = {}
    for decl in declarations:
        locations = by_short.get(decl.rsplit(".", 1)[-1], [])
        out[decl] = sorted(set(locations))
    return out


def load_signatures(certificate_path: pathlib.Path | None) -> tuple[dict[str, dict], dict | None]:
    if certificate_path is None:
        return {}, None
    certificate = load_json(certificate_path)
    signature_name = certificate.get("signature_file", "signatures.json")
    sig_path = certificate_path.parent / signature_name
    if not sig_path.exists():
        return {}, certificate
    raw = load_json(sig_path)
    if isinstance(raw, dict) and "signatures" in raw:
        raw = raw["signatures"]
    return raw if isinstance(raw, dict) else {}, certificate


def md_code_block(text: str, language: str = "") -> str:
    # TeX passages can contain backticks, so use tildes.
    return f"~~~~{language}\n{text.rstrip()}\n~~~~"


def render(output: pathlib.Path, certificate_path: pathlib.Path | None = None) -> None:
    statement_map = load_json(MAP_PATH)
    census = load_json(CENSUS_PATH)
    census_by_id = {x["id"]: x for x in census["items"]}
    tex_path = ROOT / statement_map["source"]["audit_tex"]
    claims = extract_claims(tex_path)
    signatures, certificate = load_signatures(certificate_path)

    all_decls = {
        decl
        for item in census["items"]
        for decl in item.get("lean_declarations", [])
    }
    locations = declaration_locations(all_decls)

    lines: list[str] = []
    lines += [
        "# Davis--Kahan 1970 independent statement audit packet",
        "",
        "This packet is organized one source claim at a time. The TeX passages come directly from the checked-in transformative, source-order reconstruction `DavisKahan1970_part_III.tex`; they are the repository's distributable semantic audit specification. The census status is a claim to audit, not evidence of semantic fidelity.",
        "",
        "Compiler evidence, source status, and hostile semantic certification are intentionally separate. A compiler certificate establishes that registered declarations elaborate against `DavisKahan.All`; the maintained `completion_certification` records whether the current passage has already survived an adversarial semantic review, and the auditor must independently confirm or overturn that judgement.",
        "",
        f"- Statement map: `{MAP_PATH.relative_to(ROOT)}`",
        f"- Distributable source specification: `{tex_path.relative_to(ROOT)}`",
        f"- Census: `{CENSUS_PATH.relative_to(ROOT)}`",
        f"- Registered rows: **{len(statement_map['items'])}**",
        f"- Mathematical completion obligations: **{sum(bool(x['completion_obligation']) for x in statement_map['items'])}**",
    ]
    if certificate is None:
        lines += [
            "- Compiler certificate: **not supplied**. The theorem-type boxes below are placeholders; do not infer compilation from this static packet.",
        ]
    else:
        cert_status = certificate.get("overall_status", "unknown")
        lines += [
            f"- Compiler certificate: `{certificate_path}`",
            f"- Certificate overall status: **{cert_status}**",
            f"- Clean root build requested/performed: **{certificate.get('clean_root_build', False)}**",
            f"- Certified Git HEAD: `{certificate.get('git', {}).get('head', 'unknown')}`",
            f"- Certified source-tree SHA-256: `{certificate.get('source_tree_sha256', 'unknown')}`",
        ]
    lines += [
        "",
        "## Verdict vocabulary",
        "",
        "Use one of: **PASS exact**, **PASS refuted**, **FAIL scope**, **FAIL conclusion**, **FAIL missing clause**, **FAIL source specification**, or **UNCERTAIN**.",
        "",
        "At the end, separately list any mathematical claim found in the distributable source specification that is not represented by a row in the statement map.",
        "",
    ]

    for index, mapped in enumerate(statement_map["items"], start=1):
        item_id = mapped["id"]
        c = census_by_id[item_id]
        source = claims[item_id]
        lines += [
            f"## {index}. {item_id} — {mapped['title']}",
            "",
            f"- **Source anchor:** {mapped['source_anchor']}",
            f"- **Source kind:** `{mapped['source_kind']}`",
            f"- **Completion obligation:** `{str(mapped['completion_obligation']).lower()}`",
            f"- **Census claim:** `{c['status']}` / `{c['verification']}`",
            f"- **Hostile completion certification:** `{c.get('completion_certification', 'missing')}`",
            f"- **Source-specification passage SHA-256:** `{mapped['source_specification_sha256']}`",
            "",
            "### Registered distributable source-specification passage",
            "",
            md_code_block(source, "tex"),
            "",
            "### Semantic audit clauses",
            "",
        ]
        for clause in mapped.get("audit_clauses", []):
            clause_decls = clause.get("review_declarations", [])
            lines.append(f"- **`{clause['id']}`:** {clause['description']}")
            if clause_decls:
                lines.append("  - Review declarations: " + ", ".join(f"`{d}`" for d in clause_decls))
            else:
                lines.append("  - Review declarations: *(none; inspect the row mapping/source context)*")
        holes = c.get("completion_holes") or []
        if holes:
            lines += ["", "### Known hostile-review holes", ""]
            for hole in holes:
                lines.append(f"- **`{hole.get('kind', 'unspecified')}`:** {hole.get('detail', '')}")
        if mapped.get("audit_warning"):
            lines += ["", f"> **Audit warning:** {mapped['audit_warning']}"]
        lines += [
            "",
            "### Primary Lean declarations for semantic review",
            "",
        ]
        review = mapped.get("review_declarations", [])
        if not review:
            lines.append("No primary Lean declaration is registered for this row. If it is a completion obligation, this is itself a blocking audit defect.")
            lines.append("")
        for decl in review:
            locs = locations.get(decl) or []
            lines += [
                f"#### `{decl}`",
                "",
                "Source location candidates: " + (", ".join(f"`{x}`" for x in locs[:8]) if locs else "*not found by static short-name locator*"),
                "",
            ]
            sig = signatures.get(decl)
            if sig and sig.get("resolved"):
                lines += [
                    "Compiler-printed type:",
                    "",
                    md_code_block(sig.get("type", ""), "lean"),
                    "",
                ]
            elif certificate is not None:
                lines += [
                    "Compiler-printed type: **UNRESOLVED OR MISSING FROM CERTIFICATE**",
                    "",
                ]
            else:
                lines += [
                    "Compiler-printed type: *inserted by `scripts/certify_davis_kahan_1970.py` when a certificate is supplied.*",
                    "",
                ]

        lines += [
            "<details>",
            "<summary>Full census declaration mapping for this row</summary>",
            "",
            "When a compiler certificate is supplied, `signatures.json` contains the compiler-printed type for every declaration in this full mapping, not only the primary declarations displayed above.",
            "",
        ]
        for decl in c.get("lean_declarations", []):
            locs = locations.get(decl) or []
            suffix = f" — {', '.join(locs[:3])}" if locs else ""
            captured = " — compiler type captured" if certificate is not None and signatures.get(decl, {}).get("resolved") else ""
            lines.append(f"- `{decl}`{suffix}{captured}")
        if not c.get("lean_declarations"):
            lines.append("- *(none)*")
        lines += ["", "</details>", "", "### Independent audit checklist", ""]
        for check in CHECKLIST:
            lines.append(f"- [ ] {check}")
        lines += [
            "",
            "### Auditor verdict",
            "",
            "- **Verdict:** _fill in_",
            "- **Reasoning / mismatch details:** _fill in_",
            "- **Additional Lean declaration(s) needed to establish coverage, if any:** _fill in_",
            "- **Unregistered source clause discovered, if any:** _fill in_",
            "",
            "---",
            "",
        ]

    mapped_by_id = {x["id"]: x for x in statement_map["items"]}
    completion_rows = [
        c for c in census["items"]
        if bool(mapped_by_id[c["id"]].get("completion_obligation"))
    ]
    accepted_rows = [c for c in completion_rows if c.get("completion_certification") == "accepted"]
    reopened_rows = [c for c in completion_rows if c.get("completion_certification") != "accepted"]
    accepted_exact = [c for c in accepted_rows if c.get("status") == "compiled_exact"]
    accepted_refuted = [c for c in accepted_rows if c.get("status") == "refuted_as_transcribed"]
    lines += [
        "# Final independent conclusion",
        "",
        f"- **{len(completion_rows)} explicit mathematical completion obligations reviewed:** yes / no",
        f"- **{len(accepted_exact)} currently hostile-certified exact obligations independently reconfirmed:** yes / no",
        f"- **{len(accepted_refuted)} currently hostile-certified refuted obligations independently reconfirmed:** yes / no",
        f"- **{len(reopened_rows)} currently reopened completion obligations resolved by this audit:** yes / no",
        "- **Reopened rows at packet generation:** " + (", ".join(f"`{c['id']}` ({c.get('completion_certification')})" for c in reopened_rows) if reopened_rows else "none"),
        "- **Any unregistered mathematical claims found:** yes / no",
        "- **Compiler certificate clean and complete:** yes / no",
        "- **Is the repository's claim of 100% theorem-statement-level Davis--Kahan 1970 coverage justified?** yes / no / uncertain",
        "",
        "## Findings requiring action",
        "",
        "1. _none recorded yet_",
        "",
    ]

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=pathlib.Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--certificate", type=pathlib.Path)
    parser.add_argument("--check", action="store_true", help="fail if the static default audit template is stale")
    args = parser.parse_args()
    output = args.output
    if not output.is_absolute():
        output = ROOT / output
    certificate = args.certificate
    if certificate is not None and not certificate.is_absolute():
        certificate = ROOT / certificate
    if args.check:
        if certificate is not None or output != DEFAULT_OUTPUT:
            parser.error("--check is only defined for the static default template without --certificate/--output")
        with tempfile.TemporaryDirectory(prefix="dk-audit-render-") as tmp:
            candidate = pathlib.Path(tmp) / "audit.md"
            render(candidate, None)
            expected = candidate.read_text(encoding="utf-8")
        if not DEFAULT_OUTPUT.exists() or DEFAULT_OUTPUT.read_text(encoding="utf-8") != expected:
            print(f"stale audit template: {DEFAULT_OUTPUT.relative_to(ROOT)}")
            return 1
        print(f"audit template up to date: {DEFAULT_OUTPUT.relative_to(ROOT)}")
        return 0
    render(output, certificate)
    print(f"wrote {output.relative_to(ROOT) if output.is_relative_to(ROOT) else output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
