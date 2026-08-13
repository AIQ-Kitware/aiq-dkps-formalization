#!/usr/bin/env python3
"""Render the reviewer-facing Davis--Kahan 1970 result audit packet.

The packet makes the project's claim boundary explicit:

* every source-fidelity atom remains visible and classified;
* exactly 29 results Davis--Kahan establish form the 100% denominator; and
* each result records the atoms inside its printed statement and the same-block
  material deliberately excluded from that result boundary.

With `--certificate`, compiler-printed theorem types are inserted for the
registered source-facing Lean declarations.
"""
from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import tempfile
from typing import Iterable

from check_davis_kahan_1970_statement_map import extract_claims

ROOT = pathlib.Path(__file__).resolve().parents[1]
MAP_PATH = ROOT / "dev/davis-kahan-1970-statement-map.json"
CENSUS_PATH = ROOT / "dev/davis-kahan-1970-full-source-census.json"
RESULT_PATH = ROOT / "dev/davis-kahan-1970-formalization-result-inventory.json"
DEFAULT_OUTPUT = ROOT / "dev/davis-kahan-1970-independent-audit-template.md"

DECL_LINE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|instance|alias)\s+([A-Za-z0-9_']+)\b"
)

CHECKLIST = [
    "The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.",
    "Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.",
    "The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.",
    "The Lean conclusion matches every conclusion of the counted result.",
    "Real/complex scalar scope matches the source, including field-independent statements.",
    "Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.",
    "Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.",
    "Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.",
    "Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.",
    "Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.",
    "Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.",
    "If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.",
]

NONLOCAL_CHECKLIST = [
    "The printed statement really does omit the qualification the repository says it omits.",
    "The cited earlier/later source passages really say what the repository reports them as saying.",
    "The paper-wide existence/vacuity convention plausibly governs the displayed norm in this statement.",
    "The later standing assumption is genuinely in force where the source proves this result.",
    "The extra Lean hypothesis corresponds to the omitted source qualification and to nothing stronger.",
    "The competing literal reading is stated at its strongest, not as a straw man.",
    "The decision not to classify this result as refuted is justified by the source's own semantics.",
    "The distinction from the repository's canonical refutation is real, not a softening of it.",
]


def load_json(path: pathlib.Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def production_lean_files() -> Iterable[pathlib.Path]:
    for path in ROOT.rglob("*.lean"):
        rel = path.relative_to(ROOT)
        if any(part.startswith(".") for part in rel.parts):
            continue
        if rel.parts and rel.parts[0] == "build":
            continue
        yield path


def declaration_locations(declarations: set[str]) -> dict[str, list[str]]:
    by_short: dict[str, list[str]] = {}
    wanted_short = {decl.rsplit(".", 1)[-1] for decl in declarations}
    for path in production_lean_files():
        rel = path.relative_to(ROOT)
        try:
            lines = path.read_text(encoding="utf-8", errors="ignore").splitlines()
        except OSError:
            continue
        for lineno, line in enumerate(lines, start=1):
            match = DECL_LINE.match(line)
            if not match or match.group(1) not in wanted_short:
                continue
            by_short.setdefault(match.group(1), []).append(f"{rel}:{lineno}")
    return {
        decl: sorted(set(by_short.get(decl.rsplit(".", 1)[-1], [])))
        for decl in declarations
    }


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
    return f"~~~~{language}\n{text.rstrip()}\n~~~~"


def render_nonlocal_section(
    block: dict,
    atom_by_id: dict[str, dict],
    claims: dict[str, str],
) -> list[str]:
    """Put a nonlocal source-semantics dependency in front of the reviewer.

    The failure mode this defends against is a reviewer discovering, on their own,
    that a Lean statement carries a hypothesis the printed source display does not
    mention.  Here the repository says it first, shows the exact source passages it
    used to justify the reading, states the strongest competing reading against
    itself, and asks for a verdict on precisely that question.
    """
    lines = [
        "### ⚠ NONLOCAL SOURCE-SEMANTICS DEPENDENCY",
        "",
        "**This printed result is not locally self-contained. Read this section before the Lean evidence.**",
        "",
        f"- **Interpretation review status:** `{block.get('status', 'missing')}`",
        f"- **Classification:** `{block.get('classification', 'missing')}`",
        f"- **Reviewed on:** {block.get('reviewed_on', 'missing')}",
        f"- **Kept distinct from the repository's canonical refutation:** `{block.get('distinct_from_refutation', 'missing')}`",
        "",
        "#### 1. What the printed statement actually says",
        "",
        "The full registered source block appears below under *Full registered source block*. The clause at issue and the qualification it does not carry:",
        "",
        f"{block.get('reviewer_issue', 'missing')}",
        "",
        "#### 2. Where the paper supplies the missing semantics",
        "",
    ]
    for dependency in block.get("nonlocal_dependencies", []):
        lines.append(f"- {dependency}")
    lines += [
        "",
        "#### 3. Exact source atoms used to interpret the statement",
        "",
        "| Atom | Interpretive role | Source location | Content |",
        "|---|---|---|---|",
    ]
    for atom_id in block.get("supporting_atom_ids", []):
        atom = atom_by_id.get(atom_id)
        if atom is None:
            lines.append(f"| `{atom_id}` | **MISSING ATOM — BLOCKING DEFECT** | | |")
            continue
        support = atom.get("interpretation_support") or {}
        summary = atom["summary"].replace("|", "\\|").replace("\n", " ")
        locator = atom["source_locator"].replace("|", "\\|").replace("\n", " ")
        lines.append(
            f"| `{atom_id}` | `{support.get('role', 'unrecorded')}` | {locator} | {summary} |"
        )
    lines += [
        "",
        "The source passages that carry these atoms are reproduced verbatim here so the reading can be checked without the original paper:",
        "",
    ]
    seen_blocks: list[str] = []
    for atom_id in block.get("supporting_atom_ids", []):
        atom = atom_by_id.get(atom_id)
        if atom is None:
            continue
        parent = atom["parent_claim_id"]
        if parent in seen_blocks or parent not in claims:
            continue
        seen_blocks.append(parent)
        lines += [f"<details><summary>Source block <code>{parent}</code></summary>", ""]
        lines += [md_code_block(claims[parent], "tex"), "", "</details>", ""]
    lines += [
        "#### 4. The chronological mismatch",
        "",
        f"{block.get('awkwardness', 'missing')}",
        "",
        "#### 5. What Lean says, and exactly where the implicit semantics became explicit",
        "",
    ]
    for entry in block.get("lean_explicitation", []):
        lines += [
            f"- `{entry.get('declaration', 'missing')}`",
            f"  - {entry.get('mechanism', 'missing')}",
        ]
    lines += [
        "",
        "#### 6. The repository's accepted reading",
        "",
        f"{block.get('accepted_reading', 'missing')}",
        "",
        "#### 7. The strongest competing literal reading",
        "",
        f"{block.get('alternative_literal_reading', 'missing')}",
        "",
        "#### 8. Why this is not classified as a refutation",
        "",
        f"{block.get('why_not_refutation', 'missing')}",
        "",
        "#### 9. Semantic conclusion recorded by the repository",
        "",
        f"{block.get('semantic_conclusion', 'missing')}",
        "",
        "#### Independent interpretation checklist",
        "",
    ]
    for check in NONLOCAL_CHECKLIST:
        lines.append(f"- [ ] {check}")
    lines += [
        "",
        "#### Interpretation question put to the independent reviewer",
        "",
        "> Is the extra explicit Lean structure a faithful formalization of nonlocal semantics already imposed by the paper, or an unjustified strengthening of the printed result?",
        "",
        "- **Interpretation verdict** (choose one): `PASS paper-faithful nonlocal interpretation` / `FAIL illicit strengthening` / `UNCERTAIN source interpretation`",
        "- **Verdict:** _fill in_",
        "- **If FAIL or UNCERTAIN, which specific source passage or Lean hypothesis is the problem:** _fill in_",
        "- **Would you instead classify this printed result as false as transcribed? Why:** _fill in_",
        "",
        "---",
        "",
    ]
    return lines


def render(output: pathlib.Path, certificate_path: pathlib.Path | None = None) -> None:
    statement_map = load_json(MAP_PATH)
    census = load_json(CENSUS_PATH)
    result_inventory = load_json(RESULT_PATH)
    source_inventory_path = ROOT / result_inventory["source_fidelity_inventory"]
    source_inventory = load_json(source_inventory_path)
    atoms = source_inventory["atoms"]
    atom_by_id = {atom["id"]: atom for atom in atoms}
    map_by_id = {item["id"]: item for item in statement_map["items"]}
    census_by_id = {item["id"]: item for item in census["items"]}
    results = result_inventory["results"]
    tex_path = ROOT / statement_map["source"]["audit_tex"]
    claims = extract_claims(tex_path)
    signatures, certificate = load_signatures(certificate_path)

    all_decls = {
        decl
        for item in census["items"]
        for decl in item.get("lean_declarations", [])
    }
    locations = declaration_locations(all_decls)
    terminal = [
        r for r in results
        if r.get("verification") == "proved_in_build"
        and r.get("semantic_certification") == "accepted"
        and r.get("disposition") in {"proved_exact", "compiled_exact", "refuted_as_transcribed"}
    ]
    pending = [r for r in results if r not in terminal]
    reason_counts = collections.Counter(atom["formalization_role_reason_code"] for atom in atoms)

    lines: list[str] = [
        "# Davis--Kahan 1970 independent result audit packet",
        "",
        "## Claim boundary presented to the reviewer",
        "",
        "The repository does **not** claim that every mathematical sentence, proof equation, worked example, historical comparison, or open question in the paper is separately formalized as a Lean theorem. It claims exact formal coverage of every result that Davis and Kahan actually establish in the paper.",
        "",
        "The two accounting layers are deliberately both visible:",
        "",
        f"- **Source fidelity:** `{source_inventory_path.relative_to(ROOT)}` contains **{len(atoms)} atoms** in paper order, including all **{source_inventory['coverage_summary']['numbered_equation_atoms']} numbered equations**. Every atom has an explicit result-boundary reason code and names any counted result(s) it supports.",
        f"- **Formalization denominator:** `{RESULT_PATH.relative_to(ROOT)}` contains exactly **{len(results)} counted results**: the four Section 2 headline theorems plus every named theorem, proposition, lemma, and corollary Davis--Kahan actually establish.",
        "- Section 10 questions, explicitly deferred/unproved claims, definitions, proof-only derivations, examples, numerical working, historical/external results, and theorem-adjacent remarks remain visible in source fidelity but do not enlarge the denominator.",
        "- A false counted result remains in the denominator and requires exact formal refutation plus the repository's separate best-effort repair disposition.",
        "",
        "Each counted result carries a **source-alignment classification**, and the three values are not interchangeable:",
        "",
        "1. `locally_exact` — the printed statement is self-contained and Lean matches it directly.",
        "2. `paper_faithful_nonlocal_source_interpretation` — the result is true and Lean is faithful, but the correspondence relies on source semantics stated elsewhere in the paper (a global convention, a later standing assumption, an inherited proof context). Lean therefore says something the printed display does not literally say, and the packet discloses exactly what.",
        "3. `refuted_as_transcribed` — the printed statement is meaningful and mathematically false; an exact counterexample and a separate repair record are required.",
        "",
        "Category 2 is never a softened category 3. If a reviewer concludes that a category 2 result is actually false as printed, that is a FAIL and the repository is asking to be told.",
        "",
        f"Current result-level status: **{len(terminal)}/{len(results)} terminal**, **{len(pending)} awaiting semantic closure**.",
        f"Result-selection/boundary review: **{result_inventory['result_inventory_review'].get('boundary_review_status')}** under policy `{result_inventory['result_inventory_review'].get('policy')}`.",
        "",
        "A hostile reviewer should challenge both layers independently: (1) whether the fidelity inventory omitted source material or misclassified an exclusion, and (2) whether each of the 29 counted result statements is represented exactly in Lean.",
        "",
        "## Authoritative checked-in materials",
        "",
        f"- Distributable source specification: `{tex_path.relative_to(ROOT)}`",
        f"- Source-fidelity inventory: `{source_inventory_path.relative_to(ROOT)}`",
        f"- Formalization-result inventory: `{RESULT_PATH.relative_to(ROOT)}`",
        f"- Source census: `{CENSUS_PATH.relative_to(ROOT)}`",
        f"- Organizational statement map: `{MAP_PATH.relative_to(ROOT)}`",
    ]
    if certificate is None:
        lines += ["- Compiler certificate: **not supplied**; theorem types below are placeholders."]
    else:
        lines += [
            f"- Compiler certificate: `{certificate_path}`",
            f"- Certificate overall status: **{certificate.get('overall_status', 'unknown')}**",
            f"- Certified Git HEAD: `{certificate.get('git', {}).get('head', 'unknown')}`",
            f"- Certified source-tree SHA-256: `{certificate.get('source_tree_sha256', 'unknown')}`",
        ]
    lines += [
        "",
        "## Result-level verdict vocabulary",
        "",
        "Use one of: **PASS exact**, **PASS refuted + repair**, **FAIL boundary**, **FAIL scope**, **FAIL conclusion**, **FAIL missing clause**, **FAIL evidence**, or **UNCERTAIN**.",
        "",
        "A result whose printed statement is **not locally self-contained** carries an extra section headed **NONLOCAL SOURCE-SEMANTICS DEPENDENCY**, with its own verdict: **PASS paper-faithful nonlocal interpretation**, **FAIL illicit strengthening**, or **UNCERTAIN source interpretation**. That section discloses, before you read the Lean evidence, exactly which qualification the printed statement omits and which nonlocal source material the repository used to read it. Those results are listed here so they cannot be missed: "
        + (
            ", ".join(
                f"`{r['id']}`" for r in results if r.get("local_statement_self_contained") is False
            )
            or "*(none)*"
        )
        + ".",
        "",
    ]

    for index, result in enumerate(results, start=1):
        result_id = result["id"]
        mapped = map_by_id[result_id]
        census_row = census_by_id[result_id]
        boundary = result["boundary_review"]
        source_ids = result["source_atom_ids"]
        same_included = boundary["included_same_block_atom_ids"]
        same_excluded = boundary["excluded_same_block_atom_ids"]
        cross_scope = boundary["cross_block_scope_atom_ids"]
        source = claims[result_id]

        lines += [
            f"## {index}. {result_id} — {result['title']}",
            "",
            f"- **Counted result kind:** `{result['result_kind']}`",
            f"- **Exact source anchor:** {result['source_anchor']}",
            f"- **Result disposition:** `{result['disposition']}`",
            f"- **Compiler verification:** `{result['verification']}`",
            f"- **Hostile semantic certification:** `{result['semantic_certification']}`",
            f"- **Boundary review:** `{boundary['status']}`",
            f"- **Source alignment:** `{result.get('semantic_alignment', 'unrecorded')}`",
            f"- **Printed statement locally self-contained:** `{result.get('local_statement_self_contained', 'unrecorded')}`",
            f"- **Organizational source-block hash:** `{mapped['source_specification_sha256']}`",
            "",
        ]

        nonlocal_block = result.get("nonlocal_source_interpretation")
        if isinstance(nonlocal_block, dict):
            lines += render_nonlocal_section(nonlocal_block, atom_by_id, claims)

        lines += [
            "### Atoms inside the counted printed result",
            "",
        ]
        for atom_id in source_ids:
            atom = atom_by_id[atom_id]
            source_parent = atom["parent_claim_id"]
            cross = " *(shared/cross-block scope)*" if atom_id in cross_scope else ""
            lines.append(
                f"- `{atom_id}` — **{atom['formalization_role_reason_code']}**{cross} — {atom['summary']}"
            )
        lines += ["", "### Same-block material explicitly outside the counted result", ""]
        if same_excluded:
            for atom_id in same_excluded:
                atom = atom_by_id[atom_id]
                lines += [
                    f"- `{atom_id}` — **{atom['formalization_role_reason_code']}** — {atom['summary']}",
                    f"  - Boundary rationale: {atom['formalization_role_reason']}",
                ]
        else:
            lines.append("- *(none; the primary source block contains only atoms belonging to the counted result statement)*")
        lines += [
            "",
            f"Boundary method: {boundary['method']}",
            "",
            "### Full registered source block (for context and boundary challenge)",
            "",
            md_code_block(source, "tex"),
            "",
            "### Source-facing Lean declarations",
            "",
        ]
        declarations = result.get("lean_declarations", [])
        if not declarations:
            lines.append("**No source-facing declaration is registered. This is a blocking defect.**")
            lines.append("")
        for decl in declarations:
            locs = locations.get(decl) or []
            lines += [
                f"#### `{decl}`",
                "",
                "Source location candidates: " + (", ".join(f"`{x}`" for x in locs[:8]) if locs else "*not found by static short-name locator*"),
                "",
            ]
            sig = signatures.get(decl)
            if sig and sig.get("resolved"):
                lines += ["Compiler-printed type:", "", md_code_block(sig.get("type", ""), "lean"), ""]
            elif certificate is not None:
                lines += ["Compiler-printed type: **UNRESOLVED OR MISSING FROM CERTIFICATE**", ""]
            else:
                lines += ["Compiler-printed type: *inserted when a compiler certificate is supplied.*", ""]

        if result.get("disposition") == "refuted_as_transcribed":
            repair = result.get("repair", {})
            lines += [
                "### False-source repair disposition",
                "",
                f"- **Repair status:** `{repair.get('status', 'missing')}`",
                f"- **Repair declarations:** " + (", ".join(f"`{x}`" for x in repair.get("lean_declarations", [])) or "*(none)*"),
                f"- **Repair notes:** {repair.get('notes', 'missing')}",
                "",
            ]

        lines += ["### Independent result audit checklist", ""]
        for check in CHECKLIST:
            lines.append(f"- [ ] {check}")
        lines += [
            "",
            "### Auditor verdict",
            "",
            "- **Verdict:** _fill in_",
            "- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_",
            "- **Source/Lean mismatch:** _fill in_",
            "- **Additional Lean declaration(s) needed, if any:** _fill in_",
            "",
            "---",
            "",
        ]

    lines += [
        "# Appendix A — complete source-fidelity classification",
        "",
        "Every source atom remains visible here even when it is outside the 29-result denominator. This table is the project's explicit limitation statement: an excluded item is not hidden; it has a reason code that the reviewer may challenge.",
        "",
        "## Classification totals",
        "",
    ]
    for code, count in sorted(reason_counts.items()):
        lines.append(f"- `{code}`: **{count}**")
    lines += [
        "",
        "## All source atoms in paper order",
        "",
        "| # | Atom | Parent block | Boundary classification | Counted result support | Source-fidelity summary |",
        "|---:|---|---|---|---|---|",
    ]
    for atom in atoms:
        support = ", ".join(f"`{x}`" for x in atom.get("formalization_result_ids", [])) or "—"
        summary = atom["summary"].replace("|", "\\|").replace("\n", " ")
        lines.append(
            f"| {atom['order']} | `{atom['id']}` | `{atom['parent_claim_id']}` | "
            f"`{atom['formalization_role_reason_code']}` | {support} | {summary} |"
        )

    lines += [
        "",
        "# Final independent conclusion",
        "",
        f"- **All {len(atoms)} source-fidelity atoms reviewed for omission/classification:** yes / no",
        f"- **All {len(results)} counted DK-established results reviewed against their exact printed boundaries:** yes / no",
        f"- **{len(terminal)} currently terminal results independently reconfirmed:** yes / no",
        f"- **{len(pending)} currently nonterminal/pending results resolved by this audit:** yes / no",
        "- **Any excluded fidelity atom that actually belongs to a counted result statement:** yes / no",
        "- **Any Davis--Kahan-established named/headline result missing from the 29-result inventory:** yes / no",
        "- **Any non-established/open/deferred material incorrectly included in the denominator:** yes / no",
        "- **Every nonlocal source-semantics dependency adjudicated (paper-faithful / illicit strengthening / uncertain):** yes / no",
        "- **Any Lean statement carrying a hypothesis the printed source does not impose, that the packet did NOT disclose:** yes / no",
        "- **Compiler certificate clean and complete:** yes / no",
        "- **Is the repository's explicitly limited claim of 100% result-level Davis--Kahan 1970 formalization justified?** yes / no / uncertain",
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
