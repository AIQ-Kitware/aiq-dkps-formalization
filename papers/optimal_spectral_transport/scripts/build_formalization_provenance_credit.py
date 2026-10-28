#!/usr/bin/env python3
"""Join formal-provenance citations to the whole-formalization declaration inventory.

Policy is intentionally asymmetric: only positive external formal-provenance claims
are checked in.  Every project-local declaration not named by such a claim defaults
to project formalization.  Ordinary Mathlib/Lean dependencies live outside this
project-local inventory and are therefore not counted as project formalizations.

This script never infers provenance from code similarity or filenames.  Each positive
claim must name an exact local declaration and an evidence range in repository source.
"""
from __future__ import annotations

import csv
import hashlib
import json
import pathlib
from collections import defaultdict
from typing import Any

HERE = pathlib.Path(__file__).resolve().parent
PAPER = HERE.parent
REPO = PAPER.parent.parent
DATA = PAPER / "data"
GENERATED = PAPER / "generated"
SNAPSHOTS = PAPER / "snapshots"

POLICY = DATA / "formalization_formal_provenance_policy_20260817.json"
CLAIMS = DATA / "formalization_formal_provenance_claims_20260817.csv"
NODES = DATA / "formalization_dependency_nodes_20260817.csv"
REACH = DATA / "formalization_result_reachability_20260817.csv"
THEORY_LINKS = DATA / "formalization_theory_evidence_links_20260817.csv"
TAXONOMY = DATA / "formalization_theory_taxonomy_20260817.json"


def read_csv(path: pathlib.Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: pathlib.Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields, extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)


def sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def tex_escape(s: str) -> str:
    return (s.replace("\\", r"\textbackslash{}")
             .replace("&", r"\&")
             .replace("%", r"\%")
             .replace("_", r"\_")
             .replace("#", r"\#"))


def validate_evidence(row: dict[str, str], source_label: str) -> None:
    path = REPO / row["evidence_path"]
    if not path.exists():
        raise SystemExit(f"provenance evidence path does not exist: {row['evidence_path']}")
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    a, b = int(row["evidence_start_line"]), int(row["evidence_end_line"])
    if not (1 <= a <= b <= len(lines)):
        raise SystemExit(f"invalid evidence range {path}:{a}-{b}")
    excerpt = "\n".join(lines[a - 1:b]).lower()
    tokens = [source_label.lower(), row["source_id"].lower()]
    if not any(t in excerpt for t in tokens):
        raise SystemExit(
            f"evidence range does not mention formal source {row['source_id']}: "
            f"{row['evidence_path']}:{a}-{b}"
        )


def main() -> None:
    GENERATED.mkdir(parents=True, exist_ok=True)
    SNAPSHOTS.mkdir(parents=True, exist_ok=True)
    policy = json.loads(POLICY.read_text(encoding="utf-8"))
    taxonomy = json.loads(TAXONOMY.read_text(encoding="utf-8"))
    categories = policy["primary_categories"]
    priority = {name: i for i, name in enumerate(reversed(policy["priority"]))}
    sources = policy["external_sources"]

    nodes = read_csv(NODES)
    node_by_name = {r["declaration"]: r for r in nodes}
    if len(node_by_name) != len(nodes):
        raise SystemExit("duplicate declaration rows in formalization dependency node snapshot")

    # Theory assignment is already auditable; collapse repeated source-unit links to one theory/declaration.
    theory_by_decl: dict[str, str] = {}
    for row in read_csv(THEORY_LINKS):
        d, t = row["declaration"], row["theory_id"]
        old = theory_by_decl.setdefault(d, t)
        if old != t:
            raise SystemExit(f"declaration has inconsistent theory classification: {d}: {old} vs {t}")
    theory_label = {x["id"]: x["label"] for x in taxonomy["theories"]}

    claims = read_csv(CLAIMS)
    claims_by_decl: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in claims:
        d = row["declaration"]
        if d not in node_by_name:
            raise SystemExit(f"positive provenance claim names declaration outside checked-in trace: {d}")
        if row["primary_category"] not in categories or row["primary_category"] == "project_native":
            raise SystemExit(f"invalid positive provenance category for {d}: {row['primary_category']}")
        if row["source_id"] not in sources:
            raise SystemExit(f"unknown formal source id for {d}: {row['source_id']}")
        validate_evidence(row, sources[row["source_id"]]["label"])
        claims_by_decl[d].append(row)

    # Produce exactly one primary provenance category per local declaration.  If future declarations
    # acquire multiple positive citations, keep every citation but choose the most donor-intensive
    # category for the compact accounting table.
    linked: list[dict[str, Any]] = []
    for node in sorted(nodes, key=lambda r: r["declaration"]):
        d = node["declaration"]
        dclaims = claims_by_decl.get(d, [])
        if dclaims:
            primary = max((r["primary_category"] for r in dclaims), key=lambda c: priority[c])
            source_ids = ";".join(sorted({r["source_id"] for r in dclaims}))
            relations = ";".join(sorted({r["relation"] for r in dclaims}))
            evidence = ";".join(
                sorted({f"{r['evidence_path']}:{r['evidence_start_line']}-{r['evidence_end_line']}" for r in dclaims})
            )
        else:
            primary = "project_native"
            source_ids = ""
            relations = ""
            evidence = ""
        linked.append({
            **node,
            "theory_id": theory_by_decl.get(d, "unclassified"),
            "primary_provenance": primary,
            "formal_source_ids": source_ids,
            "relations": relations,
            "evidence": evidence,
        })
    if any(r["theory_id"] == "unclassified" for r in linked):
        missing = [r["declaration"] for r in linked if r["theory_id"] == "unclassified"]
        raise SystemExit("provenance join found declarations without theory classification:\n  " + "\n  ".join(missing[:50]))

    write_csv(
        GENERATED / "formalization_declaration_formal_provenance.csv",
        linked,
        ["declaration", "module", "kind", "is_any_root", "theory_id", "primary_provenance",
         "formal_source_ids", "relations", "evidence"],
    )

    # Result/source-unit incidence: which published/census units transitively reach declarations
    # with an explicit positive formal-provenance claim?
    reach = read_csv(REACH)
    reached_by_source: dict[tuple[str, str], set[str]] = defaultdict(set)
    for r in reach:
        reached_by_source[(r["corpus"], r["source_id"])].add(r["declaration"])

    incidence: list[dict[str, Any]] = []
    for (corpus, source_id), ds in sorted(reached_by_source.items()):
        cats = defaultdict(int)
        source_ids: set[str] = set()
        for d in ds:
            lr = next((x for x in linked if x["declaration"] == d), None)
            if lr is None:
                continue
            cats[lr["primary_provenance"]] += 1
            source_ids.update(x for x in lr["formal_source_ids"].split(";") if x)
        incidence.append({
            "corpus": corpus,
            "source_id": source_id,
            "reached_project_declarations": sum(cats.values()),
            "project_native": cats["project_native"],
            "project_with_formal_reference": cats["project_with_formal_reference"],
            "adapted_or_ported": cats["adapted_or_ported"],
            "copied_or_rehomed": cats["copied_or_rehomed"],
            "formal_source_ids": ";".join(sorted(source_ids)),
        })
    write_csv(
        GENERATED / "formalization_source_unit_formal_provenance.csv",
        incidence,
        ["corpus", "source_id", "reached_project_declarations", "project_native",
         "project_with_formal_reference", "adapted_or_ported", "copied_or_rehomed", "formal_source_ids"],
    )

    # Aggregate by theory, preserving the basic theory names the paper already uses.
    theory_rows: list[dict[str, Any]] = []
    for tid in sorted({r["theory_id"] for r in linked}):
        rs = [r for r in linked if r["theory_id"] == tid]
        counts = {c: sum(r["primary_provenance"] == c for r in rs) for c in categories}
        theory_rows.append({
            "theory_id": tid,
            "theory_label": theory_label.get(tid, tid),
            "reached_declarations": len(rs),
            **counts,
            "formal_source_ids": ";".join(sorted({s for r in rs for s in r["formal_source_ids"].split(";") if s})),
        })
    write_csv(
        GENERATED / "formalization_theory_formal_provenance.csv",
        theory_rows,
        ["theory_id", "theory_label", "reached_declarations", "project_native",
         "project_with_formal_reference", "adapted_or_ported", "copied_or_rehomed", "formal_source_ids"],
    )

    totals = {c: sum(r["primary_provenance"] == c for r in linked) for c in categories}
    any_positive = len(linked) - totals["project_native"]
    donor_origin = totals["adapted_or_ported"] + totals["copied_or_rehomed"]
    referenced_local = totals["project_with_formal_reference"]
    yws_units_with_donor = sum(
        int(bool(r["adapted_or_ported"] or r["copied_or_rehomed"]))
        for r in incidence if r["corpus"] == "YWS2015"
    )
    dk_units_with_donor = sum(
        int(bool(r["adapted_or_ported"] or r["copied_or_rehomed"]))
        for r in incidence if r["corpus"] == "DK1970"
    )

    macros = [
        "% Generated by scripts/build_formalization_provenance_credit.py; do not edit by hand.",
        f"\\newcommand{{\\FormalizationProjectNativeDeclarationCount}}{{{totals['project_native']}}}",
        f"\\newcommand{{\\FormalizationProjectReferencedDeclarationCount}}{{{referenced_local}}}",
        f"\\newcommand{{\\FormalizationAdaptedDeclarationCount}}{{{totals['adapted_or_ported']}}}",
        f"\\newcommand{{\\FormalizationCopiedDeclarationCount}}{{{totals['copied_or_rehomed']}}}",
        f"\\newcommand{{\\FormalizationPositiveFormalCitationDeclarationCount}}{{{any_positive}}}",
        f"\\newcommand{{\\FormalizationExternalOriginDeclarationCount}}{{{donor_origin}}}",
        f"\\newcommand{{\\FormalizationYWSDonorAffectedUnitCount}}{{{yws_units_with_donor}}}",
        f"\\newcommand{{\\FormalizationDKDonorAffectedUnitCount}}{{{dk_units_with_donor}}}",
    ]
    (SNAPSHOTS / "formalization_provenance_macros.tex").write_text("\n".join(macros) + "\n", encoding="utf-8")

    labels = {
        "project_native": "Project formalization; no external formal donor citation",
        "project_with_formal_reference": "Project formalization with explicit formal reference/ancestry",
        "adapted_or_ported": "Adapted or ported from an external formal source",
        "copied_or_rehomed": "Copied or essentially verbatim, then re-homed",
    }
    order = ["project_native", "project_with_formal_reference", "adapted_or_ported", "copied_or_rehomed"]
    lines = [
        "% Generated by scripts/build_formalization_provenance_credit.py; do not edit by hand.",
        r"\begin{tabularx}{\textwidth}{@{}X r@{}}",
        r"\toprule",
        r"Formalization provenance & Reached declarations \\",
        r"\midrule",
    ]
    for c in order:
        lines.append(f"{tex_escape(labels[c])} & {totals[c]} \\\\")
    lines += [r"\bottomrule", r"\end{tabularx}"]
    (SNAPSHOTS / "formalization_provenance_credit_table.tex").write_text("\n".join(lines) + "\n", encoding="utf-8")

    manifest = {
        "schema": "formalization-draft2/formal-provenance-generated/v1",
        "policy_sha256": sha256(POLICY),
        "claims_sha256": sha256(CLAIMS),
        "nodes_sha256": sha256(NODES),
        "reachability_sha256": sha256(REACH),
        "theory_links_sha256": sha256(THEORY_LINKS),
        "declaration_count": len(linked),
        "positive_claim_count": len(claims),
        "primary_category_counts": totals,
        "yws_units_with_external_origin_dependency": yws_units_with_donor,
        "dk_results_with_external_origin_dependency": dk_units_with_donor,
        "interpretation": "Counts apply to the checked-in project-local declaration inventory. Positive formal citations are exact named overrides; absence defaults to project formalization. Ordinary upstream library declarations are outside the denominator."
    }
    (GENERATED / "formalization_formal_provenance_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )

    print(
        "formal provenance:", len(linked), "local declarations;",
        totals["project_native"], "project-native;",
        totals["project_with_formal_reference"], "project-with-reference;",
        totals["adapted_or_ported"], "adapted/ported;",
        totals["copied_or_rehomed"], "copied/re-homed",
    )


if __name__ == "__main__":
    main()
