#!/usr/bin/env python3
"""Build conservative source-level Lean import-closure summaries for the paper.

This analysis deliberately uses only source imports.  It is reproducible from a
clean checkout without a compiled `.lake` environment, but an import closure is
an upper bound on declaration-level proof dependence: an imported module may be
available without being used by a particular theorem.
"""

from __future__ import annotations

import csv
import pathlib
import re
from collections import Counter, deque

HERE = pathlib.Path(__file__).resolve().parent
PAPER_DIR = HERE.parent
REPO = PAPER_DIR.parent.parent
OUT = PAPER_DIR / "generated"
SNAPSHOTS = PAPER_DIR / "snapshots"
OUT.mkdir(parents=True, exist_ok=True)
SNAPSHOTS.mkdir(parents=True, exist_ok=True)

TARGETS = [
    ("YWS citation surface", "YuWangSamworth2015.CitationSurface"),
    ("Davis--Kahan umbrella", "DavisKahan.All"),
    ("Quench umbrella", "DkpsQuench2026"),
]

IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*$")


def lean_files() -> list[pathlib.Path]:
    skip_parts = {".git", ".lake", "lake-packages", "build"}
    result: list[pathlib.Path] = []
    for path in REPO.rglob("*.lean"):
        rel = path.relative_to(REPO)
        if any(part in skip_parts for part in rel.parts):
            continue
        result.append(path)
    return sorted(result)


def module_suffix(module: str) -> pathlib.PurePosixPath:
    return pathlib.PurePosixPath(*module.split(".")).with_suffix(".lean")


def make_resolver(files: list[pathlib.Path]):
    rels = [(p, p.relative_to(REPO).as_posix()) for p in files]
    cache: dict[str, pathlib.Path | None] = {}

    def resolve(module: str) -> pathlib.Path | None:
        if module in cache:
            return cache[module]
        suffix = module_suffix(module).as_posix()
        matches = [p for p, rel in rels if rel == suffix or rel.endswith("/" + suffix)]
        if not matches:
            cache[module] = None
            return None
        # Prefer the shallowest path.  This resolves the nested YWS package root
        # while remaining deterministic if a checkout contains vendored copies.
        matches.sort(key=lambda p: (len(p.relative_to(REPO).parts), p.as_posix()))
        cache[module] = matches[0]
        return matches[0]

    return resolve


def imports_of(path: pathlib.Path) -> list[str]:
    modules: list[str] = []
    for raw in path.read_text(encoding="utf-8", errors="replace").splitlines():
        line = raw.split("--", 1)[0]
        match = IMPORT_RE.match(line)
        if not match:
            continue
        for token in match.group(1).split():
            # Module identifiers contain dots/letters/digits/underscores/apostrophes.
            token = token.strip()
            if token:
                modules.append(token)
    return modules


def family(path: pathlib.Path) -> str:
    rel = path.relative_to(REPO).as_posix()
    if rel.startswith("YuWangSamworth2015/"):
        return "YuWangSamworth2015"
    if rel.startswith("DavisKahan/") or rel == "DavisKahan.lean":
        return "DavisKahan"
    if rel.startswith("ForTauCeti/") or rel == "ForTauCeti.lean":
        return "ForTauCeti"
    if rel.startswith("DkpsQuench2026/") or rel == "DkpsQuench2026.lean":
        return "DkpsQuench2026"
    return "OtherLocal"


def closure(root_module: str, resolve) -> tuple[dict[pathlib.Path, str], list[tuple[str, str]]]:
    root = resolve(root_module)
    if root is None:
        raise SystemExit(f"cannot resolve local Lean target {root_module}")

    seen: dict[pathlib.Path, str] = {root: root_module}
    missing_localish: list[tuple[str, str]] = []
    queue: deque[pathlib.Path] = deque([root])
    while queue:
        src = queue.popleft()
        for imported in imports_of(src):
            dep = resolve(imported)
            if dep is None:
                # Usually Mathlib/Lean imports. Keep only project-looking names
                # in the report so a renamed/missing local module is visible.
                if imported.startswith(("DavisKahan", "ForTauCeti", "YuWangSamworth2015", "DkpsQuench2026")):
                    missing_localish.append((src.relative_to(REPO).as_posix(), imported))
                continue
            if dep not in seen:
                seen[dep] = imported
                queue.append(dep)
    return seen, missing_localish


def write_csv(path: pathlib.Path, rows: list[dict[str, object]], fields: list[str]) -> None:
    with path.open("w", encoding="utf-8", newline="") as file:
        writer = csv.DictWriter(file, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def latex_escape(text: str) -> str:
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
    }
    return "".join(replacements.get(ch, ch) for ch in text)


def main() -> None:
    files = lean_files()
    resolve = make_resolver(files)

    closure_rows: list[dict[str, object]] = []
    summary_rows: list[dict[str, object]] = []
    closures: dict[str, set[pathlib.Path]] = {}
    unresolved: list[dict[str, str]] = []

    for label, module in TARGETS:
        reached, missing = closure(module, resolve)
        paths = set(reached)
        closures[label] = paths
        counts = Counter(family(path) for path in paths)
        summary_rows.append(
            {
                "target": label,
                "root_module": module,
                "local_modules": len(paths),
                "YuWangSamworth2015": counts["YuWangSamworth2015"],
                "DavisKahan": counts["DavisKahan"],
                "ForTauCeti": counts["ForTauCeti"],
                "DkpsQuench2026": counts["DkpsQuench2026"],
                "OtherLocal": counts["OtherLocal"],
            }
        )
        for path, imported_as in sorted(reached.items(), key=lambda kv: kv[0].as_posix()):
            closure_rows.append(
                {
                    "target": label,
                    "root_module": module,
                    "family": family(path),
                    "imported_as": imported_as,
                    "path": path.relative_to(REPO).as_posix(),
                }
            )
        for source, missing_module in missing:
            unresolved.append({"target": label, "source": source, "module": missing_module})

    write_csv(
        OUT / "dependency_import_closure.csv",
        closure_rows,
        ["target", "root_module", "family", "imported_as", "path"],
    )
    write_csv(
        OUT / "dependency_target_summary.csv",
        summary_rows,
        ["target", "root_module", "local_modules", "YuWangSamworth2015", "DavisKahan", "ForTauCeti", "DkpsQuench2026", "OtherLocal"],
    )
    write_csv(OUT / "dependency_unresolved_project_imports.csv", unresolved, ["target", "source", "module"])

    dk = closures["Davis--Kahan umbrella"]
    yws = closures["YWS citation surface"]
    quench = closures["Quench umbrella"]
    overlap_rows = [
        {"pair": "YWS ∩ Davis--Kahan", "modules": len(yws & dk)},
        {"pair": "YWS ∩ Quench", "modules": len(yws & quench)},
        {"pair": "Davis--Kahan ∩ Quench", "modules": len(dk & quench)},
    ]
    write_csv(OUT / "dependency_target_overlap.csv", overlap_rows, ["pair", "modules"])

    # Compact LaTeX table consumed by the literature memo.
    with (SNAPSHOTS / "dependency_target_table.tex").open("w", encoding="utf-8") as file:
        file.write("% Generated by scripts/build_dependency_analysis.py; do not edit.\n")
        file.write("\\begin{table}[tb]\n\\centering\n")
        file.write("\\caption{Conservative source-level local import closures for three project surfaces. The closure includes the root module and is an upper bound on declaration-level proof dependence.}\\label{tab:import-closures}\n")
        file.write("\\small\n\\begin{tabular}{lrrrrrr}\n\\toprule\n")
        file.write("Surface & Total & YWS & DK & TauCeti & Quench & Other \\\\\n\\midrule\n")
        for row in summary_rows:
            file.write(
                f"{latex_escape(str(row['target']))} & {row['local_modules']} & "
                f"{row['YuWangSamworth2015']} & {row['DavisKahan']} & "
                f"{row['ForTauCeti']} & {row['DkpsQuench2026']} & {row['OtherLocal']} \\\\\n"
            )
        file.write("\\bottomrule\n\\end{tabular}\n\\end{table}\n")

    with (SNAPSHOTS / "dependency_macros.tex").open("w", encoding="utf-8") as file:
        file.write("% Generated by scripts/build_dependency_analysis.py; do not edit.\n")
        values = {row["target"]: row for row in summary_rows}
        file.write(f"\\newcommand{{\\YWSImportClosure}}{{{values['YWS citation surface']['local_modules']}}}\n")
        file.write(f"\\newcommand{{\\YWSDKImports}}{{{values['YWS citation surface']['DavisKahan']}}}\n")
        file.write(f"\\newcommand{{\\YWSTauCetiImports}}{{{values['YWS citation surface']['ForTauCeti']}}}\n")
        file.write(f"\\newcommand{{\\DKUmbrellaImportClosure}}{{{values['Davis--Kahan umbrella']['local_modules']}}}\n")
        file.write(f"\\newcommand{{\\QuenchImportClosure}}{{{values['Quench umbrella']['local_modules']}}}\n")
        file.write(f"\\newcommand{{\\YWSDKOverlap}}{{{len(yws & dk)}}}\n")
        file.write(f"\\newcommand{{\\YWSQuenchOverlap}}{{{len(yws & quench)}}}\n")

    report = [
        "# Source-level dependency report",
        "",
        "This report is generated from Lean `import` statements only. It is deliberately conservative: importing a module makes its declarations available, but does not prove that any particular theorem depends on them. Declaration-level dependency extraction from a compiled Lean environment would be a stricter follow-up analysis.",
        "",
        "## Target closures",
        "",
    ]
    for row in summary_rows:
        report.append(
            f"- **{row['target']}**: {row['local_modules']} local modules "
            f"({row['YuWangSamworth2015']} YWS, {row['DavisKahan']} DavisKahan, "
            f"{row['ForTauCeti']} ForTauCeti, {row['DkpsQuench2026']} Quench, "
            f"{row['OtherLocal']} other local)."
        )
    report += [
        "",
        "## Framing implication",
        "",
        f"The YWS citation surface imports a meaningful slice of the foundations developed in the broader Davis--Kahan effort ({len(yws & dk)} modules overlap with the Davis--Kahan umbrella closure), but it does not import the full {len(dk)}-module Davis--Kahan umbrella. The source graph therefore supports a paper framed around the broader Davis--Kahan/YWS perturbation lineage more strongly than a claim that all of the deep Davis--Kahan infrastructure was required merely to obtain YWS.",
        "",
        "The Quench umbrella has little source-import overlap with the Davis--Kahan and YWS surfaces in this conservative graph. Its role should therefore be described by the specific formal theorems/interfaces it consumes, rather than by assuming umbrella-level dependency.",
        "",
        "## Unresolved project-looking imports",
        "",
        f"Count: {len(unresolved)}. These should be zero for the named project prefixes in the analyzed checkout.",
        "",
    ]
    (OUT / "DEPENDENCY_REPORT.md").write_text("\n".join(report), encoding="utf-8")

    print(f"wrote dependency analysis for {len(TARGETS)} targets")
    for row in summary_rows:
        print(f"  {row['target']}: {row['local_modules']} local modules")
    if unresolved:
        print(f"WARNING: {len(unresolved)} unresolved project-looking imports")


if __name__ == "__main__":
    main()
