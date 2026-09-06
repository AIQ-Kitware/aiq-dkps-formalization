#!/usr/bin/env python3
"""Build reproducible appendix evidence for the workshop paper.

The script has no network dependency. It turns the checked-in review timeline
into a TikZ figure and hashes the exact files used by the manuscript. The JSON
manifest is intended to be the machine-readable artifact; TeX outputs are only
rendered views.
"""
from __future__ import annotations

import csv
import hashlib
import json
import pathlib
import subprocess
from dataclasses import dataclass


PAPER = pathlib.Path(__file__).resolve().parents[1]


def git(*args: str, cwd: pathlib.Path | None = None) -> str | None:
    try:
        return subprocess.check_output(
            ["git", *args], cwd=cwd or PAPER, text=True, stderr=subprocess.DEVNULL
        ).strip()
    except Exception:
        return None


def repo_root() -> pathlib.Path:
    value = git("rev-parse", "--show-toplevel")
    if value:
        return pathlib.Path(value)
    # This fallback is useful when inspecting an unpacked overlay before applying it.
    candidate = PAPER.parents[1]
    return candidate


def sha256(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as file:
        for chunk in iter(lambda: file.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def tex_escape(text: str) -> str:
    table = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(table.get(ch, ch) for ch in text)


@dataclass(frozen=True)
class TimelineRow:
    date_utc: str
    commit: str
    kind: str
    summary: str
    source_url: str


def load_timeline() -> list[TimelineRow]:
    path = PAPER / "data/review_timeline.csv"
    with path.open(newline="", encoding="utf8") as file:
        rows = [TimelineRow(**row) for row in csv.DictReader(file)]
    if not rows:
        raise RuntimeError("review timeline is empty")
    previous = ""
    for row in rows:
        if len(row.commit) != 40 or any(c not in "0123456789abcdef" for c in row.commit):
            raise RuntimeError(f"invalid commit SHA: {row.commit!r}")
        if row.date_utc < previous:
            raise RuntimeError("review timeline must be sorted by date")
        previous = row.date_utc
        expected = f"https://github.com/AIQ-Kitware/aiq-dkps-formalization/commit/{row.commit}"
        if row.source_url != expected:
            raise RuntimeError(f"timeline URL does not match commit SHA: {row.source_url}")
    return rows


def write_timeline(rows: list[TimelineRow], generated: pathlib.Path) -> None:
    # The figure is deliberately generated from CSV so dates/hashes cannot drift
    # independently from the structured appendix data.
    pieces = [
        r"\begin{tikzpicture}[x=2.15cm,y=1cm,>=Stealth,",
        r"  dot/.style={circle,fill=black,inner sep=1.7pt},",
        r"  event/.style={align=center,text width=2.30cm,font=\scriptsize}]",
        rf"\draw[-{{Stealth}},line width=0.5pt] (0,0) -- ({len(rows)-1 + 0.28},0);",
    ]
    for idx, row in enumerate(rows):
        above = idx % 2 == 0
        y = 0.55 if above else -0.55
        anchor = "south" if above else "north"
        short = row.commit[:8]
        kind = tex_escape(row.kind)
        date = tex_escape(row.date_utc[5:])
        pieces.append(rf"\node[dot] at ({idx},0) {{}};")
        pieces.append(
            rf"\node[event,anchor={anchor}] at ({idx},{y}) "
            rf"{{\textbf{{{date}}}\\{kind}\\\texttt{{{short}}}}};"
        )
    pieces.append(r"\end{tikzpicture}")
    (generated / "review_timeline_tikz.tex").write_text("\n".join(pieces) + "\n")


def material_paths(root: pathlib.Path) -> list[pathlib.Path]:
    relative_to_paper = [
        "paper.tex",
        "appendix.tex",
        "related_work_condensed.tex",
        "references.bib",
        "data/review_timeline.csv",
        "figures/formalization_workflow.png",
        "figures/semantic-alignment-dashboard.png",
    ]
    paths = [PAPER / rel for rel in relative_to_paper]
    relative_to_root = [
        "prose/distilled_literature/DavisKahan1970_part_III.tex",
        "dev/davis-kahan-1970-full-source-census.json",
        "dev/davis-kahan-1970-formalization-result-inventory.json",
        "DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean",
        "submodules/aiq-lean-formalization-tools/src/aiq_lean_tools/assets/alignment_viewer.html",
    ]
    paths.extend(root / rel for rel in relative_to_root)
    return paths


def display_path(path: pathlib.Path, root: pathlib.Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return path.as_posix()


def write_manifest(root: pathlib.Path, generated: pathlib.Path) -> None:
    materials = []
    missing = []
    for path in material_paths(root):
        if not path.is_file():
            missing.append(display_path(path, root))
            continue
        materials.append({
            "path": display_path(path, root),
            "sha256": sha256(path),
            "bytes": path.stat().st_size,
        })
    if missing:
        raise RuntimeError("manifest inputs missing: " + ", ".join(missing))
    materials.sort(key=lambda item: item["path"])
    canonical = json.dumps(materials, sort_keys=True, separators=(",", ":")).encode()
    digest = hashlib.sha256(canonical).hexdigest()

    root_head = git("rev-parse", "HEAD", cwd=root)
    tool_root = root / "submodules/aiq-lean-formalization-tools"
    tool_head = git("rev-parse", "HEAD", cwd=tool_root) if tool_root.is_dir() else None
    payload = {
        "schema_version": 1,
        "hash_algorithm": "sha256",
        "material_set_sha256": digest,
        "repository_head": root_head,
        "formalization_tools_head": tool_head,
        "materials": materials,
    }
    (generated / "materials_manifest.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf8"
    )
    (generated / "materials_manifest_macros.tex").write_text(
        "% Generated by scripts/build_appendix_evidence.py; do not edit.\n"
        f"\\newcommand{{\\MaterialSetSHA}}{{{digest}}}\n",
        encoding="utf8",
    )

    shown = materials
    lines = [
        r"\begin{table}[H]",
        r"\centering",
        r"\scriptsize",
        r"\caption{Material hashes used by this paper.  The JSON manifest stores the full digests.}",
        r"\label{tab:material-hashes}",
        r"\begin{tabularx}{\linewidth}{@{}Ylr@{}}",
        r"\toprule",
        r"Path & SHA-256 prefix & bytes \\",
        r"\midrule",
    ]
    for item in shown:
        path = item["path"]
        lines.append(
            f"\\path{{{path}}} & \\texttt{{{item['sha256'][:16]}}} & "
            f"{item['bytes']:,} \\\\"
        )
    lines.extend([r"\bottomrule", r"\end{tabularx}", r"\end{table}"])
    text = "\n".join(lines) + "\n"
    (generated / "materials_manifest_table.tex").write_text(text, encoding="utf8")


def main() -> None:
    generated = PAPER / "generated"
    generated.mkdir(parents=True, exist_ok=True)
    rows = load_timeline()
    write_timeline(rows, generated)
    root = repo_root()
    write_manifest(root, generated)
    print(f"timeline rows: {len(rows)}")
    print(f"wrote: {generated / 'review_timeline_tikz.tex'}")
    print(f"wrote: {generated / 'materials_manifest.json'}")


if __name__ == "__main__":
    main()
