#!/usr/bin/env python3
"""Reconstruct accepted->nonaccepted semantic-review transitions from Git.

The workshop paper uses this as retrospective evidence.  A transition is counted
when a result's ``semantic_certification`` field is ``accepted`` at one revision
of the maintained result register and has any other value at the next revision
of that file.  This is a maintenance-history count, not an estimate of an LLM
error rate.
"""
from __future__ import annotations
import argparse
import csv
import json
import subprocess
from pathlib import Path

DEFAULT_SNAPSHOT = "5f339b74adf7e03cdd0a1f980ee63d7b78c360e7"
REGISTER = "dev/davis-kahan-1970-formalization-result-inventory.json"


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True)


def load_at(root: Path, sha: str) -> dict:
    return json.loads(git(root, "show", f"{sha}:{REGISTER}"))


def row_list(doc: dict) -> list[dict]:
    for key in ("results", "items", "rows"):
        value = doc.get(key)
        if isinstance(value, list):
            return value
    return []


def reconstruct(root: Path, snapshot: str) -> list[dict]:
    revs = git(root, "rev-list", "--reverse", snapshot, "--", REGISTER).splitlines()
    previous: dict[str, tuple[str | None, str | None, str | None]] = {}
    events: list[dict] = []
    for sha in revs:
        try:
            doc = load_at(root, sha)
        except Exception:
            continue
        current = {
            row["id"]: (
                row.get("semantic_certification"),
                row.get("disposition"),
                row.get("verification"),
            )
            for row in row_list(doc)
            if row.get("id")
        }
        for rid, state in current.items():
            old = previous.get(rid)
            if old and old[0] == "accepted" and state[0] != "accepted":
                meta = git(root, "show", "-s", "--format=%cs%x09%s", sha).rstrip().split("\t", 1)
                events.append({
                    "commit": sha,
                    "date": meta[0],
                    "subject": meta[1] if len(meta) > 1 else "",
                    "result": rid,
                    "from_semantic": old[0],
                    "to_semantic": state[0] or "",
                    "disposition": state[1] or "",
                    "verification": state[2] or "",
                })
        previous = current
    return events


def tex_escape(text: str) -> str:
    rep = {
        "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$",
        "#": r"\#", "_": r"\_", "{": r"\{", "}": r"\}",
        "~": r"\textasciitilde{}", "^": r"\textasciicircum{}",
    }
    return "".join(rep.get(ch, ch) for ch in text)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, default=None)
    parser.add_argument("--snapshot", default=DEFAULT_SNAPSHOT)
    parser.add_argument("--outdir", type=Path, default=Path(__file__).resolve().parents[1] / "generated")
    args = parser.parse_args()

    root = args.repo
    if root is None:
        root = Path(git(Path(__file__).resolve().parent, "rev-parse", "--show-toplevel").strip())
    snapshot = git(root, "rev-parse", args.snapshot).strip()
    events = reconstruct(root, snapshot)
    unique = sorted({e["result"] for e in events})

    outdir = args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    csv_path = outdir / "semantic_reversals.csv"
    with csv_path.open("w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=list(events[0]) if events else ["commit"])
        writer.writeheader()
        writer.writerows(events)

    macros = outdir / "semantic_reversal_macros.tex"
    macros.write_text(
        "\\newcommand{\\SemanticReversalCount}{%d}\n"
        "\\newcommand{\\SemanticReversalResultCount}{%d}\n"
        "\\newcommand{\\SemanticSnapshotShort}{%s}\n"
        % (len(events), len(unique), snapshot[:8])
    )

    rows = outdir / "semantic_reversal_rows.tex"
    lines = []
    for e in events:
        lines.append(
            f"{tex_escape(e['date'])} & {tex_escape(e['result'])} & "
            f"{tex_escape(e['to_semantic'])} & {tex_escape(e['commit'][:8])} \\\\"
        )
    rows.write_text("\n".join(lines) + ("\n" if lines else ""))

    print(f"snapshot={snapshot}")
    print(f"accepted_to_nonaccepted_transitions={len(events)}")
    print(f"distinct_results_reopened={len(unique)}")
    print(csv_path)


if __name__ == "__main__":
    main()
