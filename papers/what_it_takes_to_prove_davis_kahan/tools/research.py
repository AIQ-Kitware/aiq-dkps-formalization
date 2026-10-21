#!/usr/bin/env python3
"""Reproducible evidence packet for the Davis--Kahan mathematical-history study.

Paper-specific orchestration, not a new Lean parser or dependency engine.
The elaborated graph, statement closures, and source alignment come from
installed leanq / aiq-lean. Historical and mathematical judgments remain curated.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import pathlib
import re
import shlex
import shutil
import subprocess
import sys
from datetime import datetime, timezone

HERE = pathlib.Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
DATA = HERE / "data"
INVENTORY = ROOT / "dev/davis-kahan-1970-formalization-result-inventory.json"
CENSUS = ROOT / "dev/davis-kahan-1970-full-source-census.json"


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path):
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def git(*args):
    try:
        return subprocess.check_output(["git", *args], cwd=ROOT, stderr=subprocess.DEVNULL, text=True).strip()
    except (FileNotFoundError, subprocess.CalledProcessError):
        return None


def cases():
    return {r["id"]: r for r in load_json(DATA / "cases.json")["cases"]}


def selected_case(name):
    case = cases().get(name)
    if case is None:
        raise ValueError(f"unknown case {name!r}; choose one of: {', '.join(cases())}")
    matches = [r for r in load_json(INVENTORY)["results"] if r["id"] == case["source_id"]]
    source_rows = [r for r in load_json(CENSUS)["items"] if r["id"] == case["source_id"]]
    if len(matches) != 1 or len(source_rows) != 1:
        raise ValueError(f"source ID {case['source_id']} no longer uniquely resolves in BOTH maintained ledgers")
    canonical = case["roots"][0]["name"]
    if canonical not in matches[0]["lean_declarations"]:
        raise ValueError(f"{canonical} is no longer a declared result witness for {case['source_id']}; review cases.json")
    return case, matches[0], source_rows[0]


def rel(path):
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return str(path)


def output_dir(case, override):
    path = pathlib.Path(override) if override else ROOT / "build/what-it-takes-dk" / case["id"]
    return path if path.is_absolute() else ROOT / path


def write_axiom_audit(case, out):
    """One generated Lean importer checks every selected root, including opt-in modules."""
    dest = out / "source_axiom_audit.lean"
    dest.parent.mkdir(parents=True, exist_ok=True)
    lines = ["-- Generated from research cases.json; not a maintained Lean module."]
    lines.extend("import " + target for target in case["build_targets"])
    lines.append("")
    for root in case["roots"]:
        lines.extend(["#check " + root["name"], "#print axioms " + root["name"]])
    dest.write_text("\n".join(lines) + "\n", encoding="utf-8")
    return dest


def commands(case, out, reuse_index=False):
    graph = out / "semantic-index.json"
    steps = [
        ("cache", ["lake", "exe", "cache", "get"], None),
        ("build", ["lake", "build", *case["build_targets"]], None),
        ("axiom-audit", ["lake", "env", "lean", rel(out / "source_axiom_audit.lean")],
         out / "source_axiom_audit.txt"),
        ("census", ["python3", "scripts/check_davis_kahan_1970_source_census.py"], None),
    ]
    if not reuse_index:
        args = ["leanq", "graph-index"]
        for target in case["graph_targets"]:
            args.extend(["--target", target])
        steps.append(("graph-index", [*args, "--out", rel(graph)], None))
    for entry in case["roots"]:
        name = entry["name"]
        rid = entry["id"]
        slice_path = out / "slices" / f"{rid}.json"
        steps.extend([
            (f"slice-{rid}", ["leanq", "graph-slice", rel(graph), name,
                               "--transitive-reduction", "--out", rel(slice_path)], None),
            (f"statement-{rid}", ["leanq", "--lib", "DavisKahan", "statement", name,
                                   "--out", rel(out / "statements" / f"{rid}.json")], None),
        ])
    steps.append(("alignment", ["aiq-lean", "alignment", "html", rel(CENSUS),
                                "--row", case["source_id"], "--statements",
                                "--graph", rel(graph), "-o", rel(out / "source-alignment.html")], None))
    return steps


def shell_command(argv, redirect=None):
    return shlex.join(argv) + (" > " + shlex.quote(rel(redirect)) if redirect else "")


def snapshot(case, out, paper_pdf=None):
    inputs = [INVENTORY, CENSUS, ROOT / "lean-toolchain", ROOT / "lake-manifest.json",
              DATA / "cases.json", DATA / "research_questions.json",
              DATA / "history_claims.csv", DATA / "route_comparisons.csv"]
    for target in case["build_targets"]:
        inputs.append(ROOT / (target.replace(".", "/") + ".lean"))
    metadata = {
        "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
        "case": case["id"],
        "source_id": case["source_id"],
        "root_declarations": [r["name"] for r in case["roots"]],
        "git_head": git("rev-parse", "HEAD"),
        "git_dirty": git("status", "--porcelain") if git("rev-parse", "HEAD") else None,
        "input_sha256": {rel(p): sha(p) if p.is_file() else None for p in inputs},
        "scope_warning": "Only explicitly listed inputs are hashed. This is not a proof of graph freshness or of mathematical necessity.",
    }
    if paper_pdf is not None:
        p = pathlib.Path(paper_pdf).expanduser().resolve()
        if not p.is_file():
            raise ValueError(f"original paper PDF not found: {p}")
        metadata["original_source_pdf"] = {"path": str(p), "sha256": sha(p)}
    graph = out / "semantic-index.json"
    if graph.is_file():
        metadata["semantic_index_sha256"] = sha(graph)
    out.mkdir(parents=True, exist_ok=True)
    (out / "snapshot.json").write_text(json.dumps(metadata, indent=2) + "\n", encoding="utf-8")
    return metadata


def execute(steps, out):
    required = {row[1][0] for row in steps}
    missing = sorted(command for command in required if shutil.which(command) is None)
    if missing:
        raise ValueError("required commands unavailable: " + ", ".join(missing)
                         + "; install the project's aiq-lean/leanq tools and Lean before collecting")
    logdir = out / "logs"
    logdir.mkdir(parents=True, exist_ok=True)
    record = []
    for label, argv, redirect in steps:
        if redirect is not None:
            redirect.parent.mkdir(parents=True, exist_ok=True)
        dest = redirect or (logdir / f"{label}.log")
        dest.parent.mkdir(parents=True, exist_ok=True)
        print("+", shell_command(argv, redirect), flush=True)
        # Preserve the complete stdout/stderr of each command without filtering warnings.
        with dest.open("w", encoding="utf-8") as stream:
            proc = subprocess.Popen(argv, cwd=ROOT, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, text=True, errors="replace")
            assert proc.stdout is not None
            for line in proc.stdout:
                stream.write(line)
                print(line, end="", flush=True)
            proc.wait()
        record.append({"stage": label, "command": argv, "exit_code": proc.returncode,
                       "output": rel(dest)})
        (out / "executed_commands.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        if proc.returncode:
            tail = dest.read_text(encoding="utf-8", errors="replace").splitlines()[-45:]
            raise ValueError(f"{label} failed (exit {proc.returncode}); log: {dest}\n" + "\n".join(tail))
        print(f"  completed {label}: {rel(dest)}", flush=True)
    return record


def read_csv(name):
    with (DATA / name).open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream))


def md(s):
    return str(s or "").replace("|", "\\|").replace("\n", " ")


def slice_ids(path):
    if not path.is_file():
        return None
    payload = load_json(path)
    if payload.get("payloadKind") != "graph-slice" or payload.get("edgeDirection") != "dependency-to-consumer":
        raise ValueError(f"not a leanq dependency-to-consumer graph slice: {path}")
    return {str(row["id"]) for row in payload["nodes"]}


def presence(name, names):
    if names is None:
        return "not collected"
    return "observed" if name in names else "not observed (incomplete graph evidence)"


def report(case, result, out):
    roots = {r["id"]: slice_ids(out / "slices" / f"{r['id']}.json") for r in case["roots"]}
    main = roots[case["roots"][0]["id"]]
    questions = load_json(DATA / "research_questions.json")
    hs = [h for h in questions["hypotheses"] if h["case"] == case["id"]]
    history = [h for h in read_csv("history_claims.csv") if h["case"] == case["id"]]
    comparisons = [c for c in read_csv("route_comparisons.csv") if c["case"] == case["id"]]
    snap_path = out / "snapshot.json"
    snap = load_json(snap_path) if snap_path.exists() else snapshot(case, out)
    changed = []
    for name, digest in snap.get("input_sha256", {}).items():
        path = ROOT / name
        if digest != (sha(path) if path.is_file() else None):
            changed.append(name)
    formal_drift = [x for x in changed if x.endswith(".lean") or x in ("lean-toolchain", "lake-manifest.json")]
    registry_drift = [x for x in changed if x.startswith("dev/")]
    curation_drift = [x for x in changed if x not in formal_drift and x not in registry_drift]
    drift_notes = []
    if formal_drift:
        drift_notes.append("**formal inputs changed:** " + ", ".join(f"`{x}`" for x in formal_drift) + "; rebuild and re-index")
    if registry_drift:
        drift_notes.append("**source registries changed:** " + ", ".join(f"`{x}`" for x in registry_drift) + "; recheck root and alignment")
    if curation_drift:
        drift_notes.append("**research annotations changed:** " + ", ".join(f"`{x}`" for x in curation_drift) + "; refresh this report, NOT the Lean graph")
    if not drift_notes:
        drift_notes.append("no changes to the selected hashed inputs; untracked transitive proof dependencies may still have changed")
    lines = [f"# Research evidence: {case['label']}", "",
             f"Source inventory ID: `{case['source_id']}`. This is a pointer to the maintained census, **not** a copied verification status.",
             f"Recorded repository commit: `{snap.get('git_head') or 'unavailable'}`. Original PDF digest: `{snap.get('original_source_pdf', {}).get('sha256', 'not recorded')}`.",
             "", "**Evidence rule:** observed means that leanq's saved, elaborated *named declaration* closure contains the name. It is not proof of mathematical necessity. Not observed does not imply independent proof routes.",
             "**Selected-input drift:** " + "; ".join(drift_notes) + ". Graph freshness across the entire transitive environment is not certified by these hashes.",
             "", "## Proposed mathematical reduction (not a claim of minimality)", "",
             "| Step | Mathematical obligation | Formal candidates and graph observation | Mathematical source review | 1970 locator |",
             "| --- | --- | --- | --- | --- |"]
    for step in case["math_steps"]:
        ns = step["lean_candidates"]
        labels = "; ".join(f"`{md(n)}` ({presence(n, main)})" for n in ns) or "not yet formalized"
        lines.append(f"| {step['id']}: {md(step['label'])} | {md(step['statement'])} | {labels} | "
                     f"{md(step['source_review'])} | {md(step['source_locator']) or '**locator needed**'} |")
    names = sorted({n for step in case["math_steps"] for n in step["lean_candidates"]} |
                   {n for probe in case["branch_probes"] for n in probe["declarations"]} |
                   {r["name"] for r in case["roots"]})
    lines.extend(["", "## Curated declaration visibility across routes", "",
                  "This is a *compiler-indexed visibility matrix*, not a measure of mathematical indispensability.", "",
                  "| Exact declaration | " + " | ".join(r["id"] for r in case["roots"]) + " |",
                  "| --- | " + " | ".join("---" for _ in case["roots"]) + " |"])
    for name in names:
        lines.append("| `" + md(name) + "` | " + " | ".join(
            presence(name, roots[r["id"]]) for r in case["roots"]) + " |")
    lines.extend(["", "## Selected proof routes", "",
                  "| Route | Purpose | Root in its own slice |", "| --- | --- | --- |"])
    for root in case["roots"]:
        labels = roots[root["id"]]
        lines.append(f"| `{root['id']}` | {md(root['role'])} | {presence(root['name'], labels)} |")
    lines.extend(["", "## Named-declaration probes (not independence tests)", "",
                  "| Probe | Searched names | Observation in main closure |", "| --- | --- | --- |"])
    for probe in case["branch_probes"]:
        found = "; ".join(f"`{md(n)}`: {presence(n, main)}" for n in probe["declarations"])
        lines.append(f"| {probe['id']}: {md(probe['question'])} | {len(probe['declarations'])} exact declarations | {found} |")
    lines.extend(["", "## Comparing formal proof routes", "",
                  "Each comparison needs a *mathematical* comparison of hypotheses and conclusion, even when both Lean slices are available.", "",
                  "| ID | Routes | Witnesses in graph | Scope difference | Mathematical review |", "| --- | --- | --- | --- | --- |"])
    for c in comparisons:
        left, right = roots.get(c["route_left"]), roots.get(c["route_right"])
        status = f"{c['route_left']}: {'collected' if left is not None else 'missing'}, {c['route_right']}: {'collected' if right is not None else 'missing'}"
        diff = c["mathematical_gain_or_loss"] or "**unresolved**"
        witness = "; ".join(x for x in [c["hypotheses_left"], c["hypotheses_right"],
                                        c["source_witness"], c["proof_witness"]] if x)
        if witness:
            diff += "; " + witness
        lines.append(f"| {c['comparison_id']} | {c['route_left']} / {c['route_right']} | {status} | {md(diff)} | {md(c['review_status'])} |")
    lines.extend(["", "## Historical source checks", "",
                  "| Claim | Step | Work | Relationship proposed | 1970 locus | Primary-source locus | Evidence status |", "| --- | --- | --- | --- | --- | --- | --- |"])
    for h in history:
        lines.append("| " + " | ".join(md(h[k]) or "**needed**" for k in
                     ["claim_id", "step", "work", "relationship", "locator_1970", "locator_prior", "source_status"]) + " |")
    lines.extend(["", "**Historical arrows remain candidates** until both relevant statements and the proposed relationship have been inspected. A later paper cannot be an antecedent available to authors in 1970.",
                  "", "## Testable hypotheses", "",
                  "| ID | Proposal | Human verdict | What evidence is still required |", "| --- | --- | --- | --- |"])
    for h in hs:
        lines.append(f"| {h['id']} | {md(h['claim'])} | **{md(h['status'])}** | {md(h['requires'])} |")
    lines.extend(["", "## Research questions", ""])
    for q in questions["questions"]:
        lines.append(f"- **{q['id']}** {q['question']} Evidence needed: {q['deliverable']}")
    lines.extend(["", "## Next actions", "",
                  "1. Inspect the generated statement JSON and source-alignment HTML; pin exact source pages and domains in the case data.",
                  "2. Explain each mathematical edge without relying on a graph screenshot. Resolve history_claims.csv only from the actual cited passage.",
                  "3. Fill route_comparisons.csv with precise hypotheses, conclusions, and references; do not infer an equivalence from matching names.",
                  "4. Re-run `report` after curating the input files. Commit carefully reviewed mathematical conclusions separately from this generated evidence.", ""])
    out.mkdir(parents=True, exist_ok=True)
    (out / "evidence_packet.md").write_text("\n".join(lines), encoding="utf-8")
    by_id = {step["id"]: step for step in case["math_steps"]}
    diagram = ["flowchart LR"]
    for step in case["math_steps"]:
        # Nodes are curated *proposed mathematical steps*, not machine-inferred Lean edges.
        label = re.sub(r'[^A-Za-z0-9 ,.-]', '', step["label"])
        diagram.append(f'  {step["id"]}["{label}"]')
        for req in step["requires"]:
            if req not in by_id:
                raise ValueError(f"missing proposed step predecessor: {req}")
            diagram.append(f'  {req} --> {step["id"]}')
    diagram.append("  %% Curated derivation arrows; historical arrows intentionally absent")
    (out / "proposed_mathematical_route.mmd").write_text("\n".join(diagram) + "\n", encoding="utf-8")
    print("wrote", out / "evidence_packet.md")
    print("wrote", out / "proposed_mathematical_route.mmd")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["plan", "collect", "report"])
    parser.add_argument("case", choices=sorted(cases()))
    parser.add_argument("--out", help="artifact directory (default build/what-it-takes-dk/CASE)")
    parser.add_argument("--paper-pdf", help="original source PDF, hash only; never copied into the research bundle")
    parser.add_argument("--run", action="store_true", help="execute plan; otherwise only display commands")
    parser.add_argument("--reuse-index", action="store_true", help="use an existing index explicitly; YOU are responsible for checking its freshness")
    args = parser.parse_args()
    try:
        case, inventory, _ = selected_case(args.case)
        out = output_dir(case, args.out)
        if args.action in ("plan", "collect"):
            write_axiom_audit(case, out)
        steps = commands(case, out, reuse_index=args.reuse_index)
        if args.action == "plan":
            print(f"Source: {case['source_id']}; registered headline {case['roots'][0]['name']}")
            print("Run from repository root (sequentially):")
            for _, argv, redirect in steps:
                print(shell_command(argv, redirect))
            return 0
        if args.action == "collect":
            if not args.run:
                print("collect defaults to a plan; pass --run to execute.")
                for _, argv, redirect in steps:
                    print(shell_command(argv, redirect))
                return 0
            if args.reuse_index and not (out / "semantic-index.json").is_file():
                raise ValueError("--reuse-index requested but case-local semantic-index.json is absent")
            snapshot(case, out, paper_pdf=args.paper_pdf)
            execute(steps, out)
            # Record which graph was actually generated; do not infer independence.
            snapshot(case, out, paper_pdf=args.paper_pdf)
            report(case, inventory, out)
            return 0
        if args.action == "report":
            if args.paper_pdf:
                snapshot(case, out, paper_pdf=args.paper_pdf)
            report(case, inventory, out)
            return 0
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"research: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
