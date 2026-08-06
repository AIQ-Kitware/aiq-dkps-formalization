#!/usr/bin/env python3
"""
Merge per-agent findings into a single joint analysis.

Each machine/agent produces `findings/<agent-id>/` (prompts.jsonl, events.jsonl,
metrics.json, manifest.json, plus its hand-written FINDINGS.md / MISTAKES.md).
Those directories are committed and combine cleanly because they are disjoint by
construction. This script reads all of them on one machine and produces the
joint view.

Deduplication is by record `uuid`, which is globally unique per transcript
record — so if two agents ever saw the same session (shared checkout, copied
store), the prompt is counted once and the overlap is reported rather than
silently doubling the totals.

Outputs (at the repo-committed root):
  JOINT-ANALYSIS.md    the combined report
  joint-metrics.json   combined machine-readable rollup
  joint-prompts.jsonl  all prompts, deduped, each tagged with its agent_id

Usage:
  python3 tools/merge_findings.py
  python3 tools/merge_findings.py --exclude some-agent
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import statistics
from collections import Counter, defaultdict
from datetime import datetime, timezone

ROOT = pathlib.Path(os.environ.get("POSTHOC_ROOT",
                                  pathlib.Path(__file__).resolve().parent.parent))
FINDINGS = ROOT / "findings"

# Reuse the analyzer's taxonomy so joint and per-agent categories agree.
import sys
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from analyze import categorize, GROUPS_DEFAULT  # noqa: E402


def parse_ts(s):
    if not s:
        return None
    return datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(timezone.utc)


def load(agent_dir: pathlib.Path, name: str):
    f = agent_dir / name
    if not f.exists():
        return []
    return [json.loads(l) for l in f.open() if l.strip()]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--exclude", action="append", default=[],
                    help="agent-id to leave out (repeatable)")
    args = ap.parse_args()

    agents = sorted(d for d in FINDINGS.iterdir()
                    if d.is_dir() and d.name not in args.exclude) if FINDINGS.exists() else []
    if not agents:
        raise SystemExit(f"no agent findings under {FINDINGS}")

    by_uuid = {}
    seen_by = defaultdict(set)      # uuid -> {agent_id}
    events_by_uuid = {}
    per_agent = {}

    for d in agents:
        aid = d.name
        man = {}
        if (d / "manifest.json").exists():
            man = json.loads((d / "manifest.json").read_text())
        ps = load(d, "prompts.jsonl")
        es = load(d, "events.jsonl")
        per_agent[aid] = {"manifest": man, "n_prompts_reported": len(ps),
                          "n_events_reported": len(es)}
        for p in ps:
            u = p.get("uuid")
            if not u:
                continue
            seen_by[u].add(aid)
            if u not in by_uuid:
                by_uuid[u] = {**p, "agent_id": aid}
        for e in es:
            u = e.get("uuid")
            if u and u not in events_by_uuid:
                events_by_uuid[u] = {**e, "agent_id": aid}

    prompts = sorted(by_uuid.values(), key=lambda p: p.get("timestamp") or "")
    events = sorted(events_by_uuid.values(), key=lambda e: e.get("timestamp") or "")
    overlap = {u: sorted(a) for u, a in seen_by.items() if len(a) > 1}

    # Attribute each prompt to its agent for the per-agent columns.
    by_agent = defaultdict(list)
    for p in prompts:
        by_agent[p["agent_id"]].append(p)

    def stats(ps):
        if not ps:
            return {}
        chars = [p["prompt_chars"] for p in ps]
        tools = [p["response_tool_count"] for p in ps]
        days = sorted({(p["timestamp"] or "")[:10] for p in ps})
        gaps = []
        sess = defaultdict(list)
        for p in ps:
            sess[p["session_id"]].append(p)
        for v in sess.values():
            v.sort(key=lambda x: x["timestamp"] or "")
            for a, b in zip(v, v[1:]):
                ta, tb = parse_ts(a["timestamp"]), parse_ts(b["timestamp"])
                if ta and tb:
                    d = (tb - ta).total_seconds() / 60
                    if 1.0 < d <= 360:
                        gaps.append(d)
        return {
            "n_prompts": len(ps), "n_sessions": len(sess), "active_days": len(days),
            "day_range": [days[0], days[-1]],
            "chars_median": statistics.median(chars), "chars_total": sum(chars),
            "tools_total": sum(tools),
            "tools_per_prompt_median": statistics.median(tools),
            "autonomy_min_median": round(statistics.median(gaps), 1) if gaps else None,
            "categories": dict(Counter(categorize(p["prompt"]) for p in ps).most_common()),
        }

    joint = stats(prompts)
    joint["agents"] = {a: stats(v) for a, v in by_agent.items()}
    joint["overlap_prompts"] = len(overlap)
    joint["events"] = dict(Counter(e["event"] for e in events).most_common())
    (ROOT / "joint-metrics.json").write_text(json.dumps(joint, indent=2))

    with (ROOT / "joint-prompts.jsonl").open("w") as fh:
        for p in prompts:
            fh.write(json.dumps(p) + "\n")

    def pct(n, d):
        return f"{100.0*n/d:.0f}%" if d else "-"

    def table(rows, headers):
        out = ["| " + " | ".join(headers) + " |",
               "|" + "|".join("---" for _ in headers) + "|"]
        out += ["| " + " | ".join(str(x) for x in r) + " |" for r in rows]
        return out

    L = ["# Joint analysis across agents", "",
         f"Merged from **{len(agents)}** agent findings directories: "
         + ", ".join(f"`{d.name}`" for d in agents) + ".",
         "Deduplicated by transcript record `uuid`.", "",
         f"- joint human prompts: **{joint['n_prompts']}**",
         f"- sessions: **{joint['n_sessions']}**, active days: **{joint['active_days']}**",
         f"- span: {joint['day_range'][0]} -> {joint['day_range'][1]}",
         f"- prompts seen by more than one agent (deduped): **{joint['overlap_prompts']}**",
         ""]
    if overlap:
        L += ["> Overlap is expected only if two agents shared a transcript store.",
              "> Duplicates were counted once; per-agent totals below may therefore",
              "> exceed the joint total.", ""]

    L += ["## Per agent", ""]
    rows = []
    for a, s in sorted(joint["agents"].items(), key=lambda kv: -kv[1]["n_prompts"]):
        rows.append([a, s["n_prompts"], s["n_sessions"], s["active_days"],
                     f"{s['day_range'][0]}..{s['day_range'][1]}",
                     f"{s['chars_median']:.0f}", f"{s['tools_per_prompt_median']:.0f}",
                     s["autonomy_min_median"] if s["autonomy_min_median"] else "-"])
    L += table(rows, ["agent", "prompts", "sessions", "days", "span",
                      "median chars", "median tools/prompt", "median gap (min)"])
    L += [""]

    L += ["## Joint steering taxonomy", ""]
    L += table([[c, n, pct(n, joint["n_prompts"])] for c, n in joint["categories"].items()],
               ["category", "n", "share"])
    L += ["", "### Grouped", ""]
    rows = []
    for g, cs in GROUPS_DEFAULT.items():
        n = sum(joint["categories"].get(c, 0) for c in cs)
        rows.append([g, n, pct(n, joint["n_prompts"])])
    L += table(rows, ["group", "n", "share"])
    L += [""]

    L += ["## Steering mix by agent", "",
          "Share of that agent's prompts, by group.", ""]
    rows = []
    for a, s in sorted(joint["agents"].items(), key=lambda kv: -kv[1]["n_prompts"]):
        row = [a, s["n_prompts"]]
        for g, cs in GROUPS_DEFAULT.items():
            row.append(pct(sum(s["categories"].get(c, 0) for c in cs), s["n_prompts"]))
        rows.append(row)
    L += table(rows, ["agent", "prompts"] + list(GROUPS_DEFAULT))
    L += [""]

    L += ["## Harness friction events (joint)", ""]
    L += table([[k, v] for k, v in joint["events"].items()], ["event", "n"])
    L += ["",
          "## Per-agent narrative reports", "",
          "Each agent's own interpretation, unmerged (they describe different",
          "machines, lanes and time windows):", ""]
    for d in agents:
        for doc in ("FINDINGS.md", "MISTAKES.md", "ANALYSIS.md"):
            if (d / doc).exists():
                L.append(f"- [`findings/{d.name}/{doc}`](findings/{d.name}/{doc})")
    L += ["",
          "## Caveats", "",
          "- Category rules were tuned on one corpus; audit each agent's",
          "  `taxonomy.tsv` before quoting a share.",
          "- Agents with different Claude Code versions may have different field",
          "  coverage; `extract_prompts.py` falls back to text heuristics where the",
          "  `origin` field is absent.",
          "- Transcript retention is ~30 days per machine, so each agent's window",
          "  starts wherever its store was pruned.",
          ]
    (ROOT / "JOINT-ANALYSIS.md").write_text("\n".join(L) + "\n")
    print(f"merged {len(agents)} agents, {joint['n_prompts']} prompts "
          f"({joint['overlap_prompts']} overlapping) -> JOINT-ANALYSIS.md")


if __name__ == "__main__":
    main()
