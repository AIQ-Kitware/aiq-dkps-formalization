#!/usr/bin/env python3
"""Build paper-facing human/LLM interaction summaries from post-hoc findings."""

from __future__ import annotations

import importlib.util
import json
import pathlib
import statistics
from collections import Counter, defaultdict
from datetime import datetime, timezone

from accounting_lib import format_int, latex_escape, repo_root, write_csv

HERE = pathlib.Path(__file__).resolve().parent.parent
GENERATED = HERE / "generated"
ROOT = repo_root(HERE)
POSTHOC = ROOT / "dev/posthoc-prompt-analysis"
FINDINGS = POSTHOC / "findings"


def parse_ts(value: str | None):
    if not value:
        return None
    return datetime.fromisoformat(value.replace("Z", "+00:00")).astimezone(timezone.utc)


def load_taxonomy():
    path = POSTHOC / "tools/analyze.py"
    spec = importlib.util.spec_from_file_location("posthoc_analyze", path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"could not import {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.categorize, module.GROUPS_DEFAULT


def load_jsonl(path: pathlib.Path):
    if not path.exists():
        return []
    with path.open(encoding="utf-8") as file:
        return [json.loads(line) for line in file if line.strip()]


def stats(prompts, categorize):
    if not prompts:
        return {}
    chars = [int(p.get("prompt_chars") or 0) for p in prompts]
    tools = [int(p.get("response_tool_count") or 0) for p in prompts]
    sessions = defaultdict(list)
    for p in prompts:
        sessions[p.get("session_id") or "unknown"].append(p)
    gaps = []
    for values in sessions.values():
        values.sort(key=lambda p: p.get("timestamp") or "")
        for a, b in zip(values, values[1:]):
            ta, tb = parse_ts(a.get("timestamp")), parse_ts(b.get("timestamp"))
            if ta and tb:
                delta = (tb - ta).total_seconds() / 60.0
                if 1.0 < delta <= 360:
                    gaps.append(delta)
    days = sorted({(p.get("timestamp") or "")[:10] for p in prompts if p.get("timestamp")})
    return {
        "prompts": len(prompts),
        "sessions": len(sessions),
        "active_days": len(days),
        "first_day": days[0] if days else "",
        "last_day": days[-1] if days else "",
        "prompt_chars_total": sum(chars),
        "prompt_chars_median": statistics.median(chars),
        "response_tool_calls_total": sum(tools),
        "response_tool_calls_median": statistics.median(tools),
        "within_session_gap_minutes_median": round(statistics.median(gaps), 1) if gaps else None,
        "categories": Counter(categorize(p.get("prompt") or "") for p in prompts),
    }


def main():
    GENERATED.mkdir(parents=True, exist_ok=True)
    categorize, groups = load_taxonomy()
    by_uuid = {}
    events_by_uuid = {}
    seen_by = defaultdict(set)
    agents = []

    for directory in sorted(FINDINGS.iterdir()):
        if not directory.is_dir():
            continue
        agent = directory.name
        agents.append(agent)
        for p in load_jsonl(directory / "prompts.jsonl"):
            uuid = p.get("uuid")
            if not uuid:
                continue
            seen_by[uuid].add(agent)
            by_uuid.setdefault(uuid, {**p, "agent_id": agent})
        for e in load_jsonl(directory / "events.jsonl"):
            uuid = e.get("uuid")
            if uuid:
                events_by_uuid.setdefault(uuid, {**e, "agent_id": agent})

    prompts = sorted(by_uuid.values(), key=lambda p: p.get("timestamp") or "")
    events = sorted(events_by_uuid.values(), key=lambda e: e.get("timestamp") or "")
    joint = stats(prompts, categorize)
    event_counts = Counter(e.get("event") or "unknown" for e in events)

    category_rows = []
    for category, n in joint["categories"].most_common():
        category_rows.append(
            {"category": category, "prompts": n, "share": n / joint["prompts"]}
        )
    write_csv(GENERATED / "interaction_categories.csv", category_rows, ["category", "prompts", "share"])

    group_rows = []
    for group, cats in groups.items():
        n = sum(joint["categories"].get(cat, 0) for cat in cats)
        group_rows.append({"group": group, "prompts": n, "share": n / joint["prompts"]})
    write_csv(GENERATED / "interaction_groups.csv", group_rows, ["group", "prompts", "share"])

    event_rows = [
        {"event": event, "count": n} for event, n in event_counts.most_common()
    ]
    write_csv(GENERATED / "interaction_events.csv", event_rows, ["event", "count"])

    per_agent = []
    for agent in agents:
        ps = [p for p in prompts if p["agent_id"] == agent]
        s = stats(ps, categorize)
        if not s:
            continue
        per_agent.append(
            {
                "agent": agent,
                "prompts": s["prompts"],
                "sessions": s["sessions"],
                "active_days": s["active_days"],
                "first_day": s["first_day"],
                "last_day": s["last_day"],
                "median_prompt_chars": s["prompt_chars_median"],
                "median_tool_calls": s["response_tool_calls_median"],
                "median_gap_minutes": s["within_session_gap_minutes_median"],
            }
        )
    write_csv(
        GENERATED / "interaction_by_agent.csv",
        per_agent,
        list(per_agent[0].keys()) if per_agent else ["agent"],
    )

    summary = {
        "schema": "formalization-draft2/interaction-summary/v1",
        "agents": agents,
        "deduplicated_prompts": joint["prompts"],
        "sessions": joint["sessions"],
        "active_days": joint["active_days"],
        "day_range": [joint["first_day"], joint["last_day"]],
        "median_prompt_chars": joint["prompt_chars_median"],
        "total_response_tool_calls": joint["response_tool_calls_total"],
        "median_response_tool_calls": joint["response_tool_calls_median"],
        "median_within_session_gap_minutes": joint["within_session_gap_minutes_median"],
        "overlap_prompts": sum(len(v) > 1 for v in seen_by.values()),
        "categories": dict(joint["categories"]),
        "groups": {r["group"]: r["prompts"] for r in group_rows},
        "events": dict(event_counts),
        "warning": "Post-hoc transcript retention and field coverage vary by machine; taxonomy shares require manual audit before publication.",
    }
    (GENERATED / "interaction_summary.json").write_text(json.dumps(summary, indent=2) + "\n")

    macros = [
        "% Generated by scripts/build_interactions.py; do not edit by hand.",
        f"\\newcommand{{\\InteractionPromptCount}}{{{format_int(joint['prompts'])}}}",
        f"\\newcommand{{\\InteractionSessionCount}}{{{format_int(joint['sessions'])}}}",
        f"\\newcommand{{\\InteractionActiveDays}}{{{format_int(joint['active_days'])}}}",
        f"\\newcommand{{\\InteractionMedianPromptChars}}{{{format_int(joint['prompt_chars_median'])}}}",
        f"\\newcommand{{\\InteractionToolCallCount}}{{{format_int(joint['response_tool_calls_total'])}}}",
        f"\\newcommand{{\\InteractionMedianToolCalls}}{{{format_int(joint['response_tool_calls_median'])}}}",
        f"\\newcommand{{\\InteractionMedianGapMinutes}}{{{joint['within_session_gap_minutes_median']}}}",
        f"\\newcommand{{\\InteractionInterruptCount}}{{{format_int(event_counts.get('interrupt', 0))}}}",
        f"\\newcommand{{\\InteractionDroppedQueuedPromptCount}}{{{format_int(event_counts.get('queued_prompt_dropped', 0))}}}",
    ]
    (GENERATED / "interaction_macros.tex").write_text("\n".join(macros) + "\n")

    lines = [
        "% Generated by scripts/build_interactions.py; do not edit by hand.",
        "\\begin{tabular}{lrr}",
        "\\toprule",
        "Interaction group & Prompts & Share \\\\",
        "\\midrule",
    ]
    for row in group_rows:
        lines.append(
            f"{latex_escape(row['group'].replace('_', ' '))} & {row['prompts']:,} & {100 * row['share']:.1f}\\% \\\\")
    lines += ["\\bottomrule", "\\end{tabular}"]
    (GENERATED / "interaction_group_table.tex").write_text("\n".join(lines) + "\n")

    report = [
        "# Interaction analysis snapshot",
        "",
        f"- deduplicated human prompts: **{joint['prompts']:,}**",
        f"- sessions: **{joint['sessions']:,}**",
        f"- active days: **{joint['active_days']:,}** ({joint['first_day']} through {joint['last_day']})",
        f"- median prompt length: **{joint['prompt_chars_median']:.0f} characters**",
        f"- response tool calls: **{joint['response_tool_calls_total']:,} total**, median **{joint['response_tool_calls_median']:.0f} per prompt**",
        f"- median within-session human-intervention gap (filtered to 1--360 min): **{joint['within_session_gap_minutes_median']} min**",
        f"- explicit interrupt events: **{event_counts.get('interrupt', 0):,}**",
        f"- queued prompts later dropped: **{event_counts.get('queued_prompt_dropped', 0):,}**",
        "",
        "Taxonomy and transcript-retention caveats remain in the source post-hoc analysis and must be carried into the paper.",
    ]
    (GENERATED / "INTERACTION_REPORT.md").write_text("\n".join(report) + "\n")
    print(f"interactions: {joint['prompts']} prompts across {joint['sessions']} sessions and {len(agents)} agent stores")


if __name__ == "__main__":
    main()
