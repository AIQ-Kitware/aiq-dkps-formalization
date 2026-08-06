#!/usr/bin/env python3
"""
Analyze the extracted human prompts to quantify how much human steering the
"auto"-formalization effort actually required.

Reads prompts.jsonl / events.jsonl (produced by extract_prompts.py) and writes:
  metrics.json     machine-readable rollup
  ANALYSIS.md      the narrative report
  taxonomy.tsv     every prompt with its assigned category (for hand-auditing)

Category assignment is heuristic and single-label with a fixed priority order.
It is meant to be audited: taxonomy.tsv exists so mislabels can be spotted and
the rules below tightened.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import statistics
from collections import Counter, defaultdict
from datetime import datetime, timezone

# --- layout -------------------------------------------------------------
# ROOT/                       (POSTHOC_ROOT, default: parent of tools/)
#   tools/                    these scripts (committed)
#   local/raw-all/            verbatim ~/.claude/projects snapshot (NEVER committed)
#   local/claude-meta/        history.jsonl etc (NEVER committed)
#   local/sessions/           readable per-session transcripts (not committed)
#   findings/<agent-id>/      small derived artifacts (COMMITTED, merged across machines)
import os as _os
ROOT = pathlib.Path(_os.environ.get("POSTHOC_ROOT",
                                    pathlib.Path(__file__).resolve().parent.parent))
LOCAL = ROOT / "local"
RAW = LOCAL / "raw-all"


def agent_id(explicit=None):
    """Stable per-machine identity so findings from different agents never collide."""
    if explicit:
        return explicit
    v = _os.environ.get("POSTHOC_AGENT_ID")
    if v:
        return v
    import socket
    return socket.gethostname().split(".")[0]


def outdir(aid):
    d = ROOT / "findings" / aid
    d.mkdir(parents=True, exist_ok=True)
    return d

# ---------------------------------------------------------------- taxonomy ---
# (category, description, regex). Priority order: first match wins.
RULES = [
    ("error_paste",
     "Pasting compiler/build output the agent could not see itself",
     r"error:.*\.lean:\d+|^i still see:|failed to generate|unknown identifier"),
    ("correction_redirect",
     "Correcting or reversing what the agent just did or was about to do",
     r"^(no|nope|actually|wait|err|oh|not yet|stop|don'?t|dont|instead)\b"
     r"|that('| i)s (wrong|not)|there is no decision|you should not|is a mistake"
     r"|wrong agent|revert|put it back|it'?s not specific|hardely anything|still broken"),
    ("ferry_compose",
     "Asking this agent to author a prompt/question for a different agent",
     r"(write|give me|send me|what) (a |the )?(prompt|message|question)s?\b"
     r"|prompt (for|to give)|message to send|questions to ask|what should the math agent"
     r"|ferry text|i can ferry"),
    ("ferry_relay",
     "Relaying another agent's text into this session (the human as message bus)",
     r"\b(math agent|gpt[ -]?5|chat ?gpt|\bgpt\b|codex|fable|namek)\b.{0,80}\b(say|said|says|review|drop|prompt|work|response|update|finished|pushed|has|did)\b"
     r"|^(it says|here is w|i have (a |an )?(prompt|update)|new work from|response to the)"
     r"|(the )?(other|another|previous) agent|math agent (says|has|dropped|applied|came back)"),
    ("compile_cycle",
     "Routine 'inspect the latest commit and compile/fix it' hand-cranking",
     r"inspect the latest commit|compile/fix|fix (the )?(compile|lake|current|these)"
     r"|compile and repair|apply the .*overlay|read .*\.md.*and execute"
     r"|use the lean compiler to fix|review the last commit"),
    ("coordination",
     "Multi-agent bookkeeping: identity, lanes, branch fetch/merge, conflicts",
     r"\blane(s)?\b|you are (now )?(fable|opus|toothbrush|namek|edward)|commit as such"
     r"|fetch and merge|merge (in |the )?(remote|upstream|main|branch|fable|any)|merge conflict"
     r"|resolve conflict|push(ed)? up|remote branch|coordinat|other agents"),
    ("env_infra",
     "Environment and tooling breakage (lake, symlinks, MCP, keys, fonts, LaTeX build)",
     r"\.lake\b|symlink|bind mount|virtiofs|deploy key|\bmcp\b|apt install|font|olean|\blsp\b"
     r"|lake build error|don'?t build|dont build|install it"),
    ("paper_editorial",
     "Prose/LaTeX editorial direction on the write-up",
     r"\.tex\b|abstract|\bpaper\b|disclosure|writeup|write-up|prose|concise|tighten"
     r"|compress the|section length|latex|\bpdf\b|formatting|counter ?example writeup"),
    ("quality_gate",
     "Asserting a standard the agent would otherwise relax (rigor, artifacts, trust)",
     r"never (cheat|commit)|don'?t (cheat|trust|blindly)|push back|challenge it|no admission"
     r"|leaf sorr|only tex|not perfect|to 100%|axiom|verif(y|ied)|is this right"
     r"|keep trying and failing|don'?t lose work"),
    ("session_lifecycle",
     "Managing the session itself: stopping points, handoffs, context budget",
     r"stopping point|write a handoff|read the handoff|compact context"
     r"|new session|finish what you are doing"),
    ("context_supply",
     "Supplying out-of-band state the agent cannot observe (the human's own work, "
     "other machines, parallel merges)",
     r"^(i |i'm |i've |note i|note that|oh,? |yeah|ok,? now)\b.{0,200}?"
     r"(fixed|merged|pushed|copied|working on|landed|just |verified|setup|set up|don'?t need)"
     r"|on my (host|machine)|i'?m pushing|dropped new code|has already been applied"),
    ("priority_scope",
     "Setting or re-setting priorities and scope the agent did not choose",
     r"priorit|focus on|let'?s (push|keep going|start|update)|we should( probably)? (work|move|be)"
     r"|ignore (it|that|the) for now|the move is|i want (you )?to (start|push|know)"
     r"|in the mean ?time|crown jewel|work autonomously|different agent"),
    ("status_query",
     "Asking for status/information rather than issuing work",
     r"^(how|what|are you|do you|is there|has anyone|am i|would any|did|can we)\b"
     r"|\?\s*$|how far away|what is .* status|cant tell if you are"),
    ("decision_answer",
     "Answering a question the agent asked (choosing between options it surfaced)",
     r"^(yes|yeah|yep|no|fine|ok|okay|sure|both|choose|option|q\d)\b"
     r"|^both \d|^\d\.\s|promote anything that is clean"),
    ("throughput_nudge",
     "Pure 'keep going' with no new information",
     r"^(continue|go|go on|start|do it|finish that|keep going|proceed"
     r"|take it on|stop deliberating|stop wasting time|do the \w+|next)\b\.?$"),
    ("task_spec",
     "A substantial new mandate / specification (>1200 chars)",
     r".{1200,}"),
    ("task_direct",
     "A concrete, short work order naming the unit of work",
     r"^(do|continue|finish|push|promote|fix|read|apply|review|make|write|take|get|resolve"
     r"|inspect|switch|check|send|just|please|can you|let'?s)\b|\bpd-\d+|prop \d|section \d|theorem\s?\d"),
]
# Coarse groups used by both the per-agent report and merge_findings.py.
GROUPS_DEFAULT = {
    "multi-agent logistics": ["ferry_relay", "ferry_compose", "coordination"],
    "judgment (irreducibly human)": ["correction_redirect", "quality_gate",
                                     "priority_scope", "decision_answer"],
    "work orders": ["compile_cycle", "task_direct", "task_spec", "throughput_nudge"],
    "editorial": ["paper_editorial"],
    "gap-filling for a blind agent": ["context_supply", "error_paste", "env_infra",
                                      "status_query", "session_lifecycle"],
}

COMPILED = [(c, d, re.compile(r, re.I | re.S)) for c, d, r in RULES]
OTHER = ("other", "Did not match any rule")


def categorize(text: str) -> str:
    t = text.strip()
    for cat, _desc, rx in COMPILED:
        if rx.search(t):
            return cat
    return OTHER[0]


def parse_ts(s):
    if not s:
        return None
    return datetime.fromisoformat(s.replace("Z", "+00:00")).astimezone(timezone.utc)


def pct(n, d):
    return f"{100.0 * n / d:.0f}%" if d else "-"


def summarize(prompts, events, label):
    """Compute the rollup for one slice of the corpus."""
    prompts = sorted(prompts, key=lambda p: p["timestamp"] or "")
    n = len(prompts)
    out = {"label": label, "n_prompts": n}
    if not n:
        return out

    out["first"] = prompts[0]["timestamp"]
    out["last"] = prompts[-1]["timestamp"]
    days = sorted({(p["timestamp"] or "")[:10] for p in prompts})
    out["active_days"] = len(days)
    out["day_range"] = [days[0], days[-1]]

    chars = [p["prompt_chars"] for p in prompts]
    out["chars_median"] = statistics.median(chars)
    out["chars_mean"] = round(statistics.mean(chars))
    out["chars_total"] = sum(chars)
    out["short_prompts"] = sum(1 for c in chars if c < 80)

    tools = [p["response_tool_count"] for p in prompts]
    turns = [p["response_assistant_turns"] for p in prompts]
    out["tools_per_prompt_median"] = statistics.median(tools)
    out["tools_per_prompt_mean"] = round(statistics.mean(tools), 1)
    out["tools_total"] = sum(tools)
    out["turns_per_prompt_median"] = statistics.median(turns)
    out["zero_tool_prompts"] = sum(1 for t in tools if t == 0)

    # Autonomy interval: wall-clock the agent ran unattended between two human
    # turns of the same session. Gaps > 6h are treated as "human went away",
    # not "agent worked", so they are reported separately.
    # Prompts fired within 60s of each other are one "steering burst" (the user
    # queueing follow-ups while the agent runs), not independent interventions.
    gaps, long_gaps, bursts, burst_sizes = [], 0, 0, []
    by_sess = defaultdict(list)
    for p in prompts:
        by_sess[p["session_id"]].append(p)
    for ps in by_sess.values():
        ps.sort(key=lambda x: x["timestamp"] or "")
        cur = 1
        for a, b in zip(ps, ps[1:]):
            ta, tb = parse_ts(a["timestamp"]), parse_ts(b["timestamp"])
            if not ta or not tb:
                continue
            d = (tb - ta).total_seconds() / 60.0
            if d <= 1.0:
                cur += 1
                continue
            burst_sizes.append(cur)
            cur = 1
            if d > 360:
                long_gaps += 1
            else:
                gaps.append(d)
        burst_sizes.append(cur)
    bursts = len(burst_sizes)
    out["steering_bursts"] = bursts
    out["burst_size_max"] = max(burst_sizes) if burst_sizes else 0
    out["queued_followups"] = sum(b - 1 for b in burst_sizes)
    out["n_sessions"] = len(by_sess)
    out["prompts_per_session_median"] = statistics.median(len(v) for v in by_sess.values())
    if gaps:
        gaps.sort()
        out["autonomy_min_median"] = round(statistics.median(gaps), 1)
        out["autonomy_min_p25"] = round(gaps[len(gaps) // 4], 1)
        out["autonomy_min_p75"] = round(gaps[3 * len(gaps) // 4], 1)
        out["autonomy_min_max"] = round(gaps[-1], 1)
        out["autonomy_under_5min"] = sum(1 for g in gaps if g < 5)
        out["autonomy_n"] = len(gaps)
    out["long_gaps_over_6h"] = long_gaps

    cats = Counter(categorize(p["prompt"]) for p in prompts)
    out["categories"] = dict(cats.most_common())

    ev = Counter(e["event"] for e in events)
    out["events"] = dict(ev.most_common())
    out["interrupts"] = ev.get("interrupt", 0)
    out["compactions"] = ev.get("compact_continuation", 0)
    out["stop_hook_replays"] = ev.get("stop_hook_replay", 0)

    per_day = Counter((p["timestamp"] or "")[:10] for p in prompts)
    out["per_day"] = dict(sorted(per_day.items()))
    return out


def md_table(rows, headers):
    out = ["| " + " | ".join(headers) + " |",
           "|" + "|".join("---" for _ in headers) + "|"]
    for r in rows:
        out.append("| " + " | ".join(str(x) for x in r) + " |")
    return out


def week_of(ts):
    d = parse_ts(ts)
    return d.strftime("%Y-W%V") if d else "?"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--label", default="aiq-dkps-formalization (+ TauCeti subrepos)",
                    help="human-readable name for the scope under study")
    ap.add_argument("--agent-id", default=None)
    args = ap.parse_args()
    aid = agent_id(args.agent_id)
    OUT = outdir(aid)

    prompts = [json.loads(l) for l in (OUT / "prompts.jsonl").open()]
    events = [json.loads(l) for l in (OUT / "events.jsonl").open()]
    # Scope is enforced at extraction time (extract_prompts.py --scope), so
    # everything present here is in scope.
    f = summarize(prompts, events, args.label)
    (OUT / "metrics.json").write_text(json.dumps({"agent_id": aid, "focus": f}, indent=2))

    with (OUT / "taxonomy.tsv").open("w") as fh:
        fh.write("timestamp\tsession\tcategory\tchars\ttools\tturns\tprompt_head\n")
        for p in sorted(prompts, key=lambda x: x["timestamp"] or ""):
            head = " ".join(p["prompt"].split())[:200]
            fh.write(f"{p['timestamp']}\t{p['session_id'][:8]}\t{categorize(p['prompt'])}"
                     f"\t{p['prompt_chars']}\t{p['response_tool_count']}"
                     f"\t{p['response_assistant_turns']}\t{head}\n")

    descs = {c: d for c, d, _ in RULES}
    descs[OTHER[0]] = OTHER[1]
    ordered = sorted(prompts, key=lambda p: p["timestamp"] or "")

    L = ["# How much human steering did the formalization actually need?", "",
         f"Scope: **{args.label}**. Generated by `analyze.py` from `prompts.jsonl`;",
         "see `extract_prompts.py` for how a human prompt is identified and how the",
         "scope filter is applied. Every number is auditable: `taxonomy.tsv` lists each",
         "prompt with its category, `sessions/*.md` has the full prompt + response text.",
         "Hand-written interpretation lives in `FINDINGS.md`.", "",
         "## Scope of the visible slice", "",
         "- Claude Code retains roughly 30 days of session transcripts. The oldest",
         f"  surviving record here is **{f['day_range'][0]}**; the newest is **{f['day_range'][1]}**.",
         "  Earlier work is gone except for the typed-prompt index in",
         "  `claude-meta/history.jsonl` (prompt text only, no responses, CLI sessions only).",
         "- No session was ever run with a TauCeti subrepo as its cwd; all subrepo work",
         "  was driven from the parent repo, so the scope filter changes nothing in",
         "  practice beyond excluding unrelated projects.",
         f"- **{f['n_prompts']} human prompts** across **{f['n_sessions']} sessions** on",
         f"  **{f['active_days']} active days**.", "",
         "## Headline", ""]
    L += md_table([
        ["Human prompts", f["n_prompts"]],
        ["Steering bursts (prompts within 60s merged)", f["steering_bursts"]],
        ["Human-authored characters", f"{f['chars_total']:,}"],
        ["Median prompt length", f"{f['chars_median']:.0f} chars"],
        ["Prompts under 80 chars", f"{f['short_prompts']} ({pct(f['short_prompts'], f['n_prompts'])})"],
        ["Agent tool calls in response", f"{f['tools_total']:,}"],
        ["Tool calls per human prompt (median)", f"{f['tools_per_prompt_median']:.0f}"],
        ["Tool calls per human prompt (mean)", f"{f['tools_per_prompt_mean']}"],
        ["Median unattended run between prompts", f"{f.get('autonomy_min_median', '-')} min"],
        ["Interquartile unattended run",
         f"{f.get('autonomy_min_p25','-')}-{f.get('autonomy_min_p75','-')} min"],
        ["Longest unattended run (intra-session)", f"{f.get('autonomy_min_max','-')} min"],
        ["Handoffs shorter than 5 min",
         f"{f.get('autonomy_under_5min','-')} of {f.get('autonomy_n','-')}"],
        ["User interrupts (ESC mid-run)", f["interrupts"]],
        ["Context compactions", f["compactions"]],
        ["Stop-hook goal replays", f["stop_hook_replays"]],
    ], ["metric", "value"])
    L += ["", f"One human turn bought a median of **{f['tools_per_prompt_median']:.0f} tool calls** "
          f"(mean {f['tools_per_prompt_mean']}) of autonomous agent work.", ""]

    L += ["## What the steering was actually for", "",
          "Single-label heuristic classification, priority-ordered (first rule wins).", ""]
    L += md_table([[c, n, pct(n, f["n_prompts"]), descs.get(c, "")]
                   for c, n in f["categories"].items()],
                  ["category", "n", "share", "what it means"])
    L += [""]

    # Grouped view: which buckets are logistics vs judgment vs work orders.
    GROUPS = GROUPS_DEFAULT
    rows = []
    for g, cs in GROUPS.items():
        n = sum(f["categories"].get(c, 0) for c in cs)
        rows.append([g, n, pct(n, f["n_prompts"]), ", ".join(cs)])
    L += ["### Grouped", "", ]
    L += md_table(rows, ["group", "n", "share", "categories"])
    L += [""]

    # How the mix moved over time.
    weeks = sorted({week_of(p["timestamp"]) for p in ordered})
    wk_cat = defaultdict(Counter)
    for p in ordered:
        wk_cat[week_of(p["timestamp"])][categorize(p["prompt"])] += 1
    L += ["## How the steering mix moved over time", "",
          "Share of that week's prompts, by group.", ""]
    rows = []
    for w in weeks:
        tot = sum(wk_cat[w].values())
        row = [w, tot]
        for g, cs in GROUPS.items():
            row.append(pct(sum(wk_cat[w].get(c, 0) for c in cs), tot))
        rows.append(row)
    L += md_table(rows, ["week", "prompts"] + list(GROUPS))
    L += [""]

    L += ["## Prompt volume by day", ""]
    L += md_table([[d, n] for d, n in f["per_day"].items()], ["day", "prompts"])
    L += [""]

    # Longest unattended runs: what a good "go do this" prompt looked like.
    runs = []
    by_sess = defaultdict(list)
    for p in ordered:
        by_sess[p["session_id"]].append(p)
    for ps in by_sess.values():
        for a, b in zip(ps, ps[1:]):
            ta, tb = parse_ts(a["timestamp"]), parse_ts(b["timestamp"])
            if not ta or not tb:
                continue
            d = (tb - ta).total_seconds() / 60.0
            if d <= 360:
                runs.append((d, a))
    runs.sort(key=lambda x: -x[0])
    L += ["## Longest unattended runs", "",
          "The prompts that bought the most autonomous work before the next human turn.", ""]
    L += md_table([[f"{d:.0f} min", a["response_tool_count"], categorize(a["prompt"]),
                    " ".join(a["prompt"].split())[:110]] for d, a in runs[:15]],
                  ["unattended", "tool calls", "category", "prompt"])
    L += [""]

    L += ["## Tightest loops", "",
          "Consecutive human turns under 3 minutes apart - where the human was", 
          "watching closely or the agent kept stalling.", ""]
    tight = [(d, a) for d, a in runs if d < 3]
    L += md_table([[f"{d:.1f} min", categorize(a["prompt"]),
                    " ".join(a["prompt"].split())[:110]]
                   for d, a in sorted(tight, key=lambda x: x[0])[:15]],
                  ["gap", "category", "prompt that opened the gap"])
    L += [""]

    L += ["## Harness friction events", ""]
    L += md_table([[k, v] for k, v in f["events"].items()], ["event", "n"])
    L += ["",
          "## Caveats", "",
          "- Category rules are regex heuristics tuned on this corpus; treat shares as",
          "  approximate and audit `taxonomy.tsv` before quoting any single number.",
          "- The unattended-run figure measures wall-clock between human turns within a",
          "  session, excluding gaps over 6 hours (human away, not agent working). It",
          "  conflates 'agent still running' with 'agent finished and idled'.",
          "- Sub-agent (Task tool) prompts are excluded: they are agent-authored.",
          "- Prompts from sessions that already aged out, or from another machine or",
          "  account, are invisible here.",
          ]
    (OUT / "ANALYSIS.md").write_text("\n".join(L) + "\n")
    print(f"{f['n_prompts']} prompts, {f['n_sessions']} sessions -> ANALYSIS.md, metrics.json, taxonomy.tsv")


if __name__ == "__main__":
    main()
