#!/usr/bin/env python3
"""
Assemble evidence for classifying agent mistakes.

`prompts.jsonl` records what the human said and what the agent did *next*. To
identify a mistake you need what the agent did *before* the correction. This
script re-walks the raw transcripts and, for every human turn that looks like it
is responding to an error, emits a context window:

    [what the agent said/did just before]  ->  [the human's correction]  ->  [the agent's reply]

Interrupts (ESC mid-run) are included: they are corrections with no prompt text,
and the preceding tool call says what was being interrupted.

Output: mistake-evidence.md  (read this and classify by hand)
"""

from __future__ import annotations

import json
import pathlib
import re
from collections import defaultdict

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
SCOPE = "/aiq-dkps-formalization"

# Human turns worth inspecting for an underlying agent mistake. Deliberately
# broader than the `correction_redirect` category in analyze.py: a mistake is
# often reported inside a status query ("wait, you have a counterexample?") or a
# quality gate ("never cheat").
SIGNAL = re.compile(
    r"\b(no|nope|actually|wait|err|oh|instead|revert|undo|wrong|mistake|broken|bug"
    r"|don'?t|dont|stop|not yet|shouldn'?t|should not|incorrect|false|failed|fail"
    r"|cheat|fake|hallucinat|doesn'?t|didn'?t|isn'?t|can'?t|never|too |over|clobber"
    r"|regress|lost|missing|stale|conflict|put it back|why |but )\b", re.I)


def text_blocks(msg):
    out = []
    for b in (msg or {}).get("content") or []:
        if not isinstance(b, dict):
            continue
        if b.get("type") == "text" and b.get("text", "").strip():
            out.append(("text", b["text"].strip()))
        elif b.get("type") == "tool_use":
            inp = b.get("input") or {}
            desc = inp.get("description") or inp.get("command") or inp.get("file_path") \
                or inp.get("pattern") or inp.get("old_string") or ""
            out.append(("tool", f"{b.get('name')}: {str(desc)[:300]}"))
    return out


def main():
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--agent-id", default=None)
    args = ap.parse_args()
    OUT = outdir(agent_id(args.agent_id))
    prompts = {p["uuid"]: p for p in
               (json.loads(l) for l in (OUT / "prompts.jsonl").open())}
    windows = {}

    for f in sorted(RAW.rglob("*.jsonl")):
        recs = []
        with f.open(errors="replace") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    recs.append(json.loads(line))
                except json.JSONDecodeError:
                    continue
        if not any(SCOPE in (r.get("cwd") or "") for r in recs):
            continue

        for i, r in enumerate(recs):
            if r.get("type") != "user" or r.get("isSidechain"):
                continue
            msg = r.get("message")
            if not isinstance(msg, dict):
                continue
            content = msg.get("content")
            raw = content if isinstance(content, str) else " ".join(
                b.get("text", "") for b in content or [] if isinstance(b, dict))
            uuid = r.get("uuid")

            is_interrupt = raw.strip().startswith("[Request interrupted")
            p = prompts.get(uuid)
            if not p and not is_interrupt:
                continue
            if p and not SIGNAL.search(p["prompt"][:600]):
                continue
            if uuid in windows:
                continue

            # Walk back for the last assistant activity.
            before = []
            for rr in reversed(recs[max(0, i - 14):i]):
                if rr.get("type") == "assistant":
                    before = text_blocks(rr.get("message")) + before
                    if sum(len(x[1]) for x in before) > 900:
                        break
            after = []
            for rr in recs[i + 1:i + 8]:
                if rr.get("type") == "assistant":
                    after += text_blocks(rr.get("message"))
                    if sum(len(x[1]) for x in after) > 700:
                        break

            windows[uuid] = {
                "timestamp": r.get("timestamp"),
                "session": (r.get("sessionId") or f.stem)[:8],
                "kind": "interrupt" if is_interrupt else "correction",
                "prompt": (p["prompt"] if p else raw.strip()),
                "before": before[-6:],
                "after": after[:4],
            }

    rows = sorted(windows.values(), key=lambda w: w["timestamp"] or "")
    out = ["# Mistake evidence windows", "",
           f"{len(rows)} human turns that look like they are responding to an agent error,",
           "each with the agent activity immediately before and after.", "",
           "Read and classify by hand; the SIGNAL regex over-collects on purpose.", ""]
    for n, w in enumerate(rows, 1):
        out += ["---", "",
                f"## [{n}] {w['timestamp']}  ({w['kind']}, session {w['session']})", "",
                "**Agent was doing:**", ""]
        if w["before"]:
            for kind, t in w["before"]:
                out.append(f"- `{kind}` {' '.join(t.split())[:400]}")
        else:
            out.append("- _(nothing captured)_")
        out += ["", "**Human said:**", "", "```text",
                w["prompt"][:1500], "```", "", "**Agent replied:**", ""]
        if w["after"]:
            for kind, t in w["after"]:
                out.append(f"- `{kind}` {' '.join(t.split())[:400]}")
        else:
            out.append("- _(nothing captured)_")
        out.append("")
    (LOCAL / "mistake-evidence.md").write_text("\n".join(out) + "\n")
    print(f"{len(rows)} windows -> mistake-evidence.md")


if __name__ == "__main__":
    main()
