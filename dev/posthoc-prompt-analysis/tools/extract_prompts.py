#!/usr/bin/env python3
"""
Extract human prompts (and the LLM's immediate response to each) from the raw
Claude Code session transcripts snapshotted in ``raw-all/``.

Classifier, validated against ``claude-meta/history.jsonl`` and by manual
sampling (see ANALYSIS.md "How a human prompt is identified"):

  A human prompt is a ``type=="user"`` record where
    * ``isSidechain`` is false        -> excludes sub-agent Task prompts, which
                                         are stored as user records too;
    * ``message.content`` is text     -> excludes tool_result turns;
    * ``origin`` is absent or ``origin.kind == "human"``
                                      -> excludes task-notification, coordinator
                                         and hook-injected turns on versions that
                                         carry the field;
    * the text does not start with a known harness-synthetic marker
                                      -> excludes slash-command stdout, compact
                                         continuations, Stop-hook replays, etc.

  Records are deduped by ``uuid``: resuming or forking a session copies every
  prior record into the new session file, which otherwise inflates counts ~3x.

Harness-synthetic turns are not discarded outright; they are emitted to
``events.jsonl`` because interrupts, Stop-hook replays and compactions are
themselves friction signals.

Outputs (all under this directory):
  prompts.jsonl             one record per human prompt, with its response
  events.jsonl              interrupts / hook replays / compactions / slash cmds
  index.md                  session table
  sessions/<date>-<id>.md   readable prompt+response transcript per session
"""

from __future__ import annotations

import argparse
import json
import json as _json
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

IDE_RE = re.compile(r"<ide_[a-z_]+>.*?</ide_[a-z_]+>", re.S)
REMINDER_RE = re.compile(r"<system-reminder>.*?</system-reminder>", re.S)
CMD_NAME_RE = re.compile(r"<command-name>(.*?)</command-name>", re.S)
CMD_ARGS_RE = re.compile(r"<command-args>(.*?)</command-args>", re.S)
CAVEAT_RE = re.compile(r"<local-command-caveat>.*?</local-command-caveat>", re.S)

# (prefix, event_type). Order matters: first match wins.
SYNTHETIC = [
    ("[Request interrupted", "interrupt"),
    ("Stop hook feedback:", "stop_hook_replay"),
    ("A session-scoped Stop hook", "stop_hook_set"),
    ("This session is being continued", "compact_continuation"),
    ("<local-command-stdout>", "command_stdout"),
    ("<task-notification>", "task_notification"),
    ("[SYSTEM NOTIFICATION", "task_notification"),
    ("The coordinator sent a message", "coordinator_message"),
    ("API Error", "api_error"),
    ("<bash-stdout>", "bash_output"),
    ("<bash-stderr>", "bash_output"),
]


def text_of(content):
    """Text of a message, or None if it is a tool result / non-text."""
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        if any(isinstance(b, dict) and b.get("type") == "tool_result" for b in content):
            return None
        parts = [b.get("text", "") for b in content
                 if isinstance(b, dict) and b.get("type") == "text"]
        return "\n".join(p for p in parts if p) or None
    return None


def classify(rec: dict, txt: str) -> str:
    """Return 'human', an event type, or 'drop'."""
    if rec.get("isSidechain"):
        return "drop"
    origin_kind = (rec.get("origin") or {}).get("kind")
    if origin_kind and origin_kind != "human":
        return {"task-notification": "task_notification",
                "coordinator": "coordinator_message"}.get(origin_kind, "drop")

    s = txt.strip()
    if not s:
        return "drop"
    for prefix, kind in SYNTHETIC:
        if s.startswith(prefix):
            return kind
    body = CAVEAT_RE.sub("", s).strip()
    if CMD_NAME_RE.search(body[:400]):
        return "slash_command"
    if body.startswith("<local-command") or not body:
        return "drop"
    # A turn that is only a system-reminder is harness bookkeeping.
    if not REMINDER_RE.sub("", body).strip():
        return "drop"
    # Slash-command *body* expansions (the skill/command markdown, injected
    # after the invocation) start with the command's own heading.
    if body.startswith("# /") or body.startswith("---\nname:"):
        return "slash_body"
    return "human"


def clean(txt: str):
    notes = []
    for m in IDE_RE.finditer(txt):
        notes.append("ide_context: " + m.group(0)[:160])
    txt = IDE_RE.sub("", txt)
    if REMINDER_RE.search(txt):
        notes.append("system-reminder stripped")
    txt = REMINDER_RE.sub("", txt)
    txt = CAVEAT_RE.sub("", txt)
    return txt.strip(), notes


def scan_file(path: pathlib.Path):
    recs = []
    with path.open(errors="replace") as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            try:
                recs.append(json.loads(line))
            except json.JSONDecodeError:
                continue

    meta = {"file": str(path.relative_to(RAW)), "session_id": path.stem,
            "project_dir": path.parent.name, "cwd": None, "git_branch": None,
            "version": None, "start": None, "end": None}
    for r in recs:
        ts = r.get("timestamp")
        if ts:
            meta["start"] = min(meta["start"], ts) if meta["start"] else ts
            meta["end"] = max(meta["end"], ts) if meta["end"] else ts
        for k, f in (("cwd", "cwd"), ("git_branch", "gitBranch"), ("version", "version")):
            meta[k] = meta[k] or r.get(f)

    hits = []  # (index, kind, record, text)
    for i, r in enumerate(recs):
        if r.get("type") != "user":
            continue
        msg = r.get("message")
        if not isinstance(msg, dict):
            continue
        txt = text_of(msg.get("content"))
        if txt is None:
            continue
        kind = classify(r, txt)
        if kind == "drop":
            continue
        hits.append((i, kind, r, txt))

    # Response span for a human prompt = everything up to the next human prompt.
    human_idx = [h[0] for h in hits if h[1] == "human"] + [len(recs)]
    out_prompts, out_events = [], []
    for i, kind, r, txt in hits:
        base = {"session_id": meta["session_id"], "project_dir": meta["project_dir"],
                "cwd": r.get("cwd") or meta["cwd"], "git_branch": r.get("gitBranch"),
                "timestamp": r.get("timestamp"), "uuid": r.get("uuid"),
                "prompt_source": r.get("promptSource"),
                "origin_kind": (r.get("origin") or {}).get("kind"),
                "entrypoint": r.get("entrypoint"),
                "permission_mode": r.get("permissionMode"),
                "version": meta["version"], "file": meta["file"]}
        if kind != "human":
            cmd = CMD_NAME_RE.search(txt)
            argm = CMD_ARGS_RE.search(txt)
            out_events.append({**base, "event": kind,
                               "slash_command": cmd.group(1).strip() if cmd else None,
                               "slash_args": argm.group(1).strip() if argm else None,
                               "text": txt.strip()[:4000]})
            continue

        body, notes = clean(txt)
        if not body:
            continue
        nxt = next(x for x in human_idx if x > i)
        first_text, tools, turns, models = None, [], 0, set()
        for rr in recs[i + 1:nxt]:
            if rr.get("type") != "assistant":
                continue
            m2 = rr.get("message") or {}
            turns += 1
            if m2.get("model"):
                models.add(m2["model"])
            for b in m2.get("content") or []:
                if not isinstance(b, dict):
                    continue
                if b.get("type") == "text" and first_text is None and b.get("text", "").strip():
                    first_text = b["text"].strip()
                elif b.get("type") == "tool_use":
                    tools.append(b.get("name"))
        span_end = recs[nxt - 1].get("timestamp") if nxt - 1 > i else r.get("timestamp")
        out_prompts.append({**base, "prompt": body, "prompt_chars": len(body),
                            "notes": notes,
                            "response_first_text": first_text,
                            "response_tools": tools,
                            "response_tool_count": len(tools),
                            "response_assistant_turns": turns,
                            "response_models": sorted(models),
                            "span_end": span_end,
                            "span_records": nxt - i - 1})
    meta["prompt_count"] = len(out_prompts)
    return meta, out_prompts, out_events


def dedupe(rows):
    """Keep the richest copy of each uuid (resumed sessions duplicate records)."""
    best = {}
    for r in rows:
        u = r.get("uuid")
        if not u:
            continue
        cur = best.get(u)
        if cur is None or r.get("span_records", 0) > cur.get("span_records", 0):
            best[u] = r
    return sorted(best.values(), key=lambda r: (r.get("timestamp") or ""))


# Only this repo tree is in scope. The TauCeti submodules (external/TauCeti,
# submodules/TauCetiRoadmap, submodules/TauCetiReview) and the standalone
# TauCetiRoadmap/TauCetiReview checkouts are included by prefix, but note that
# no session was ever run with one of them as cwd -- all work on them happened
# from the parent repo.
DEFAULT_SCOPE = [
    "/aiq-dkps-formalization",
    "/TauCetiRoadmap",
    "/TauCetiReview",
    "/TauCeti",
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--response-limit", type=int, default=4000)
    ap.add_argument("--scope", action="append", default=None,
                    help="cwd substring to include (repeatable). Default: the dkps "
                         "formalization tree and its TauCeti subrepos.")
    ap.add_argument("--all-projects", action="store_true",
                    help="ignore --scope and extract every project in raw-all/")
    ap.add_argument("--agent-id", default=None,
                    help="identity for this machine/agent; findings land in "
                         "findings/<agent-id>/. Defaults to $POSTHOC_AGENT_ID or hostname.")
    args = ap.parse_args()
    aid = agent_id(args.agent_id)
    OUT = outdir(aid)
    scope = None if args.all_projects else (args.scope or DEFAULT_SCOPE)

    def in_scope(rec):
        if scope is None:
            return True
        cwd = rec.get("cwd") or ""
        return any(s in cwd for s in scope)

    # Scope is decided PER SESSION, not per record.
    #
    # A record's `cwd` is where that record's tool call ran, not which project the
    # session belongs to. On a checkout where the formalization is a subdirectory
    # of a parent repo (`aiq-eval-runner/formalizations/aiq-dkps-formalization`),
    # the session is opened at the parent, so every human prompt carries the
    # parent cwd while only the `Bash` records that `cd` into the formalization
    # carry the in-scope one. Filtering record-by-record therefore kept 6408 tool
    # results and dropped 100% of the human prompts -- the extractor reported
    # `human prompts: 0` on a store containing 110 of them.
    #
    # Session-level scoping is also the right semantics: a session is one unit of
    # work, and a prompt typed in it counts toward that work regardless of which
    # directory the shell happened to be in. This is strictly more inclusive than
    # the record-level test, so it cannot drop anything the old code kept.
    def session_in_scope(f) -> bool:
        if scope is None:
            return True
        with f.open(errors="replace") as fh:
            for line in fh:
                try:
                    r = _json.loads(line)
                except Exception:
                    continue
                if in_scope(r):
                    return True
        return False

    all_p, all_e, metas = [], [], []
    for f in sorted(RAW.rglob("*.jsonl")):
        if not session_in_scope(f):
            continue
        meta, p, e = scan_file(f)
        if not (p or e):
            continue
        metas.append(meta)
        all_p += p
        all_e += e

    prompts = dedupe(all_p)
    events = dedupe(all_e)

    with (OUT / "prompts.jsonl").open("w") as fh:
        for p in prompts:
            fh.write(json.dumps(p) + "\n")
    with (OUT / "events.jsonl").open("w") as fh:
        for e in events:
            fh.write(json.dumps(e) + "\n")

    # Per-session markdown, using the deduped canonical prompts.
    by_sess = defaultdict(list)
    for p in prompts:
        by_sess[p["session_id"]].append(p)
    mmap = {}
    for m in metas:
        prev = mmap.get(m["session_id"])
        if prev is None or (m["start"] or "") < (prev["start"] or ""):
            mmap[m["session_id"]] = m

    sessdir = LOCAL / "sessions"
    sessdir.mkdir(parents=True, exist_ok=True)
    for old in sessdir.glob("*.md"):
        old.unlink()
    for sid, ps in by_sess.items():
        m = mmap[sid]
        day = (ps[0]["timestamp"] or "unknown")[:10]
        lines = [f"# Session {sid}", "",
                 f"- project dir: `{m['project_dir']}`", f"- cwd: `{m['cwd']}`",
                 f"- branch: `{m['git_branch']}`",
                 f"- span: {m['start']} -> {m['end']}",
                 f"- cc version: {m['version']}", f"- human prompts: {len(ps)}", ""]
        for n, p in enumerate(ps, 1):
            tools = ", ".join(dict.fromkeys(t for t in p["response_tools"] if t))
            lines += ["---", "", f"## [{n}] {p['timestamp']}", "", "**Prompt**", "",
                      "```text", p["prompt"], "```", "",
                      f"**Immediate response** - {p['response_assistant_turns']} assistant turn(s), "
                      f"{p['response_tool_count']} tool call(s)" + (f": {tools}" if tools else ""), ""]
            rt = p["response_first_text"]
            if rt:
                lim = args.response_limit
                if lim and len(rt) > lim:
                    rt = rt[:lim] + f"\n... [truncated, {len(rt)} chars]"
                lines += ["```text", rt, "```", ""]
            else:
                lines += ["_(no leading prose; went straight to tools)_", ""]
        (sessdir / f"{day}-{sid[:8]}.md").write_text("\n".join(lines))

    by_project = defaultdict(list)
    for sid, ps in by_sess.items():
        by_project[mmap[sid]["project_dir"]].append((sid, ps))
    idx = ["# Prompt extraction index", "",
           f"- sessions with >=1 human prompt: **{len(by_sess)}**",
           f"- human prompts (deduped): **{len(prompts)}**",
           f"- harness events (interrupts/hooks/slash/compaction): **{len(events)}**", ""]
    for proj, ss in sorted(by_project.items(), key=lambda kv: -sum(len(x[1]) for x in kv[1])):
        ss.sort(key=lambda x: x[1][0]["timestamp"] or "")
        idx += [f"## `{proj}` - {sum(len(x[1]) for x in ss)} prompts / {len(ss)} sessions", "",
                "| start | session | prompts | file |", "|---|---|---|---|"]
        for sid, ps in ss:
            day = (ps[0]["timestamp"] or "?")[:16].replace("T", " ")
            idx.append(f"| {day} | `{sid[:8]}` | {len(ps)} | "
                       f"`sessions/{(ps[0]['timestamp'] or 'unknown')[:10]}-{sid[:8]}.md` |")
        idx.append("")
    (OUT / "index.md").write_text("\n".join(idx))

    manifest = {
        "agent_id": aid,
        "scope": scope,
        "n_prompts": len(prompts),
        "n_events": len(events),
        "n_sessions": len(by_sess),
        "first_prompt": prompts[0]["timestamp"] if prompts else None,
        "last_prompt": prompts[-1]["timestamp"] if prompts else None,
        "cwds": sorted({p.get("cwd") for p in prompts if p.get("cwd")}),
        "transcript_files_scanned": len(metas),
    }
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=2))
    print(f"[{aid}] human prompts: {len(prompts)}   events: {len(events)}   "
          f"sessions: {len(by_sess)}  -> {OUT}")


if __name__ == "__main__":
    main()
