# Prompt: post-hoc prompt/friction analysis on your own session store

Hand this file to each agent that has worked on the Davis–Kahan / DKPS
formalization on a **different machine or under a different account**. Each agent
runs it against *its own* `~/.claude` store, writes into a directory keyed by its
own identity, and commits. The results merge into a single joint analysis.

Paste everything below the line.

---

You are contributing to a post-hoc study of how much human steering this
formalization effort actually required, and what kinds of mistakes had to be
corrected. Other agents on other machines are doing the same thing against their
own session histories. Your job is to produce **your machine's slice** in a form
that merges cleanly with theirs.

## 0. Time matters

Claude Code prunes session transcripts at roughly 30 days. Whatever is not
snapshotted now is gone permanently. **Do the snapshot step first**, before any
analysis, before asking any clarifying questions.

## 1. Pick your agent id

Choose a stable, unique id for this machine+agent, lowercase, hyphenated:
`<hostname>-<who>` — e.g. `toothbrush-jon`, `namek-jon`, `yardrat-edward`.

It must not collide with another agent's id. Check what already exists:

```bash
ls dev/posthoc-prompt-analysis/findings/
```

Export it so every command below picks it up:

```bash
export POSTHOC_AGENT_ID=<your-id>
```

## 2. Snapshot your raw session store (do this first)

```bash
cd <your checkout of aiq-dkps-formalization>
mkdir -p dev/posthoc-prompt-analysis/local
rsync -a ~/.claude/projects/ dev/posthoc-prompt-analysis/local/raw-all/
mkdir -p dev/posthoc-prompt-analysis/local/claude-meta
cp ~/.claude/history.jsonl ~/.claude/settings.json \
   dev/posthoc-prompt-analysis/local/claude-meta/ 2>/dev/null
du -sh dev/posthoc-prompt-analysis/local/raw-all
```

`local/` is gitignored and **must stay that way** — it is large (~1.5G here) and
contains transcripts from unrelated projects plus account metadata. Never commit
it, never copy it into `findings/`.

`~/.claude/history.jsonl` is a separate, much smaller log of typed CLI prompts
that often reaches further back than the transcripts. Grab it even if it looks
redundant.

## 3. Run the pipeline

The tooling is committed at `dev/posthoc-prompt-analysis/tools/`. Do not rewrite
it — if it fails on your data, fix the tool and say what you changed, so every
agent's numbers stay comparable.

```bash
cd dev/posthoc-prompt-analysis
python3 tools/extract_prompts.py    # -> findings/$POSTHOC_AGENT_ID/{prompts,events}.jsonl, index.md, manifest.json
python3 tools/analyze.py            # -> findings/$POSTHOC_AGENT_ID/{ANALYSIS.md,metrics.json,taxonomy.tsv}
python3 tools/mistakes.py           # -> local/mistake-evidence.md (evidence windows, stays local)
```

Scope defaults to the DKPS formalization tree and its TauCeti subrepos. If your
checkout lives at a different path, the default substrings
(`/aiq-dkps-formalization`, `/TauCeti…`) should still match; if they do not, pass
`--scope` and record that in your manifest note.

## 4. Validate before you interpret

The extraction has three failure modes that silently corrupt the numbers.
Check all three and report what you found:

1. **Resume duplication.** Resuming or forking a session copies every prior
   record into the new file. Records are deduped by `uuid`; confirm your raw row
   count is meaningfully higher than your deduped count (here: 1280 raw -> 389
   unique for this repo). If they are equal, dedup may not be working.
2. **Sub-agent prompts leaking in.** Task-tool prompts are stored as `user`
   records. They are excluded via `isSidechain`. Spot-check
   `findings/$POSTHOC_AGENT_ID/prompts.jsonl` for second-person specifications
   like *"You are auditing part of the repo at…"* — those are agent-authored and
   should not be present.
3. **Synthetic turns.** Slash-command stdout, `Stop hook feedback:` replays,
   compact continuations and task notifications are not human prompts; they are
   routed to `events.jsonl` instead. Confirm `prompts.jsonl` has none.

Cross-check against `local/claude-meta/history.jsonl`, which independently logs
typed CLI prompts. Expect partial overlap only — it does not record VSCode-entry
prompts.

## 5. Write your interpretation

Two hand-written documents in `findings/$POSTHOC_AGENT_ID/`:

**`FINDINGS.md`** — where the friction was on *your* machine. Use
`ANALYSIS.md` for the numbers and the readable transcripts in `local/sessions/`
for the quotes. Cover at least:

- what the steering was actually for (the grouped taxonomy);
- how the mix moved over time;
- what real autonomy looked like (unattended-run distribution, and which prompts
  bought the most work);
- where the tight loops were and what caused them;
- what should not have been human at all.

Quote actual prompts. A share with no example behind it is not usable.

**`MISTAKES.md`** — classification of agent mistakes that had to be corrected.
This is the part the paper most needs, so be concrete and cite instances by
date, declaration name, or commit. Sources beyond the transcripts:

- `local/mistake-evidence.md` — 100-ish context windows of
  [what the agent was doing] -> [the human's correction] -> [what it did next];
- **your own memory store** (`~/.claude/projects/<project>/memory/*.md`) — many
  memories exist *because* a mistake was made; they are pre-distilled evidence;
- `AGENTS.md` and `dev/lean-proof-engineering-lessons.md` in the repo — policy
  written in response to specific failures, often naming the incident.

Use the existing classification in
`findings/toothbrush-jon/MISTAKES.md` as the shared schema (classes A–E:
soundness failures, phantom API, measurement failures, Lean/environment
mechanics, process/workflow). **Reuse those class names** so the classifications
can be pooled. Add a new class only if your evidence genuinely does not fit, and
say so explicitly.

For each instance record: what the agent did, how it was caught, and whether the
compiler could have caught it. The last column is the one that matters — the
central finding so far is that the build going green is weak evidence, and that
every soundness failure was caught by a human or a second agent rather than by
Lean.

## 6. Commit

Commit **only** `findings/<your-id>/`. Nothing else from this directory.

```bash
cd <repo root>
git status --short dev/posthoc-prompt-analysis/    # confirm local/ is not listed
git add dev/posthoc-prompt-analysis/findings/$POSTHOC_AGENT_ID
git commit -m "posthoc: prompt/friction analysis from $POSTHOC_AGENT_ID"
git push
```

If `git status` shows anything under `local/`, stop and fix the `.gitignore`
before committing. A 1.5G accidental commit is not easily undone.

Your directory is disjoint from every other agent's, so this merges without
conflict regardless of ordering.

## 7. Merging (whoever runs the joint analysis)

After the per-agent directories have been collected on one machine:

```bash
cd dev/posthoc-prompt-analysis
python3 tools/merge_findings.py     # -> JOINT-ANALYSIS.md, joint-metrics.json, joint-prompts.jsonl
```

Merging is idempotent and deduplicates by record `uuid`, so an agent that
appears twice, or a session present in two stores, is counted once and reported
as overlap rather than inflating the totals.

## Rules

- **Never commit `local/`.** Raw transcripts contain unrelated projects and
  account metadata.
- **Do not edit another agent's `findings/` directory.** Disjointness is what
  makes this merge without coordination.
- **Do not edit generated files by hand.** `ANALYSIS.md`, `metrics.json`,
  `taxonomy.tsv` and `index.md` are overwritten on every run; put your prose in
  `FINDINGS.md` / `MISTAKES.md`.
- **Report honestly.** If your store was pruned, or a session is missing, or a
  heuristic misfired, say so in your `FINDINGS.md` rather than presenting a
  clean number. The joint analysis is worth less than the caveats it carries.
