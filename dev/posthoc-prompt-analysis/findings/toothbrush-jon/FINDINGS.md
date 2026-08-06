# Findings: where the friction was in the DKPS formalization

Hand-written interpretation of `ANALYSIS.md` (machine-generated — don't edit it,
`analyze.py` overwrites it). Every claim is traceable to `taxonomy.tsv` and
`sessions/*.md`.

**Scope:** the `aiq-dkps-formalization` repo and its TauCeti subrepos, only.
No session was ever run with `external/TauCeti`, `submodules/TauCetiRoadmap` or
`submodules/TauCetiReview` as its cwd — all subrepo work was driven from the
parent repo — so the scope filter excludes unrelated projects and nothing else.

**Visible slice:** 2026-07-04 → 2026-08-06. 197 human prompts (183 steering
bursts once queued follow-ups are merged), 21 sessions, 17 active days,
~9,700 agent tool calls in response, ~291k characters typed.

---

## 1. Half the human effort was logistics, not direction

| group | n | share |
|---|---|---|
| multi-agent logistics (ferry in, ferry out, lanes/branches) | 73 | **37%** |
| judgment (corrections, quality gates, priorities, decisions) | 39 | 20% |
| work orders (compile cycle, task directives, nudges) | 36 | 18% |
| gap-filling for a blind agent (context supply, env, status, errors) | 32 | 16% |
| editorial (the paper) | 17 | 9% |

The workflow was a math agent (GPT 5.5/5.6, no Lean environment) producing
overlays and a compiler agent (Claude, with `lake`) repairing them — with a
human hand-carrying text between them. `ferry_relay` alone is 18% of all
prompts: `Math agent says: …`, `GPT says this: and you can push back`,
`New work from the math agent: …`. Another 5% (`ferry_compose`) is you asking
the agent to *write the prompt for the other agent* — you already knew this part
was mechanical and were trying to delegate it:

> `if you give me a question for the math agent I can ferry text around.`
> `So what should the math agent build. Write a prompt for it.`
> `Give me a message to send to fable asking about coordination`

None of this is steering in the sense of judgment. It is IO, and it is the
single largest automatable category in the corpus.

## 2. The logistics load appeared with the second agent and never went away

Share of each week's prompts:

| week | prompts | logistics | judgment | work orders | gap-filling |
|---|---|---|---|---|---|
| W27 (Jul 4) | 6 | 0% | 50% | 50% | 0% |
| W28 (Jul 7-13) | 12 | 8% | 8% | 33% | 42% |
| W29 (Jul 14-20) | 12 | **58%** | 33% | 0% | 8% |
| W30 (Jul 21-27) | 102 | 39% | 14% | 21% | 14% |
| W31 (Jul 28-Aug 3) | 64 | 39% | 25% | 12% | 20% |

W27–W28 is single-agent work: directives and environment fixing. From W29 the
math-agent/compiler-agent split lands and logistics immediately becomes the
dominant cost, holding at ~39% for the rest of the project. Prompt volume also
jumps 8x in W30 — the split bought throughput, but paid for it in human turns.

Also worth noting: W28 is 42% gap-filling. That is the week of the `.lake`
symlink, virtiofs/olean, fonts and MCP problems.

## 3. Genuine "go do this thing" autonomy did happen, at ~20-minute granularity

- median unattended run between human turns: **21.5 min** (IQR 8.2–51.1)
- longest intra-session unattended run: **245 min**
- one human turn bought a median of **18 tool calls** (mean 49)

The prompts that bought the most autonomous work are instructive — they are
short and architectural, not detailed specs:

| unattended | prompt |
|---|---|
| 243 min | `There is no decision there, the clean names belong to the library, the facade does not get the clean name.` |
| 227 min | `Inspect the latest commit and compile/fix it. This batch adds the planar singular-value layer…` |
| 174 min | `yes` |
| 158 min | `start` |
| 117 min | `You should not switch to ambition, keep doing what you are doing here in lean.` |

A one-word `yes` bought ~3 hours. The binding constraint was never prompt
length; it was whether the agent had an unambiguous next objective.

## 4. The tight loops cluster in two identifiable failure modes

26 of 152 handoffs were under 5 minutes. Reading them, they are almost all one
of two things:

**(a) The agent deliberating instead of acting.** 2026-07-29 has a four-prompt
burst fired in the same second:
`Finish tan 2 theta` / `You can work autonomously` / `stop deliberating` /
`stop wasting time`. Later the same day: `I cant tell if you are stopped or just
waiting.` That last one is a UI/legibility gap, not a capability gap.

**(b) Environment breakage with a slow diagnosis loop.**
`Symlink is broken: .lake -> …` → `Still broken` → `Its' broken on my machine
fuck` → `On my host.` → `Oh, bind mount is a good idea.` Four round-trips
because the agent could not see the host filesystem it was breaking on.

## 5. Judgment was 20% of turns — and it is the part worth keeping

`correction_redirect` (9%) is the largest judgment bucket, and the corrections
are architectural, not syntactic:

- `don't do reorganization yet. The math agent has a plan, we just need to hand off.`
- `Fine, do it to fix, but then put it back.`
- `You should not switch to ambition, keep doing what you are doing here in lean.`
- `There is no decision there, the clean names belong to the library, the facade does not get the clean name.`

`quality_gate` is only 7 prompts (4%) but sets the project's standards, and the
good ones became durable rules rather than repeated corrections:
`always commit. Leaf sorrys are fine.` / `never commit a pdf, only tex` /
`GPT 5.6 review, again push back when necessary. Don't trust blindly.` /
`The omit issue is a mistake agents constantly make. Can we add a note to
AGENTS.md about how to correctly do it?`

That last one is the pattern to generalize: a repeated correction converted into
a written rule. Several of these are now AGENTS.md entries or persistent
memories, and they stopped recurring.

## 6. Costs that should not have been human at all

- **`compile_cycle` (9%, 18 prompts)** — `Inspect the latest commit and
  compile/fix it.` A branch watcher could have triggered this on every math-lane
  commit.
- **`context_supply` (4%)** — `I fixed the filesystem issue.` / `I just merged
  the hard part in.` / `On my host.` The agent was blind to your parallel work
  on another machine. Each of these is a missing feed, not a decision.
- **`env_infra` (4%)** — `.lake` across a virtiofs boundary, LaTeX fonts, MCP
  setup, deploy keys. Mostly one-time, but each stopped work dead.
- **`status_query` (6%)** — `how far away are we from the full DK 1970 paper?` A
  standing generated status report answers most of these without a turn.

## 7. Friction that shows up as harness events, not prompts

- **19 interrupts** (ESC mid-run) — low; the agent was rarely charging off in the
  wrong direction.
- **23 context compactions** — each a point where state was lost and often
  re-supplied by hand (`Write a handoff for a new session.`).
- **74 Stop-hook goal replays** — the `/goal` hook re-asserting one instruction
  dozens of times. This is *machine-substituted* steering and should be counted
  as an automation success, not human effort: you wrote the goal once.

## 8. What to change next

Ranked by share × automatability:

1. **Kill the ferry.** Give the math agent and compiler agent a git-mediated
   protocol (overlay commits + a status file) or a shared queue, so relaying is
   not a human action. Addressable: ~30% of all human turns.
2. **Automate the compile cycle.** Trigger repair on new math-lane commits
   instead of on `Inspect the latest commit`. (~9%)
3. **Feed out-of-band state in.** A machine-readable "what the human and other
   hosts just did" surface removes `context_supply` and much of `coordination`.
4. **Make agent liveness legible.** `I cant tell if you are stopped or just
   waiting` should be impossible to need to type.
5. **Keep asserting standards once, in writing.** `quality_gate` deserves *more*
   human input, not less — it is where judgment lives and it is 4% of turns.

The irreducible residue in this slice is corrections + quality gates: roughly
**one prompt in eight** carried judgment no tooling would have supplied.

## Caveats

- Category assignment is regex-heuristic and tuned on this corpus; audit
  `taxonomy.tsv` before quoting a single number.
- Only ~30 days of transcripts survive. `claude-meta/history.jsonl` reaches back
  to 2026-04-04 but stores typed prompt text only, no responses, CLI-only.
- Prompts from sessions that already aged out, or from another machine or
  account, are invisible here.
- A cross-repo control comparison was computed in an earlier pass and dropped as
  out of scope; `raw-all/` still holds every project, so
  `extract_prompts.py --all-projects` reproduces it.
