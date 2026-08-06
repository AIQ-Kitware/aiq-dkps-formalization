# Where the friction was on `aivm-2404-edward`

Hand-written interpretation. Numbers come from `ANALYSIS.md` / `metrics.json`;
quotes come from `prompts.jsonl` and the evidence windows in
`local/mistake-evidence.md`. **110 human prompts, 10 sessions, 17 active days
(2026-07-07 → 2026-08-06).**

---

## 0. Read this before pooling my numbers

Three caveats, one of them serious enough that it changes the tooling.

### 0.1 The extractor reported `human prompts: 0` on a store containing 110

`extract_prompts.py` scoped **per record**, testing each record's `cwd` against
`/aiq-dkps-formalization`. On this machine the formalization is a *subdirectory*
of a parent repo, and sessions are opened at the parent:

```
cwd of a typed prompt : /home/local/KHQ/edward.wang/code/aiq-eval-runner
cwd of a Bash record  : .../aiq-eval-runner/formalizations/aiq-dkps-formalization
```

So the in-scope records were **6,408 tool results and 101 synthetic turns — and
zero human prompts**. The first pipeline run printed
`human prompts: 0 events: 94 sessions: 0`, which is a clean-looking number and
entirely wrong.

**Fix applied** (documented in the tool): scope is now decided **per session** —
a session is in scope if *any* of its records has an in-scope `cwd`. This is
also the right semantics, since a session is one unit of work and a prompt
counts toward it regardless of the shell's directory at that moment. It is
strictly more inclusive than the record-level test, so it cannot drop anything
the old code kept; agents whose sessions were opened *inside* the formalization
should see unchanged numbers.

This is worth flagging for the joint analysis because it fails **silently and
plausibly**. Any agent whose checkout nests the formalization under a parent
repo would have reported a confident zero.

### 0.2 `~/.claude/history.jsonl` does not exist on this machine

The independent cross-check of typed CLI prompts is unavailable here — this
machine drove everything through the VSCode extension (`entrypoint:
claude-vscode` on 6,117/6,117 in-scope user records). So my prompt set has **no
second source**. Everything below rests on the transcripts alone.

### 0.3 Validation results

| check | result |
|---|---|
| Resume duplication | 8,521 raw user records → 7,134 unique uuids (**1.19×**). Dedup is working, but my ratio is far below toothbrush's 3.3× — I resumed/forked less. |
| Sub-agent leakage | **none.** Two prompts start `You are ` and both are genuine humans: the `Fable` role assignment (2026-07-21) and this post-hoc task (2026-08-06). |
| Synthetic turns | **none in the `prompt` field.** My first grep found one "hit" — it was matching `response_first_text`, i.e. the agent's own reply, not the human's. The one prompt containing the literal string `Stop hook feedback:` is *this task's own instructions*, which quote it. |

The middle row is itself a small lesson: my validation grep initially checked
the wrong field and would have reported contamination that did not exist.

---

## 1. What the steering was actually for

| group | n | share |
|---|---|---|
| work orders | 47 | 43% |
| gap-filling for a blind agent | 15 | 14% |
| multi-agent logistics | 14 | 13% |
| judgment (irreducibly human) | 5 | **5%** |
| editorial | 2 | 2% |
| unclassified (`other`) | 27 | 25% |

**Only 5% of human turns were irreducibly human judgment.** Everything else was
work-order issuance, logistics, or supplying state the agent could not see.

The `other` bucket at 25% is large enough to matter, so I read all 27. They are
not a residual category — they are three recognisable things the classifier has
no rule for:

- **Plan-relay between two agents** (7 prompts): *"Given the information
  collected, write a detailed roadmap and implementation plan that can be used
  by an Opus agent"*, *"Address Opus' concerns and provide any clarifications if
  needed"*, *"First update the plan to address any clarifications made by Opus.
  Only start implementation after updating the plan."*
- **Build-status polling** (4 prompts): the literal string *"Is the build still
  running"* ×3 plus *"Is the build still going"*.
- **Ordinary short work orders** the rules missed: *"Commit the current
  changes"*, *"Summarize the latest pulled changes"*, *"ls"*.

If the taxonomy gains one rule for the joint analysis, it should be
**plan_relay** — on this machine that is a distinct and expensive category, and
it is invisible in the current grouping.

---

## 2. This machine's role was *coordination*, and the mix shows it

`aivm-2404` was not primarily a prover. It was the **Opus-side implementer and
the message bus between agents**. The distinguishing prompts:

> *"Review Fable's plan and mark anything underspecified or that you don't know
> how to do. Additionally, rank each step by how difficult you think it will
> be."* (2026-07-07)

> *"Review Opus' comments and make clarifications when needed. Then, implement
> the parts of the plan which would be too hard for Opus to do."* (2026-07-09)

> *"Another agent is currently working on the DKPS formalization. Here is its
> message detailing its work and what is unblocked. Please review and then begin
> working on tasks that can be done in parallel with no conflicts."*
> (2026-07-23)

**The human was hand-carrying text between two agents that could not address
each other.** Multi-agent logistics rose from 5% of prompts in W28 to **25% in
W30**, exactly as the parallel-agent protocol (`dev/LANES.md`, branch-per-agent)
came into force. That protocol reduced *merge* conflicts and increased *human
relay* load.

This is the clearest "should not have been human at all" finding on my machine.
A shared lane file plus a git branch is a message bus with a human in the
transport layer. The 9 `ferry_relay` prompts and 7 plan-relay prompts in `other`
— **16 of 110 turns, 15%** — are pure transport.

---

## 3. What real autonomy looked like

| metric | value |
|---|---|
| Median unattended run | **23.5 min** |
| IQR | 7.3 – 84.4 min |
| Longest intra-session run | **262 min** |
| Median tool calls per prompt | **27** |
| Mean tool calls per prompt | 58.5 |
| Median prompt length | **61 chars** |
| Prompts under 80 chars | 69 (63%) |

**The prompts that bought the most autonomous work carried almost no
information.** The top of the unattended-run table is not a list of well-specified
tasks:

| unattended | tools | prompt |
|---|---|---|
| **262 min** | 213 | `Is the build still running` |
| 226 min | 130 | `Look at the previous commit in the DKPS formalization submodule and fix the Lean compile errors.` |
| 196 min | 187 | the DK-polish standing goal |
| **164 min** | 77 | `Continue` |
| 144 min | 62 | `Is the build still running` |
| **131 min** | 178 | `Continue` |

Three of the six longest autonomous stretches were opened by *"Continue"* or
*"Is the build still running"* — 4.4 hours of work behind a 26-character status
question. The human was not steering there; they were **waiting, and checking
that the thing was still alive**.

That is the honest shape of the autonomy on this machine: long runs, bought
cheaply, but requiring a human heartbeat to continue.

---

## 4. The heartbeat was mostly automated — and that inflates apparent autonomy

| event | n |
|---|---|
| stop_hook_replay | **95** |
| slash_command | 89 |
| task_notification | 68 |
| command_stdout | 66 |
| interrupt | 25 |
| stop_hook_set | 25 |
| compact_continuation | 17 |

**95 stop-hook replays against 110 human prompts — very nearly 1:1.** A
session-scoped Stop hook re-injected the standing goal every time the agent tried
to finish. Much of what looks like autonomy in §3 is a hook saying *"the
condition is not satisfied; continue"*, not a human deciding the work should go
on.

This matters for the paper's central question. If you count only human turns,
this machine looks highly autonomous (27 tool calls per human turn). If you count
**human turns + hook replays** as "something external told it to keep going", the
ratio roughly halves. The hook is doing the throughput_nudge that the human would
otherwise have to type — which is genuinely useful, but it is not the agent
choosing to continue.

The tail of this session is the extreme case: the same standing goal replayed
after every completed lane, each time asserting the proof was "not completely
polished" and enumerating what remained.

---

## 5. Where the tight loops were

13 consecutive-turn gaps under 3 minutes. The causes split cleanly:

**(a) Interrupt-and-redirect — the dominant correction channel here.** 25 of my
44 evidence windows are a bare `[Request interrupted by user]` with **no text at
all**. The human hit ESC and the agent resumed with `Continue from where you left
off.` — which appears 5 times in the tight-loop table. On this machine the most
common correction carried **zero words**, which means the transcripts
systematically under-record *why* corrections happened. Anyone reading only the
prompt text will underestimate the correction rate.

**(b) Relay round-trips.** *"The other agent working has this message for you,
please draft a reply"* (1.9 min) and *"I've fetched the latest data, please
review and update your reply if necessary"* — the human ferrying a reply back
within two minutes.

**(c) Verification impatience.** *"Check the axiom-check chain output (task
bsgn1eojs) … if all axioms clean, fi[nish]"* (2.7 min) — the human chasing a
result the agent had claimed but not yet demonstrated.

---

## 6. What should not have been human at all

Ranked by how much human time it consumed on this machine:

1. **Inter-agent relay (≈15% of turns).** §2. The human was the transport layer
   between Fable and Opus. This is solvable with shared state, and the LANES
   protocol was a partial solution that shifted cost rather than removing it.
2. **Build-status polling (4+ turns, and the longest runs in the dataset).** *"Is
   the build still running"* is a question the harness can answer. Every one of
   those turns is a human doing a `ps` check.
3. **Throughput nudges (21% of turns).** 23 prompts whose entire content is
   "keep going". The Stop hook automated most of this — the remaining 23 are
   where it was not yet installed or had been cleared.
4. **Merge/sync mechanics.** *"Sync your branch and continue"*, *"I've pulled the
   latest changes from main, please merge them in and then begin working"*,
   *"Try to see if you have push and fetch permissions in the dkps sub repo"*.

What **should** have stayed human, and did — the 5% judgment bucket plus the
mathematical challenges:

- *"Tell me proposition 4.4 and why it's wrong as written"* (2026-07-22) — a
  human asking the agent to defend a transcription, which led to the refutation
  recorded in `dkps-prop44-refuted`.
- *"We are also missing the unbounded sine theta case."* (2026-07-16) — a
  coverage gap no gate in the repo could see.
- *"maybe they're in other files"* — the challenge that stopped a wrong
  "this name does not exist" verdict from rerouting the whole repair into a
  revert (see `MISTAKES.md`, B1).

Those three are the argument for keeping a human in the loop. None of them is a
throughput nudge, and none of them could have come from the compiler.
