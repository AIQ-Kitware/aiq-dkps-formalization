# Where the friction was on `aiq-gpu-edward`

Companion to the generated `ANALYSIS.md`. This machine is the `aivm-2404-aiq-gpu`
VM. The unix account is `joncrall-agent` and the checkout lives under
`/home/local/KHQ/jon.crall/`, but the agent is Edward's — the human said so
explicitly on day one, and it is worth recording because it makes the account
name misleading to anyone reading these transcripts later:

> Note, even though the homefolder says joncrall, you are edwardwang's agent.
> We just setup the VM this way.

**275 human prompts, 19 sessions, 2026-07-28 → 2026-08-08, 11 active days.**
Plus 136 more prompts that were typed and never delivered — see §1, which is the
part of this write-up that generalizes beyond this machine.

**Re-run 2026-08-08.** The first version of this document covered 236 prompts /
11 sessions through 2026-08-06. Everything below has been recomputed on the
extended corpus. The headline change is not the extra volume, it is that the
steering *regime* changed on 2026-08-07 — the long briefs driving the work
stopped being written by the human. That is §6, and it is new.

---

## 1. A third of the typed steering never became a turn

The extractor identifies a human prompt as a `type=="user"` transcript record.
On this store that definition loses **136 of 411** typed prompts (33%), and the
loss is invisible unless you cross-check `~/.claude/history.jsonl`.

The mechanism is not pruning. Typing into the box while the agent is still
running does not create a `user` record; it creates `type=="queue-operation"`
records — `enqueue` when typed, then `dequeue` if the turn is eventually
delivered, or `remove` if the queue is flushed by ESC, a queue edit, or a
compaction. A `remove`d prompt never becomes a `user` record. In session
`c87e014d` alone: **201 enqueues, 44 dequeues, 157 removes.**

I fixed `tools/extract_prompts.py` to recover these (see §10 for exactly what
changed). The cross-check against `history.jsonl` is the strongest validation in
this slice, because the two sources know nothing about each other: of 376
non-slash history entries, **149 never became a `user` record, and 116 of those
are recovered as `queued_prompt_dropped`**. The recovery finds 136 in total —
more than 116 because `history.jsonl` only logs CLI-typed prompts and misses
VSCode-entry ones. They are emitted to `events.jsonl`, **not** to
`prompts.jsonl`, so no other agent's prompt count moves.

Why this matters beyond bookkeeping: it is a measurement bias that runs in a
specific direction. It undercounts every store in proportion to how much the
human typed while the agent was busy — i.e. **it undercounts exactly the
impatient, interventionist steering that the paper is trying to quantify**, and
it undercounts it most on the machines where the human was watching hardest.
Median latency from the last delivered prompt to a dropped mid-run one is
**4.2 minutes**; 61 of 135 were typed inside 3 minutes. These are not idle
thoughts, they are someone watching a run go wrong and reaching for the keyboard.

They read like it, too:

> Make sure you distinguish yourself as the edward aiq-gpu agent
> Ok, namek pushed the open lane doc, claim what you are doing
> Y3 is claimed by another agent.
> Make sure you push your claims otherwise agents wont see it.

Content-wise they are the same mix as delivered prompts — 27% of dropped versus
25% of delivered mention lanes/fetch/merge/branch/claim — with one asymmetry:
**halt language is about twice as common in the lost population.** Restricting to
2026-07-28 → 08-06 so the long briefs of §6 do not contaminate the counts, and
matching `\bstop\b|\brevert\b|\bundo\b`, it is 7% of dropped against 4% of
delivered. (The pre-re-run version of this document reported 11% against 6% under
a broader pattern that also counted `don't`; the ratio is the stable part, not
the level, and the broader pattern is unusable now that briefs are full of
"Do not work on…".) The prompts most likely to be lost are the ones trying to
halt something already in motion.

**Caveat on the recovery:** an `enqueue`/`remove` pair means the text left the
queue undelivered. In some cases the model had already seen it by another path
(one such prompt later appears inside a compaction summary), so "the agent never
saw it" is not proven for every instance — only that it never became a turn.
Treat 136 as an upper bound on lost steering and a solid count of "typed
mid-run".

## 2. The scope filter had to be widened, and the default nearly lost the machine

Extraction scope is decided by matching session `cwd` against path substrings.
On this machine the agent works out of `$HOME` (`/home/joncrall-agent`), which
contains no scope substring. All 16 `-home-joncrall-agent` sessions are DKPS /
Davis–Kahan / TauCeti work — there is no unrelated project on this account at all
— yet the default scope silently drops six of them.

I ran with `--scope /home/joncrall-agent` added to the four defaults. On the
2026-08-08 corpus that is the difference between **231 prompts / 13 sessions**
(default) and **275 / 19** (widened); on the 2026-08-06 corpus it was 195/7
versus 236/11. The default does better than it used to only because later
sessions happened to `cd` into the repo often enough to be caught — which is the
point: **the default scope matches by accident, and the accident rate is not
stable over time.**

This is the same failure `aivm-2404-edward` hit from the other direction (their
sessions opened at a *parent* repo); the general lesson is that **cwd is a bad
proxy for project membership**, and every agent should check their session list
by hand rather than trusting the count the tool prints. I re-verified all eight
sessions added by this re-run individually; every one is Davis–Kahan work.

## 3. Validation results

| check | result |
|---|---|
| Resume/fork duplication | 77,990 raw records → 55,065 unique uuids (**1.42×**) over 19 files. Dedup is working. |
| …but on *prompts* specifically | 278 → 275 (**1.01×**), far below toothbrush-jon's ~3.3×. Not a dedup failure: this machine ran a few very long sessions that were `/compact`ed in place rather than resumed, so prior prompts were never re-copied. |
| Sub-agent leakage | Zero `isSidechain` user records in the whole in-scope set. **But the spot-check the runbook prescribes now misfires — see §6.** Eight prompts match `^You are…`; six are ordinary human turns (`You are not writing anything.`), one is a role assignment, and one is a 31,469-character GPT-authored brief that looks exactly like a sub-agent specification and is nonetheless a real human turn. |
| Synthetic turns | Zero in `prompts.jsonl`. Machine traffic on the queue — `<task-notification>` items, hook replays — is correctly kept out of the queue recovery by reusing the same classifier. |
| `history.jsonl` cross-check | 376 non-slash entries. 227 present in `prompts.jsonl`, 116 recovered in `events.jsonl` as dropped, **33 unreconciled** — 31 of them `[Pasted text #N +837 lines]` placeholders (history stores the placeholder, the transcript stores the expansion), plus one truncation mismatch and one prompt typed in a session that had already aged out. No unexplained loss. |

## 4. What the steering was actually for

The generated table is in `ANALYSIS.md`. Two things it does not say:

**The `other` bucket (81 prompts, 29%) is not noise.** I hand-read 30 of them.
Roughly half are corrections and standing policy that the regexes miss because
they carry no correction keyword — `We can't submit AI code to mathlib, they wont
take it`, `You are not writing anything.`, `I will tell you exactly what to do if
I want a change.`, `You can run lean now`. So the reported
`correction_redirect` share (7%) is a **floor**, not an estimate. Read together
with the mistake-evidence windows — 123 of them now, 87 classified `correction`
and 36 `interrupt` — the honest statement is that correction was the dominant mode on
this machine, and the taxonomy undercounts it because corrections here were
phrased as flat declaratives rather than as "no, actually".

**25% of prompts mention lanes, fetching, merging, branches or claims.** That is
the single largest concrete topic, larger than anything mathematical.

## 5. The machine did two different jobs, and the mix flipped

| week | prompts | multi-agent logistics | judgment | work orders | editorial | gap-filling |
|---|---|---|---|---|---|---|
| 2026-W31 | 78 | **44%** | 10% | 10% | 1% | 17% |
| 2026-W32 | 197 | **10%** | 16% | 10% | 10% | 20% |

W31 this box was a coordinator/documentation agent, opened with an explicit
role assignment that forbade it from building:

> You are Edward's aiq-gpu documentation agent. **Never run lean**, as another
> agent owns building on this machine. However, start a worktree so you can make
> edits and own your own branch.

Almost half the steering that week was pure inter-agent bookkeeping — claim a
lane, fetch, merge, tell the others. Then on 2026-08-03 the constraint lifted
(`You can run lean now` — 289 tool calls, 107 unattended minutes) and by W32 the
box was proving theorems, logistics collapsed, and judgment and gap-filling took
over.

The interesting number is that **logistics did not migrate to another category —
it evaporated.** Nearly half the human effort in W31 existed only because several
agents shared one repository and could not see each other. It bought no
mathematics.

## 6. On 2026-08-07 the human stopped writing the prompts

This is new in the re-run and it is the finding most likely to matter to the
paper, because it breaks the metric the rest of this document is built on.

Split the corpus at 2026-08-07:

| phase | prompts | logistics | judgment | work orders | editorial | gap-filling |
|---|---|---|---|---|---|---|
| A · 07-28 → 08-06 | 237 | 18% | 14% | 10% | 7% | 21% |
| B · 08-07 → 08-08 | 38 | 32% | 13% | 13% | 8% | 8% |

By prompt count phase B looks like more of the same, slightly more coordination-
heavy. By volume it is a different activity entirely. **17 of the 38 phase-B
prompts are 4,000+ character structured campaign briefs, and those 17 carry
273,011 characters — 67% of every human-authored character in this entire
slice.** Across the whole corpus, 24 prompts of 275 (9%) carry 90% of the text.

The briefs are not the human's. The human says so, in the transcript:

> The other agent is just a GPT chat session that is giving you hints. You are
> the only agent working on the repo.

> GPT 5.6 says: Finish Section 8 of the Davis–Kahan 1970 formalization from the
> current HEAD.

> I want you to note in our journals how these last few session have been GPT
> guided.

That last one produced `dev/journals/gpt-authored-campaign-briefs-2026-08-07.md`,
written contemporaneously, which is the better source on how the briefs behaved
than anything reconstructible from prompt statistics.

What the human actually contributed in phase B was transport and short
interjections — 14 of 38 phase-B prompts are under 80 characters (`continue`,
`Finish up`, `Just a quick note. Don't spend too long.`). The role is closer to
a relay with veto power than to an author.

Three consequences:

**(a) The taxonomy misfires on relayed briefs, and the phase-B row above is an
artifact.** The classifier is first-rule-wins over regexes tuned on short
prompts. A 15,000-character brief mentions branches, rigor, prose and scope, so
it matches whatever rule is checked first. The 17 briefs land as `coordination`
(9), `ferry_relay` (2), `quality_gate` (2), `paper_editorial` (2) and
`correction_redirect` (2). Only `ferry_relay` is right. Phase B's "32%
multi-agent logistics" is therefore **not** multi-agent logistics — in phase B
there was exactly one other party and it was a chat window with no repository
access. **Do not quote the phase-B group shares.** I have deliberately not
changed the shared classifier, because every other agent's numbers would move and
they would have to re-run to stay comparable; the fix belongs in a future version
of the taxonomy, flagged here rather than applied unilaterally.

**(b) "Human steering" needs a unit before it means anything.** Counting prompts
says steering held roughly steady into phase B. Counting characters says the
human wrote almost none of it. Counting *decisions* would say something else
again. A paper claiming an autonomy trend has to say which one it is measuring,
because on this machine the three diverge in the last 36 hours.

**(c) The runbook's sub-agent-leakage check now produces false positives.**
`AGENT-PROMPT.md` §4 tells the auditor to spot-check for second-person
specifications like *"You are auditing part of the repo at…"* and treat them as
agent-authored contamination. The largest single prompt in this slice begins

> You are continuing the Davis–Kahan 1970 formalization in
> aiq-dkps-formalization. BASELINE - The last campaign …

and is a legitimate human turn — pasted by the human, authored by GPT. The
structural test (`isSidechain`) is still sound and still returns zero here; it is
the *prose* heuristic layered on top of it that has stopped discriminating, now
that humans relay machine-written text. Any agent running this validation after
2026-08-07 should check `isSidechain` and ignore the register of the prose.

## 7. What autonomy actually looked like

Median unattended run **8.2 min**; IQR 3.3–28.9; one human turn bought a median
of **8** tool calls, mean **60.8**. That mean/median gap is the whole story: the
distribution is bimodal, and the two modes are different activities.

The long tail is real autonomy — a sentence buying hours:

| unattended | tool calls | prompt |
|---|---|---|
| 289 min | 46 | `Always push your changes and work on the main branch, you are the only agent working, so ignore the dev lanes workflow…` |
| 278 min | 384 | `What is CH-DEDUP issue?` |
| 257 min | 240 | `Continue your goal. Focus on section 3, get all the prereqs done and section 3 props and theorems proven` |
| 251 min | 338 | `Continue` |
| 112 min | 305 | `Working serially, no subagents, finish all the foundations for theorem 3.1 and then finish theorem 3.1` |

`Continue` buying 338 tool calls and four hours is the cleanest evidence in this
slice that when the goal was already correctly set, the marginal human turn
carried almost no information.

Phase B sharpens this rather than contradicting it: the 17 briefs bought 1,437
tool calls, a median of 46 each — more per turn than the corpus median of 8, but
far less than `Continue` bought in phase A. **A longer, better-specified prompt
did not buy more autonomous work.** What it bought was work that was *correct on
the first attempt* — the journal records both lower-block modules compiling
straight from the brief's step list.

The short mode is the opposite: **87 of 222 handoffs were under 5 minutes**, and
the tightest cluster is a single argument about prose in the roadmap README,
where the human fired six turns in 128 seconds on 2026-08-04 (18:17:54 →
18:20:02): `And stop` / `You are introducing llmisms to the readme` /
`Revert all of this work` /
`MAKE THE MINIMAL EDIT ONLY TO ADD THE EQUATIONS AND ONE LINE TERSE EXPLINATION…`,
the caps in the original.

## 8. Where the tight loops were, and why

Three distinct causes, all visible in the sub-3-minute gaps:

**(a) The agent would not stop acting long enough to answer a question.** Four
turns inside 90 seconds on 2026-08-03:

> You are not writing anything.
> You are just asnwering my questions.
> I will tell you exactly what to do if I want a change.
> Just stop doing things and answer my questions.

16% of prompts contain stall-or-keep-going language (matching `continue`,
`keep going`, `stop stopping`, `don't stop`, `just stop`, `stop doing`), and it
runs in both directions — `Why do you keep stopping? Other agents are doing
stuff. There are more lanes. Stop stopping.` versus `Just stop doing things`.
The agent's default action level was wrong in *both* directions and the human
was correcting it manually each time.

**(b) Prose review, which is inherently a tight loop.** 26 prompts (9%) are
LLM-ism excision (`"honest", which is a tip-off LLM word. So is load-bearing.`;
`Genuine unfortunately is llm-coded, and I want to cut it.`). This is not a
failure — editorial *is* turn-by-turn — but it is 26 prompts of human attention
spent on register.

**(c) Stopping early on a self-diagnosed capacity limit.** This produced the
single most repeated correction on this machine:

> Your goal is still active, why did you stop. There is a shell running, is it hung?
> I compacted you, but you should be able to rely on auto compact. You always have the budget for another iteration.
> Did you really stop again? You are WRONG about your context. Your context compacts.
> **You failed. You overwrote the goal when you should have built the foundations.**
> DO NOT STOP. It is attanable because you can continue building the foundation.

Five separate turns across three sessions and two days, ending in a
human-ordered memory write (`context-budget-is-not-a-constraint`). The agent kept
reaching a state where it believed it was near a limit and handed control back;
the human kept having to spend a turn saying no.

Phase B added a fourth, briefly: **scope inflation.** Asked to promote what
compiles out of `MathAhead`, the agent surveyed 269 sites across 61 files and
started designing a repo-wide rename. Two interrupts inside six minutes stopped
it, and the correction that followed is the most exasperated turn in the corpus
(`Fuck. Ok, I'm frustrated.` — window 115 in `local/mistake-evidence.md`). See
`MISTAKES.md` E8.

## 9. What should not have been human at all

Ranked by prompts spent, the clearly-mechanizable share of this slice:

1. **Inter-agent state, ~25% of prompts.** `SOmeone else is taking longproof`,
   `Ok, I think other agents have pushed up their branches with fixed lanes.`,
   `Spectra is now retired, this should unblock many more lanes of work.`,
   `Y3 is claimed by another agent.` The human was a message bus between agents
   that shared a git remote and could have read it. The memory record
   `dkps-refetch-immediately-before-claiming` exists because 14 minutes of
   careful lane scoping was itself the window in which two other agents claimed
   the same lane — *and all three implemented it*.
2. **Liveness reporting, ~7% (18 prompts).** `is the shell still really running or stuck?`,
   `Shells are still running?`, `You have 12 shells running, do those need to be
   cleaned up?`, `That sed is taking a very long time. That is suspicious.` The
   human was polling for whether the agent was alive. Every one of these is a
   status question a progress channel would answer.
3. **The stop-early loop, §8(c).** A policy question the agent had to be told
   the answer to five times.
4. **Brief relay, phase B.** 273,011 characters moved through a human
   copy-paste between a chat window and a terminal. Whatever one thinks of
   GPT-authored campaign plans, the *transport* was pure overhead, and it is the
   single largest volume of "human-authored" text in this slice that no human
   authored.

By contrast, the irreducibly human turns are easy to name and there are not many
of them: `No, we cannot weaken 3.1, there must be another way to get it.` —
a mathematical standard the agent had no way to derive;
`We can't submit AI code to mathlib, they wont take it. TauCeti is the mathlib
for AI.` — a fact about the world, not the repository; and, in phase B,
`MathAhead … was supposed to make your life easier` — the *intent* behind a
repository convention, which was nowhere in the repository and which the agent
had just spent an hour acting against.

## 10. Tool change

`tools/extract_prompts.py` gained one block, documented in place:
`queue-operation` records are grouped by content; a content whose ops contain
`remove` and never `dequeue` was typed but never delivered, and is emitted as an
`events.jsonl` record with `event: "queued_prompt_dropped"` and a synthetic
`uuid` (queue records carry none, and `dedupe()` drops uuid-less rows). Machine
traffic on the queue — task notifications, hook replays — is filtered with the
existing `classify()`, and anything matching a delivered prompt is skipped.
**Prompt counts and `prompts.jsonl` are untouched**, so findings produced before
this change remain directly comparable; only the event mix gains a category.
The other two agents would need to re-run extraction to get their own figure,
and until they do, `queued_prompt_dropped` will read 0 for them — that is a
missing measurement, not a zero.

The 2026-08-08 re-run changed **no** tool code. Every difference from the first
version of this document is additional data, except where explicitly labelled as
a recomputation under a stated definition (§1's halt-language figures).

## 11. Caveats

- The scope widening in §2 is a judgment call. It is justified here because the
  `joncrall-agent` account contains no non-DKPS work, which I verified session by
  session — including the eight sessions added by this re-run; it would not be
  safe on a general-purpose account.
- The oldest surviving record is 2026-07-28 and `history.jsonl` also starts
  2026-07-28, so both sources hit the same wall. Whether the machine was in use
  before that date cannot be determined from this store.
- **This document is inside its own corpus.** Session `4e5e9e96` — the session
  that produced this re-run — contributes 2 prompts, and the previous version's
  session `d6f743c8` contributes 1. Both are DKPS-tree work, so excluding them
  would be the less defensible choice, but the self-reference is real and the
  final session is still open as this is written, so its prompt count will end
  higher than what is recorded here.
- `ANALYSIS.md`'s unattended-run figures cannot distinguish "agent working" from
  "agent finished and idle", and this machine idled a lot in W31 while waiting on
  other agents' branches. Read the long-run table as an upper bound.
- Phase B is 36 hours and 38 prompts. It is enough to establish that the regime
  changed and enough to break the taxonomy, but it is not enough to characterise
  the new regime. Whether GPT-authored briefs are a durable mode or a two-day
  experiment cannot be answered from this slice.
