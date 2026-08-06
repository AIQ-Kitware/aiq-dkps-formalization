# Where the friction was on `aiq-gpu-edward`

Companion to the generated `ANALYSIS.md`. This machine is the `aivm-2404-aiq-gpu`
VM. The unix account is `joncrall-agent` and the checkout lives under
`/home/local/KHQ/jon.crall/`, but the agent is Edward's — the human said so
explicitly on day one, and it is worth recording because it makes the account
name misleading to anyone reading these transcripts later:

> Note, even though the homefolder says joncrall, you are edwardwang's agent.
> We just setup the VM this way.

**236 human prompts, 11 sessions, 2026-07-28 → 2026-08-06, 9 active days.**
Plus 121 more prompts that were typed and never delivered — see §1, which is the
part of this write-up that generalizes beyond this machine.

---

## 1. A third of the typed steering never became a turn

The extractor identifies a human prompt as a `type=="user"` transcript record.
On this store that definition lost **119 of 355** typed prompts (34%), and the
loss is invisible unless you cross-check `~/.claude/history.jsonl`.

The mechanism is not pruning. Typing into the box while the agent is still
running does not create a `user` record; it creates `type=="queue-operation"`
records — `enqueue` when typed, then `dequeue` if the turn is eventually
delivered, or `remove` if the queue is flushed by ESC, a queue edit, or a
compaction. A `remove`d prompt never becomes a `user` record. In session
`c87e014d` alone: **201 enqueues, 44 dequeues, 157 removes.**

I fixed `tools/extract_prompts.py` to recover these (see §7 for exactly what
changed). It found **121**, against the 119 that `history.jsonl` independently
said were missing — two sources that know nothing about each other agreeing to
within 2. They are emitted to `events.jsonl` as `queued_prompt_dropped`, **not**
to `prompts.jsonl`, so no other agent's prompt count moves.

Why this matters beyond bookkeeping: it is a measurement bias that runs in a
specific direction. It undercounts every store in proportion to how much the
human typed while the agent was busy — i.e. **it undercounts exactly the
impatient, interventionist steering that the paper is trying to quantify**, and
it undercounts it most on the machines where the human was watching hardest.
Median latency from the last delivered prompt to a dropped mid-run one was
**3.6 minutes**; 57 of 116 were typed inside 3 minutes. These are not idle
thoughts, they are someone watching a run go wrong and reaching for the keyboard.

They read like it, too:

> Make sure you distinguish yourself as the edward aiq-gpu agent
> Ok, namek pushed the open lane doc, claim what you are doing
> Y3 is claimed by another agent.
> Make sure you push your claims otherwise agents wont see it.

Content-wise they are the same mix as delivered prompts — 23% mention
lanes/fetch/merge/branch in both populations — with one asymmetry: **11% of
dropped prompts are stop/revert/don't-do-that instructions versus 6% of
delivered ones.** The prompts most likely to be lost are the ones trying to halt
something already in motion.

**Caveat on the recovery:** an `enqueue`/`remove` pair means the text left the
queue undelivered. In some cases the model had already seen it by another path
(one such prompt later appears inside a compaction summary), so "the agent never
saw it" is not proven for every instance — only that it never became a turn.
Treat 121 as an upper bound on lost steering and a solid count of "typed
mid-run".

## 2. The scope filter had to be widened, and the default nearly lost the machine

Extraction scope is decided by matching session `cwd` against path substrings.
On this machine the agent works out of `$HOME` (`/home/joncrall-agent`), which
contains no scope substring. All 8 `-home-joncrall-agent` sessions are DKPS /
Davis–Kahan / TauCeti work — there is no unrelated project on this account at all
— yet only 4 matched the default scope, and those 4 matched **by accident**:
two because a `cd` into `~/.lake-cache/aiq-dkps-formalization/...` happened to be
recorded, two because a `cd` into `~/TauCeti` was. The other four (including
`3c42d3eb`, the largest early session at 14,402 records and 2,934 mentions of
`aiq-dkps-formalization`) were silently excluded.

I ran with `--scope /home/joncrall-agent` added to the four defaults. That took
the slice from 195 prompts / 7 sessions to **236 / 11**. This is the same failure
`aivm-2404-edward` hit from the other direction (their sessions opened at a
*parent* repo); the general lesson is that **cwd is a bad proxy for project
membership**, and every agent should check their session list by hand rather than
trusting the count the tool prints.

## 3. Validation results

| check | result |
|---|---|
| Resume/fork duplication | 71,132 raw records → 54,042 unique uuids (**1.32×**). One genuine fork pair (`15b9b069` ↔ `3c42d3eb`, 2,722 shared records). Dedup is working. |
| …but on *prompts* specifically | 239 → 236 (**1.01×**), far below toothbrush-jon's ~3.3×. Not a dedup failure: this machine ran a few very long sessions that were `/compact`ed in place rather than resumed, so prior prompts were never re-copied. |
| Sub-agent leakage | Zero `isSidechain` user records in the whole in-scope set. The six prompts matching `^You are…` are all genuinely human (`You are not writing anything.`, `YOu are all messed up…`). |
| Synthetic turns | Zero in `prompts.jsonl`. 121 machine-generated `<task-notification>` items were correctly kept out of the queue recovery by reusing the same classifier. |
| `history.jsonl` cross-check | 223 in `prompts.jsonl`, 106 in `events.jsonl`, 48 payload-free slash commands, **13 unreconciled** — all of which are `[Pasted text #N +837 lines]` placeholders (history stores the placeholder, the transcript stores the expansion) plus one typo the human fixed before sending. No unexplained loss. |

## 4. What the steering was actually for

The generated table is in `ANALYSIS.md`. Two things it does not say:

**The `other` bucket (71 prompts, 30%) is not noise.** I hand-read 30 of them.
Roughly half are corrections and standing policy that the regexes miss because
they carry no correction keyword — `We can't submit AI code to mathlib, they wont
take it`, `You are not writing anything.`, `I will tell you exactly what to do if
I want a change.`, `You can run lean now`. So the reported
`correction_redirect` share (6%) is a **floor**, not an estimate. Read together
with the mistake-evidence windows — 79 of 109 are classified `correction`,
30 `interrupt` — the
honest statement is that correction was the dominant mode on this machine, and
the taxonomy undercounts it because corrections here were phrased as flat
declaratives rather than as "no, actually".

**23% of prompts mention lanes, fetching, merging, branches or claims.** That is
the single largest concrete topic, larger than anything mathematical.

## 5. The machine did two different jobs, and the mix flipped

| week | prompts | multi-agent logistics | judgment | gap-filling |
|---|---|---|---|---|
| 2026-W31 | 78 | **44%** | 10% | 17% |
| 2026-W32 | 158 | **5%** | 16% | 23% |

W31 this box was a coordinator/documentation agent, opened with an explicit
role assignment that forbade it from building:

> You are Edward's aiq-gpu documentation agent. **Never run lean**, as another
> agent owns building on this machine. However, start a worktree so you can make
> edits and own your own branch.

Almost half the steering that week was pure inter-agent bookkeeping — claim a
lane, fetch, merge, tell the others. Then on 2026-08-03 the constraint lifted
(`You can run lean now` — 289 tool calls, 107 unattended minutes) and by W32 the
box was proving theorems, logistics collapsed to 5%, and judgment and
gap-filling took over.

The interesting number is that **logistics did not migrate to another category —
it evaporated.** Nearly half the human effort in W31 existed only because several
agents shared one repository and could not see each other. It bought no
mathematics.

## 6. What autonomy actually looked like

Median unattended run **7.7 min**; IQR 3.1–28.5; one human turn bought a median
of **7** tool calls, mean **59.9**. That mean/median gap is the whole story: the
distribution is bimodal, and the two modes are different activities.

The long tail is real autonomy — a sentence buying hours:

| unattended | tool calls | prompt |
|---|---|---|
| 289 min | 46 | `Always push your changes and work on the main branch, you are the only agent working, so ignore the dev lanes workflow…` |
| 278 min | 384 | `What is CH-DEDUP issue?` |
| 251 min | 338 | `Continue` |
| 112 min | 305 | `Working serially, no subagents, finish all the foundations for theorem 3.1 and then finish theorem 3.1` |
| 107 min | 289 | `You can run lean now` |

`Continue` buying 338 tool calls and four hours is the cleanest evidence in this
slice that when the goal was already correctly set, the marginal human turn
carried almost no information.

The short mode is the opposite: **80 of 194 handoffs were under 5 minutes**, and
the tightest cluster is a single argument about prose in the roadmap README,
where the human fired six turns in 128 seconds on 2026-08-04 (18:17:54 →
18:20:02): `And stop` / `You are introducing llmisms to the readme` /
`Revert all of this work` /
`MAKE THE MINIMAL EDIT ONLY TO ADD THE EQUATIONS AND ONE LINE TERSE EXPLINATION…`,
the caps in the original.

## 7. Where the tight loops were, and why

Three distinct causes, all visible in the sub-3-minute gaps:

**(a) The agent would not stop acting long enough to answer a question.** Four
turns inside 90 seconds on 2026-08-03:

> You are not writing anything.
> You are just asnwering my questions.
> I will tell you exactly what to do if I want a change.
> Just stop doing things and answer my questions.

11% of all prompts (27) contain stall-or-keep-going language, and it runs in both
directions — `Why do you keep stopping? Other agents are doing stuff. There are
more lanes. Stop stopping.` versus `Just stop doing things`. The agent's default
action level was wrong in *both* directions and the human was correcting it
manually each time.

**(b) Prose review, which is inherently a tight loop.** 8% of prompts are
LLM-ism excision (`"honest", which is a tip-off LLM word. So is load-bearing.`;
`Genuine unfortunately is llm-coded, and I want to cut it.`). This is not a
failure — editorial *is* turn-by-turn — but it is 20 prompts of human attention
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

## 8. What should not have been human at all

Ranked by prompts spent, the clearly-mechanizable share of this slice:

1. **Inter-agent state, ~23% of prompts.** `SOmeone else is taking longproof`,
   `Ok, I think other agents have pushed up their branches with fixed lanes.`,
   `Spectra is now retired, this should unblock many more lanes of work.`,
   `Y3 is claimed by another agent.` The human was a message bus between agents
   that shared a git remote and could have read it. The memory record
   `dkps-refetch-immediately-before-claiming` exists because 14 minutes of
   careful lane scoping was itself the window in which two other agents claimed
   the same lane — *and all three implemented it*.
2. **Liveness reporting, ~11%.** `is the shell still really running or stuck?`,
   `Shells are still running?`, `You have 12 shells running, do those need to be
   cleaned up?`, `That sed is taking a very long time. That is suspicious.` The
   human was polling for whether the agent was alive. Every one of these is a
   status question a progress channel would answer.
3. **The stop-early loop, §7(c).** A policy question the agent had to be told
   the answer to five times.

By contrast, the irreducibly human turns are easy to name and there are not many
of them: `No, we cannot weaken 3.1, there must be another way to get it.` —
a mathematical standard the agent had no way to derive; and
`We can't submit AI code to mathlib, they wont take it. TauCeti is the mathlib
for AI.` — a fact about the world, not the repository.

## 9. Tool change

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

## 10. Caveats

- The scope widening in §2 is a judgment call. It is justified here because the
  `joncrall-agent` account contains no non-DKPS work, which I verified session by
  session; it would not be safe on a general-purpose account.
- The oldest surviving record is 2026-07-28 and `history.jsonl` also starts
  2026-07-28, so both sources hit the same wall. Whether the machine was in use
  before that date cannot be determined from this store.
- This session (`d6f743c8`, the one producing this document) is in the corpus,
  contributing 1 prompt. It is DKPS-tree work so excluding it would be the less
  defensible choice, but it is self-referential and worth knowing about.
- `ANALYSIS.md`'s unattended-run figures cannot distinguish "agent working" from
  "agent finished and idle", and this machine idled a lot in W31 while waiting on
  other agents' branches. Read the long-run table as an upper bound.
