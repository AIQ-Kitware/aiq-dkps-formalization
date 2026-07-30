# `dev/topurge/` — staged, and deliberately left in place

> **DECISION — jon, 2026-07-30: leave this directory. Do not delete it, and do
> not propose deleting it again.**
>
> The review pass it was staged for is finished: the three wrongly-swept files
> were restored on 2026-07-29 and everything else here was re-checked against
> the "does its *analysis* still bind" test. The outcome is that these 79 files
> stay where they are.
>
> **Agents: this is not an open task.** It was raised four times across one
> session before the decision was made; the cost of raising it again is another
> round of that. Five live documents cite paths under `dev/topurge/` for
> superseded detail, and those pointers now resolve permanently rather than
> pending a deletion.


Everything here was moved out of `dev/` or `docs/` by lane D1 on 2026-07-29
(`jon (yardrat)`), because it read as current documentation while describing
work that has since been finished, abandoned, or superseded.

**Nothing here has been deleted, and nothing will be.** Each file sits at its
original path under `dev/topurge/`, moved with `git mv`, so the diff is
rename-only and every file keeps its full history. The directory existed to make
one review pass cheap — skim it, pull back anything that should not have gone.
That pass ran; three files came back; the rest stay here as a labelled archive.

## Why this happened

`dev/` and `docs/` carried 169 tracked markdown files, about 1.9 MB. Roughly half
were single-commit, zero-inbound-reference notes written during the
2026-07-18…07-24 Davis--Kahan campaign, before the dual-track Tau Ceti policy
replaced the "finish the paper first, migrate second" gate.

That is not a cosmetic problem. `HANDOFF-toothbrush-2026-07-29.md` recorded two
lane reversals in a single session that were **caused** by documentation which no
longer matched practice, and asked for a cleanup lane of its own. This is that
lane.

## Restoring a file

```bash
git mv dev/topurge/<path> <path>
```

`<path>` is the file's original location — it is exactly the path under
`dev/topurge/`.

A handful of surviving documents carry an explicit `dev/topurge/…` pointer where
a link used to resolve, so a reader who needs the superseded detail can still
find it. **Those pointers are permanent and correct** — they resolve today and
will keep resolving. `git grep topurge` finds them all.

## What was NOT purged, and why

Purge-by-default was applied with a hard allowlist. A file stayed put, no matter
how old, if any of the following held:

- a script under `scripts/` reads it or generates it — e.g.
  `dev/davis-kahan-hidden-foundations-status.md` is the *output* of
  `scripts/check_davis_kahan_hidden_foundations.py`;
- it is listed in a manifest a script validates for existence — the five
  markdown paths in `dev/overlays/pending-mathahead-rebased-53297a4-gpt56.manifest.txt`
  are checked by `scripts/check_davis_kahan_rebased_mathahead.py`;
- a Lean source, `AGENTS.md`, `README.md`, or `lakefile.toml` points at it;
- a live coordination doc that this lane is not allowed to edit points at it —
  `dev/tauceti/extraction-cluster-classification.md` is held by another agent's
  row, so the three inventories it links stayed;
- it is cross-referenced from `papers/` or `prose/` manifests, which are outside
  this lane.

`docs/planning/historical/` was left intact on purpose. It is already a labelled
archive, its `README.md` explains each file's disposition, and
`prose/distilled_literature/source_manifest.json` — validated by
`scripts/check_distilled_literature_index.py` — names a file inside it. It is not
what made the tree confusing; unlabelled stale notes in `dev/` were.

## Second review pass — 2026-07-29, `edward (aiq-gpu)` lane COORD

**Three files restored. The allowlist was right; it just could not see them.**

The rule "it is listed in a manifest a script validates for existence" was
applied to *paths*. These were named as a **string**, in the live
`roadmap_target` field of `dev/tauceti/extraction-manifest.json` — the manifest
`scripts/refresh_tauceti_pr1_consistency.py` validates:

> `SpectralSubspacePerturbation Part B (Approximation numbers and rectangular
> symmetric ideals) / public-api-integration-review PR 1`

No path resolution could catch that, which makes it the same trap this
repository already documents for declaration names: **something asserted as
data, where no checker looks.**

| restored | to | why |
|---|---|---|
| `dev/tauceti/SpectralSubspacePerturbation/README.md` | `ForTauCetiRoadmap/SpectralSubspacePerturbation/README.md` | It **is a Tau Ceti roadmap draft** — it says so in its own first section. `AGENTS.md` says roadmaps are drafted in `ForTauCetiRoadmap/`, so it is restored *there*, not to `dev/tauceti/`. Purging the roadmap for the cluster the live manifest points at, while the project's goal is to generate polished roadmaps, was backwards. |
| `dev/tauceti/SpectralSubspacePerturbation/Suggested.lean.md` | alongside it | The API sketch its README calls definitive-modulo-prose. Matches the `ApproximationNumbers/Suggested.lean` pattern. |
| `dev/tauceti/public-api-integration-review.md` | `dev/tauceti/` (original path) | Its analysis binds under this file's own restoration lesson. It specifies *API shape* — generic mathematics in canonical namespaces, paper numbering in source-facing wrappers, one roadmap target per PR — which transfers to Tau Ceti unchanged. Its `ForMathlib` namespace section is now directly load-bearing for lane `FM-RETIRE`. |

Everything else in this directory was re-checked against the same lesson and
stays purged.

## Judgement calls worth a second look

These are the moves most likely to be wrong. Check these first.

- **`dev/sorry-difficulty-ranking.md`** (92 KB, 10 commits) — the largest single
  file moved. Superseded by `dev/tauceti/experimental-sorry-triage.md`
  (2026-07-24), which is newer, is scoped to where the remaining work actually
  lives, and carries the owner's standing decision that the 18 INVESTIGATE items
  are KEEP. The ranking was still linked from
  `docs/planning/davis-kahan-full-paper-goal.md`; that link now points at the
  triage.
- ~~`docs/planning/prep_mathlib_review_and_readiness.md`~~ — **RESTORED
  2026-07-29 (jon), and the reasoning that purged it was wrong.** I moved it as
  Mathlib-track material and wrote that it would be worth keeping "if the
  Mathlib track is ever reopened." It will not reopen — but **Tau Ceti holds a
  comparable bar**, so the readiness checklist, per-candidate reviewer
  objections, readiness ratings and PR sequencing transfer as-is; only the
  destination library changed. It now lives at
  `docs/planning/upstream-readiness-audit.md`, renamed off the dead track and
  retargeted. **The lesson for the rest of this review: judge a document by
  whether its *analysis* still binds, not by whether its stated destination is
  still live.** Anything else here purged on "aimed at Mathlib" grounds deserves
  the same second look.
- **`docs/planning/fable-options.md`** — **re-checked 2026-07-29 under the
  lesson above, and it stays purged.** It differs in kind from the readiness
  audit: that one analyses *how a reviewer receives a result*, which transfers to
  Tau Ceti unchanged, while this one ranks *which task to pick next* under a
  priority that no longer holds. Items 1 and 2 are marked DONE in the file
  itself, items 3–5 are explicitly "marginal or disproportionate effort, not
  recommended", and task selection is now the lane system's job. Nothing in it
  binds.
- **`dev/full-unbounded-sin-theta/README.md`** — a completion guide whose stated
  audit gate, `SinTheta/FullUnboundedAudit.lean`, does not exist anywhere in the
  tree, while its target endpoints have reached production
  (`DavisKahan/SinTheta/Unbounded/AllGap.lean`). Stale on its own gate.
- **`dev/tauceti/experimental-promotion-roadmap.md`** (15 KB, 6 commits) — an
  overnight worklist, not a reference. Moved as spent, but it is the most
  substantial `dev/tauceti/` file to go.
- **`dev/handoff-2026-07-24-frontier.md`** and
  **`dev/circle-riesz-lane-status-2026-07-23.md`** — session handoffs whose
  contents landed. They name a repository path that no longer applies
  (`/home/joncrall/code/aiq-dkps-formalization`).

## Categories

### Overlay delivery receipts (`dev/overlays/`) — 15 files, 66 KB

| file | last commit | commits | size |
|---|---|---|---|
| `dev/overlays/free-beam-hard-theory-scratch-dfd9d37-gpt56.md` | 2026-07-24 | 2 | 10 KB |
| `dev/overlays/full-frontier-scaffold-gpt56.md` | 2026-07-22 | 1 | 3 KB |
| `dev/overlays/independent-scratch-continuation-4080ec3-gpt56.md` | 2026-07-23 | 1 | 6 KB |
| `dev/overlays/independent-scratch-lanes-4080ec3-gpt56.md` | 2026-07-23 | 1 | 3 KB |
| `dev/overlays/milestone-first-opus-plan-dfd9d37-gpt56.md` | 2026-07-23 | 1 | 1 KB |
| `dev/overlays/namek-lake-build-report-b2ea942-gpt56.md` | 2026-07-23 | 1 | 1 KB |
| `dev/overlays/namek-lake-build-report-batch-progress-b2ea942-gpt56.md` | 2026-07-27 | 1 | 1 KB |
| `dev/overlays/namek-operatorabs-final-fix-b2ea942-gpt56.md` | 2026-07-27 | 2 | 1 KB |
| `dev/overlays/namek-operatorabs-namespace-repair-b2ea942-gpt56.md` | 2026-07-27 | 2 | 1 KB |
| `dev/overlays/namek-shared-ideal-compile-repair-b2ea942-gpt56.md` | 2026-07-27 | 1 | 1 KB |
| `dev/overlays/namek-twoway-namespace-fix-b2ea942-gpt56.md` | 2026-07-27 | 1 | 1 KB |
| `dev/overlays/section4-independent-scratch-7f9f562-gpt56.md` | 2026-07-23 | 1 | 3 KB |
| `dev/overlays/shared-hard-foundations-dfd9d37-gpt56.md` | 2026-07-23 | 1 | 8 KB |
| `dev/overlays/sintheta-general-current-api-ee5673e-gpt56.md` | 2026-07-23 | 1 | 3 KB |
| `dev/overlays/sylvester-semigroup-mathpass-gpt56.md` | 2026-07-22 | 1 | 19 KB |

### One-off agent / compiler prompts — 14 files, 49 KB

| file | last commit | commits | size |
|---|---|---|---|
| `dev/namek-lake-build-report-batch-progress-compiler-prompt.md` | 2026-07-27 | 1 | 1 KB |
| `dev/namek-lake-build-report-compiler-prompt.md` | 2026-07-23 | 1 | 1 KB |
| `dev/namek-nonacute-direct-rotation-scratch-compiler-prompt.md` | 2026-07-27 | 1 | 1 KB |
| `dev/namek-operatorabs-final-fix-compiler-prompt.md` | 2026-07-27 | 1 | 1 KB |
| `dev/namek-operatorabs-namespace-repair-compiler-prompt.md` | 2026-07-23 | 1 | 1 KB |
| `dev/namek-section4-proposition41-hard-math-compiler-prompt.md` | 2026-07-27 | 1 | 1 KB |
| `dev/namek-section7-infinite-tan2-core-compiler-prompt.md` | 2026-07-27 | 1 | 1 KB |
| `dev/namek-shared-ideal-compile-repair-compiler-prompt.md` | 2026-07-27 | 1 | 1 KB |
| `dev/namek-twoway-namespace-fix-compiler-prompt.md` | 2026-07-27 | 1 | 1 KB |
| `dev/opus-next-agent-prompt.md` | 2026-07-23 | 1 | 5 KB |
| `dev/opus-polar-extraction-agent-prompt.md` | 2026-07-23 | 1 | 2 KB |
| `dev/real-route-completion-prompt.md` | 2026-07-19 | 2 | 12 KB |
| `dev/shared-hard-foundations-compiler-prompt.md` | 2026-07-23 | 1 | 2 KB |
| `dev/sin-theta-admission-elimination-prompt.md` | 2026-07-19 | 1 | 16 KB |

### Superseded Tau Ceti working notes (`dev/tauceti/`) — 6 files, 40 KB

| file | last commit | commits | size |
|---|---|---|---|
| `dev/tauceti/SpectralSubspacePerturbation/README.md` | 2026-07-20 | 1 | 10 KB |
| `dev/tauceti/SpectralSubspacePerturbation/Suggested.lean.md` | 2026-07-20 | 1 | 2 KB |
| `dev/tauceti/experimental-promotion-roadmap.md` | 2026-07-24 | 6 | 15 KB |
| `dev/tauceti/guidance-issue-draft.md` | 2026-07-20 | 1 | 3 KB |
| `dev/tauceti/public-api-integration-review.md` | 2026-07-27 | 3 | 5 KB |
| `dev/tauceti/source-sine-theta-completion-audit.md` | 2026-07-20 | 1 | 3 KB |

### Superseded planning docs (`docs/planning/`) — 2 files, 15 KB

| file | last commit | commits | size |
|---|---|---|---|
| `docs/planning/fable-options.md` | 2026-06-12 | 2 | 5 KB |
| `docs/planning/opus-next-polar-extraction-campaign.md` | 2026-07-23 | 1 | 10 KB |

### Dated Davis--Kahan campaign notes (`dev/`) — 40 files, 318 KB

| file | last commit | commits | size |
|---|---|---|---|
| `dev/angle-coordinate-redesign-compiler-handoff-2026-07-20.md` | 2026-07-20 | 1 | 5 KB |
| `dev/circle-riesz-lane-status-2026-07-23.md` | 2026-07-23 | 2 | 9 KB |
| `dev/column-expansion-and-finite-multiplicity-math-ahead-2026-07-20.md` | 2026-07-20 | 1 | 5 KB |
| `dev/compile-repair-rebase-note-2026-07-20.md` | 2026-07-20 | 7 | 9 KB |
| `dev/continuation-close-projections-2026-07-18.md` | 2026-07-18 | 1 | 1 KB |
| `dev/davis-kahan-1970-flawless-sine-theta-handoff-2026-07-19.md` | 2026-07-20 | 2 | 7 KB |
| `dev/davis-kahan-1970-full-sine-theta-specification-2026-07-19.md` | 2026-07-20 | 1 | 6 KB |
| `dev/davis-kahan-1970-sine-theta-correspondence-2026-07-19.md` | 2026-07-20 | 3 | 5 KB |
| `dev/davis-kahan-theorem62-hard-front-2026-07-19.md` | 2026-07-20 | 1 | 7 KB |
| `dev/final-finite-part-iii-math-ahead-2026-07-21.md` | 2026-07-21 | 1 | 2 KB |
| `dev/finite-coordinate-tangent-singular-values-2026-07-20.md` | 2026-07-20 | 1 | 2 KB |
| `dev/finite-sharpness-correction-2026-07-20.md` | 2026-07-21 | 1 | 1 KB |
| `dev/full-part-iii-admission-elimination-agent-prompt-2026-07-20.md` | 2026-07-20 | 2 | 4 KB |
| `dev/full-part-iii-admission-elimination-math-ahead-2026-07-20.md` | 2026-07-20 | 2 | 8 KB |
| `dev/full-part-iii-experimental-closure-2026-07-21.md` | 2026-07-21 | 1 | 3 KB |
| `dev/full-part-iii-math-ahead-restoration-manifest-2026-07-20.md` | 2026-07-21 | 8 | 3 KB |
| `dev/full-part-iii-staged-repair-agent-prompt-2026-07-20.md` | 2026-07-20 | 1 | 2 KB |
| `dev/full-part-iii-staged-repair-plan-2026-07-20.md` | 2026-07-20 | 1 | 7 KB |
| `dev/full-unbounded-sin-theta/README.md` | 2026-07-20 | 2 | 10 KB |
| `dev/general-sin-theta-extension-handoff-2026-07-19.md` | 2026-07-19 | 1 | 6 KB |
| `dev/general-sine-theta-direct-spectra-production-plan-2026-07-20.md` | 2026-07-20 | 1 | 10 KB |
| `dev/halmos-two-projection-survey-2026-07-18.md` | 2026-07-18 | 1 | 4 KB |
| `dev/handoff-2026-07-24-frontier.md` | 2026-07-24 | 1 | 7 KB |
| `dev/mathlib-reducing-restriction-extraction-2026-07-19.md` | 2026-07-19 | 1 | 3 KB |
| `dev/namek/SESSION-CLOCK.md` | 2026-07-28 | 1 | 1 KB |
| `dev/paper-hilbert-schmidt-history-recovery-2026-07-20.md` | 2026-07-20 | 2 | 3 KB |
| `dev/paper-sharpness-frobenius-repair-note-2026-07-20.md` | 2026-07-20 | 1 | 3 KB |
| `dev/paper-theorem62-defect-first-architecture-2026-07-19.md` | 2026-07-20 | 1 | 8 KB |
| `dev/paper-theorem62-math-ahead-handoff-2026-07-19.md` | 2026-07-20 | 1 | 9 KB |
| `dev/real-operator-angle-complexification-survey-2026-07-18.md` | 2026-07-18 | 1 | 1 KB |
| `dev/real-route-status-2026-07-19.md` | 2026-07-19 | 2 | 13 KB |
| `dev/real-spectral-subspace-descent-audit-2026-07-19.md` | 2026-07-19 | 1 | 9 KB |
| `dev/rectangular-schatten-compiler-handoff-2026-07-20.md` | 2026-07-20 | 1 | 10 KB |
| `dev/resolvent-distance-bound-2026-07-18.md` | 2026-07-19 | 1 | 1 KB |
| `dev/resolvent-path-lipschitz-2026-07-18.md` | 2026-07-19 | 1 | 1 KB |
| `dev/resolvent-spectral-parameter-lipschitz-2026-07-18.md` | 2026-07-19 | 1 | 1 KB |
| `dev/sine-theta-move-manifest-2026-07-20.md` | 2026-07-20 | 5 | 14 KB |
| `dev/sorry-difficulty-ranking.md` | 2026-07-21 | 10 | 92 KB |
| `dev/stage1-finite-dimensional-infrastructure-math-ahead-2026-07-20.md` | 2026-07-20 | 1 | 3 KB |
| `dev/sylvester-analytic-frontier-closure-2026-07-23.md` | 2026-07-23 | 1 | 7 KB |


## Two families that need no second look

**Overlay delivery receipts.** Every file in the first table is a receipt for a
zip drop applied at a commit that is now weeks old (`b2ea942`, `dfd9d37`,
`7f9f562`, `4080ec3`, `53297a4`, `9e2557`, `ee5673e`). Six of them name a target
worktree, `/home/joncrall/code/aiq-dkps-namek`, that is not this checkout. The
overlays were applied; the scratch files they delivered are in the tree; the
receipts describe how to apply them again to a repository state that no longer
exists. The four whose promotion instructions are still live were kept, plus
their paired `.manifest.txt` files.

**One-off agent and compiler prompts.** Task briefs written for a single
session, naming commits and worktrees that have moved on. They are not
instructions to anybody now.
