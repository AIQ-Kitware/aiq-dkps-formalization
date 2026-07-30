# `dev/audit/` — the hostile review

**COMPLETE 2026-07-29 — 1,167 files, 112 groups, ~261,000 lines.**

A review of **every load-bearing tracked file** in the repository, written in the
voice of a reviewer **who does not want to inherit this code** and has to justify that
position. The output is not an opinion: it is a set of findings, each tagged
with a lane, that another agent can pick up and execute.

| File | What it is |
|---|---|
| [`FILE-CHECKLIST.md`](FILE-CHECKLIST.md) | Every file, once. **1,160 files, 112 groups.** |
| [`GROUP-CHECKLIST.md`](GROUP-CHECKLIST.md) | Every group, reviewed *after* its files. Cross-file findings only. **112 groups.** |
| `review-<group>.md` | The findings. One document per group, written as the group is completed. |
| [`review-ForTauCeti-vs-tauceti-rubrics.md`](review-ForTauCeti-vs-tauceti-rubrics.md) | **A different axis**: `ForTauCeti/**` read against Tau Ceti's *own* ten review rubrics (`TauCetiReview/rubrics/`), rather than against a hostile reader. Seven `RUB-*` lanes, three recorded negative results. |

Both checklists are **generated**:

```sh
python3 scripts/audit_checklist.py            # regenerate, preserving every [x]
python3 scripts/audit_checklist.py --progress # counts, and which groups are now READY
```

Marks survive regeneration, so the lists stay correct as files move — which is
the only way a 790-file checklist stays trustworthy. Do not hand-edit them
except to tick a box.

## The two passes, and why the order matters

**File pass** finds what is visible inside one file: a misleading name, a
theorem doing three things, a proof that reproves a lemma that exists, a
definition with no consumers.

**Group pass** finds what is only visible across files: the same lemma proved in
two modules, an abstraction defined twice under different names, a `Basic.lean`
that is not basic, a directory whose contents do not share a subject, the result
the group obviously ought to contain and does not.

A group is **blocked** until every file in it is ticked. That is not
bureaucracy — the cross-file findings genuinely are invisible beforehand, and a
group review done early produces impressions rather than findings.

## Rules that keep this honest

1. **Tick a file only when its findings are written down.** An unrecorded review
   is indistinguishable from no review, and six months later nobody can tell
   which files were actually read.
2. **Every finding carries a lane tag** — `{lane:ID}`, matching
   `dev/LANES.md` so `scripts/check_lane_graph.py` sees it. A finding without a
   lane is a complaint; a finding with a lane is work someone can take.
3. **A finding names the file and line.** "The Sylvester code is confusing" is
   not reviewable; "`SylvesterBound.lean:412` restates the hypothesis of
   `sylvester_bound` in its conclusion" is.
4. **Record what is good, briefly.** A review that only lists defects cannot be
   used to decide what to keep, and this codebase contains a lot of correct,
   hard mathematics that should not be disturbed.
5. **Do not fix while reviewing.** The review is the deliverable; fixes go
   through lanes so they are claimed, built and checked like any other work.

## Recommended order

Not by size — by what the finding changes.

1. **`ForTauCeti` (22 topic groups, 161 files).** It is the deliverable, its
   groups *are* the submission units, and a finding here changes what gets
   proposed upstream. Start with the topics that have no prerequisites — T01,
   T12, T14, T21, T22 — because they can be submitted first.
2. **`FinishTanTwoTheta` (21 files).** Small, outside `defaultTargets`, and
   already known to carry naming problems. Feeds lanes `FTT-PROMOTE` and
   `FTT-DEDUP` directly.
3. **Production `DavisKahan`** — `SinTheta`, `Sylvester`, `SpectralTheory`,
   `Sources/DavisKahan1970`, `Geometry`, `FiniteDimensional`, `OperatorIdeal`,
   `Riccati`. The paper-facing library, and the largest duplication surface.
4. **`DavisKahan/Interop` (30 files).** Was the Spectra bridge; the donor is
   retired, so the question for every file is whether it should still exist.
5. **`DkpsQuench2026`, `Acharyya2024/2025`, `Helm2025`, `FinishYuWangSamworth`.**
   Paper libraries, reviewed for what they duplicate out of the core.
6. **`DavisKahan/Experimental` (151 files).** Last, deliberately: it is outside
   the default build, and lanes `EXP-PROMOTE-*` and `EXP-UNBLOCK` already
   measure what is promotable. Review it to decide what to *delete*.
7. **`Challenge` (49 files).** Immutable conformance statements — review for
   whether the right theorems are pinned, never to change them.

## Scope — load-bearing files only

**In scope: every tracked file whose *content*, if wrong, would mislead a reader
or break a gate.** That is all 787 Lean sources plus 373 load-bearing non-Lean
files — **1,160 total, 112 groups.**

Excluded, with the reason recorded in `scripts/audit_checklist.py` so the
decision is auditable rather than a silent filter (111 files):

| n | dropped | why |
|---|---|---|
| 57 | `.tex` / `.sty` / `.bst` / `.bib`, `papers/` | paper sources, reviewed as prose not as code |
| 17 | root `*_MANIFEST.txt`, `OVERLAY-METADATA/`, `_overlay/` | overlay delivery receipts, superseded by `dev/overlays/` |
| 27 | `.pyc`, `.gz`, `.ots`, `.patch`, `SHA256SUMS` | build and archive artifacts |
| 3 | `lake-manifest.json`, `lean-toolchain`, `LICENSE` | generated, or a single pinned value |

**`dev/overlays/*.manifest.txt` is deliberately NOT dropped**, even though it
matches the word "manifest": `scripts/check_davis_kahan_rebased_mathahead.py`
checks it, so its content is load-bearing. That distinction is why the exclusion
is a function with reasons rather than a glob.

### Two corrections, recorded because the second is the instructive one

The first version of this checklist covered **787 files: only `*.lean`**, while
presenting itself as an audit of every file. jon caught it. It silently omitted
the files a hostile reviewer attacks first — `ELEGANCE_AUDIT.md`,
`GROUNDING.md` and `PROOF_OBLIGATIONS.md` in the `Finish*` libraries, which make
**claims about completeness**; `verify_grounding.py`, the tools that assert those
claims hold; and `comparator/*.json`, which stores declaration names as data.

The over-correction then swept in 1,271 files including LaTeX styles and
compiled `.pyc`. Both errors are the same one in opposite directions: **a
checker whose scope does not match its name.** "Audit complete" over 787 of 1271
would have meant nothing; an audit padded with `.bst` files would have meant
little more.

### Review depth by kind

Every file in scope is on the list, labelled with its kind:

| Kind | n | What review means |
|---|---|---|
| **Lean source** | 787 | Line by line: duplication, splitting, simplification, naming, placement. |
| **documentation** | 226 | Does it state something false or stale? Does it match the tree it describes? |
| **tooling** | 69 | Does it check what it claims? Does a green result mean anything? |
| **data/config** | 56 | Do the names it pins still resolve? Generated or hand-edited? |
| **manifest/notes** | 12 | Is it still checked by something, and does it still match? |

## Mergeworthiness

[`MERGEWORTHINESS.md`](MERGEWORTHINESS.md) is the operative file for
`ForTauCeti`: every open defect that stands between it and Mathlib-quality
merge, each mapped to the lane that fixes it, plus what is measured green, what
is deliberately *not* a defect, and the three properties a static review cannot
check. Read that before asking what is left.

## Result

**Complete.** All 1,167 files and all 112 groups reviewed. Findings are in the
`review-*.md` documents in this directory, and every one carries a lane tag.

| review | covers |
|---|---|
| `review-ForTauCeti-T01.md` | T01, in depth — the first group, read file by file |
| `review-ForTauCeti-T02-T03-T06-T11-T21-T22.md` | six topics; the modulus duplication |
| `review-ForTauCeti-T04-T20.md` | the remaining fifteen topics; the `ForTauCeti` verdict |
| `review-DavisKahan-production.md` | all eighteen production groups |
| `review-Experimental-and-papers.md` | `Experimental` and all six paper libraries |
| `review-Challenge-MathlibPending.md` | the duplicated challenge admissions |
| `TAUCETI-RUBRIC-REVIEW.md` | the ten Tau Ceti review rubrics applied to both libraries |
| `review-docs-tooling-config.md` | documentation, tooling, config, `Challenge`; the whole-repo verdict |

**Lanes opened by the audit:** `HDR-DEST`, `T01-SQRT`, `MODULUS-DEDUP`,
`NS-SPREAD` (superseding `T01-NS`), `T15-SPLIT`, `DK-INTEROP`, `DK-FRAME`,
`CH-DEDUP`, `CLAIM-DOC` — plus scope widenings to `SPLIT-1K` and `PLACE-SYLV`.

**Renames carry the review; splits do not.** When a reviewed file is renamed the
checklist shows it unreviewed at its new path, because the path is new. If the
content is unchanged (git reports 90%+ similarity) the review carries and the
box is re-ticked. A file *created by splitting* a reviewed one is different: the
split itself is new structure and gets looked at. Both cases occurred on
2026-07-29 — nine `Experimental`→production promotions and the `PLACE-SYLV`
moves were renames; the four files from splitting `ReciprocalMultiplier` and
`SpectralMeasure` were checked, and both splits documented their own seams.

**Re-running:** `python3 scripts/audit_checklist.py` regenerates both checklists
against the current tree and preserves every mark, so new files arrive
unchecked. A file added after 2026-07-29 is *not* covered by this audit and the
checklist will say so.
