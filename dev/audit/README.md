# `dev/audit/` — the hostile review

A line-by-line review of **every tracked file** in the repository, written in the
voice of a reviewer **who does not want to inherit this code** and has to justify that
position. The output is not an opinion: it is a set of findings, each tagged
with a lane, that another agent can pick up and execute.

| File | What it is |
|---|---|
| [`FILE-CHECKLIST.md`](FILE-CHECKLIST.md) | Every file, once. **1,271 files, 315,880 lines, 128 groups.** |
| [`GROUP-CHECKLIST.md`](GROUP-CHECKLIST.md) | Every group, reviewed *after* its files. Cross-file findings only. **128 groups.** |
| `review-<group>.md` | The findings. One document per group, written as the group is completed. |

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

## Scope — and a correction

**Scope is every tracked file except `retired/`, `external/`, `vendor/` and
`.lake/`** — the trees that are not ours to review. Nothing else is dropped.

The first version of this checklist covered **787 files: only `*.lean`.** That
was wrong, and jon caught it. It silently omitted **484 files**, including
exactly the ones a hostile reviewer attacks first:

- `FinishYuWangSamworth/ELEGANCE_AUDIT.md`, and `GROUNDING.md` /
  `PROOF_OBLIGATIONS.md` in both `Finish*` libraries — documents that make
  **claims about completeness**. A false claim there is more damaging than a
  weak proof, because it is what a reader trusts instead of checking.
- `scripts/verify_grounding.py` ×2 — the tools that *assert* those claims hold.
- `comparator/*.json` (23) — declaration names stored as data, already the
  documented rename trap.
- 232 `.md`, 63 `.py`, 55 `.json`, 45 files under `scripts/`.

The lesson is the one this repository keeps relearning: **a checker whose scope
is narrower than its name reports a green result that means nothing.** "Audit
complete" over 787 of 1271 files would have been exactly that.

### Review depth by kind

Every file is on the list. What "reviewed" means varies, and the checklist
labels each entry with its kind:

| Kind | What review means |
|---|---|
| **Lean source** (787) | Line by line: duplication, splitting, simplification, naming, placement. |
| **documentation** (232) | Does it state something false or stale? Does it match the tree it describes? |
| **tooling** (63 `.py`, 6 `.sh`) | Does it check what it claims? Is it reachable? Does a green result mean anything? |
| **data/config** (55 `.json`) | Do the names it pins still resolve? Is it generated or hand-edited? |
| **paper source** (49 `.tex`, styles, `.bib`) | Shallow: does it match the formalized statements it cites? Not a LaTeX review. |
| **artifact** (`.pyc`, `.gz`, `.ots`, `.patch`) | Should this be tracked at all? **12 `.pyc` files are committed — that is already a finding.** |

Binary files have no lines to read but stay on the list, because "why is this
tracked" is a legitimate review question.
