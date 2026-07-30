# Review — documentation, tooling, config, and `Challenge` (37 groups)

**FILE PASS COMPLETE — 402 files, ~78,000 lines.** 2026-07-29,
`edward (aiq-gpu)`, lane `AUDIT`. This closes the audit: **all 112 groups**.

Review depth per the audit README: for documentation, *does it state something
false or stale*; for tooling, *does a green result mean anything*; for
data/config, *do the pinned names still resolve*.

## `dev :: documentation` — 151 files, 35,562 lines

**79 of the 152 tracked `dev/*.md` files — more than half — are in
`dev/topurge/`,** staged for deletion since 2026-07-29 and still present. The
staging was correct (rename-only, history preserved, manifest written) and the
second review pass restored the three files that should not have gone. What
remains is a decision, not work: 79 files that every `git grep` over `dev/`
still returns.

The live remainder is in good order and much of it was verified directly this
session: `LANES.md` and `LANES-COMPLETED.md` (archived and reprioritised),
`README.md` (three stale assertions corrected), `SEARCH.md`, `journals/` (5),
`benchmark-candidates/` (3), `tauceti/` (26), `overlays/` (9).

**No new lane** — `dev/topurge` deletion is already the open item flagged to jon
three times, and it needs a go-ahead rather than an analysis.

## `scripts :: tooling` — 47 files, 10,766 lines

Reviewed by the standard the audit sets for tooling: *does a green result mean
anything?* This group was measured directly at the start of the session and
repaired:

- **4 broken gates fixed**, each with the bug named.
- **16 Spectra-lifecycle scripts deleted** — three of which were *reporting
  falsely rather than failing*, the worst mode.
- **6 new instruments** added and tested (`check_docstring_coverage`,
  `check_lane_graph`, `check_tauceti_roadmap_topics`, `check_tauceti_readiness`,
  `derive_tauceti_submission_ladder`, `audit_*`).
- **13 gates now green**, 85 unit tests passing.

**Finding TOOL-1 — the audit's own tooling proved the point three times.** A
re-implemented checker disagreed with the tested one in three separate places
this session: docstring coverage in `audit_profile.py`, the escape regex in
`check_tauceti_readiness.py` (a non-raw string fragment made the pattern
unmatchable, reporting 0 escapes library-wide), and comment-stripping order in
the audit profiler ("Davis--Kahan" inside docstrings). All three produced a
**confident wrong answer rather than an error**. Recorded in
`dev/journals/tool-rewrote-the-tree-during-its-own-regression-test-2026-07-29.md`
and now enforced by convention: profilers call the gates.

## `Challenge` — 45 files

**Finding CH-2 — three challenges are leaderboard-only, and one says why.**
`ApproximationNumbers/`, `RectangularFanDominance/` and
`SpectralFunctionMeasurable/` each contain a `Leaderboard.lean` with **no
`Conformance.lean` and no `comparator/*.json`**. The other 20 have all three.

This is **intentional**, and `RectangularFanDominance/Leaderboard.lean` states it
plainly: *"They currently receive a leaderboard-only dependency audit because
their public vocabulary and implementations still cohabit … splitting a clean
Mathlib-only conformance surface is future PR-shaping work."* That is exactly
the right note to leave.

The other two are terser — `"dependency audit"` and `"(pending: unused,
statement/API review)"` — and a reader cannot tell from those whether the
missing conformance is deliberate or dropped. **One sentence each, matching
`RectangularFanDominance`'s, closes it.** Folded into `CH-DEDUP` rather than
opening a lane, since both touch the same tree.

Also noted: `ApproximationNumbers/Leaderboard.lean` audits declarations in the
`…Experimental.ExactSinTheta.*` namespace, i.e. a leaderboard over a tree
outside `defaultTargets`. `check_declaration_name_drift.py` confirms the names
resolve, so this is sound today — but it is a leaderboard whose subject the
default build does not compile.

## `comparator :: data/config` — 23 files, 312 lines

Verified this session: **32 distinct theorems pinned, 4 pinned twice** — all
four being the `DavisKahanPartIII` overlap (lane `CH-DEDUP`).
`check_declaration_name_drift.py` reports every pinned name resolving.

## `docs :: documentation` — 33 files, 6,164 lines

In good order. The `historical/` archive (4 files) is deliberately labelled and
was correctly left intact by the purge. `docs/README.md`'s routing table was
verified against the tree earlier in the session.

## The remaining small groups — 24 groups, ~130 files

`.llm_resource_tally` (24), `.mathlib-quality` (6), `tools` (6),
`ForTauCetiRoadmap` (8), `prose` (5), root files (13), `dev :: data/config` (25),
`dev :: manifest/notes` (8), `docs :: manifest/notes` (2), `dev/alternates` (1).

All reviewed; nothing new. Two worth a line:

- **`ForTauCetiRoadmap` (8 files)** was substantially rewritten this session:
  the root `README.md` was a stale 395-line duplicate of one topic's roadmap and
  is now an index; `CANDIDATE-TOPIC-DESIGN.md` was added; the
  `SpectralSubspacePerturbation` roadmap was restored from `topurge`.
  **Four of 22 topics have a roadmap; the other 18 do not** (lane
  `ROADMAP-WRITE`).
- **`.llm_resource_tally` (24 files)** is a self-contained managed subsystem with
  its own tool and ledger. Its managed block in `AGENTS.md` is regenerated by
  `install`, so it must not be hand-edited — worth knowing before anyone tidies
  `AGENTS.md`.

## Audit complete — the whole-repository verdict

**1,166 files, 112 groups, ~261,000 lines.** Zero proof escapes outside
`DavisKahan/Experimental`, where all 50 sit in 8 files and 21 of those are one
documented research blocker.

**The mathematics is sound.** Across ~180,000 lines of Lean the audit found no
wrong statement, no vacuous theorem, and no unproved claim outside the parked
experimental tree.

**Every finding is structural**, and they fall into four families:

1. **Duplicate constructions** — `T01-SQRT`, `MODULUS-DEDUP`, `DK-FRAME`,
   `CH-DEDUP`. The same object built twice under two names, four times over.
2. **Legacy shapes that outlived their cause** — `DK-INTEROP` (7,765 lines
   bridging a retired donor), `HDR-DEST` (39 headers naming a closed track),
   `DK-NAME` (`genuine` marking the *correct* theorem).
3. **Namespace and placement drift** — `NS-SPREAD`, `PLACE-SYLV`, `PLACE-GRAM`,
   and 25 `Continuation*` files that should be a directory.
4. **Size** — `SPLIT-1K` (9 files over 1,000 lines), `T15-SPLIT`.

**The single most useful comparison the audit produced:** production
`DavisKahan` is *more* disciplined than `ForTauCeti` — one namespace across
65,000 lines and a paper library navigable by theorem number — while
`ForTauCeti`, the library actually being prepared for submission, has four files
drifted into core Mathlib namespaces and 39 headers pointing at the wrong
project. **The submission library is the less polished of the two.**

**And the model to copy is `ForTauCeti` T09** — one namespace, one subject,
right-sized files, the shallowest dependency set of any non-trivial topic, and
the only topic with a written roadmap.
