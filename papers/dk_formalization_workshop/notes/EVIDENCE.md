# Evidence notes for the four-page semantic-alignment paper

Evidence snapshot: `5f339b74adf7e03cdd0a1f980ee63d7b78c360e7` (2026-09-04).

## Quantitative retrospective claim

`scripts/reconstruct_semantic_reversals.py` reconstructs the maintained
Davis--Kahan result register through the snapshot above.  It counts a reversal
when a row changes from `semantic_certification: accepted` to any other state at
the next revision of that file.

At the pinned snapshot:

- 14 accepted-to-nonaccepted transitions;
- 10 distinct results affected;
- denominator in the current result register: 29 results.

Interpretation: these are semantic-review acceptance reversals in one evolving
project.  Some exposed a narrower mathematical statement; others exposed a
mapping/correspondence defect or a weakness in the audit checker.  Do not call
them 14 wrong proofs and do not derive an LLM failure percentage from them.

## Representative history anchors

- `7001ed05` (2026-08-12), **Reopen three overclaimed DK1970 result rows**.
  Reopens `S2-sin-two-theta`, `DK-3.4-prop`, and `DK-8.2-thm` before repair.
  The commit records three concrete mismatches: reflection residual versus the
  printed trial residual; a complex direct-rotation endpoint weaker than the
  printed positivity clauses; and missing standing-scope / ambient-angle
  evidence.  The commit is attributed to a fresh Claude Opus 5 session.

- Earlier commits accepting/promoting rows in this episode include GPT-5.6
  Thinking / GPT-5.6 Sol co-author metadata (`7cc049b4`, `535dab99`).  This is a
  useful cross-session anecdote, not a controlled comparison of the models.

- `cc824790` (2026-08-31), **Hostile re-review of all 29 results; four findings
  repaired, four checker holes closed**.  The review found four
  mathematical/registration defects and four weaknesses in the checker.  The
  former include arbitrary-unitarily-invariant-norm scope and missing
  representation correspondence.

- `2a027968` (2026-09-02) closed the last directed tan-two-theta correspondence
  at 29/29 and strengthened the checker.  `de65f4fc`, 33 minutes later, reopened
  that result after a hostile review reproduced two high-severity defects: the
  correspondence only covered a special reflection object, and the registered
  real clause used a complex witness.  The status returned to 28/29 before the
  later repair.

## Current case-study endpoint

The maintained 29-result register currently reports 29 terminal results: 28
proved at the scope asserted in the 1970 source and Proposition 4.4 formally
refuted as printed.  This workshop paper should use that status only as context
for the semantic-alignment tooling; the mathematical results belong in the
separate formalization manuscript.

## Dashboard implementation facts

The reusable `aiq-lean-formalization-tools` package supports:

- source passages and clause-level semantic review records;
- a three-lane alignment page: literature, correspondence, Lean;
- elaborated Lean signatures, statement closure, and proof dependencies when
  compiler/graph evidence is available;
- source-fragment hashes and elaborated-statement hashes;
- drift checks that invalidate prior review when either reviewed side changes;
- separate compiler/formal-disposition/semantic-review status axes;
- explicit correspondence witnesses for representation changes;
- a live server with cross-ledger navigation, search, annotations, and reload.

The manuscript should emphasize that the correspondence judgment remains a
review judgment.  The mechanical evidence establishes which source passage and
which elaborated Lean statement were reviewed and detects later drift.
