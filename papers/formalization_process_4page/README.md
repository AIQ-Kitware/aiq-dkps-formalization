# Did We Really Formalize Davis--Kahan?

This directory contains a four-page workshop draft about one LLM-assisted Lean
formalization and the problem of deciding whether the checked declarations
match the source mathematics. The paper places that experience beside public
first-person reports from other researchers.

## Source notes

The public-account table is:

- `data/practitioner_accounts.csv`

The monthly activity counts used in the introduction are:

- `data/lean_publication_activity.csv`

The tracked CSV records the audited January 2024--September 2026 series.
Figure 2 shows complete months through August 2026; the partial September value
is retained only for audit provenance.
To reproduce or re-audit the source definition, run the separate survey:

```bash
make survey-publication-activity
```

This networked command captures the exact `site_papers.json` corpus and
statistics-page HTML, records content hashes and source metadata, parses the
live chart, groups the corpus by its `published` field, and compares both
series against the tracked overlap.  Each run writes a timestamped audit under
`generated/lean_publication_survey/`, which is ignored by Git.  The report is
produced even when the candidate corpus date definition fails to reproduce the
chart.  Use `make check-publication-survey` when that mismatch should also make
the command fail, and `make self-test-publication-survey` for an offline test of
the parser and comparison logic.

The survey never changes the tracked CSV by default.  An explicit
`scripts/refresh_lean_publication_activity.py survey --write-tracked` is guarded
by the January 2025--July 2026 overlap validation and refuses to write if the
candidate metric does not match.  This is the frozen chart interval that was
known before the 2024 extension.  `make sources` remains network-free.

Running:

```bash
make sources
```

validates the structured source snapshot and Git chronology and regenerates:

- `notes/practitioner_accounts.md` - one source record per public account plus
  the descriptive counts quoted in the paper;
- `generated/practitioner_account_macros.tex` - TeX macros consumed by
  `paper.tex`;
- `generated/lean_activity_timeline_tikz.tex` - the appendix timeline figure;
- `generated/review_timeline_table.tex` and `generated/resource_snapshot_table.tex`;
- `generated/materials_manifest.json` and its aggregate SHA-256.

`brainstorm.md` contains the original informal notes and a verbatim log of the
human prompts available from the retained paper-revision transcript. Earlier
prompts that are not available verbatim are not reconstructed from summaries.

## Worked semantic-alignment example

The four-page paper uses the historical directed $\sin 2\Theta$
correspondence failure. One checked theorem had the printed trial residual,
factor two, and norm family, but only bounded complex operator scope. A separate
checked theorem had unbounded scope but used a reflection residual rather than
the printed trial residual. The paper shows a compact generated scope table;
full historical signatures and alternative repository-backed examples remain in
`notes/SEMANTIC_ALIGNMENT_CANDIDATES.md`.

`scripts/build_evidence.py` extracts the historical witness and the current real
and complex source-facing endpoints to build that table. The current exact
source interface uses `NormalizedUnitaryInvariantNorm`; the proof layer may pass
through `SymmetricNormingFunction`. The candidate-note generator preserves full
verbatim signatures from pinned Git history.

The manuscript reports mathematical resolution of all 29 tracked Davis--Kahan
results while keeping semantic alignment separate: the latest signature/context
review in the paper snapshot still records source-surface issues to repair.

## Public project repository

The live project repository is:

`https://github.com/AIQ-Kitware/aiq-dkps-formalization`

That URL identifies the authors. The default `paper.tex` build is anonymous.
`paper_public.tex` sets `\PublicVersion` to expose the authors and public links
for a preprint or camera-ready version.

## Figure

The paper uses local rendered PNGs for the workflow figure and appendix screenshot, but binary render outputs are never staged or committed. The source repository keeps only text/code inputs; rendered figures remain local build artifacts. The workflow figure remains in the four-page body and the semantic-alignment screenshot remains in the appendix.

## Build

```bash
make -C papers/formalization_process_4page
make -C papers/formalization_process_4page public
make -C papers/formalization_process_4page check-prose
```

`make` builds the anonymous review version with the official NeurIPS 2026
MATH-AI double-blind workshop style. `make public` builds `paper_public.pdf`
with Jonathan Crall, Brian Hu, Edward Wang, and Carey E. Priebe as authors,
exposes the public GitHub URLs, and includes the DARPA acknowledgment in the main
paper.  The anonymous review build omits that acknowledgment.

`neurips_2026.sty` is the official workshop style supplied with the MATH-AI
2026 template. `draft_neurips_2026.sty` is retained only as the earlier local
page-budget approximation and is not used by either build.

Detailed Davis--Kahan and Yu--Wang--Samworth mathematics remain in
`../formalization_draft2/` for the longer formalization paper.

## Semantic-alignment candidate cases

`notes/SEMANTIC_ALIGNMENT_CANDIDATES.md` is generated from pinned Git revisions by
`make sources`.  It contains short candidate writeups plus verbatim Lean signatures,
commit/path/line provenance, and snippet hashes.  The Section 8 bounded/unbounded and
extra-hypothesis cases are included explicitly.
