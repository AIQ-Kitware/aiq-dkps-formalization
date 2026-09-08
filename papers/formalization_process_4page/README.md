# Did We Really Formalize Davis--Kahan? Semantic Alignment for LLM-Assisted Lean Formalization

This directory contains a VeriCodeGen workshop draft about one LLM-assisted Lean
formalization and the problem of deciding whether the checked declarations
match the source mathematics. The paper places that experience beside public
first-person reports from other researchers.

## Source notes

The public-account table is:

- `data/practitioner_accounts.csv`

The monthly activity counts retained as appendix context are:

- `data/lean_publication_activity.csv`

The tracked CSV records the audited January 2024--September 2026 series.
Figure 2 reproduces the Papers With Lean public-chart window from January 2025
through August 2026 using complete months only; the extra tracked months remain
available for audit provenance.
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

## Formalization system description

The main paper describes the formalization setup as a small set of persistent
components: source/target records, the pinned Lean workspace and reusable
foundations, the implementation loop, mechanical checks, and semantic review.
The main text stays at the architectural level. `appendix.tex` records the
concrete repository artifacts, dependency revisions, checker roles, audit-packet
path, and actor responsibilities needed to reproduce or inspect that setup.

The workflow figure remains a high-level control-flow view. The appendix
semantic-review screenshot is a later inspection interface and is not presented
as the mechanism used for every historical review.

## Worked semantic-alignment example

The paper uses the historical directed $\sin 2\Theta$
correspondence failure. One checked theorem had the printed trial residual,
factor two, and norm family, but only bounded complex operator scope. A separate
checked theorem had unbounded scope but used a reflection residual rather than
the printed trial residual. The paper shows a generated version of the historical
theorem statement with names adjusted for readability; full exact historical
signatures and alternative repository-backed examples remain in
`notes/SEMANTIC_ALIGNMENT_CANDIDATES.md`.

`scripts/build_evidence.py` extracts the historical witness and writes its
signature verbatim to `generated/historical_scope_mismatch_exact.lean`.  It then
builds the separate `historical_scope_mismatch_presentation.lean` used by
`listings`.  That presentation applies only the audited readability name changes
and replaces display-sensitive Lean Unicode with unique ASCII `LeanLit...`
sentinels.  `paper.tex` maps those sentinels to LaTeX glyphs with `literate=`.
The presentation file is therefore intentionally not Lean source and begins
with comments pointing back to the exact sidecar.  This split is deliberate:
it avoids fragile Unicode handling in LaTeX/Overleaf without losing the exact
Lean being discussed.  The current exact source interface uses
`NormalizedUnitaryInvariantNorm`; the candidate-note generator preserves full
verbatim signatures from pinned Git history.

The manuscript reports checked formal treatments for all 29 tracked Davis--Kahan
results while keeping semantic alignment separate.  The latest source/signature
review found no remaining material mismatch, but no further independent review
has yet followed that pass; the paper therefore avoids a 100-percent
semantic-completeness claim.

## Public project repository

The live project repository is:

`https://github.com/AIQ-Kitware/aiq-dkps-formalization`

That URL identifies the authors. The default `paper.tex` build is anonymous.
`paper_public.tex` sets `\PublicVersion` to expose the authors and public links
for a preprint or camera-ready version.

## Figure

The paper uses local rendered PNGs for the workflow figure and appendix screenshot, but binary render outputs are never staged or committed. The source repository keeps only text/code inputs; rendered figures remain local build artifacts. The workflow figure remains in the main body and the semantic-alignment screenshot remains in the appendix.

## Build

```bash
make -C papers/formalization_process_4page
make -C papers/formalization_process_4page public
make -C papers/formalization_process_4page check-prose
make -C papers/formalization_process_4page check-layout
```

`make` builds the anonymous review version with the supplied NeurIPS 2026
VeriCodeGen workshop style. `make public` builds `paper_public.pdf`
with Jonathan Crall, Brian Hu, Edward Wang, and Carey E. Priebe as authors,
exposes the public GitHub URLs, and includes the DARPA acknowledgment in the main
paper.  The anonymous review build omits that acknowledgment.

The anonymous submission must remain within the workshop's 4--9-page main-text
limit. References, the technical appendix, and checklist follow outside that
limit. The public version groups authors by affiliation and shows the DARPA
acknowledgment. The historical signature uses the normal footnote-size code
font and is kept with its caption on one page.

`make check-layout` builds both versions and checks the actual PDF text and TeX
logs. It requires `pdftotext` from Poppler. It checks the 4--9-page anonymous main-text budget,
reference boundary, conclusion placement, an intact historical signature, early
workflow figure, appendix publication figure, checklist presence, anonymous/public
author visibility, and major TeX rendering diagnostics. It does not replace visual inspection. `check-prose`
checks both the main paper and appendix, leaving the historical prompt log alone.

`neurips_2026_vericode.sty` is the supplied VeriCodeGen workshop style and is
used unchanged. `checklist.tex` comes from the same workshop bundle; its questions
and guidelines are unchanged. `neurips_2026.sty` and `draft_neurips_2026.sty` are
retained only as files from the earlier MATH-AI target and are not used by either
build.

Detailed Davis--Kahan and Yu--Wang--Samworth mathematics remain in
`../formalization_draft2/` for the longer formalization paper.

## Semantic-alignment candidate cases

`notes/SEMANTIC_ALIGNMENT_CANDIDATES.md` is generated from pinned Git revisions by
`make sources`.  It contains short candidate writeups plus verbatim Lean signatures,
commit/path/line provenance, and snippet hashes.  The Section 8 bounded/unbounded and
extra-hypothesis cases are included explicitly.
