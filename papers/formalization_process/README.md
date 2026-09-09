# Did We Really Formalize Davis--Kahan? Semantic Alignment for LLM-Assisted Lean Formalization

This directory contains a VeriCodeGen workshop draft about one LLM-assisted Lean
formalization and the problem of deciding whether the checked declarations
match the source mathematics. The paper places that experience beside public
first-person reports from other researchers.

## Source notes

The public-account snapshot is normalized into:

- `data/practitioner_accounts.csv` - one row per project/workflow episode;
- `data/practitioner_account_sources.csv` - primary, supplemental, and corroborating public sources;
- `data/practitioner_account_screening.csv` - screening decisions, including holds and supplemental sources.

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

- `notes/practitioner_accounts.md` - account records with their attached public
  sources, screening decisions, and descriptive counts quoted in the paper;
- `generated/practitioner_account_macros.tex` - TeX macros consumed by
  `paper.tex`;
- `generated/lean_activity_timeline_tikz.tex` - the appendix timeline figure;
- `generated/review_timeline_table.tex` and `generated/resource_snapshot_table.tex`;
- `generated/materials_manifest.json` and its aggregate SHA-256.

`brainstorm.md` contains the original informal notes and a verbatim log of the
human prompts available from the retained paper-revision transcript. Earlier
prompts that are not available verbatim are not reconstructed from summaries.

## Formalization procedure description

The main paper describes the setup from the researcher's point of view: how a
source target was fixed before implementation, what work the agents performed,
what Lean and project scripts checked mechanically, what was inspected during
source correspondence review, and how the review result was retained.  This is
presented as a short bullet sequence rather than a component table.  Exact
dependency revisions, repository records, checker behavior, and the audit-packet
script remain in `appendix.tex`.

The existing workflow figure remains Figure 1. The process bullets map onto it
conceptually: Gather Context summarizes the Inputs panel, Formalize includes the
Compile & Revise box, and Skeptical Review corresponds to the Skeptical Critic.
Do not redraw the figure merely to force one-to-one labels. The appendix
semantic-review screenshot is a later inspection interface and is not presented
as the mechanism used for every historical review.

## Worked semantic-alignment example

The paper shows an ambient $\sin 2\Theta$ theorem from the 17 August checkpoint
that had been accepted for the source result despite having only bounded operator
scope. Real and complex versions were already present, and the directed residual
clause already had unbounded real and complex witnesses; scalar coverage was not
the mismatch. The historical review had combined scope and conclusions across
different declarations.

The rendered paper states only that mathematical mismatch. Detailed checkpoint
chronology, the later gap-placement correction, and exact provenance are retained
in LaTeX comments, `data/review_timeline.csv`, and generated metadata rather than
narrated in the worked example. The appendix states only the chronology fact needed
to correct the paper's account.

`scripts/build_evidence.py` extracts the historical ambient witness and its section
context and writes them verbatim to
`generated/historical_scope_mismatch_exact.lean`. It then builds the separate
`historical_scope_mismatch_presentation.lean` used by `listings`. That
presentation applies only the audited readability name changes and replaces
display-sensitive Lean Unicode with unique ASCII `LeanLit...` sentinels.
`paper.tex` maps those sentinels to LaTeX glyphs with `literate=`. The
presentation file begins with comments pointing back to the exact sidecar.
Formalization 2 uses `NormalizedSymmetricOperatorIdealFamily`; its where-defined
Fan comparison is an explicit field of that record.

The worked comparison now displays the compiled common-domain theorem from
`DavisKahan/Sources/DavisKahan1970/SinTwoThetaCommonDomain.lean` as
Formalization 2. The manuscript explains the mathematical difference from the
preceding bounded-trial refinement without narrating the review chronology:
the directed clause uses a bounded residual on the common operator domain,
while the ambient clause separately uses a bounded self-adjoint perturbation.
The appendix defines reducing subspaces for partial operators and gives a
reader's guide to every hypothesis in the displayed theorem. Historical review
state remains in `dev/davis-kahan-1970-sin-two-theta-review-2026-09-09.md` rather
than in the manuscript narrative.

## Public project repository

The live project repository is:

`https://github.com/AIQ-Kitware/aiq-dkps-formalization`

That URL identifies the authors. The default `paper.tex` build is anonymous.
`paper_public.tex` sets `\PublicVersion` to expose the authors and public links
for a preprint or camera-ready version.

## Double-blind supplementary copy

Create a Git-history-free review copy from the tracked repository files with:

```bash
python3 papers/formalization_process/scripts/anonymize_repo.py
```

Use `--output PATH` to choose the destination and `--force` to replace an
existing destination. The script honors Git `filter=crypt` attributes, rewrites
known author, institution, repository-organization, email, and contract
identifiers in UTF-8 text, byte-audits copied binary files for the same obvious
identifiers, and fails rather than leaving a known residual. Gitlink/submodule
entries and `.git` history are omitted. The tracked `.llm_resource_tally/tool`
zipapp is also omitted because its binary payload contains an author alias, and
the anonymizer itself is omitted because it contains the private replacement
vocabulary. The generated `ANONYMIZATION_REPORT.txt` records all explicit
omissions. The resulting directory still requires a final human inspection
before submission.

## Figure

The workflow figure remains the existing `figures/formalization_workflow.png`
artifact used by the main paper. Do not replace or redraw it as part of prose
revisions. The appendix includes the semantic-alignment screenshot only when its
file is present; the paper does not depend on that screenshot for its argument.

## Build

```bash
make -C papers/formalization_process
make -C papers/formalization_process public
make -C papers/formalization_process check-prose
make -C papers/formalization_process check-layout
```

`make` builds the anonymous review version with the supplied NeurIPS 2026
VeriCodeGen workshop style. `make public` builds `paper_public.pdf`
with Jonathan Crall, Brian Hu, Edward Wang, and Carey E. Priebe as authors,
exposes the public GitHub URLs, and includes the DARPA acknowledgment in the main
paper.  The anonymous review build omits that acknowledgment.

The anonymous submission must remain within the workshop's 4--9-page main-text
limit. References, the technical appendix, and checklist follow outside that
limit. The public version groups authors by affiliation and shows the DARPA
acknowledgment. The two displayed formalizations use the normal footnote-size code font; the
layout check keeps each signature with its caption on one page.

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
