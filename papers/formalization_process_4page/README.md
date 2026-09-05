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

## Historical false finish

The paper replaces the old dashboard screenshot figure with a typeset Lean
signature from a real earlier state of the Davis--Kahan formalization. The
historical endpoint had the printed directed `sin 2 Theta` trial-residual bound
for bounded complex operators. A separate unbounded theorem used a different
reflection residual. A source comparison on 12 August 2026 showed that the existing endpoints did
not yet combine the printed residual with the full scalar and operator scope.
The later repair exposed unbounded trial-residual endpoints for real and complex
scalars.

The manuscript currently reports checked evidence for all 29 tracked
Davis--Kahan results while treating that conclusion as provisional: we think all
29 are covered at the intended source scope, or are very close.

## Public project repository

The live project repository is:

`https://github.com/AIQ-Kitware/aiq-dkps-formalization`

That URL identifies the authors. The default `paper.tex` build is anonymous.
`paper_public.tex` sets `\PublicVersion` to expose the authors and public links
for a preprint or camera-ready version.

## Figure

The paper keeps the author-provided workflow figure with ordinary LaTeX
`\includegraphics`:

- `figures/formalization_workflow.png`

The workflow figure remains in the four-page body.  The semantic-alignment
screenshot is included in the appendix with ordinary `\includegraphics` so the
reader can see the current source/correspondence/Lean review interface.

## Build

```bash
make -C papers/formalization_process_4page
make -C papers/formalization_process_4page public
make -C papers/formalization_process_4page check-prose
```

`make` builds the anonymous review version. `make public` builds
`paper_public.pdf` with Jonathan Crall and Brian Hu as authors and exposes the
public GitHub URLs.

`draft_neurips_2026.sty` is a local page-budget approximation. Replace it with
the official workshop template before submission and recheck the four-page
content limit.

Detailed Davis--Kahan and Yu--Wang--Samworth mathematics remain in
`../formalization_draft2/` for the longer formalization paper.
