# Who Checks the Formalization?

This directory contains a four-page workshop draft about human supervision in
LLM-assisted Lean formalization. The paper uses a snapshot of public
first-person accounts together with the Davis--Kahan project as a case study.

## Public source notes

The editable account table is:

- `data/practitioner_accounts.csv`

The monthly activity counts used in the introduction are:

- `data/lean_publication_activity.csv`

Running:

```bash
make sources
```

regenerates:

- `notes/practitioner_accounts.md` - one source record per account plus the
  counts quoted in the paper;
- `generated/practitioner_account_macros.tex` - TeX macros consumed by
  `paper.tex`.

The notes keep unreported and ambiguous fields explicit. Source URLs and short
evidence notes are stored with every record so the numerical statements in the
paper can be checked against the underlying public accounts.

## Public project repository

The live project repository is:

`https://github.com/AIQ-Kitware/aiq-dkps-formalization`

That URL identifies the authors. `paper.tex` therefore keeps
`\showartifacturlfalse` in the double-blind review build. Set it to true for a
public preprint or camera-ready version.

## Figures

Both author-provided figures are included with ordinary LaTeX
`\includegraphics`:

- `figures/formalization_workflow.png`
- `figures/semantic-alignment-sine-theta-row.png`

The dashboard screenshot is cropped only at typesetting time with `trim` /
`clip`; the PNG is unchanged. Figure 1 mentions Tau Ceti, so its caption
explains and cites it.

## Build

```bash
make -C papers/formalization_process_4page
make -C papers/formalization_process_4page check-prose
```

`draft_neurips_2026.sty` is a local page-budget approximation. Replace it with
the official workshop template before submission and recheck the four-page
content limit.

Detailed Davis--Kahan and Yu--Wang--Samworth mathematics remain in
`../formalization_draft2/` for the longer formalization paper.
