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

## Worked semantic-alignment example

The four-page paper uses the historical Section 2 `tan Theta` mismatch involving
condition (3.5). `scripts/build_evidence.py` extracts the full historical and
repaired theorem signatures from Git and writes
`generated/historical_false_finish.json`. The PDF displays only the relevant
ASCII-safe lines in `generated/historical_false_finish.lean`; the full verbatim
Lean is also retained in `notes/SEMANTIC_ALIGNMENT_CANDIDATES.md`.

The historical endpoint exposed
`h35 : CrossedDefectsEquivalent U V` as a caller hypothesis even though Davis
and Kahan introduce condition (3.5) only in Section 3. The repaired Section 2
endpoint instead takes `HasDefinedAmbientTangent`, which represents the source's
earlier convention that the tangent norm must exist, and derives the crossed-
defect condition internally. Alternative repository-backed examples remain in
`notes/SEMANTIC_ALIGNMENT_CANDIDATES.md`.

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
