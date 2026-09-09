# Data used by the workshop paper

This directory keeps the small structured inputs behind claims made in the
workshop paper.  Generated prose and TeX are views; these files are the data to
edit and review.

## `practitioner_accounts.csv`

One row per project/workflow episode, plus one row marked `human_study` for the
Collins et al. comparison study.  Account rows contain the coded workflow
observation and review fields, but no longer treat a URL as the unit of
observation.  `practitioner_cluster` marks known cross-account practitioner
overlap, while `project_cluster` can group multiple workflow episodes from one
project.  The cluster identifier is an overlap component, not a unique-person
identifier.  Field meanings and categorical values are documented in
`practitioner_accounts.schema.json`.

## `practitioner_account_sources.csv`

One row per public source supporting an account.  Every account has exactly one
`primary` source; additional `supplemental` or `corroborating` rows can strengthen
its evidence without increasing the project-account denominator.  The source
table retains URLs and bibliography keys plus objective provenance fields:
first-person status, public-artifact availability, build/provenance availability,
and whether the source supports the coded account observation.  The schema is
`practitioner_account_sources.schema.json`.

The snapshot was assembled with LLM-assisted web search.  Its representativeness
is unknown.  The source records and account qualification notes are retained so
another reader can check the coding against public evidence.  The categorical
fields should not be used to estimate prevalence among Lean users.

## `practitioner_account_screening.csv`

A screening log for candidate sources and nearby evidence.  The log was
introduced on 8 September 2026.  It records the sources already present in the
paper snapshot at that point and candidates reviewed during the current
expansion and later searches.  Dispositions are `include_account`,
`supplemental_source`, `structured_study`, `related_work`, `hold`, `duplicate`,
or `exclude`.  `supplemental_source` is used when a new URL adds evidence to an
existing project account; `duplicate` is reserved for a source that adds no new
evidence.  `hold` records plausible candidates for which the available
first-person material is not yet strong enough for detailed workflow coding.

The log does not reconstruct every candidate encountered before it was
introduced and should not be treated as an exhaustive search record.  New
candidates should be logged when evaluated.  The builder validates all three
schemas, account/source relationships, screening dispositions, URLs, and
bibliography keys, then regenerates `notes/practitioner_accounts.md` and the
paper macros.

## `lean_publication_activity.csv`

Monthly Lean-related arXiv-paper counts derived from Papers With Lean for the
paper's 6 September 2026 cutoff.  The tracked range is January 2024 through
September 2026, with September explicitly partial.

The public statistics chart begins in January 2025.  To extend the figure back
to 2024 without changing metrics, `scripts/refresh_lean_publication_activity.py`
captures both the exact statistics-page HTML and the upstream
`site_papers.json` corpus, records source hashes, and groups corpus records by
their `published` calendar month.  Before the tracked CSV was extended, that
grouping reproduced every frozen January 2025--July 2026 chart value; the
6 September run also reproduced the displayed August 2026 value of 108 and
partial September value of 3.

Run:

```bash
make survey-publication-activity
```

to create a timestamped audit under the ignored
`generated/lean_publication_survey/` directory.  The raw corpus, raw statistics
HTML, exact tracked CSV, SHA-256 hashes, Git-blob SHA-1s, parsed series, overlap
comparison, machine-readable manifest, and human-readable report are retained
there.  `make check-publication-survey` makes a failed candidate-definition
validation nonzero.  Offline captures can be replayed with `--corpus-file` and
`--stats-file`.

An explicit `survey --write-tracked` is guarded by the original January
2025--July 2026 chart overlap.  Normal `make sources` never performs network
access.  `make check-publication-activity` checks the complete chart months
available in both the tracked snapshot and the live page; it excludes the
cutoff month's partial September count from that live-drift check.

## `review_timeline.csv`

Selected public Git events used in the paper and appendix.  Every event is keyed
by commit and an evidence path.  `scripts/build_evidence.py` checks that the
commits exist in the repository and that their commit date agrees with the CSV.
The table intentionally records project-level events rather than model chat.
Completion checkpoints may recur: a later source/signature review can return a
row to review while its Lean proof remains valid, so a 29/29 entry is a dated review state
rather than an irreversible milestone.

## `resource_snapshot.csv`

A compact copy of the transparency numbers reported in the longer
`papers/formalization_draft2` manuscript.  Rows say whether a value is directly
observed (and incomplete), a coverage denominator, or a quantity modeled from
the observed telemetry.  The source path for each value is included.

## Reproduction hashes

`scripts/build_evidence.py` hashes the manuscript inputs and selected project
evidence and writes `generated/materials_manifest.json`.  The manifest includes
the primary Git HEAD and the formalization-tools submodule revision when
available.  Generated hash tables are derived from that JSON.
