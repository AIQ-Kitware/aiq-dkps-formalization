# Data used by the workshop paper

This directory keeps the small structured inputs behind claims made in the
workshop paper.  Generated prose and TeX are views; these files are the data to
edit and review.

## `practitioner_accounts.csv`

One row per public first-person account, plus one row marked `human_study` for
the Collins et al. comparison study.  Each row carries its source URL,
bibliography key, a concise observation, a source note explaining ambiguous
coding, and the fields used for descriptive counts.  The allowed categorical
values and field meanings are documented in
`practitioner_accounts.schema.json`.  `scripts/build_practitioner_accounts.py`
validates the file and regenerates `notes/practitioner_accounts.md`.

The snapshot was assembled with LLM-assisted web search.  Its
representativeness is unknown.  The source URL, citation key, observation, and
qualification note are retained so another reader can check each row against
the public account.  The categorical fields should not be used to estimate
prevalence among Lean users.

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
