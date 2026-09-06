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

The snapshot was assembled by web search and citation chasing.  Its
representativeness is unknown.  The source URL, citation key, observation, and
qualification note are retained so another reader can check each row against
the public account.  The categorical fields should not be used to estimate
prevalence among Lean users.

## `lean_publication_activity.csv`

Monthly counts transcribed from the Papers With Lean statistics page,
https://paperswithlean.com/stat/, as displayed on the snapshot updated
2026-08-24.  The paper uses complete months from January 2025 through July
2026, avoiding the then-incomplete August 2026 count.

The tracked CSV is intentionally frozen with the paper's reporting window.
`make check-publication-activity` fetches the current statistics page, verifies
that those 19 historical month/count pairs still agree, and reports newer live
months without changing the tracked snapshot or the normal `make sources`
build.  Use `scripts/check_lean_publication_activity.py --emit-csv` to print the
live series when reviewing a future reporting-window update.

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
