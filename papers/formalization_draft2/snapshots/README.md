# Tracked manuscript snapshots

This directory contains small, reviewable artifacts generated from repository
analysis or external bibliometric queries and consumed by the manuscript.
These files are intentionally tracked in Git so the paper builds offline from a
stable evidence snapshot.

Detailed working CSV/JSON inventories, diagnostic reports, and raw API responses
belong under `../generated/` and are gitignored. Refresh snapshots explicitly
with the corresponding analysis command, review the diff, and commit the small
artifacts that changed.

- `make accounting` refreshes repository-derived TeX macros and tables here.
- `make bibliometrics` refreshes the compact OpenAlex JSON, citation-trend CSV,
  citation-trend TeX table, and bibliometric macros here while leaving the raw
  response under `../generated/`.
