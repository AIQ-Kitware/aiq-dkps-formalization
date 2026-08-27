# Historical hostile-review audit records

This directory is a **historical review corpus**, not a current work queue.
Most files were written during the July 2026 hostile-review campaign and retain
the vocabulary, lane identifiers, counts, and proposed fixes from that campaign.
Those details are useful evidence for why the current gates and APIs exist, but
they are not instructions for new work.

The multi-agent lane system is retired.  Do not claim `{lane:...}` tags or route
new work through `dev/LANES.md` merely because an old review file does so.

## Current authorities

For work on the current tree, start from these sources instead:

- `../../AGENTS.md` — repository workflow and dependency policy;
- `../../ForTauCeti/README.md` — current reusable-library contract;
- `../README.md` and `../SEARCH.md` — engineering-memory navigation;
- `../tauceti/extraction-manifest.json` and the checked Tau Ceti status tools —
  reusable-library ownership/provenance;
- `../davis-kahan-1970-full-source-census.json` plus
  `../davis-kahan-1970-formalization-result-inventory.json` — Davis--Kahan source
  coverage and the 29-result completion denominator;
- `../../scripts/run_gates.py` — current automated repository checks.

The audit checklists remain useful for reconstructing what was reviewed.  Their
progress is measured by:

```bash
python3 scripts/audit_checklist.py --progress
```

That command reports the historical checklist campaign.  It is **not** a
merge-readiness verdict for the present tree.

## How to read the files here

`review-*.md`, `TAUCETI-RUBRIC-REVIEW.md`, `FILE-CHECKLIST.md`, and
`GROUP-CHECKLIST.md` are preserved as review evidence.  Treat statements such as
"open", "claimed", "ready", exact file counts, and lane assignments as dated
observations unless a current checker independently reproduces them.

`MERGEWORTHINESS.md` is retained only as the snapshot that accompanied that
campaign.  Current readiness is established by the present build, gates, and
upstream review process, not by that file.

When an old finding still matters, fix the current source and its current gate or
owner document.  Do not update the historical review narrative just to make its
old status words look current.
