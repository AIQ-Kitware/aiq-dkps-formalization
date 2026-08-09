# Historical record: Tau Ceti extraction cluster classification

This file previously classified reusable declarations into proposed upstream PR
clusters and carried rapidly changing migration statuses such as
`blocked-on-spectra-removal`, `staged`, and lane ownership.  That operational
classification is obsolete: Spectra and `ForMathlib` are retired, and the
maintained package is `ForTauCeti`.

The file path is retained because historical tooling and completed-lane records
refer to it.  It is **not** a current submission plan.

Use these current authorities instead:

- `ForTauCeti/README.md` — package architecture and current policy;
- `dev/tauceti/extraction-manifest.json` — machine-readable module ownership,
  provenance, and export clusters;
- `dev/tauceti/README.md` — navigation for Tau Ceti engineering records;
- `scripts/check_tauceti_readiness.py` and
  `scripts/check_tauceti_roadmap_topics.py` — current measured readiness signals;
- `scripts/derive_tauceti_submission_ladder.py` — derived submission ordering
  where that workflow is still relevant.

Historical PR ordering, old Spectra blockers, and `ForMathlib` source paths can
be recovered from Git history when provenance work requires them.  They should
not be copied back into current planning prose.
