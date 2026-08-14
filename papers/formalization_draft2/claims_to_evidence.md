# Claims-to-evidence map

Working map for the paper. This is intentionally stricter than a prose outline:
each headline claim should point to source material that can be independently
audited before submission.

| Claim | Primary repository evidence | Paper role |
|---|---|---|
| YWS is represented source-faithfully at published numbering/generality | `FinishYuWangSamworth/README.md`, `FinishYuWangSamworth/PROOF_OBLIGATIONS.md`, `dev/yu-wang-samworth-2015-full-source-census.json` | Main mathematical contribution |
| 24/24 source census rows are proved in the default build | `FinishYuWangSamworth/PROOF_OBLIGATIONS.md` | Coverage statement |
| Printed YWS equation (4) is false and corrected | `FinishYuWangSamworth/FinishYuWangSamworth/Symmetric/AngleIdentity.lean` | Formalization-as-audit case study |
| Printed YWS Theorem 3 rank-boundary convention is false and corrected | `FinishYuWangSamworth/FinishYuWangSamworth/Rectangular/RankBoundary.lean` | Formalization-as-audit case study |
| Davis--Kahan Proposition 4.4 is false as printed | `papers/davis_kahan_prop_4_4_counterexample.tex`, corresponding Lean source under `DavisKahan/` | Independent source-audit result |
| The formal spectral stack supports a contemporary downstream theorem | `DkpsQuench2026/README.md`, `DkpsQuench2026/Paper/Theorem2.lean`, `DkpsQuench2026/Geometry/AlignedCMDS.lean` | Reuse / integration case study |
| DK/YWS development forced foundational operator-theory layers absent from the needed Mathlib surface | `ForTauCeti/`, `DavisKahan/`, Tau Ceti roadmap submodule and migration notes | Motivation and amortization argument |
| A substantial fraction of project history lacks exact commit-level telemetry | `generated/commit_accounting_manifest.csv`, `generated/accounting_summary.json` | Accounting limitation/result |
| Backfilled usage includes measured but commit-unattributed sessions | `.llm_resource_tally/ledger/ledger.jsonl`, `generated/pending_segments.csv` | Missing-data methodology |
| Human steering can be characterized from retained transcripts | `dev/posthoc-prompt-analysis/findings/`, `generated/interaction_summary.json` | Human--LLM process analysis |
| Chat-interface work is incompletely observed | manual provenance review + `data/accounting_overrides.csv` | Explicit limitation; do not overclaim from telemetry |

## Before submission

- Replace path-level evidence with declaration-level citations for each formal
  theorem quoted in the paper.
- Freeze and archive the accounting snapshot used for final numbers.
- Audit every non-empty row of `data/accounting_overrides.csv` against an external
  record or author recollection note.
- Re-run a related-work search immediately before submission; AI formalization is
  changing too quickly for the current scaffold to freeze a novelty claim.
- Keep the Davis--Kahan priority language cautious unless the historical search is
  completed and documented.
