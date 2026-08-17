# Claims-to-evidence map

Working map for the paper. This is intentionally stricter than a prose outline:
each headline claim should point to source material that can be independently
audited before submission.

| Claim | Primary repository evidence | Paper role |
|---|---|---|
| YWS is represented source-faithfully at published numbering/generality | `YuWangSamworth2015/README.md`, `YuWangSamworth2015/PROOF_OBLIGATIONS.md`, `dev/yu-wang-samworth-2015-full-source-census.json` | Main mathematical contribution |
| The paper-keyed YWS tracking census has 24 entries and all currently resolve in the default build | `generated/yws_census_items.csv`, `generated/CENSUS_REPORT.md`, source census JSON | Coverage statement; explicitly explain what the entries count |
| The 24-entry census is not a count of named YWS theorems and includes two explicitly marked non-source additions | `generated/yws_census_items.csv`, `generated/yws_census_by_kind.csv` | Prevent misleading coverage language |
| Printed YWS equation (4) is false and corrected | `YuWangSamworth2015/YuWangSamworth2015/Symmetric/AngleIdentity.lean` | Formalization-as-audit case study |
| Printed YWS Theorem 3 rank-boundary convention is false and corrected | `YuWangSamworth2015/YuWangSamworth2015/Rectangular/RankBoundary.lean`, source census row `YWS-T3-rankBoundary` | Formalization-as-audit case study |
| Davis--Kahan Proposition 4.4 is false as printed | `papers/davis_kahan_prop_4_4_counterexample.tex`, corresponding Lean source under `DavisKahan/` | Independent source-audit result |
| The formal spectral stack supports a contemporary downstream theorem | `DkpsQuench2026/README.md`, `DkpsQuench2026/Paper/Theorem2.lean`, `DkpsQuench2026/Geometry/AlignedCMDS.lean` | Reuse / integration case study |
| DK/YWS development forced foundational operator-theory layers absent from the needed Mathlib surface | `ForTauCeti/`, `DavisKahan/`, Tau Ceti roadmap submodule and migration notes | Motivation and amortization argument |
| Some formal proofs/strategies have Spectra or other external Lean ancestry and require explicit scholarly citation | `generated/proof_provenance_inventory.csv`, `dev/tauceti/spectra-provenance-map.md`, `dev/external-lean-references.md`, module `## Provenance` blocks | Proof-provenance/citation audit |
| A substantial fraction of project history lacks exact commit-level telemetry | `generated/commit_accounting_manifest.csv`, `generated/accounting_summary.json` | Accounting limitation/result |
| Program-wide measured token totals include explicitly allowlisted cross-repository Tau Ceti foundations work, whereas commit-coverage denominators use the primary Git history | `analysis_config.json`, `generated/ledger_repository_summary.csv`, `generated/accounting_summary.json` | Keep accounting-program scope distinct from available Git-history scope |
| Commits touching only `papers/formalization_draft2/` are excluded from the formalization-history corpus; mixed commits remain included | `analysis_config.json`, `generated/study_commit_exclusions.csv` | Prevent manuscript production from feeding back into formalization-cost estimates |
| PDF presentation uses a snapshot date while retaining the exact Git hash only as generated source/tooltip metadata | `generated/accounting_macros.tex`, `paper.tex` | Reproducibility without presenting hashes as reader-facing values |
| Backfilled usage includes measured but commit-unattributed sessions | `.llm_resource_tally/ledger/ledger.jsonl`, `generated/pending_segments.csv` | Missing-data methodology |
| Measured tokens can be attributed exactly by model and token class | ledger `bm` vectors, loader reconciliation check, `generated/model_token_breakdown.csv` | Model-resolved accounting/cost basis |
| Model-resolved dollar cost requires historically applicable model- and token-class rates | `data/model_pricing.csv`, `generated/model_cost_breakdown.csv`, `generated/model_cost_summary.csv` | Pricing methodology; do not use a global token price |
| Git co-author model provenance can corroborate or disagree with exact ledger model attribution | `generated/coauthor_model_summary.csv`, `generated/model_provenance_reconciliation.csv`, `generated/model_provenance_disagreements.csv` | Provenance reconciliation |
| Unledgered GPT-5.6 High/Thinking trailers in the author-confirmed 2026-06-03--2026-08-14 study window are interpreted as GPT-5.6 Sol chat-interface work, while exact ledger attribution takes precedence | `analysis_config.json`, `generated/gpt_chat_rule_matches.csv`, raw/resolved columns in `generated/commit_accounting_manifest.csv` | Bounded historical provenance rule; preserve raw labels and do not project into future history |
| Raw GPT-5.6 Sol trailer commits without independent channel evidence remain review candidates rather than automatic chat classifications | `generated/chat_interface_review_candidates.csv`, `data/accounting_overrides.csv` | Separates author-confirmed High/Thinking rule from weaker raw-Sol recollection |
| Anthropic Fable/Opus trailer labels can disagree with exact measured model use after mid-session model switches | raw/resolved/ledger columns in `generated/commit_accounting_manifest.csv`, `generated/model_provenance_disagreements.csv` | Treat mismatch as provenance evidence, not an error to normalize away |
| Confirmed chat-interface work is incompletely observed by the local harness | bounded GPT rule + manual provenance review + `data/accounting_overrides.csv` | Explicit limitation; do not overclaim from telemetry |
| Human steering can be characterized from retained transcripts | `dev/posthoc-prompt-analysis/findings/`, `generated/interaction_summary.json` | Human--LLM process analysis |
| The first formal YWS census commit records a human request but an agent-designed elaboration into richer tooling | commit `c559384a51e2fb55d3111bc00e8e450fccaa47ac`, `development_notes.md` | Coordination-tooling case study |
| Retrospective recollection can disagree with retained process records in this project | `development_notes.md` + contemporaneous census commit | Qualitative limitation/interaction archaeology; single-project observation only |

## Before submission

- Replace path-level evidence with declaration-level citations for each formal
  theorem quoted in the paper.
- Complete the proof-provenance audit: cite Spectra, external Lean sources,
  Mathlib PRs, and mathematical literature at the relevant proof/construction,
  distinguishing adaptation from strategy influence and ordinary dependencies.
- Freeze and archive the accounting snapshot used for final numbers.
- Fill `data/model_pricing.csv` only with historically applicable rates and
  record effective dates and sources before quoting dollar costs.
- Audit `generated/model_provenance_disagreements.csv` and every proposed chat
  attribution. Enter confirmed channel/model evidence in
  `data/accounting_overrides.csv`; do not infer chat from a missing ledger row.
- Inspect model-specific calibration coverage before quoting imputed usage or
  imputed cost for model variants with no exact measured examples.
- Re-run a related-work search immediately before submission; AI formalization is
  changing too quickly for the current scaffold to freeze a novelty claim.
- Keep the Davis--Kahan priority language cautious unless the historical search is
  completed and documented.
