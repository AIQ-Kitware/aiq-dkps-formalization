# Accounting coverage report

Pinned study snapshot: **August 13, 2026** (source commit `7aeff6b62ccab2f96ee64606bc87e368a1650502`; 4,637 included primary-repository commits).
Instrumentation enters history on **July 3, 2026** (source commit `9f59916f1c7af3f06b6b0f24e31e2431a7e259d7`; Git author-date presentation).

## Study scope

Commit-level coverage is computed on the primary formalization repository after path-only exclusions. Measured token totals are program-wide across the explicitly allowlisted ledger repositories.
- `aiq-dkps-formalization`: **36,116** turns, **40,456,441** output tokens; primary formalization repository
- `aiq-gpu-docs`: **5,974** turns, **4,494,495** output tokens; author-confirmed cross-repository work in scope as part of the TauCeti foundations contribution

## Measured lower bound

- ledger model turns: **42,090**
- output tokens: **44,950,936**
- billable-input accounting measure: **15,750,533,373**
- exact ledger commit IDs across the in-scope program: **1,485**; primary-repository exact IDs: **939**; on included pinned history: **933**
- pinned-history commits without exact commit-level accounting: **3,704**
- commits preceding the instrumentation commit: **193**
- measured but commit-unattributed pending segments: **96** containing **10,204** turns
- note: `lifetime-totals.json` is behind the current ledger (1,651 vs. 1,698 ledger rows); the paper pipeline recomputes measured totals from the ledger itself

## Commit accounting states

- `exact_measured`: **933**
- `instrumentation_commit_unmeasured`: **1**
- `unmeasured_post_instrumentation`: **3,510**
- `unmeasured_pre_instrumentation`: **193**

## Measured tokens by model

Ledger schema v3 supplies an exact per-model token vector for every measured row. This remains exact when a session switched models; model turns are not allocated because the ledger has no by-model turn count.
- `claude-opus-5`: output **20,629,210**; billable-input measure **9,925,849,182** (986 ledger rows)
- `claude-opus-4-8`: output **15,967,324**; billable-input measure **3,804,650,205** (390 ledger rows)
- `claude-fable-5`: output **7,487,637**; billable-input measure **1,472,244,294** (158 ledger rows)
- `gpt-5.6-terra`: output **539,325**; billable-input measure **376,932,060** (87 ledger rows)
- `gpt-5.6-sol`: output **327,440**; billable-input measure **170,857,632** (36 ledger rows)
- dollar costs are intentionally not computed yet: `data/model_pricing.csv` has no verified historical rates for measured models

## Git/ledger model provenance reconciliation

- raw Git/ledger model signals with partial overlap or disjoint labels: **79**
- time-bounded GPT-5.6 High/Thinking -> Sol chat-rule commits: **217**
- additional GPT-5.6 Sol chat-interface review candidates: **87**
- total commits currently classified as chat-interface: **217**
The GPT High/Thinking rule is an author-confirmed historical convention, applies only to unledgered commits in the configured study interval, and never overrides exact ledger model attribution. Raw trailer labels remain in the manifest. Other trailer/ledger differences remain review signals rather than errors.

## Provenance warning

Exact ledger rows establish measured harness model usage. Git co-author trailers are a separate provenance signal and can be stale when a session changes models before committing (notably among Anthropic Opus/Fable sessions). Outside the explicit bounded GPT chat rule, interface provenance remains unknown unless a manual override or another contemporaneous trace establishes it.

## Exploratory extrapolation

The current model has 1,826 extrapolation-eligible commits. These are positive-evidence LLM-assisted commits with neither exact accounting nor overlap with a measured pending segment.
- turns: point **33,235**, residual-bootstrap 5--95% sensitivity interval **28,271--39,430**
- input_tokens: point **6,797,026**, residual-bootstrap 5--95% sensitivity interval **4,021,219--12,809,217**
- cache_write_tokens: point **38,542,773**, residual-bootstrap 5--95% sensitivity interval **30,366,983--50,665,777**
- cache_read_tokens: point **8,737,201,457**, residual-bootstrap 5--95% sensitivity interval **7,074,950,830--10,891,879,094**
- output_tokens: point **24,896,765**, residual-bootstrap 5--95% sensitivity interval **20,791,463--29,582,185**
- billable_input_tokens: point **8,831,882,493**, residual-bootstrap 5--95% sensitivity interval **7,233,347,041--11,241,379,425**

These model-based values are not part of the measured lower bound and should not be quoted without first auditing the override file, the validation table, model calibration coverage, and the missingness assumptions.
