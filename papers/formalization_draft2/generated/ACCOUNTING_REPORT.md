# Accounting coverage report

Pinned history cutoff: `7aeff6b62ccab2f96ee64606bc87e368a1650502` (4,637 commits).
Instrumentation enters history at `9f59916f1c7af3f06b6b0f24e31e2431a7e259d7` (2026-07-04T00:58:13+00:00).

## Measured lower bound

- ledger model turns: **42,090**
- output tokens: **44,950,936**
- billable-input accounting measure: **15,750,533,373**
- exact ledger commit IDs: **1,485**; on pinned history: **1,475**
- pinned-history commits without exact commit-level accounting: **3,162**
- commits preceding the instrumentation commit: **193**
- measured but commit-unattributed pending segments: **96** containing **10,204** turns
- note: `lifetime-totals.json` is behind the current ledger (1,651 vs. 1,698 ledger rows); the paper pipeline recomputes measured totals from the ledger itself

## Commit accounting states

- `exact_measured`: **1,475**
- `instrumentation_commit_unmeasured`: **1**
- `unmeasured_post_instrumentation`: **2,968**
- `unmeasured_pre_instrumentation`: **193**

## Provenance warning

Automatic LLM provenance is conservative: it recognizes explicit LLM co-author trailers and a small set of agent authors. Chat-interface work must be entered in `data/accounting_overrides.csv`; absent such an override, it remains `unknown`.

## Exploratory extrapolation

The current model has 1,296 extrapolation-eligible commits. These are positive-evidence LLM-assisted commits with neither exact accounting nor overlap with a measured pending segment.
- turns: point **21,334**, residual-bootstrap 5--95% sensitivity interval **18,320--26,256**
- output_tokens: point **16,927,224**, residual-bootstrap 5--95% sensitivity interval **14,324,753--21,183,456**
- billable_input_tokens: point **6,842,269,704**, residual-bootstrap 5--95% sensitivity interval **5,806,171,263--8,512,169,190**

These model-based values are not part of the measured lower bound and should not be quoted without first auditing the override file, the validation table, and the missingness assumptions.
