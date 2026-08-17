# formalization_draft2

Second paper scaffold for the source-faithful Lean formalization of the
Davis--Kahan / Yu--Wang--Samworth perturbation lineage.  The final manuscript
may emphasize Davis--Kahan more strongly than YWS; the source intentionally
keeps that framing question open while the mathematical and dependency evidence
is audited.  The current scaffold has three supporting stories:

1. formalization as mathematical audit: two printed YWS source defects and the
   false Davis--Kahan Proposition 4.4;
2. formalization as reusable statistical infrastructure: the Quench theorem
   family and the operator-theory layer now being staged toward Tau Ceti; and
3. formalization as an instrumented human--LLM development process: measured
   token/resource usage, incomplete accounting coverage, model and interaction
   provenance, and an explicit missing-data model rather than a single
   misleading cost number.

The directory is intentionally self-contained at the paper layer. Raw evidence
continues to live in the repository; scripts here read it without rewriting it.
`development_notes.md` records process observations that are worth preserving
but are not yet manuscript claims.

## Build

All paper-local analysis outputs under `generated/` are reproducible and are
therefore gitignored. LaTeX/latexmk build products (including `paper.pdf`) are
also gitignored; source `.tex` and `.bib` files remain tracked. This keeps a
plain `git add papers/formalization_draft2` limited to durable source inputs.

Build the manuscript from a clean checkout with:

```bash
make -C papers/formalization_draft2 paper
```

The `paper` target first rebuilds every required generated analysis artifact via
`scripts/build_all.py`, then runs `latexmk`. To regenerate the analysis without
building the PDF, use:

```bash
make -C papers/formalization_draft2 accounting
```

`make -C papers/formalization_draft2 clean` removes both LaTeX build products
and the paper-local `generated/` tree.

### Literature-review memo

`literature_review.tex` is a standalone, deliberately over-complete literature
and positioning memo.  It is a superset of what should eventually appear in
`paper.tex`: mathematical perturbation lineage, pre-LLM formalization practice,
AI theorem proving and project-scale formalization, semantic/source-fidelity
work, statistics and applied-science formalization, human--AI process studies,
proof provenance, and open novelty checks.  Whole subsections are expected to be
cut when the eventual Related Work section is written.

Build it from a clean checkout with:

```bash
make -C papers/formalization_draft2 literature
```

The literature search is date-stamped in the memo because the nearby 2026
literature is changing rapidly.

## Dependency analysis for framing

`scripts/build_dependency_analysis.py` parses local Lean import statements and
computes conservative source-level import closures for the YWS citation surface,
the Davis--Kahan umbrella, and the Quench umbrella.  The generated report is
used to test framing claims rather than assume that every foundational module
built during the Davis--Kahan effort was required by YWS.

The present source-level result is directionally important: the YWS citation
surface closes over 60 local modules, whereas `DavisKahan.All` closes over 711;
the two closures overlap in 37 modules.  Import closure is only an upper bound
on declaration-level proof dependence, so these counts should not be presented
as a proof-dependency census without a stronger environment/declaration graph.

## Source-census design

The YWS census is keyed on the **paper**, not on the Lean tree. A source claim
gets a row even when no Lean declaration exists, so an absence remains visible.
The current census has 24 tracking entries, but those entries are not "24 YWS
theorems": they include theorem conclusions, lemmas, corollaries, equations,
identities, examples, a definition, source-scope/audit rows, and two explicitly
marked additions beyond the printed paper.

`scripts/build_source_census.py` reads the repository census and generates a
paper-local full inventory plus a source-kind summary. This is the mechanism the
paper should introduce before quoting the census size.

## Proof-provenance design

The project borrowed or adapted proof ideas from several formal sources,
especially the former Spectra collaboration, as well as external Lean projects
and Mathlib PRs. `scripts/build_provenance.py` inventories the module-level
`## Provenance` blocks and the maintained external-source registries. Its output
is a **citation-audit seed**, not an automatic intellectual-provenance detector.

Before submission, proofs discussed in the manuscript should distinguish:

1. copied or closely adapted code;
2. mathematics ported with substantial API rewriting;
3. a donor proof strategy followed by an independent re-derivation; and
4. an ordinary upstream Mathlib dependency.

## Accounting design

The accounting study has two related scopes. Commit-level coverage is measured
against the pinned Git history of the primary formalization repository. Measured
token totals use an explicit allowlist of ledger repositories because some
Tau Ceti foundations work relevant to the paper was carried out in a second
repository. The allowlist is configured in `analysis_config.json`; repository
identity is never inferred from a commit hash.

Commits that touch **only** `papers/formalization_draft2/` are excluded from the
formalization-history corpus. Mixed commits remain in scope. This makes the
exclusion policy useful when the snapshot is advanced during paper preparation
without deleting legitimate mathematical work that happened to share a commit
with documentation.

The paper deliberately separates three kinds of resource evidence.

- **Exact commit-attributed measurement.** A ledger row names a git commit SHA.
  These numbers can be summed at commit or component level.
- **Measured but commit-unattributed usage.** `pending@...` ledger rows retain
  measured session-level usage but not a defensible allocation to individual
  commits. `generated/pending_segments.csv` lists time-window candidate commits;
  the script never silently assigns the tokens.
- **Unmeasured work.** This includes work before instrumentation and work done
  through interfaces for which equivalent telemetry was unavailable. A small
  log-ridge model emits exploratory estimates only for commits with positive LLM
  provenance and no overlap with a pending measured window. The paper continues
  to report measured values separately from modeled values.

### Model-resolved token accounting

Ledger schema v3 stores an exact `bm` token vector by model on every measured
token-bearing row. The accounting loader verifies that those vectors sum to the
row total. Consequently measured ordinary-input, cache-write, cache-read, and
output tokens can be tied exactly to the model that consumed them, even in a
session that switched models. The ledger does not expose a corresponding
per-model turn count, so the scripts do not invent one.

Model-resolved pricing is deliberately a separate transformation. Populate
`data/model_pricing.csv` with historically applicable per-million rates for each
model and token class, together with the rate's effective date and source. Cost
columns remain blank until a complete rate vector exists. Never price a
project-wide aggregate with one average token rate.

For extrapolated usage, `generated/imputed_tokens_by_model.csv` records both the
model assignment and the number of exact ledger commits providing direct
calibration for that model. Models with no direct measured calibration are
flagged explicitly.

### Git co-authors versus ledger models

Git `Co-authored-by` trailers provide a second model-provenance channel. The
analysis preserves four levels separately: the raw trailer text, canonicalized
trailer labels, any explicitly configured historical interpretation, and exact
ledger model attribution. Exact ledger attribution wins whenever it exists.

For this study only, `analysis_config.json` contains an author-confirmed,
time-bounded GPT rule. On **unledgered** commits dated 2026-06-03 through
2026-08-14, raw GPT-5.6 `High` and `Thinking` trailer labels are interpreted as
GPT-5.6 Sol chat-interface work. The raw labels remain in the manifest, and the
rule expires after 2026-08-14 rather than becoming a permanent model-name
synonym. `generated/gpt_chat_rule_matches.csv` is the complete audit trail.

Raw GPT-5.6 Sol trailer commits are *not* automatically labeled as chat. They
remain in `generated/chat_interface_review_candidates.csv` unless contemporaneous
evidence or an explicit row in `data/accounting_overrides.csv` establishes the
interaction channel.

Anthropic trailers are handled differently. Fable/Opus model switches could
occur inside a harness session without updating the commit-time co-author
instruction, so the scripts do not normalize those trailer names toward the
ledger. Mismatches are retained as review signals. For measured usage, the
ledger's per-model token vector is authoritative.

`data/accounting_overrides.csv` remains the manual provenance seam for evidence
that cannot be reconstructed mechanically. Silence is left `unknown`; apart
from the bounded historical GPT rule, chat-interface assistance is not guessed
from missing telemetry.

The analysis history is pinned in `analysis_config.json`. The rendered PDF shows
the snapshot **date**, not the Git hash; the full hash is retained in generated
source and attached to the displayed date as PDF tooltip metadata.

## Citation-count snapshots

Citation counts used for motivation in the manuscript are collected separately
from the normal paper build.  OpenAlex is queried by the two published DOIs in
`data/bibliometrics/openalex_works.json`; the network utility writes a dated,
tracked source snapshot to `data/bibliometrics/openalex_snapshot.json` and TeX
macros to `generated/openalex_bibliometrics_macros.tex`.

OpenAlex currently requires an API key.  Obtain a free key from OpenAlex, then
run:

```bash
export OPENALEX_API_KEY=...
make -C papers/formalization_draft2 bibliometrics
```

For an audit of the exact requests without making a network call:

```bash
python3 papers/formalization_draft2/scripts/fetch_openalex_bibliometrics.py --dry-run
```

The snapshot deliberately records the retrieval timestamp, DOI, OpenAlex work
identifier, total `cited_by_count`, `counts_by_year`, and OpenAlex `updated_date`,
but never records the API key.  The regular `paper` and `accounting` targets do
not contact OpenAlex.

Google Scholar counts are intentionally not scraped by repository tooling.  If
we report them, record the visible `Cited by` values and observation date
manually in the manuscript or a tracked bibliometric note, alongside the dated
OpenAlex snapshot.  Both sources should be named explicitly because citation
counts are database- and date-dependent.

## Generated artifacts

`generated/dependency_import_closure.csv`, `generated/dependency_target_summary.csv`,
`generated/dependency_target_overlap.csv`
: Conservative local Lean source-import closures and target overlaps used to
  distinguish the YWS dependency surface from the much larger Davis--Kahan
  development.  These are source-level upper bounds, not declaration-level use
  graphs.

`generated/yws_census_items.csv`, `generated/yws_census_by_kind.csv`
: Full paper-keyed YWS tracking inventory and a compact explanation of what its
  rows count.

`generated/proof_provenance_inventory.csv`, `generated/proof_provenance_sources.csv`
: Module-level recorded provenance plus the maintained source registries that
  seed the declaration-level citation audit.

`generated/commit_accounting_manifest.csv`
: One row per commit in the pinned history, including code-change features,
  trailer/manual/ledger model provenance, exact ledger measurements,
  pending-window overlap, component labels, and extrapolation eligibility.

`generated/study_commit_exclusions.csv`
: Commits excluded because every touched path matches a configured manuscript-
  only prefix. Mixed mathematical/manuscript commits remain in the study.

`generated/ledger_repository_summary.csv`
: Program-wide measured usage broken out by explicitly allowlisted ledger
  repository. This is separate from primary-repository Git coverage.

`generated/gpt_chat_rule_matches.csv`
: Every commit affected by the bounded historical GPT-5.6 High/Thinking -> Sol
  chat-interface interpretation, with the raw label retained.

`generated/pending_segments.csv`
: Measured `pending@...` usage segments and all commits whose timestamps fall in
  the recorded session span. These are allocation candidates, not allocations.

`generated/model_token_breakdown.csv`
: Exact measured token counts by normalized model and token class, derived from
  the ledger's per-model vectors.

`generated/coauthor_model_summary.csv`, `generated/model_provenance_reconciliation.csv`
: Counts and commit-level relations between Git co-author model provenance,
  manual provenance, and exact ledger models.

`generated/model_provenance_disagreements.csv`
: The subset with partial overlap or disjoint declared/ledger model sets.

`generated/chat_interface_review_candidates.csv`
: Conservative review queue for raw GPT-5.6 Sol trailer commits whose interface
  is not otherwise established. Candidate status is not a channel label.

`generated/model_cost_breakdown.csv`, `generated/model_cost_summary.csv`
: Cost worksheets. Dollar columns remain blank until historical pricing is
  supplied and sourced.

`generated/accounting_state_summary.csv`
: Exact-versus-unaccounted commit coverage.

`generated/component_accounting_summary.csv`
: Coverage and exact measured usage for YWS, Davis--Kahan, Quench, Tau Ceti
  staging, paper/docs, and tooling path families. Components overlap by design.

`generated/accounting_coverage_by_week.csv`
: Time series for visualizing the transition from pre-instrumentation work to
  partially instrumented development.

`generated/imputation_validation.csv`
: Rolling-origin validation for the exploratory missing-cost model.

`generated/imputation_predictions.csv`, `generated/imputed_tokens_by_model.csv`
: Per-commit and model-grouped exploratory predictions. Only rows marked
  `extrapolation_eligible=1` enter the default extrapolated total.

`generated/interaction_*.csv`
: Deduplicated post-hoc human-prompt, taxonomy, event, and per-agent summaries.

`generated/*_macros.tex` and `generated/*_table.tex`
: Small LaTeX fragments consumed by `paper.tex`.

## Important limitations to retain in the paper

- Accounting began after substantial work had already occurred.
- Backfilled agent transcripts recover some earlier usage but do not make the
  early history complete.
- Some work happened through chat interfaces with no equivalent local token
  telemetry. Missing chat logs also remove evidence about initiative and
  steering, not just token counts.
- Git co-author trailers establish model provenance, not token use. Interaction
  channel is inferred only from explicit evidence or the narrow, time-bounded
  GPT-5.6 chat rule recorded in `analysis_config.json`.
- Anthropic ledger/trailer disagreement must be reviewed rather than normalized
  away because mid-session model switches can make the commit trailer stale.
- `pending@...` time spans can be broad; a timestamp overlap is evidence for a
  possible allocation, not proof that a particular commit consumed those tokens.
- Missingness is not random. Agent-harness, chat-interface, pre-instrumentation,
  and manual work have different observation mechanisms.
- Some model variants used in unmeasured work have no direct measured ledger
  calibration. Their extrapolations require wider skepticism/sensitivity tests.
- Monetary cost depends on historically applicable model- and token-class rates;
  token measurements are primary evidence and pricing inputs must be sourced.
- The current extrapolation model is exploratory. Its validation and provenance
  overrides must be audited before any modeled total is quoted as a result.
- The committed `lifetime-totals.json` can lag the append-only ledger. The paper
  scripts recompute measured totals from the ledger and report the reconciliation.
- Retrospective author memory is not treated as ground truth where contemporaneous
  traces exist; see `development_notes.md`.

## Editorial strategy for the process study

`appendix_process.tex` is intentionally over-complete. The main manuscript should
keep YWS, the source audits, the foundational mathematical stack, and Quench at
the center. Detailed accounting mechanics, provenance reconciliation, prompt
taxonomies, and interaction archaeology are developed in the appendix first so
they can be cut aggressively without losing the underlying generated evidence.
