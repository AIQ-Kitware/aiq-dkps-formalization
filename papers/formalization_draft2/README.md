# formalization_draft2

Second paper scaffold centered on the source-faithful Lean formalization of
Yu--Wang--Samworth (YWS), with three supporting stories:

1. formalization as mathematical audit: two YWS source defects and the false
   Davis--Kahan Proposition 4.4;
2. formalization as reusable statistical infrastructure: the Quench theorem
   family and the operator-theory layer now being staged toward Tau Ceti; and
3. formalization as an instrumented human--LLM development process: measured
   token/resource usage, incomplete accounting coverage, interaction traces,
   and an explicit missing-data model rather than a single misleading cost
   number.

The directory is intentionally self-contained at the paper layer. Raw evidence
continues to live in the repository; scripts here read it without rewriting it.

## Build

Rebuild all generated accounting and interaction artifacts:

```bash
python3 papers/formalization_draft2/scripts/build_all.py
```

or, from this directory:

```bash
make accounting
```

Then build the manuscript:

```bash
make -C papers/formalization_draft2 paper
```

Run the analysis smoke tests with:

```bash
make -C papers/formalization_draft2 test
```

## Accounting design

The paper deliberately separates three kinds of evidence.

- **Exact commit-attributed measurement.** A ledger row names a git commit SHA.
  These numbers can be summed at commit or component level.
- **Measured but commit-unattributed usage.** `pending@...` ledger rows retain
  measured session-level usage but not a defensible allocation to individual
  commits. `generated/pending_segments.csv` lists time-window candidate commits;
  the script never silently assigns the tokens.
- **Unmeasured work.** This includes work before instrumentation and work done
  through interfaces for which equivalent telemetry was unavailable. A small
  log-ridge model emits exploratory estimates only for commits with positive LLM
  provenance and no overlap with a pending measured window. The paper should
  continue to report measured values separately from modeled values.

`data/accounting_overrides.csv` is the manual provenance seam. It is where we
can record commits known from historical evidence to have been produced via a
chat interface, manually, or by a mixed workflow. Silence is left `unknown`;
chat-interface assistance is not guessed from the absence of telemetry.

The analysis history is pinned in `analysis_config.json`. This prevents later
paper-writing commits from silently entering the historical development corpus.
Update `history_cutoff_commit` only when intentionally advancing the snapshot.

## Generated artifacts

`generated/commit_accounting_manifest.csv`
: One row per commit in the pinned history, including code-change features,
  LLM provenance, exact ledger measurements, pending-window overlap, component
  labels, and extrapolation eligibility.

`generated/pending_segments.csv`
: Measured `pending@...` usage segments and all commits whose timestamps fall in
  the recorded session span. These are allocation candidates, not allocations.

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

`generated/imputation_predictions.csv`
: Per-commit model predictions. Only rows marked `extrapolation_eligible=1` are
  included in the default extrapolated total.

`generated/interaction_*.csv`
: Deduplicated post-hoc human-prompt, taxonomy, event, and per-agent summaries.

`generated/*_macros.tex` and `generated/*_table.tex`
: Small LaTeX fragments consumed by `paper.tex`.

## Important limitations to retain in the paper

- Accounting began after substantial work had already occurred.
- Backfilled agent transcripts recover some earlier usage but do not make the
  early history complete.
- Some work happened through chat interfaces with no equivalent local token
  telemetry.
- `pending@...` time spans can be broad; a timestamp overlap is evidence for a
  possible allocation, not proof that a particular commit consumed those tokens.
- Missingness is not random. Agent-harness, chat-interface, pre-instrumentation,
  and manual work have different observation mechanisms.
- The current extrapolation model is exploratory. Its validation and provenance
  overrides must be audited before any modeled total is quoted as a result.
- The committed `lifetime-totals.json` can lag the append-only ledger. The paper
  scripts recompute measured totals from the ledger and report the reconciliation.
