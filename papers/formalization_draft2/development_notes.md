# Development/process notes for formalization_draft2

These notes record observations that may or may not survive into the submitted
paper. They are deliberately separated from polished manuscript claims so that
interesting process evidence is not lost while its interpretation is still
being audited.

## Source census: what it is and how it arose

The YWS census is a **paper-keyed progress and audit instrument**, not a count of
Lean declarations and not a count of named theorems. Its defining design choice
is that rows are created from the source paper, including rows for material that
is absent from the formalization. A Lean-tree inventory cannot expose an absent
source obligation because it only enumerates artifacts that already exist.

The current census has 24 entries. The entries include theorem conclusions,
lemmas, corollaries, equations, identities, examples, a definition, a source
scope/convention check, and exposition/audit rows. Two current rows are
explicitly marked as additions beyond the printed paper: the application-shaped
rank-one singular-vector consequences and the modern self-adjoint-dilation
alternative. See `generated/yws_census_items.csv` and `CENSUS_REPORT.md`.

The interaction history should not be simplified into either "the human designed
the census" or "the LLM spontaneously invented project management." The first
formal YWS census commit is
`c559384a51e2fb55d3111bc00e8e450fccaa47ac` (2026-07-29). Its commit message
explicitly records that Jon asked for a manifest and a programmatic check of the
paper's total formalization coverage. The implementation then elaborated this
request substantially: it keyed rows on the paper rather than the Lean tree,
distinguished mathematical `status` from build-backed `verification`, detected
private-versus-missing declarations, added a canary, generated a rendering, and
tested failure/staleness behavior. Later review adopted and constrained this
tooling as part of the progress-audit workflow.

This chronology should be reconstructed from contemporaneous records before any
claim about agent initiative/autonomy is made in the paper.

## Retrospective recall is incomplete

During discussion on 2026-08-14, Jon did not initially remember whether he had
explicitly requested the source-tracking mechanism. The retained commit record
then showed an explicit request for the manifest/programmatic check.

This is worth retaining as a methodological observation: long-running agentic
work generates many short-lived operational requests and decisions that are not
necessarily rehearsed or retained in the human participant's memory.
Contemporaneous logs can therefore function as **interaction archaeology**: they
can reconstruct initiative, refinement, and decision history more reliably than
retrospective recollection alone.

This also changes how missing chat-interface data should be described. Missing
chat logs are not only missing token telemetry. They remove evidence about what
the human requested, what the model elaborated, and how a result evolved. In the
paper, author recollection should be labeled as recollection and corroborated
against retained traces where possible. No broad cognitive/psychological claim
should be inferred from this single project.

## Wording of the YWS audit findings

Use **"two printed source defects in YWS"**, not "two false YWS theorems."

1. Printed equation (4) is a false polynomial identity because a square is
   missing. The repository contains a machine-checked refutation of the printed
   formula and a proof of the corrected identity.
2. Theorem 3's printed convention
   `sigma^2_{rank(A)+1} := -infinity` is false at the rank boundary. The theorem's
   intended Gram-matrix argument uses the ambient singular/eigenvalue index and
   the zero continuation of singular values. Several theorem-facing census rows
   use the corrected convention, which is why `compiled_corrected` occurs on
   more than two rows; it does **not** mean that five independent source defects
   were discovered.

Reserve "false theorem/proposition" for a precisely identified false
specialization or for Davis--Kahan Proposition 4.4, for which the project has an
explicit finite-dimensional counterexample.

## Proof provenance and citation debt

The final paper must cite mathematical and Lean proof donors at the points where
the borrowed ideas matter. The repository already contains substantial
provenance evidence:

- `dev/tauceti/spectra-provenance-map.md`;
- `dev/external-lean-references.md`;
- `dev/external-literature-references.md`;
- module-level `## Provenance` blocks throughout `ForTauCeti`, `DavisKahan`,
  `YuWangSamworth2015`, and `DkpsQuench2026`;
- `papers/formalization_draft1/model_provenance.md`.

`generated/proof_provenance_inventory.csv` inventories the module-level blocks
for paper review. This is only a seed for a declaration-level citation audit.
For the paper, distinguish at least:

1. copied or closely adapted code;
2. mathematics ported with substantial API rewriting;
3. a donor proof strategy followed by an independent re-derivation; and
4. an ordinary upstream Mathlib dependency.

Spectra ancestry is especially important because many foundational proofs were
ported or adapted from that collaboration. External Lean libraries and Mathlib
PRs also served as donors/references for some cases and need their own citations.

## Model provenance, chat-interface work, and accounting

The resource ledger and Git history give two independent model-provenance views.
Ledger schema v3 includes an exact `bm` per-model token vector on every measured
token-bearing row; the accounting script verifies that the per-model vectors sum
exactly to each row total. Git `Co-authored-by` trailers record contribution
provenance at commit time, but neither exact token usage nor, in general, the
interaction channel.

The analysis therefore preserves raw trailer labels, canonical trailer labels,
study-specific historical interpretations, and exact ledger model attribution as
separate fields. Exact ledger attribution is authoritative whenever present. A
trailer/ledger mismatch remains useful provenance evidence rather than being
automatically treated as an error.

Raw GPT-5.6 Sol trailers form a useful review population, but they are not by
themselves sufficient to classify the interaction as chat-based. Confirmed manual
provenance belongs in `data/accounting_overrides.csv`; the separately documented
High/Thinking historical rule is the only current automatic chat-interface
interpretation.

Token cost analysis must be **model resolved and token-class resolved** before
pricing. `generated/model_token_breakdown.csv` gives exact measured token counts
by model. `data/model_pricing.csv` is the explicit seam for historically
applicable input/cache-write/cache-read/output rates, effective dates, and
sources. Dollar figures should remain blank until those rates are verified.

For unmeasured work, model identity should be used as a predictor/stratum where
available. The extrapolation output records direct measured calibration coverage
per model. Models with no exact ledger observations must remain visibly less
identified than models with direct calibration.

## Analysis scope and manuscript-production exclusion

The accounting study should not equate "work in this Git repository" with the
full research program. On 2026-08-14 Jon clarified that ledger rows from the
second retained repository are related to the Tau Ceti foundations contribution
and are in scope for this paper. `analysis_config.json` therefore has an explicit
allowlist of ledger repositories. Program-wide measured token totals use that
allowlist, while commit-level coverage statistics use the primary formalization
Git history available in this checkout. The paper must keep those denominators
and numerators visibly distinct.

Paper production should not inflate the formalization cost as the snapshot moves
forward. The configured exclusion removes a commit only if *all* paths touched by
that commit lie under `papers/formalization_draft2/`. A mixed commit remains in
scope. This is a simple blocklist policy rather than an attempt to infer intent
from commit messages, and it can be expanded if future clearly non-research path
families need exclusion.

Presentation rule: the manuscript should display a human-readable snapshot date.
The exact Git hash remains in generated source metadata and can appear as a PDF
hover tooltip on the date, but should not be a visible value in prose/tables.

## GPT-5.6 chat-interface historical rule

Jon clarified a project-specific convention for GPT-5.6 Git trailers. During the
study interval from 2026-06-03 through 2026-08-14, unledgered commits carrying
`GPT-5.6 High` or `GPT-5.6 Thinking` co-author labels came from GPT-5.6 Sol chat
interactions; High/Thinking described the chat setting rather than a distinct
model identity relevant to this study. This knowledge should be encoded as a
bounded historical rule, not as a permanent global model-name alias.

The rule has strict precedence semantics:

1. Preserve the raw trailer string in the manifest.
2. If exact ledger model attribution exists, the ledger wins and the heuristic
   is not applied.
3. Otherwise, inside the date window only, High/Thinking resolve to GPT-5.6 Sol
   and channel `chat_interface`.
4. Do not project the rule past 2026-08-14 without new author confirmation.

At the pinned snapshot this rule matches 217 commits. Raw `GPT-5.6 Sol` trailer
commits are a separate case: many are believed to have come from chat, but the
current automatic analysis leaves them as review candidates unless independent
evidence establishes the channel.

Do not apply an analogous normalization to Anthropic Fable/Opus trailers. Jon
notes that a harness session could switch between those models without updating
the commit-time co-author instruction. In measured sessions the ledger's
per-model token vector is therefore stronger evidence of actual model use than
the trailer; mismatches should be retained as evidence about provenance mechanics
rather than "fixed" into agreement.

## Editorial strategy for the empirical/process material

The process study is likely to be much shorter in the submitted paper than in the
working draft. For now, elaborate the complete methodology and observations in
appendix-ready source: accounting scope, missingness classes, model resolution,
Git/ledger reconciliation, pricing, imputation, interaction taxonomy, source-
census chronology, and interaction archaeology. This makes it possible to see
what is actually interesting before cutting.

The main paper should keep only empirical results that sharpen or qualify the
mathematical story. Fine-grained diagnostics and qualitative case studies can be
moved to the appendix or removed without deleting the generated evidence base.
