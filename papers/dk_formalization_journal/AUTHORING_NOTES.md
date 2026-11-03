# Author decisions and evidence

These notes support editing; they are not rendered manuscript text. They record
the 28 October 2026 review in `\jonrsp` and distinguish lasting preferences
from the pending correction pass. Current user instructions determine the stage.

## Calibration from the review

- Put the numbers of external theorems, propositions, lemmas, and examples
  inside citation postnotes, for example
  `\citep[Proposition~4.4]{davis1970rotation}`. The original review pointed
  to the Davis 1958 citation as the model. Keep local result references as
  `\cref` references.
- The abstract may name established objects, summarize attribution, and make
  broad connections. Define and explain them in the body. The author rejected
  the agent's demand for more detail throughout the abstract.
- Give definitions and brief reminders where needed. “Define intertwining” is
  a request for exposition, not necessarily a direct question requiring a chat
  tutorial. Singular values need at most a quick reminder; operator ideals need
  a definition. Give an interval example rather than merely replacing
  “half-infinite” with “half-line.”
- Preserve the current follow-on heading unless the author revisits it. A
  foundation-section heading may explicitly identify formalized operator theory.
- Name what we formalized and what we reused directly. Keep detailed evidence
  accessible to authors so the scientific prose can be decisive and accurate.
- Distinguish the known complex mechanism from the apparently unreported
  identification of the error in the printed real Proposition 4.4. The intended
  novelty statement is qualified by “to the best of our knowledge”; it is not a
  claim that all ingredients or the Q-norm conclusion are new.
- The current AI-role paragraph proposed in chat was rejected. The author is
  considering discussion-section placement. Do not infer an accepted replacement
  from earlier agent suggestions. Name systems “ChatGPT and Claude” if needed;
  no expanded tool taxonomy or task-allocation narrative is requested.

## Manuscript correction pass (28 October 2026)

The accepted edits are now applied. The original review is preserved in Git;
this summary keeps the decisions available for the next round.

- Kept the abstract's accepted level of compression; revised the introduction,
  definitions, historical transitions, mathematical relationships, and headings.
  The follow-on heading is preserved. Trace-norm terminology is consistent.
- Stated the exact source-result selection criterion and kept all 29 result IDs.
  Removed the disposition column and the source-correspondence review appendix.
  The underlying inventories and result-to-Lean mapping are unchanged.
- Introduced the explicit Proposition 4.4 counterexample with the qualified
  priority claim and its mathematical predecessors. The figure caption also
  identifies it as the counterexample. Added the Frobenius Q-norm example.
- Removed the unfulfilled quantitative-bound promise, with source comments
  pointing to the additional formalized results. Removed rendered references to
  separate manuscripts and pinned dependencies; kept mathematical and formal
  attribution, with exact provenance evidence in source comments and this index.
- Added a self-contained proof outline for the matching result, including the
  real block reduction for exponents above one and compact continuation to the
  trace-norm endpoint. The theorem statement and its global scope are preserved.
- Enabled author--year citations, linked the MSC codes, and added publication
  years to the historical table. The final venue's numeric/IEEE formatting and
  any later timeline remain future choices.
- Added independent anonymization and symbol-color conditionals. The Manim role
  palette is unchanged. The perturbed operator is consistently written as
  `\widehat A`; the exact coordinate space is written as `F_ex` to distinguish
  it from the perturbation `H`. The displayed Lean declaration is unchanged and
  its caption gives the notation correspondence.
- Removed all review-note invocations from the included manuscript files and
  retained the `\jonsays`, `\agentsays`, and `\jonrsp` definitions for the
  next round.

The AI-role paragraph proposed in chat remains rejected. The article keeps a
brief disclosure naming ChatGPT and Claude. A broader discussion paragraph has
not been substituted; its wording and placement remain open for author review.

## Second prose correction pass (28 October 2026)

The author's subsequent responses are applied, with review-note invocations
removed and their three macro definitions retained. The committed review
preserves the original comments and replies.

- Added the operator-perturbation viewpoint to the introduction: a bound on
  the error in an available Hermitian matrix estimate controls its eigenspace
  residual relative to the unknown matrix. Kept the explanation concise.
- Added the QUENCH citation at the DKPS motivation, inside the existing
  non-anonymous branch. Used “half-infinite intervals” consistently and
  removed “unnumbered” from the rendered target-selection description.
- Described the Q-norm conclusion as a repair by restricting the norm class,
  preserving Proposition 4.3 and the earlier Bolotnikov--Li--Rodman results.
  Highlighted the proved global trace minimum for the four-dimensional pair.
  `TraceOptimality.lean` supplies the lower bound and the explicit attainer.
- Dimension minimality was left as a separate Lean task during the prose pass.
  It is now proved in `DirectRotation/DimensionMinimality.lean`:
  `nuclear_directRotation_le_of_finrank_le_three` gives trace-norm minimality
  for every real orthogonal transporter in dimension at most three, under the
  acute-pair and largest-angle-at-most-pi/3 hypotheses.
  `isLeast_real_shortAngle_nuclear_counterexample_dimension` proves the least
  dimension admitting such a counterexample is four. The source comment beside
  the counterexample links the declarations and proposes the corollary for
  the next prose review; the rendered article has not been expanded.
- Used the author's “a significant amount of operator theory, namely” wording
  as a local exception. Named the foundations adapted into Tau Ceti, with the
  Courant--Fischer/Weyl direction established by the linked audit. Preserved
  the broader lineage-consolidation TODO.
- Called the transport contribution a reduction to weighted matching. Kept
  “under spectral separation” as the author requested on reconsideration.
- Introduced the cited historical surveys as surveys and moved their overview
  table before the historical subsections. Removed the unused CSD acronym.
- Added the finite-dimensional principal-angle interpretation of an acute
  pair, a spectral-theorem statement, the meaning of its spectral projections,
  and a resolvent definition before the contour formula. Explained domains
  using the Hellinger--Toeplitz theorem, citing the original 1910 paper
  ([publisher metadata](https://link.springer.com/article/10.1007/BF01456325)).
- Applied semantic symbol colors by mathematical role throughout the main
  exposition and included proofs. Extended the existing symbol dictionary and
  notation appendix for the spectral measure, generic Sylvester equation,
  and matching proof; kept the Manim palette and monochrome control.

## Historical survey clarification (2 November 2026)

The author accepted the two historical-background suggestions. The prose now
distinguishes Davis and Kahan's assembly of the principal ideas of the
cosine--sine decomposition from Stewart's later completion and explicit
formulation, following Paige and Wei (1994). This relationship is stated in
both the survey overview and the principal-angle discussion.

Simon (2018) is introduced as a historical survey of Kato's work in
non-relativistic quantum mechanics. Its relevance here is the Sz.-Nagy--Kato
projection transport, with the precise orthogonal-projection condition
`||P-Q||op < 1` and the locator `Theorem 5.1` in the later mathematical
exposition. The opening of Section 2 establishes the history, the scope of
the existing surveys, and their relationship to the exposition that follows.
The overview links to our direct-rotation discussion; the projection condition
and spectral application are developed there, after introducing the spectral
subspaces and their projections. The theorem
itself concerns general projections; the unitary assertion uses orthogonal
projections on a Hilbert space. The resolved review notes are removed; their
macro definitions remain available.

Böttcher and Spitkovsky's historical contribution is identified explicitly:
their Remark 1.3 (pp. 1415–1417) compares Halmos's block representation with
the earlier formulations of Dixmier and Davis and the related Davis–Kahan
projection results. This passage was read in the
[full publisher PDF held by William & Mary](https://scholarworks.wm.edu/server/api/core/bitstreams/2f948a85-8996-4351-a490-510f6b58f69e/content).
The overview cites that remark rather than describing the survey only by its
mathematical subject.

## Result summary and detailed table (2 November 2026)

The author accepted keeping both tables together in Appendix C: the compact
Table 3 comes first, followed by the detailed table in subsection C.1.
`appendix_result_summaries.tex` contains the same 29 IDs with columns for
assumptions and main conclusions, grouped by mathematical topic, and is
included from `appendix_process.tex`. There is no separate Appendix D.
The summaries were checked against the result passages in the distributable
source specification. Shared conventions preserve domain and norm scope,
the source's crossed-defect acute condition, and the distinct spectral gap
hypotheses. The false printed displacement claim and its Q-norm repair remain
distinct. The source direct rotation has its own glossary key because the
table also covers the nonacute case.

The [Table 4 Lean audit](TABLE4_LEAN_AUDIT.md) compares all 29 rows with the
78 registered Lean statements and the supporting declarations needed for
extensions and representation changes. The correction pass makes norm
definedness, common domains, nonzero eigenvectors, finite residual rank,
matched defects, and finite-dimensional spectral-repulsion scope explicit.
The unbounded symmetric sine row uses the existing common-domain presentation
theorem in addition to the bounded primary witnesses. No Lean source was changed.
Validation passed: the full `DavisKahan.All` build, a fresh compiler probe for
the 78 registered and nine supporting declarations, and the manuscript build
without warnings or unresolved references.

## Matching exposition: accepted review applied (2 November 2026)

The author accepted the four comments and their inline responses in
`formalization_enabled_extension.tex`. The correction pass:

- explains rotation, reflection, and two-plane coupling before defining
  indexed paired and singleton costs; removes the undeclared auxiliary angle;
- identifies the figure as a graph of angle labels with arbitrary vertex
  positions, labels its graph and cost-table panels, and explains the geometric
  meaning of selected edges and unmatched vertices in the caption;
- justifies existence using orthonormal basis extension, Heine--Borel, the
  closed transport constraint, and the extreme value theorem;
- explains the simultaneous invariant decomposition before the stationarity
  argument, then separates feasible variations, gradient levels, the two-phase
  projection, and its real/imaginary decomposition into successive steps.

The existence argument follows `SchattenTransportExistence.lean`. The block
explanation follows `SchattenRealDecomposition.lean`, `SchattenRealGradientBlocks.lean`,
and `RealTwoPhaseBlocks.lean` under
`DavisKahan/FiniteDimensional/DirectRotation/`, together with
`ForTauCeti/Analysis/InnerProductSpace/Projection/ComplexRealBlocks.lean`.
Resolved comment calls are removed from this section; macro definitions remain.

## Learning-oriented matching proof (3 November 2026)

The author requested enough detail to follow and learn the matching proof.
The new note on disjoint pairs is resolved by defining a matching as pairs of
labels using each label at most once, with a three-label example and explicit
treatment of equal angle values.

The proof now has six steps: compact attainment for a differentiable cost;
constraint-preserving variations and the gradient compressions; small real
blocks; one- and two-angle costs; both matching inequalities; and the trace-norm
limit. It derives the displacement chord, tests stationarity with the gradient's
own source compression, explains the complex structure and the two phase roots,
constructs the projection blocks, and gives the full four-dimensional
rotation/reflection parametrization and its scalar reduction. It explicitly
rules out an improvement from using zero angles as extra partners.

The additional scalar explanation follows `RealFourCoordinates.lean`,
`RealFourPositive.lean`, `RealFourPhaseRectangle.lean`, and
`RealFourOptimization.lean` under
`DavisKahan/FiniteDimensional/DirectRotation/`. The gradient explanation follows
`SchattenRealStationarity.lean` and `SchattenGradientSpectrum.lean`; the explicit
projection-block construction follows
`ForTauCeti/Analysis/InnerProductSpace/Projection/ComplexRealBlocks.lean`.
No Lean statement or source-result selection changed. New power-cost and
complex-structure symbols have glossary reminders and notation-appendix entries.

## Matching terminology and notation review (3 November 2026)

Applied the author's follow-up comments directly and removed the resolved
comment calls, retaining the review macros. The section now specifies
maximum-weight matching on a finite general graph. Edge weights are defined
as the two-singleton cost minus the paired cost; “savings” is no longer the
reader-facing term. Maximum cardinality is a different objective. No
infinite-dimensional matching theorem is asserted.

The invalid overlapping-pair example leads with its prohibition. The redundant
zero-angle sentence before the theorem is removed; the proof retains the
argument excluding zero angles as cheaper extra partners. The figure caption
starts with the ambient R6 space, two three-dimensional subspaces with zero
intersection, and their three positive principal angles. Figure and Manim
labels use the same edge-weight terminology.

The proof introduction explains why we use the differentiable p > 1 cost
before taking the trace-norm limit. Step 5 explains the cost-preserving
construction from matchings and extraction from minimizers without asserting
a bijection between all transporters and matchings. Terminology is kept
consistent rather than varied for style.

The orthogonal group is defined before the theorem. Named auxiliary objects
in the matching proof now use the same semantic registry as the main text,
with neutral ink and detailed hover reminders. Auxiliary gradient, phase, and
power-cost rows were removed from the printed notation appendix; the registry
retains them. The numerical model's internal `savings` dictionary key is left
unchanged to preserve its existing consumers. No mathematical theorem changed.

## Generated artifacts (2 November 2026)

The author requested ignoring regenerable outputs. Figure PGF/PDF/SVG exports,
derived analysis TeX/CSV views, previews, and LaTeX auxiliaries are no longer
tracked. Figure scripts and numerical models remain the sources; the Makefile
and latexmk configuration regenerate the figures needed by the main paper.
The two authored SVGs and dated external observation JSON remain tracked inputs.
The rendered reviewer packet is also ignored and regenerated with
`scripts/render_davis_kahan_1970_audit_packet.py` from the root.
Authored semantic reviews, Lean audit wrappers, and source inventories remain
source evidence rather than disposable outputs.

## Local evidence index

Paths below are relative to this paper directory. Prefer these existing records
and exact source declarations to a competing provenance inventory.

| Question | Evidence to consult |
| --- | --- |
| Which 29 source results were selected, and which Lean declarations represent each ID? | [Result inventory](../../dev/davis-kahan-1970-formalization-result-inventory.json), particularly `selection_definition` and each result's `id`, `source_anchor`, and `lean_declarations`. |
| How are source passages, result IDs, and declarations connected? | [Statement map](../../dev/davis-kahan-1970-statement-map.json) and [full source census](../../dev/davis-kahan-1970-full-source-census.json). The result inventory already maps the table IDs directly to declarations. |
| What is the source's mathematical scope? | [Distributable source specification](../../prose/distilled_literature/DavisKahan1970_part_III.tex) and [claims to evidence](claims_to_evidence.md). |
| What supports the correction and its literature comparison? | [Proposition 4.4 literature map](PROPOSITION_4_4_LITERATURE_MAP.md), [literature audit](submission/LITERATURE_AUDIT.md), and [claims to evidence](claims_to_evidence.md). Check each claim at the source's real/complex, norm, and angle scope. |
| Which formal results were adapted into Tau Ceti, independently re-proved there, or built on earlier donors? | [Contribution and lineage census](../../dev/tauceti/dkps-upstream-contribution-census.md) and [upstream consumption review](../../dev/tauceti/upstream-consumption-review-2026-10-22.md). These are dated evidence, not proof of current remote status. |
| Did our Courant--Fischer/Weyl proofs originate here? | [28 October proof-lineage audit](COURANT_FISCHER_LINEAGE_AUDIT.md): immutable June/August donor sources, the accepted October port, and six declaration/proof comparisons establish local development followed by upstream adaptation and local consumption. The broader lineage consolidation requested in the review remains pending. |
| Which parts have Spectra ancestry? | [Spectra provenance map](../../dev/tauceti/spectra-provenance-map.md), [preserved upstream attribution](../../retired/Spectra.UPSTREAM.md), and the Lean provenance headers. |
| Which roadmap topics correspond to donor work? | [Donor topic map](../../dev/tauceti/roadmap-topic-map.md). Topic overlap alone does not establish proof descent. |
| What notation and colors does this article use? | [Symbol macros](math_symbol_colors.tex), [notation appendix source](appendix_notation.tex), and the [Manim glossary](../../visualizations/dkvis/slides_glossary.py). |

## Optional campaign checkout

The author also identified `/home/joncrall/code/tauceti-dkps-campaign`. On this
machine the inspected checkout is at `bd68dba` (26 October 2026). It is an
optional evidence source, never a manuscript or Lean build dependency. Its
README indexes:

- `proof/campaign/STATUS.md`: last-known campaign observations and their dates;
- `docs/OPERATOR_THEORY_LEDGER.md`: roadmap items and evidence relationships;
- `docs/PROOF_LINEAGE.md` and `proof/proof_lineage.json`: a pinned proof-lineage
  case study with its stated limits;
- `docs/UPSTREAM_REVIEW_LESSONS.md`: lessons from upstream review and repair.

This checkout is read-only for this task. No refresh, remote action, or new
integration claim was made. Before claiming current upstream acceptance,
inspect the accepted revision and distinguish submission, integration, direct
adaptation, independent work, and transitive use. Add findings to the maintained
census when appropriate; this index supplies navigation rather than a new
campaign ledger.
