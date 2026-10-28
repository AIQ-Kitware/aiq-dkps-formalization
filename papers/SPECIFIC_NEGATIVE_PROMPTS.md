# Recurring manuscript review failures

Read [STYLE_GUIDE.md](STYLE_GUIDE.md) for affirmative guidance. The rules below
record recurring mistakes; apply them with the audience and purpose of the
passage in mind.

## Do not demand every detail everywhere

- Do not criticize an abstract merely for naming established concepts without
  defining them, grouping contributions, or giving broad context. The body is
  where the definitions and detailed comparisons belong.
- Do not turn a request to define a term into an extended elementary tutorial.
  A brief definition, reminder, or example often supplies what is missing.
- Do not answer an editorial comment such as “intertwining needs a definition”
  only with a chat explanation when the task is to revise the manuscript.
- Do not make every heading purely mathematical. A heading can appropriately
  name a formalization contribution or a follow-on result. Preserve author
  approval of a specific heading.
- Do not treat an appendix as the automatic destination for every omitted
  detail. Implementation evidence can remain in author notes and source
  comments. Include only appendices that help the reader.

## Do not replace direct language with more elaborate synonyms

Avoid “reviewed source scope,” “full-scope,” “supplied interfaces,” and “analytic
proof engine” when the mathematical statement can be named directly. State
which theorem we proved or which foundations we formalized. Prefer consistent
technical terms and ordinary verbs to ornamental variation. Do not presume a
reader finds an object “familiar,” or call a construction “transparent” in place
of explaining it. Replacing “half-infinite interval” with “half-line” does not
address a request for an example.

## Do not turn supporting evidence into the paper's subject

- Keep pinned dependency revisions, PR-status bookkeeping, source-review
  procedures, and proof-repair history in author files or artifact documentation.
  Mathematical provenance and credit for reused formal work remain scholarly
  content; state those contributions directly.
- Do not add status or disposition columns simply because those fields exist
  in an internal inventory. A column must convey something the reader needs.
- Do not replace compact result IDs with unwieldy Lean names when the artifact
  already maps those IDs to declarations.
- Do not narrate the choice between sibling manuscripts or send readers to an
  unpublished companion for the explanation needed to assess an included result.
  Keep the current paper self-contained at its chosen level of exposition.

## Do not obscure a specific contribution with blanket caution

Acknowledging an earlier mathematical mechanism does not dispose of a claim
that a particular published theorem is false. Compare those claims precisely.
Support a concise “to the best of our knowledge” statement where justified;
do not replace it with recurring declarations that novelty is unresolved.
Conversely, author approval of a proposed priority statement is not evidence
that every ingredient or repair is new.

## Do not expand AI disclosures by default

A request to discuss AI's role does not require a detailed account of source
selection, human/agent task allocation, review passes, or software products in
every disclosure. Use the author's chosen level of detail. If a substantive
discussion covers the topic, a separate disclosure may be unnecessary. Use the
requested product names without expanding them into a taxonomy of interfaces
and models. Keep uncertainty about a proposed paragraph or its placement open
until the author settles it.

## Banned repository-development vocabulary in the main text

Do not use repository-internal development labels as scientific terminology in the main body when direct mathematical prose is available. This includes:

- `source-faithful`;
- `project-local`;
- `inventory` when it refers to internal bookkeeping;
- `dependency snapshot`;
- `machine-readable correspondence`;
- `positive formal-source claim`;
- `census` when discussing the scientific result rather than the appendix audit method;
- `canonical declaration` or `canonical Lean surface` without a mathematical uniqueness statement supporting "canonical".

These terms may appear in appendices when they identify reproduction machinery precisely.

## Banned external-auditor voice for our own work

Do not write as though repository notes were discovered by an outside observer. Avoid formulations such as:

- "the repository documents ancestry in Spectra";
- "we found a note saying the proof was adapted";
- "the data records that we used..." when the manuscript can state directly what we used.

State the ancestry, adaptation, workflow, or methodological choice as an authorial claim and cite the source.

## Lean terminology restrictions

Do not:

- call displayed Lean code a `listing` or `surface`;
- call a Lean declaration `canonical` without a mathematical reason;
- discuss glyph substitutions or TeX rendering accommodations;
- repeat implementation identifiers in prose when a mathematical description suffices;
- explain generic Lean syntax around each theorem after the appendix reader guide has been cited.

## Resource-accounting restrictions

Do not:

- place modeled USD, CO2e, or kWh estimates in the abstract as though they were direct measurements;
- show incomplete resource telemetry without identifying it as retained/incomplete in the relevant table header and caption;
- combine live exact observations, explicit backfills, or project-total extrapolations without labeling the accounting class;
- describe extrapolations as confidence intervals unless a statistical model actually supports that interpretation;
- use CO2e in the current manuscript unless the authors explicitly decide to restore it.

## Citation and appendix restrictions

Do not:

- use a hand-written `thebibliography` block in `paper.tex`;
- leave a vague sentence such as "the appendix gives..." when an explicit section reference can be used;
- put census construction, exact source registries, file paths, or declaration-level provenance tables in the main body;
- place appendices before the references.


## Do not promote recent discussion into manuscript prominence

Do not let the most recent review, correction, user comment, or agent discussion
set the emphasis of a manuscript revision merely because it is fresh in context.
Use new information to revise the paper's understanding, then write at the level
of the paper's stable research question and evidence.

In particular:

- do not move a newly discussed episode into the title, abstract, contribution
  list, or conclusion unless it is independently central to the paper;
- do not summarize the conversation that led to a revision when the manuscript
  only needs the resulting scientific point;
- do not enumerate review rounds, transient classifications, or recent repair
  details in the abstract unless the count or chronology is itself a reported
  result;
- keep concrete episodes in the body when they provide evidence for a broader
  claim, rather than making every episode a headline claim;
- after incorporating new evidence, reread the abstract and conclusion from the
  perspective of a reader who has not seen the development conversation and
  remove details whose prominence depends on that conversation.

## Keep revision history out of rendered prose

A correction may require substantial historical work to establish what happened.
Preserve that work in source comments, notes, supplementary data, or audit artifacts
when it is useful for reproducibility. Rendered manuscript prose normally needs the
resulting scientific fact, not the story of how the authors discovered or repaired it.

Do not:

- narrate prompt history, review-state transitions, checkpoint counts, re-openings,
  repairs, commit order, or repository cleanup in rendered prose merely to justify a
  corrected statement;
- turn a correction into a dramatic or causal section title such as "How X passed
  review too early";
- explain why a paragraph was rewritten or what a recent discussion changed;
- import dates, commit hashes, checker names, or intermediate classifications into a
  worked mathematical example unless the chronology itself is evidence for the claim;
- render a commit-by-commit or review-by-review chronology in an appendix merely
  because the data exist. Keep detailed reconstruction in supplementary data or
  source notes unless readers need it to evaluate a reported result.

When historical provenance is useful to future editors, prefer non-rendered LaTeX
comments immediately beside the relevant prose. When a historical correction changes
a worked example, rewrite the example in its final mathematical form and keep the
repair history out of the rendered explanation.

## Formalization-paper editorial rules (2026-10-28)

These rules apply to the Davis--Kahan formalization manuscript and, where
relevant, to other formal-mathematics papers. They override an agent's tendency
to insert self-protective commentary into published prose.

- **Do not insert generic validation disclaimers.** In particular, do not write
  variants of "source correspondence and interpretation require independent
  mathematical review" or "the authors retain responsibility". A paper should
  state its actual formalized mathematical results, hypotheses, and source
  mapping directly, not advertise an unspecified future review.
- **Do not state the obvious about Lean.** Ban filler such as "Lean checked the
  encoded propositions" or recurrent reminders that a compiling proof is
  checked by Lean. Describe any nontrivial methodological distinction once,
  where scientifically necessary; focus on the mathematics and formalization.
- **Do not put reproduction instructions in the paper.** Move `lake` commands,
  environment installation, build recipes, exact checkout procedures, and
  file-by-file reproduction checklists to the repository README or dedicated
  artifact documentation. A concise artifact-availability citation or link
  may remain in the manuscript.
- **Do not invent bibliographic citations.** Every `\\cite{...}` must resolve
  to a real bibliography entry representing an actual source. In particular,
  do not present TauCeti as a published paper if no such publication exists.
  Cite the actual mathematical originator where applicable; identify TauCeti
  as a software library with an accurate project URL/version when relevant.
  Distinguish mathematical source attribution from formalization/API ancestry.
- **Do not insert ritual uncertainty about historical priority.** Avoid
  unsupported metacommentary such as "its historical priority remains under
  study", "novelty remains provisional", and repeated defensive qualifications.
  State the precise result proved, cite and compare the closest established
  predecessors, and say concretely what differs. Do not claim "first" without
  evidence; do not add disclaimers merely because exhaustive priority
  certification is impossible. Keep live research questions in internal notes.
- **Do not narrate novelty as a list of things the authors cannot claim.**
  Ban defensive attribution wording such as "This prior work rules out
  crediting the original complex mechanism or general trace-norm
  nonminimality to the present project." Give the historical fact directly:
  "Davis and Kahan exhibited the complex-phase counterexample to trace-norm
  optimality" (with the primary citation). Then describe precisely the
  result obtained here. Prefer affirmative, source-grounded mathematical
  comparisons over self-referential credit disclaimers. This does not
  justify erasing credit for predecessors.
- **Do not compress away the historical mathematical development.** The
  formalization paper should situate its constructions and prerequisites in
  the development of principal angles, projections, direct rotation,
  perturbation theory, and operator-theoretic foundations. Explain how
  existing theorems and theorems formalized for the project fit together.
  Longer exposition is acceptable when it contributes to understanding; do
  not optimize for page-count reduction as an end in itself.
- **Do not conflate dependency provenance with logical consequence.** New
  transport research can be enabled by the formalization infrastructure,
  including DKPS material later moved upstream to TauCeti, without following
  logically from the Davis--Kahan sine-theta theorem. Attribute direct ports,
  independent upstream re-proofs, and common classical sources accurately.

These editorial rules do not authorize omitting genuine mathematical
hypotheses, known counterexamples, material limitations, or necessary source
attribution. Express such facts precisely rather than through generic hedges.

## Research ownership without default external escalation (2026-10-28)

- **Do not end a manuscript/research task with generic advice to seek expert
  review.** The project does not have a standing external reviewer. A
  recommendation for unspecified external validation is not an action item.
  Instead, provide concrete, internally executable checks: an explicit
  theorem-to-source comparison, a small worked example, a conventional
  proof, a counterexample search, or a direct analysis of the relevant
  Lean statement and dependencies.
- Historical attribution should cite actual publications and contrast
  their precise claims with ours; do not replace this with a request for
  a specialist to adjudicate priority.
- Keep real limitations explicit: do not infer a false claim of priority,
  or inflate scope, merely to avoid mentioning an unresolved mathematical
  question. A concrete open conjecture belongs in the research notes; a
  generic appeal for review does not belong in the paper.
- Existing historical surveys are valuable prior scholarship. Credit
  specialized surveys on CS decomposition, pairs of projections, and Kato
  rather than presenting our narrative as the first historical account.
