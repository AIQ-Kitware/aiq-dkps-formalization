# What Does It Take to Prove Davis--Kahan?

## Research question

Which mathematical principles suffice to derive the full-scope spectral-subspace
perturbation theorems of Davis and Kahan (1970), how are those principles related,
and how did they enter the mathematical literature? The existing Lean 4
development supplies verified examples of such derivations, including
infinite-dimensional and unbounded-operator cases. The research will compare
the printed arguments, their formal realizations, and documented historical
antecedents.

A successful paper should enable a mathematician to follow one or more major
Davis--Kahan results from hypotheses to conclusion, see where spectral theory,
operator equations, projection geometry, and operator ideals enter, and compare
alternative ways to discharge the same obligations.

## 1. Specific research questions

1. **Mathematical architecture.** What is the shortest convincing mathematical
   derivation of the complete single-angle sine theorem, including domain,
   spectral-gap, scalar-field, and norm-ideal conditions? Which intermediate
   statements genuinely do work in the derivation?
2. **Original versus modern routes.** Which arguments in the 1970 paper can be
   recovered as stated, which are recast using modern spectral/operator-ideal
   language, and which have independent alternatives? What does each route gain
   or require in hypotheses?
3. **Historical ancestry.** Which mathematical results did Davis and Kahan cite
   directly, which earlier results are visible through the mathematics, and
   which dependencies arise only because of the chosen Lean implementation?
   Record the evidence for each relationship.
4. **Assumptions exposed.** Where do unbounded domains, residual extension,
   finite versus ordered half-infinite gaps, real/complex transfer, and
   where-defined unitarily invariant norms force distinctions that a short
   matrix-level proof suppresses?
5. **Independent branch and correction.** How is the direct-rotation extremal
   theory related to the perturbation inequalities, and what exactly fails in
   Proposition 4.4? Does identifying the false implication reveal a reusable
   mathematical boundary between squared and unsquared displacement?
6. **New mathematical conclusions.** Are there sharpened equivalences,
   redundancy/elimination results, or precise best-possible estimates that can
   be stated, proved, and distinguished from existing perturbation theory?

Do not treat the number of Lean dependencies as the answer to any question above.

### Testable initial hypotheses

- **H1: independent branches.** The full-scope sine estimate has a valid
  residual/Sylvester derivation without invoking Section 4 full-displacement
  extremal claims. Test this against original source dependencies and the
  selected formal theorem's proof graph; if either route actually uses the
  branch, report the dependence rather than preserving the hypothesis.
- **H2: analytically distinct gap cases.** Finite interval/exterior and ordered
  half-infinite separation use distinguishable spectral-order arguments at
  unbounded scope, even if they feed one abstract gap interface. Test by
  reconstructing the relevant Sylvester estimates and their domain conditions.
- **H3: normalization is a mathematical bridge.** The equivalence between the
  rectangular complementary block and the positive sine operator is the
  critical transition allowing operator-ideal norms to be transported to the
  source statement. Test the exact modulus identity, then inspect whether
  different proof routes can avoid the same representation change.
- **H4: formal architecture is nonunique.** A finite-dimensional or bounded
  proof of a narrower theorem avoids some tools required by the current full-
  scope Lean implementation. Produce an explicit alternate route and quantify
  the difference in **assumptions and mathematical lemmas**, rather than counts
  of imported modules.

For every hypothesis, keep an evidence table with a mathematical argument, a
source locator, a compiler-derived declaration trace when applicable, and a
verdict of supported, contradicted, or unresolved.

## 2. Starting evidence and ownership

The historical source is Chandler Davis and W. M. Kahan, *The Rotation of
Eigenvectors by a Perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1--46,
DOI: https://doi.org/10.1137/0707001. Use the complete paper, including
its standing assumptions and appendices; do not reconstruct its claims from
a popular modern finite-dimensional formulation.

The project already has a **29-result source inventory**: 28 results proved
at their reviewed source scope and Proposition 4.4 refuted as printed. The
parameterized, arbitrarily-small-angle extension is additionally Lean-verified
according to the successful build and axiom audit reported on October 20, 2026.
The later sharp-displacement and global-minimizer extensions have separate
verification obligations; do not conflate them with the checked extension.

Use these maintained authorities rather than building another status ledger:

- `dev/davis-kahan-1970-formalization-result-inventory.json` and
  `dev/davis-kahan-1970-full-source-census.json`: result IDs, formal statements,
  source clauses, and reviewed correspondence.
- `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`:
  `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`, the selected
  full-scope sine-theta theorem.
- `DavisKahan/Sources/DavisKahan1970/`: the remaining source-facing results.
- `ForTauCeti/`: reusable mathematical definitions and lemmas; provenance
  and Mathlib/Tau Ceti origins must be respected.
- `dev/tauceti/spectra-provenance-map.md`: formal ancestry of the retired
  Spectra collaboration and retained mathematical adaptations.
- `papers/dk_formalization_journal/`: the independent, current mathematical
  formalization manuscript, including its existing source and norm analyses.
- `papers/dk_formalization_journal/data/formalization_*_20260817.*` and
  analysis scripts: useful historical snapshots and generators. The dated data
  cannot be presented as the current dependency graph without regeneration.
- `dev/README.md` and `semantic-alignment-page.sh`: the current `leanq`/`aiq-lean`
  source-to-Lean inspection route.

At the start of an evidence run, record `git rev-parse HEAD`, the Lean toolchain,
the pinned dependency revisions, the exact version of the original source, and
the commands used to generate each graph or annotation. The new paper's case
studies should link to maintained inventory IDs; they should not copy mutable
completion status into a separate system.

## 3. Three kinds of evidence, kept separate

| Evidence type | How to collect | What it supports | What it does not establish |
| --- | --- | --- | --- |
| Historical source argument | Original 1970 paper, page and formula, its bibliography, and independently checked primary antecedents | What an author stated, proved, assumed, or cited | That every implicit step was unknown or historically novel |
| Mathematical reconstruction | Explicit definitions, lemmas, proof reductions, exact hypotheses, and checked counterexamples | A sufficient proof route; when a displayed reduction is valid | That no other proof route can avoid a lemma |
| Lean dependency evidence | Source-census mapping, elaborated theorem type, proof/declaration index, and imported-module graph | Which declarations and encodings occur in this formal realization, at the granularity the exporter exposes | A minimal logical basis or historical influence |

For each proposed dependency, classify its status:

- **Required by the examined proof route:** the cited derivation explicitly
  invokes the stated mathematical assertion.
- **Required by one formal implementation:** a Lean declaration/representation
  depends on it, but an alternative mathematical proof may avoid it.
- **Convenient abstraction:** an equivalent or stronger interface packages
  mathematics that could be expressed without that abstraction.
- **Alternative route:** a separately established argument discharges the
  same goal with different prerequisites.
- **Historical antecedent:** a specific earlier statement is documented by
  publication and page; classify as explicitly cited in 1970, an indirect
  mathematical predecessor, or a later reformulation.

Unproved claims of indispensability should not appear in the manuscript.
Removing a dependency from an example proof does not by itself show that it is
unnecessary in all proofs; observing a dependency does not prove necessity.

Keep two computed graph layers separate. Import closure is a potentially large
**upper bound** on declarations available to a theorem; the existing
`build_formalization_prerequisite_trace.py` explains that its compiler-visible
named-declaration reachability may omit opaque or proof-internal dependencies.
Neither graph is an exact count of mathematical concepts. Check mathematical
claims against actual proof expressions, types, and alternative formulations.

## 4. The pilot: full-scope single-angle sine theorem

**Source target:** `S2-sin-theta` in the 29-result inventory, with the relevant
Section 5 and Section 6 lemmas and unbounded-operator appendices. Do not infer
that one numbered source result corresponds to exactly one Lean proof.

**Formal endpoint:** `sinTheta_unbounded_formGap_whereDefinedUIN_rclike`.

**Mathematical backbone to reconstruct:** with trial isometry $E_0$,
self-adjoint trial operator $A_0$, full-space operator $A$, bounded residual
$R = AE_0-E_0A_0$ on the appropriate domain, and complementary exact
isometry $F_1$ with block operator $\Lambda_1$, put $X=F_1^*E_0$.
The complementary residual identity is, where defined,

$$
  F_1^*R = \Lambda_1 X-XA_0.
$$

The spectral separation gives an appropriate Sylvester estimate; ideal
inequalities give $\delta N(X)\leq N(R)$. The orthogonal decomposition and
polar/modulus identities identify $|X|$ with the positive trial-coordinate
$\sin\Theta_0$, or pass through the equivalent rectangular complementary
block. The target bound is

$$
  \delta N(\sin\Theta_0)\leq N(R).
$$

Record the *actual* operator domains and norm-membership requirements needed
at every step. Do not use this schematic derivation as a substitute for
checking the formal statement, especially in the ordered half-infinite-gap
cases or during real/complex transfer.

The case study must answer, by worked mathematics:

1. How does a residual between two self-adjoint problems become a Sylvester
   equation? Specify which adjoint/composition equalities use domain or
   reducing-subspace hypotheses.
2. What spectral separation makes the Sylvester map quantitatively invertible?
   Compare finite interval/exterior and both ordered half-infinite cases, and
   explain why the most familiar bounded-matrix proof does not cover them.
3. Why is the rectangular complementary block norm-equivalent to the source's
   positive sine operator? Exhibit the modulus identity and the exact norm
   transfer, including where-defined conditions.
4. Which of these results persist unchanged over real scalars, and which proofs
   pass through complexification or a real-transfer lemma?
5. Where are the actual theorem-level claims proven, and which pieces of the
   declaration graph are only encodings or infrastructure?
6. Which intermediate facts were available in 1970? Support answers with
   primary sources; reserve 'introduced by' for cases where priority is
   genuinely documented.

**Required pilot artifacts:** one readable 6--10-page mathematical exposition,
a source-to-step table with page/formula anchors, a curated theorem-level Lean
proof subgraph, a typed hypotheses table, an evidence-backed historical
lineage, and a short list of genuinely distinct proof alternatives. Seed notes
are in `cases/sine_theta.md`.

**Pilot acceptance criterion:** a mathematically informed reader can reconstruct
the bound, identify the assumptions behind each inequality, and navigate from
each major step to an actual Lean theorem or proof. Every historical arrow is
supported by a citable passage. A dependency graph image without these pieces
does not complete the pilot.

## 5. Ordered work packages

### WP0. Freeze inputs and assess existing analysis tools

- Record baseline revision and source PDF identity; confirm the result census.
- Generate the current `leanq` declaration index without overwriting the dated
  August research snapshots.
- Inspect the existing prerequisite-trace and theory-graph scripts for their
  root selections, declaration coverage, and documented blind spots.
- Identify source-facing theorem roots, independent proof engines, wrappers,
  and theorem statements specialized for exposition. Map the relationships.

**Deliverable:** a one-page evidence index with the actual revision, commands,
root theorem, and graph locations. **Gate:** a reviewer can identify exactly
which version of the mathematical theorem the graphs describe.

### WP1. Write the mathematical sine-theta derivation

- Write the theorem and its assumptions before adding history or Lean names.
- Give the residual-to-Sylvester reduction, gap estimate, modulus step, and
  ideal-norm transport as a sequence of explicit mathematical lemmas.
- Cover the unbounded case without substituting a bounded special case.
- Put the real/complex and gap alternatives in a matrix of exact hypotheses.
- Distinguish proof of the source theorem from an equivalent representation
  chosen to simplify the formal statement.

**Deliverable:** complete pilot mathematical exposition. **Gate:** each
composition and inequality has named and verified hypotheses; no unexplained
transition invokes a bounded-only or finite-dimensional fact.

### WP2. Curate the formal dependency route

- Generate proof/declaration evidence from the actual endpoint. Review the
  project-local and Mathlib/Tau Ceti boundaries; include reused Spectra work
  with provenance rather than crediting its adaptation as wholly new.
- Label each node as mathematical lemma, definition/representation bridge,
  scalar-field transfer, domain bookkeeping, or formal infrastructure.
- Cross-check ten to twenty load-bearing lemmas against their Lean statements
  and the mathematical narrative. Annotate omissions due to opaque proof terms.
- Compare at least two graph cuts: the selected general theorem and a finite,
  bounded, or stronger-gap specialization.

**Deliverable:** a curated, source-linked proof diagram and an evidence table.
**Gate:** graph edges report what the tool actually extracted; every claim of
mathematical dependence has a human-readable proof explanation.

### WP3. Establish a defensible historical lineage

- Read the original paper's introduction, Section 3 geometry bibliography,
  Section 5 operator-equation discussion, and appendices.
- Trace cited predecessors first. Candidate starting points include Jordan's
  work on canonical angles, Davis's earlier eigenvector-rotation papers,
  classical singular-value/majorization theory, Sylvester's matrix equation,
  and Rosenblum's operator-equation results.
- Verify publication year, exact theorem/page, statement scope, and the
  relationship to the specific proof step. If a work is cited by Davis and
  Kahan, record its exact citation; otherwise label the relationship as a
  retrospective mathematical connection.
- Research post-1970 formulations used by modern Mathlib/Tau Ceti APIs
  separately from works available to Davis and Kahan.

Bibliographic starting points requiring source-level study:

- Davis--Kahan (1970): https://doi.org/10.1137/0707001
- Davis (1963), *The Rotation of Eigenvectors by a Perturbation. I*:
  https://doi.org/10.1016/0022-247X(63)90001-5
- Rosenblum (1956), *On the operator equation BX-XA=Q*:
  https://doi.org/10.1215/S0012-7094-56-02324-9
- Bolotnikov--Li--Rodman (2001), later direct-rotation minimization:
  https://doi.org/10.13001/1081-3810.1058
- Zhang--Qiu (2010), Section 4, later canonical-angle/direct-rotation analysis:
  https://doi.org/10.1137/09074841X

**Deliverable:** an annotated historical source table and timeline with
page-level evidence. **Gate:** no arrow is asserted from date alone; distinguish
what the 1970 authors cited from what a modern reconstruction uses.

### WP4. Challenge dependency necessity with alternative routes

Choose two local proof steps with plausible alternatives, such as the
bounded-matrix Sylvester estimate versus an operator-theoretic proof, or a
projection/modulus route versus a principal-plane argument in finite dimension.

- Write both proofs mathematically; reuse existing Lean proofs where available.
- Record what each route assumes, what it proves, and which results it bypasses.
- Prefer comparing existing proved routes. If a new Lean lemma would be
  necessary to test a research hypothesis, obtain explicit approval for that
  separate mathematical extension. Do not create a new source-fidelity
  obligation or alter the 29-result mapping.
- Compare hypotheses and scope, not line counts or build time as proxies for
  mathematical simplicity.

**Deliverable:** an explicit alternative-proof comparison. **Gate:** any
claim that a specific theory is *required* is qualified by the route or is
supported by a separate impossibility/independence argument.

### WP5. Study the independent direct-rotation branch

- Map Section 3 geometry, Section 4 restricted-displacement and
  squared-displacement results, and the known failure of Proposition 4.4.
- Explain mathematically why the failed Ky Fan inequality cannot combine
  plane-by-plane inequalities into unrestricted full-displacement minimality.
- Relate the checked real four-dimensional family to the complex two-dimensional
  phase construction, checking the relationship with Davis--Kahan Example 4.2.
- Separate results checked in Lean from ongoing sharpness/global-minimizer
  proof attempts, and compare every novelty claim with Bolotnikov--Li--Rodman
  and Zhang--Qiu.
- Test the hypothesis that the main sine-theta proof can be developed without
  this extremal branch; evidence must come from proof routes, not merely the
  paper's table of contents or imports.

**Deliverable:** a second mathematical case study exposing a false inference
and a genuine branch distinction. **Gate:** no claim that correcting 4.4
changes the validity of the sine-theta theorem without direct evidence.

### WP6. Synthesize mathematical results and decide paper scope

Evaluate findings from the first two cases:

- A new or clarified mathematical reduction with exact hypotheses.
- A genuinely independent proof route that changes the prerequisite set.
- A source theorem whose valid scope depends on nonlocal conventions.
- A corrected false inference, with precisely stated relation to prior art.
- A reusable dependency structure that makes a full-scope theorem accessible
  without reproducing a whole code graph.

Draft a 1--2-page mathematical contribution statement and request review from
an operator theorist and a formalized-mathematics researcher. If the results
mostly explain existing mathematics, pursue a rigorous expository/formalized-
mathematics article rather than claiming new operator theory. A general
mathematics journal requires a stronger mathematical contribution than a graph
of formal dependencies.

**Deliverable:** a manuscript outline, an evidence-to-claims table, and a
venue decision after the mathematical review. **Gate:** a referee can name
what new knowledge the paper establishes beyond the already submitted
formalization paper.

## 6. Proposed manuscript organization

A possible article after the pilot and second case succeed:

1. A mathematical question: reconstruct the full-scope sine-theta estimate.
2. The theorem with its unbounded, real/complex, gap, and norm hypotheses.
3. The residual--Sylvester--modulus derivation and the load-bearing lemmas.
4. Alternative proof routes and which hypotheses they exchange.
5. Historical reconstruction of the component ideas, cited only when relevant
   to an actual mathematical step.
6. Direct rotations as an independent branch: optimality, the false 4.4
   extension, and the corrected mathematical boundary.
7. What the formal proof graph reveals and what it cannot establish.
8. Consequences, open questions, and a compact reproducibility appendix.

A compact figure should show the mathematical chain
`residual -> Sylvester equation -> spectral-gap estimate -> modulus/angle ->
unitarily invariant norm`. A separate, aligned panel can display the Lean
proof dependencies and historical antecedents. Historical arrows and Lean
edges must be visibly distinguishable; they represent different claims.

Do not lead the article with repository statistics, AI-workflow chronology, or
publication logistics. Declare AI assistance and reuse of formal work in the
appropriate methods/attribution sections. Follow `papers/AGENTS.md`,
`papers/BANNED_WORDS_AND_PHRASES.md`, and
`papers/SPECIFIC_NEGATIVE_PROMPTS.md` for all rendered prose.

## 7. Separation from the existing journal submission

The existing `papers/dk_formalization_journal/` manuscript continues to own the
29-result coverage claim, the formal statements, the Proposition 4.4 correction,
and the compact account of reusable foundations. This project owns the
mathematical proof reconstruction, comparison of alternative routes, and
historically grounded ancestry of its components.

Substantial overlap of text, figures, or novelty claims between two submitted
articles requires coauthor review and journal-policy checks. Prefer citations
to the formalization paper for source coverage and artifact details rather than
republishing the same contribution with a new title. Do not change the current
journal manuscript until the pilot produces new results and an editorial choice
has been made.

## 8. Immediate execution order

1. Inspect `dev/davis-kahan-1970-formalization-result-inventory.json` and
   `dev/davis-kahan-1970-full-source-census.json`; pin the full-scope theorem.
2. Build that theorem and generate the current formal proof-dependency index.
3. Populate `cases/sine_theta.md` with the exact six-or-fewer main
   mathematical reductions and their original-paper locators.
4. Annotate each reduction with the verified Lean dependency and one source
   question; explicitly record remaining gaps rather than inferring answers.
5. Expand the derivation into a readable mathematical pilot, then extract a
   simple route comparison against a finite or bounded case.
6. Review the pilot's mathematical correctness and historical attributions.
7. Only after those gates, begin the direct-rotation case and the full article.

Suggested commands, run **sequentially** in the repository root (the index can
be time-consuming; do not run it concurrently with Lake builds):

```bash
cd ~/code/aiq-dkps-formalization
git rev-parse HEAD
lake exe cache get
lake build DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation
python3 scripts/check_davis_kahan_1970_source_census.py
leanq graph-index --out build/leanq/project-semantic-graph.json
./semantic-alignment-page.sh --statements \
  --graph build/leanq/project-semantic-graph.json \
  --importance headline --no-open
```

If `leanq` or `aiq-lean` is unavailable, inspect the installed
`aiq-lean-formalization-tools` package instructions in `dev/README.md`; record
that the graph step is unavailable rather than substituting an import-only
graph and calling it an exact proof trace. The existing dated `20260817`
prerequisite/theory snapshots are useful evidence of previous analyses, but
must be regenerated or checked against the current declarations before any
new quantitative claim.

The first checkpoint is complete when the pilot can be evaluated as a
mathematical argument without opening Lean, and a reader can inspect each
critical implementation and historical source through explicit references.
