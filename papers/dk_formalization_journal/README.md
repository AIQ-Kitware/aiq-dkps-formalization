# Davis--Kahan (1970) in Lean: Formalization, Counterexample, and Repair

This directory contains the journal manuscript on the Lean formalization and
mathematical audit of Davis--Kahan perturbation theory. **Start with
[`PAPER_CONTEXT.md`](PAPER_CONTEXT.md)** for established results, verification
status, unresolved publication questions, and current editorial decisions.
The YWS source audit and old manuscript sections now live in the separate
[`yws_formalization_conference`](../yws_formalization_conference/) stub.
The scope is now fixed:

- **primary subject:** Davis and Kahan's 1970 perturbation paper and the reusable
  operator-theoretic infrastructure required to formalize it;
- **additional verified mathematical results:** a real four-dimensional refutation
  at every positive acute angle, an all-norm projection-displacement lower bound,
  the sharp secant approximation factor, an attained real trace-norm optimum,
  the directed-sine trace decomposition, and the all-pairs exact complex
  trace-norm minimum, the unrestricted finite complex Schatten-`p` minimum
  for `1 < p < 2` with its exact canonical cutoff, and the smoothed transport
  minimum and growth estimates; and
- **out of scope for this manuscript:** downstream application projects and the
  workshop paper's empirical human--LLM/process study, practitioner corpus, and
  resource-accounting analysis.

The finite complex Schatten theorem is included in
`schatten_transport_verified.tex`. Its Lean endpoint is
`SchattenGlobalAttainment.exists_unitary_minimizing_schatten_transport_principalAngles_complex`
(module-qualified shorthand), with canonical optimality in
`SchattenCanonicalOptimality.nonacuteDirectRotation_schatten_minimal_iff_complex`.
The exact value and cutoff cover all admissible complex unitary transports;
the real matching formula, classification of every minimizer, and
infinite-dimensional Schatten extension remain separate research drafts.

The workshop paper in `../dk_formalization_workshop/` remains useful editorially. In
particular, this journal draft adopts its sharper separation between kernel
verification and semantic/source correspondence, its treatment of representation
mismatches, and its more precise language for source defects. It does not import
the workshop paper's process-study contribution as a journal-paper contribution.

## October 23 mathematical and manuscript status

The parameterized counterexample compiles in the pinned Lean development. The
user-reported targeted build on 23 October 2026 completed successfully (3,477
jobs) for `SmallAngleCounterexample`, `Section4SmallAngle`, and the source-facing
audit. The audit reported only `propext`, `Classical.choice`, and `Quot.sound`
for its inspected declarations. The 29-result source inventory is unchanged.

The conventional and formalized parameterized counterexample is in
`counterexample.tex`, `DavisKahan/FiniteDimensional/DirectRotation/
SmallAngleCounterexample.lean`, and the source-facing Section 4 extension.
The journal prose credits the complex phase mechanism in Davis--Kahan Example
4.2 and the norm-minimization literature of Bolotnikov--Li--Rodman (2001),
Qiu--Zhang--Li (2005), and Zhang--Qiu (2010).

The additional sharp-displacement results have been separated by verification
status. `sharp_displacement.tex` is always included in `paper.tex`, and the
older `sharp_displacement_verified.tex` remains a reference file. The included
section contains the projector-distance lower bound, real four-dimensional
global trace minimum, sharp universal UI-seminorm displacement estimate,
fixed-angle necessity and the original $2/\sqrt{3}$ and uniform $\sqrt{2}$ constants.
The corresponding Lean modules `ProjectionDisplacement`, `TraceRatio`,
`TraceOptimality`, and `SharpDisplacement` compiled in user-confirmed builds
on 23 October 2026. These are additional results beyond the fixed 29 source
targets, not revisions to that count.

A separate `SharpDisplacementLimit.lean` provides a focused one-sided-limit
corollary stating the necessity of the uniform `sqrt(2)` constant; it has
not yet been included in the user-confirmed build set.

The complex exact trace optimum is now proved in Lean for **every** equal-rank
pair in finite-dimensional complex Hilbert space, with no acuteness or
principal-plane-coordinate assumption. `ComplexCrossedDefects.lean` constructs
the matched right-angle defect equivalence, `ComplexPhaseTrace.lean` gives the
unconditional optimal transporter, `TraceSine.lean` splits the positive
projector-difference modulus and its trace into two directed sines over both
real and complex scalars, and `ComplexTracePrincipalAngles.lean` proves
$\min_W\|I-W\|_1=\|P_U-P_V\|_1=2\sum_j\sin\theta_j$.
`ComplexTraceFiniteModel.lean` and the previous block-assembly files remain
proved special cases. These additions do not change the original 29 source
results. `paper.tex` states the complex theorem without a red frame; the only
provisional red-framed theorem in `paper_working.tex` is the real rank-one /
hyperplane formula behind `\includeUnformalizedRealTransport`. The former
`sharp_displacement_unformalized.tex` is a superseded conventional derivation,
not included in either build.

`submission/VALIDATION.md` gives the distinction between the user-confirmed
Lean build and LaTeX checks, and lists the remaining proof-development tasks.
`submission/LITERATURE_AUDIT.md` records the bounded prior-art comparison.

## Current mathematical status

The maintained Davis--Kahan result inventory contains 29 source targets. At the
current snapshot:

- all 29 are verified in the Lean build;
- all 29 have accepted semantic/source-correspondence review;
- 28 are proved at their reviewed source scope; and
- Proposition 4.4 is refuted as printed by a machine-checked finite-dimensional
  counterexample and accompanied by a valid Q-norm repair.

The journal paper should present those facts as distinct claims. A declaration
that compiles establishes kernel acceptance of a formal statement. Matching that
formal statement to a printed source statement, including conventions and
representation choices, is a separate review obligation.

The current headline sine-theta endpoint is
`sinTheta_unbounded_formGap_whereDefinedUIN_rclike` in
`DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`. It covers the
current real/complex, unbounded, unitarily invariant norm formulation with the
full finite-interval/exterior and ordered half-infinite form-gap alternatives.
The manuscript should not revert to the older finite-gap specialization as the
main theorem.

A key correspondence point is also part of the journal story. The source's
positive `sin Theta` operator acts on trial coordinates, as does the selected
public Lean statement. Its analytic proof uses the rectangular map
`(I - F0 F0*) E0`. The modulus of this rectangular map is the positive sine
operator, and the relevant unitarily invariant norms agree. The paper should
state this bridge explicitly rather than identify the two representations.

## Manuscript organization

`paper.tex` is the journal manuscript. Its structure is:

1. mathematical motivation and source scope;
2. the full-scope sine-theta theorem and Sylvester reduction;
3. the parameterized Proposition 4.4 counterexample, proof diagnosis,
   Q-norm consequence, and verified sharp displacement estimates;
4. mathematical architecture and formal ancestry;
5. related work, conclusion, AI-assistance disclosure, and artifact availability;
6. references and appendices with the notation guide, Davis--Kahan result
   inventory, source review, and reproduction information.

`appendix_process.tex` now contains supporting review methodology and the
complete Davis--Kahan inventory. It is not an empirical process-study appendix.

`literature_review.tex` is an older broad research memo. It contains material for
several paper directions and should not be treated as defining this journal
paper's scope. Relevant citations may be migrated into `paper.tex`; unrelated
process/application material should not be reintroduced merely because it
appears in the memo.

## Canonical evidence

Use the current repository rather than old prose summaries as the source of
truth. The main evidence locations are:

- `dev/davis-kahan-1970-formalization-result-inventory.json`: 29-target
  Davis--Kahan result inventory, build verification, disposition, and semantic
  certification;
- `DavisKahan/Sources/DavisKahan1970/`: source-facing Davis--Kahan declarations;
- `DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean`:
  machine-checked semantic-surface audit declarations;
- `DavisKahan/Sources/DavisKahan1970/SineTheta/Presentation.lean`: current
  source-facing sine-theta endpoint;
- `DavisKahan/Sources/DavisKahan1970/Section4.lean`: source-facing Proposition
  4.4 aliases and section-level results;
- `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean`:
  explicit Proposition 4.4 counterexample;
- `DavisKahan/FiniteDimensional/DirectRotation/QNorm.lean`: repaired Q-norm
  theorem;
- `ForTauCeti/`: reusable mathematical foundations, with final declarations in
  the `TauCeti.*` namespace;
- `../yws_formalization_conference/`: the separate YWS conference-paper stub.

`claims_to_evidence.md` records the claims that are safe to make in the current
journal manuscript and their supporting artifacts.

## Build

The paper-local snapshots are checked in so the manuscript can be built without
rerunning repository analyses:

```bash
make -C papers/dk_formalization_journal paper
```

The Makefile uses `latexmk` and expects a BibTeX-compatible executable named
`bibtex`. Some minimal TeX installations provide only `bibtex8`; in that case a
local PATH shim or an equivalent LaTeX build command is sufficient and does not
change the source.

`make -C papers/dk_formalization_journal accounting` belongs to the older
instrumentation workflow. It is not required to substantiate the journal
paper's central mathematical claims, and parts of it may require optional review
tooling/submodules that are absent from a lightweight source archive.

## Editing rules for this draft

- Keep the manuscript on Davis--Kahan; YWS material belongs in the separate
  conference-paper stub.
- State the mathematical theorem before discussing its Lean representation.
- Distinguish proof/kernel verification from semantic/source correspondence.
- For non-literal representation matches, state the mathematical equivalence
  being used (for example the modulus relation for the sine operator).
- Describe Proposition 4.4 precisely: printed claim, counterexample, failed proof
  step, and repaired theorem.
- Keep implementation/project-management chronology out of the main scientific
  narrative unless it is required to explain a mathematical audit result.
- Keep the workshop paper's empirical resource accounting, practitioner corpus,
  workflow taxonomy, and the personal learning narrative out of this manuscript.
  Disclose AI use in formalization and prose preparation explicitly.
- Put declaration inventories and detailed review mechanics in appendices or
  supplemental material.
- Do not infer source fidelity from declaration names. Use the reviewed source
  inventory and correspondence evidence.
