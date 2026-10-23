# Davis--Kahan (1970) in Lean: Formalization, Counterexample, and Repair

This directory contains the journal manuscript on the Lean formalization and
mathematical audit of Davis--Kahan perturbation theory. The scope is now fixed:

- **primary subject:** Davis and Kahan's 1970 perturbation paper and the reusable
  operator-theoretic infrastructure required to formalize it;
- **secondary application:** Yu--Wang--Samworth (YWS), where it gives a compact
  statistical specialization and an independent source-audit case;
- **additional mathematical result:** an explicit family refuting full-displacement
  trace-norm minimality at every positive acute angle, with a conventional proof
  and a verified Lean proof of the parameterized strengthening; and
- **out of scope for this manuscript:** downstream application projects and the
  workshop paper's empirical human--LLM/process study, practitioner corpus, and
  resource-accounting analysis.

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

A separate `sharp_displacement_unformalized.tex` contains mathematical proofs
for the universal projector lower bound, sharp `sec(alpha/2)` approximation
factor, optimality of the real four-dimensional competitor, and exact complex
trace-norm formula. The projector lower bound is Lean-verified in
`ProjectionDisplacement.lean`, and the counterexample's exact trace ratio is
Lean-verified in `TraceRatio.lean`. The universal sharp factor and global
minimization theorems are **not** yet Lean-verified.
The file is included in a red, breakable frame when the working-draft switch
`\includeUnformalizedDisplacementtrue` is selected in `paper.tex`; switch it
to `\includeUnformalizedDisplacementfalse` to omit the proposed extension
before preparing a checked-only submission. The unverified results are absent
from the abstract, formalized contribution list, and conclusion.

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
2. the parameterized Proposition 4.4 counterexample, proof diagnosis, Q-norm
   consequence, and relationship to prior minimization theory, with a visibly
   marked optional mathematical draft of sharp displacement bounds;
3. the full-scope sine-theta theorem, explicit separation hypotheses, modulus
   identity, and Sylvester reduction;
4. mathematical architecture and formal ancestry;
5. YWS as a shorter statistical specialization and source-audit case;
6. related work, conclusion, AI-assistance disclosure, and artifact availability;
7. references; then
8. appendices with Lean-reading notation, result inventory, correspondence review,
   artifact organization, and reproduction and extension verification evidence.

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
- `YuWangSamworth2015/`: YWS formalization and source-audit material; and
- `snapshots/census_macros.tex`: manuscript-facing YWS census counts.

`claims_to_evidence.md` records the claims that are safe to make in the current
journal manuscript and their supporting artifacts.

## YWS terminology

Use **two printed source defects in YWS**, not “two false YWS theorems.” The two
printed defects are:

1. equation (4) is missing a square; and
2. Theorem 3's printed rank-boundary convention uses `rank(A)+1` where the
   argument requires the ambient singular/eigenvalue index together with the
   ordinary zero continuation of singular values.

Several theorem-facing census rows depend on these corrections, so the number
of rows marked corrected is larger than two. That row count is not a defect
count.

Reserve “false proposition” for Davis--Kahan Proposition 4.4, where the
repository contains an explicit formal counterexample to the printed claim.

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

- Keep Davis--Kahan dominant. YWS may clarify impact, conventions, or statistical
  specialization, but should not become a co-equal second paper.
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
