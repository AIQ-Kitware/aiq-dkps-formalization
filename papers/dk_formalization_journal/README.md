# formalization_draft2

This directory contains the journal manuscript on the Lean formalization and
mathematical audit of Davis--Kahan perturbation theory. The scope is now fixed:

- **primary subject:** Davis and Kahan's 1970 perturbation paper and the reusable
  operator-theoretic infrastructure required to formalize it;
- **secondary application:** Yu--Wang--Samworth (YWS), where it gives a compact
  statistical specialization and an independent source-audit case;
- **methodological observation:** a concise discussion of AI-assisted
  formalization and the primary author's starting background, together with an
  explicit AI-use disclosure; and
- **out of scope for this manuscript:** downstream application projects and the
  workshop paper's empirical human--LLM/process study, practitioner corpus, and
  resource-accounting analysis.

The workshop paper in `../formalization_process/` remains useful editorially. In
particular, this journal draft adopts its sharper separation between kernel
verification and semantic/source correspondence, its treatment of representation
mismatches, and its more precise language for source defects. It does not import
the workshop paper's process-study contribution as a journal-paper contribution.

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
positive `sin Theta` operator acts on trial coordinates, while the Lean theorem
uses the rectangular map `(I - F0 F0*) E0`. These are not literally the same
operator. The modulus of the rectangular map is the source positive sine
operator, so the relevant unitarily invariant norms agree. The paper should
state this bridge explicitly rather than identify the two representations.

## Manuscript organization

`paper.tex` is the journal manuscript. Its intended structure is:

1. mathematical motivation and contribution statement;
2. a concise statement of Davis--Kahan scope, with detailed counting deferred to
   the appendix;
3. the full-scope sine-theta theorem and the modulus identification connecting
   the Lean operator to the source angle operator;
4. mathematical architecture: direct rotations, operator ideals/majorization,
   Sylvester separation, unbounded operators, and formal ancestry;
5. the Proposition 4.4 counterexample, proof diagnosis, and Q-norm repair;
6. YWS as a shorter statistical specialization and source-audit case;
7. AI-assisted formalization as an observation about the changing tooling
   landscape, with limitations stated explicitly;
8. related work, conclusion, and an AI-assistance disclosure;
9. references; then
10. appendices containing the detailed result inventory, review methodology,
    model/tool details, and artifact organization.

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
make -C papers/formalization_draft2 paper
```

The Makefile uses `latexmk` and expects a BibTeX-compatible executable named
`bibtex`. Some minimal TeX installations provide only `bibtex8`; in that case a
local PATH shim or an equivalent LaTeX build command is sufficient and does not
change the source.

`make -C papers/formalization_draft2 accounting` belongs to the older
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
  and workflow taxonomy out of this manuscript. A concise author-background and
  AI-tooling observation, plus full disclosure of AI use in formalization and
  prose preparation, belongs in the journal paper.
- Put declaration inventories and detailed review mechanics in appendices or
  supplemental material.
- Do not infer source fidelity from declaration names. Use the reviewed source
  inventory and correspondence evidence.
