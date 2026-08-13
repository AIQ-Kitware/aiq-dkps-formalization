# Davis--Kahan 1970 source atom inventory

**Purpose: exhaustive source fidelity and explicit claim-boundary accounting, not the 100% formalization denominator.** Every source atom remains visible so a hostile reviewer can challenge either an omission or the reason an item is outside the counted result set.

- Source blocks: **50**
- Source-fidelity atoms: **272**
- Numbered equations represented: **64/64**
- Atoms supporting one or more of the 29 counted results: **69**
- Fidelity-only atoms: **203**
- Boundary-classified atoms: **272/272**
- Atoms carrying a nonlocal-interpretation link: **11**
- Formalization-result denominator: **29 results**, maintained separately in `dev/davis-kahan-1970-formalization-result-inventory.json`.

The result denominator consists only of the four Section 2 headline theorems and the named theorems, propositions, lemmas, and corollaries Davis--Kahan actually establish. Definitions, proof derivations, examples, numerical work, historical/external results, Section 10, and explicitly unresolved/deferred claims remain here with explicit exclusion reasons but do not become Lean theorem obligations.

Two different links appear below and must not be confused. **Counted result support** is the printed-statement boundary: the atom is part of the hypotheses, conclusions, or scope of a counted result. **Nonlocal interpretation support** is evidence about how a printed statement is to be *read* — a global convention, a later standing assumption, a separating example, an inherited proof context. An interpretation-support atom is deliberately *not* part of the counted statement and adds nothing to the 29-result denominator.

## Boundary-classification vocabulary

- `background_theory_not_designated_result` — **2 atoms**
- `counted_result_hypothesis` — **10 atoms**
- `counted_result_scope` — **10 atoms**
- `counted_result_statement` — **49 atoms**
- `deferred_unproved_claim` — **2 atoms**
- `definition_not_result` — **9 atoms**
- `expository_commentary_not_result` — **3 atoms**
- `external_result_not_dk_result` — **3 atoms**
- `historical_knowledge_state` — **1 atoms**
- `introductory_background_not_designated_result` — **26 atoms**
- `open_question` — **5 atoms**
- `paper_wide_semantic_convention_not_result` — **1 atoms**
- `post_result_consequence_not_in_printed_statement` — **4 atoms**
- `post_result_interpretation_not_result` — **1 atoms**
- `post_result_scope_remark_not_in_printed_statement` — **4 atoms**
- `pre_result_motivation_not_result` — **1 atoms**
- `pre_result_setup_not_in_printed_statement` — **4 atoms**
- `proof_detail_not_in_printed_statement` — **4 atoms**
- `proof_or_derivation_not_result` — **67 atoms**
- `remark_or_example_not_result` — **6 atoms**
- `restatement_of_counted_result` — **6 atoms**
- `section10_motivation_not_result` — **3 atoms**
- `section9_worked_example_not_result` — **43 atoms**
- `section_setup_not_result` — **2 atoms**
- `sharpness_commentary_not_designated_result` — **6 atoms**

## Source-spec repairs retained from the PDF re-audit

- `S1-ui-norms.cosine-law` — Restored the unnumbered cosine-law identity immediately after (1.14).
- `DK-3.3-prop.eq-3-7` — Restored equation (3.7), the block formula for Q=UPU^{-1}.
- `DK-4.1-prop.eq-4-1` — Restored equation (4.1), the minimax characterization of the singular displacement values.
- `DK-4.1-prop.eq-4-2` — Restored equation (4.2), the pointwise angle comparison used in Proposition 4.1.
- `DK-9-model.unperturbed-strict-eigenvalue-order` — Restored the source ordering alpha1=0=alpha2<alpha3<alpha4<... rather than weakening it to positivity of the later roots.
- `DK-9.8.lower-bound-asymptotic` — Restored the source lower-bound comparison and O(epsilon^4) asymptotic preceding (9.8).

## Source material added by the 2026-08-12 nonlocal-semantics re-audit

The printed Section 2 tan Theta theorem is not locally self-contained: its faithful reading depends on the paper-wide vacuity convention and on the standing condition (3.5) introduced only in Section 3. That dependency was previously visible only in prose review notes.

- `S1-block-residual.norm-existence-vacuity-convention`
- `DK-3.2-prop.finite-crossing-automatic`
- `DK-3.1-thm.angle-operator-partial-isometry`
- `DK-6.3-thm.tangent-proof-temporary-boundedness`
- `DK-6.3-thm.ambient-wholeSpace-assembly`

Atoms carrying an `interpretation_support` block are reverse-linked to the counted result whose nonlocal reading they support. That link is deliberately separate from `formalization_result_ids`, which remains the printed-statement boundary: an interpretation-support atom is NOT part of the counted result statement.

Effect on the completion denominator: none; the completion denominator remains the 29 established results.

## Atoms in source order

### `S1-block-residual`

- `S1-block-residual.setup-hilbert-scope` — **scope / introductory_background_not_designated_result** — Separable real or complex Hilbert space; bounded main setting with stated unbounded extension.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.norm-existence-vacuity-convention` — **scope / paper_wide_semantic_convention_not_result** — Paper-wide convention: some of the paper's results are vacuous when certain norms occurring in them fail to exist, and the source will not repeat that qualification at the individual statements.
  - Counted result support: none
  - Boundary rationale: A global semantic reading convention for the paper's statements, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary. It is not a completion obligation, but it is load-bearing evidence for how the printed Section 2 tangent theorem is to be read when a displayed norm does not exist.
  - Nonlocal interpretation support for `S2-tan-theta` (`paper_wide_convention`): Supplies the source's own semantics for a printed conclusion whose displayed norm need not exist; the ambient tangent conclusion is exactly such a case when the perturbed crossing subspace is nonzero.
- `S1-block-residual.reducing-projector-setup` — **construction / introductory_background_not_designated_result** — P reduces A and E0,E1 are isometries onto the two reducing summands.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.q-reduces-perturbed` — **construction / introductory_background_not_designated_result** — Q reduces A+H and F0,F1 give its reducing decomposition.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.no-spectral-projector-assumption` — **scope / introductory_background_not_designated_result** — P and Q need not be spectral projectors and the diagonal spectral sets may overlap.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.unitary-intertwiner-dimension-criterion` — **assertion / introductory_background_not_designated_result** — A unitary carrying P-space to Q-space exists precisely with the two matching dimension conditions.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.within-subspace-coordinate-freedom` — **assertion / introductory_background_not_designated_result** — Changing the intertwining unitary changes only the within-subspace unitary coordinates W0,W1.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.residual-inherited-block` — **identity / introductory_background_not_designated_result** — When A0 is inherited from A, R=H E0 and is the first block column of H.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.rayleigh-ritz-h0-zero` — **identity / introductory_background_not_designated_result** — The Rayleigh--Ritz choice A0=E0*(A+H)E0 is equivalent here to H0=0.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.residual-gram-split` — **identity / introductory_background_not_designated_result** — R*R=H0^2+B*B.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.rayleigh-ritz-minimizes-residual` — **extremal / introductory_background_not_designated_result** — The Rayleigh--Ritz choice minimizes residual size among the block choices under discussion.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.one-sided-vs-strong-offdiagonal` — **scope / introductory_background_not_designated_result** — H0=0 is distinguished from the stronger H0=H1=0 condition.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.residual-eigenvalue-sum` — **consequence / introductory_background_not_designated_result** — There is an ordering of m exact eigenvalues with sum_j (alpha_j-lambda_j)^2 <= ||R||_sq^2.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.residual-eigenvalue-pointwise` — **consequence / introductory_background_not_designated_result** — The same ordering satisfies |alpha_j-lambda_j| <= ||R||_1.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-block-residual.eq-1-1` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.1) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-block-residual.eq-1-2` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.2) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-block-residual.eq-1-3` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.3) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-block-residual.eq-1-4` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.4) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-block-residual.eq-1-5` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.5) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
  - Nonlocal interpretation support for `S2-tan-theta` (`related_dimension_condition`): The matching-dimension condition (1.5) is the only dimension condition available when the Section 2 tangent theorem is printed; the Proposition 3.2 remark shows it does not imply (3.5).
- `S1-block-residual.eq-1-6` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.6) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-block-residual.eq-1-7` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.7) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-block-residual.eq-1-8` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.8) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `S1-ui-norms`

- `S1-ui-norms.ui-rank-one-normalization` — **definition / definition_not_result** — Rank-one operators satisfy the normalized unitary-invariant norm convention.
  - Counted result support: none
  - Boundary rationale: This atom is definitional/setup material. It is retained for source fidelity and notation, but definitions are not counted Davis--Kahan result obligations.
- `S1-ui-norms.ui-contraction-monotonicity` — **assertion / introductory_background_not_designated_result** — Left and right multiplication by contractions cannot increase a unitary-invariant norm.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.singular-minimax-noncompact-scope` — **scope / introductory_background_not_designated_result** — The singular-value minimax expression extends to bounded noncompact operators, with spectral-multiplicity cautions.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.hilbert-schmidt-identity` — **definition / definition_not_result** — The Hilbert--Schmidt norm is the square root of the sum of squared singular values and trace K*K.
  - Counted result support: none
  - Boundary rationale: This atom is definitional/setup material. It is retained for source fidelity and notation, but definitions are not counted Davis--Kahan result obligations.
- `S1-ui-norms.fan-dominance` — **theorem / introductory_background_not_designated_result** — All-unitary-invariant-norm comparison is equivalent to comparison in every Ky Fan norm.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.eq1-13-variational` — **variational / introductory_background_not_designated_result** — The Ky Fan norm also equals the supremum of the real sum of y_k* K x_k over orthonormal tuples.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.cosine-law` — **identity / introductory_background_not_designated_result** — The vector-angle convention satisfies ||x+y||^2=||x||^2+||y||^2+2||x||||y||cos angle(x,y).
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.s0-singular-values` — **assertion / introductory_background_not_designated_result** — The singular values of S0 are sin(theta_k) for the principal-angle data.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.ambient-angle-doubling` — **assertion / introductory_background_not_designated_result** — Section 1 states, in anticipation of the Section 3 direct-rotation construction and without restating a dimension hypothesis, that the nonzero angle data of the ambient angle operator are those of Theta_0 occurring twice, once from each side.
  - Counted result support: none
  - Boundary rationale: Section 1 background stated in anticipation of the Section 3 direct-rotation construction, not a designated result. It is recorded as interpretation evidence because the same infinite-dimensional configuration that makes the ambient tangent norm fail to exist also qualifies this doubling sentence.
  - Nonlocal interpretation support for `S2-tan-theta` (`related_unqualified_claim`): Section 1 asserts the doubling of the nonzero ambient angle data without a dimension hypothesis; the same bilateral-shift configuration qualifies this sentence, so the omitted qualification is not peculiar to the tangent theorem.
- `S1-ui-norms.directed-sine-norm` — **identity / introductory_background_not_designated_result** — ||Q^perp P||=||Q^perp E0||=||sin Theta0|| for every UI norm.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.ambient-sine-norm` — **identity / introductory_background_not_designated_result** — ||P-Q||=||sin Theta|| for every UI norm.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.operator-largest-one-sided-distance` — **identity / introductory_background_not_designated_result** — In operator norm the largest one-sided distance is ||sin Theta||_1.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.closest-unit-vector-distance` — **identity / introductory_background_not_designated_result** — The closest-unit-vector distance is 2||sin(Theta/2)||_1.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.j-block-form` — **construction / introductory_background_not_designated_result** — Section 3 constructs the skew block partial isometry J from J0.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.direct-rotation-exponential` — **identity / introductory_background_not_designated_result** — The distinguished direct rotation satisfies U=exp(J Theta)=cos Theta+J sin Theta with the displayed block form.
  - Counted result support: none
  - Boundary rationale: This is Section 1 introductory setup/background or an introductory consequence, not one of the four Section 2 headline theorems or a named theorem/proposition/lemma/corollary counted by the project.
- `S1-ui-norms.eq-1-9` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.9) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-ui-norms.eq-1-10` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.10) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-ui-norms.eq-1-11` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.11) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-ui-norms.eq-1-12` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.12) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-ui-norms.eq-1-13` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.13) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-ui-norms.eq-1-14` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.14) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-ui-norms.eq-1-15` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.15) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-ui-norms.eq-1-16` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.16) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-ui-norms.eq-1-17` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.17) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `S1-ui-norms.eq-1-18` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (1.18) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `S2-sin-theta`

- `S2-sin-theta.family-distinctness` — **scope / expository_commentary_not_result** — The four Section 2 theorem families are distinct rather than mere restatements.
  - Counted result support: none
  - Boundary rationale: This atom is explanatory/source-scope commentary rather than a counted Davis--Kahan result statement.
- `S2-sin-theta.ui-norm-scope` — **scope / counted_result_scope** — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
  - Counted result support: `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta`
  - Boundary rationale: This atom records printed scope shared by a counted Davis--Kahan result (such as norm, scalar, dimension, or unbounded scope) and must be matched by its Lean evidence.
- `S2-sin-theta.gap-hypothesis` — **hypothesis / counted_result_hypothesis** — The sine theorem uses interval/exterior separation, allowing the A0 and Lambda1 roles to be interchanged.
  - Counted result support: `S2-sin-theta`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `S2-sin-theta.directed-conclusion` — **theorem / counted_result_statement** — delta ||sin Theta0|| <= ||R||.
  - Counted result support: `S2-sin-theta`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `S2-tan-theta`

- `S2-tan-theta.ordered-gap-hypothesis` — **hypothesis / counted_result_hypothesis** — The tangent theorem assumes A0 below Lambda1 by delta.
  - Counted result support: `S2-tan-theta`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `S2-tan-theta.rayleigh-ritz-hypothesis` — **hypothesis / counted_result_hypothesis** — The tangent theorem assumes H0=0, equivalently the Rayleigh--Ritz block choice.
  - Counted result support: `S2-tan-theta`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `S2-tan-theta.directed-conclusion` — **theorem / counted_result_statement** — delta ||tan Theta0|| <= ||R||.
  - Counted result support: `S2-tan-theta`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `S2-tan-theta.ambient-conclusion` — **theorem / counted_result_statement** — delta ||tan Theta|| <= ||H||.
  - Counted result support: `S2-tan-theta`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
  - Nonlocal interpretation support for `S2-tan-theta` (`printed_statement_clause`): This is the printed clause whose faithful reading depends on nonlocal source material; the directed conclusion is unaffected.
### `S2-sin-two-theta`

- `S2-sin-two-theta.gap-hypothesis` — **hypothesis / counted_result_hypothesis** — The double-sine theorem separates Lambda0 from Lambda1 by an interval/exterior gap.
  - Counted result support: `S2-sin-two-theta`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `S2-sin-two-theta.directed-conclusion` — **theorem / counted_result_statement** — delta ||sin(2 Theta0)|| <= 2||R||.
  - Counted result support: `S2-sin-two-theta`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `S2-sin-two-theta.ambient-conclusion` — **theorem / counted_result_statement** — delta ||sin(2 Theta)|| <= 2||H||.
  - Counted result support: `S2-sin-two-theta`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `S2-tan-two-theta`

- `S2-tan-two-theta.ordered-gap-hypothesis` — **hypothesis / counted_result_hypothesis** — The double-tangent theorem assumes A0 below A1 by delta.
  - Counted result support: `S2-tan-two-theta`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `S2-tan-two-theta.strong-offdiagonal-hypothesis` — **hypothesis / counted_result_hypothesis** — The double-tangent theorem assumes H0=H1=0.
  - Counted result support: `S2-tan-two-theta`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `S2-tan-two-theta.no-extra-pole-hypothesis` — **scope / counted_result_scope** — The printed theorem has no independent tan-pole exclusion or perturbed-block spectral-placement hypothesis.
  - Counted result support: `S2-tan-two-theta`
  - Boundary rationale: This atom records printed scope shared by a counted Davis--Kahan result (such as norm, scalar, dimension, or unbounded scope) and must be matched by its Lean evidence.
- `S2-tan-two-theta.directed-conclusion` — **theorem / counted_result_statement** — delta ||tan(2 Theta0)|| <= 2||R||.
  - Counted result support: `S2-tan-two-theta`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `S2-tan-two-theta.ambient-conclusion` — **theorem / counted_result_statement** — delta ||tan(2 Theta)|| <= 2||H||.
  - Counted result support: `S2-tan-two-theta`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `S2-tan-two-theta.pole-exclusion-derived` — **proof-claim / proof_or_derivation_not_result** — Section 7 derives the needed nonvanishing cosine factors from the printed hypotheses.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `S2-sharpness`

- `S2-sharpness.constants-best-possible` — **sharpness / sharpness_commentary_not_designated_result** — The constants in all four theorem families are best possible.
  - Counted result support: none
  - Boundary rationale: This is sharpness/equality commentary outside a designated result statement. It remains visible for fidelity but does not create an additional result obligation.
- `S2-sharpness.two-dimensional-equality` — **sharpness / sharpness_commentary_not_designated_result** — Two-dimensional examples attain the constants.
  - Counted result support: none
  - Boundary rationale: This is sharpness/equality commentary outside a designated result statement. It remains visible for fidelity but does not create an additional result obligation.
- `S2-sharpness.direct-sum-simultaneous-equality` — **sharpness / sharpness_commentary_not_designated_result** — Orthogonal sums give simultaneous equality for all UI norms.
  - Counted result support: none
  - Boundary rationale: This is sharpness/equality commentary outside a designated result statement. It remains visible for fidelity but does not create an additional result obligation.
- `S2-sharpness.first-order-asymptotic` — **sharpness / sharpness_commentary_not_designated_result** — All four estimates share the stated first-order epsilon asymptotics.
  - Counted result support: none
  - Boundary rationale: This is sharpness/equality commentary outside a designated result statement. It remains visible for fidelity but does not create an additional result obligation.
### `S2-unbounded-scope`

- `S2-unbounded-scope.infinite-dimensional-scope` — **scope / counted_result_scope** — All four main results apply in infinite as well as finite dimension.
  - Counted result support: `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta`
  - Boundary rationale: This atom records printed scope shared by a counted Davis--Kahan result (such as norm, scalar, dimension, or unbounded scope) and must be matched by its Lean evidence.
- `S2-unbounded-scope.arbitrary-ui-scope` — **scope / counted_result_scope** — All four main results apply to arbitrary UI norms.
  - Counted result support: `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta`
  - Boundary rationale: This atom records printed scope shared by a counted Davis--Kahan result (such as norm, scalar, dimension, or unbounded scope) and must be matched by its Lean evidence.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **scope / counted_result_scope** — The results extend to unbounded self-adjoint A under the stated domain condition.
  - Counted result support: `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta`
  - Boundary rationale: This atom records printed scope shared by a counted Davis--Kahan result (such as norm, scalar, dimension, or unbounded scope) and must be matched by its Lean evidence.
- `S2-unbounded-scope.bounded-residual-needed` — **scope / counted_result_scope** — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
  - Counted result support: `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta`
  - Boundary rationale: This atom records printed scope shared by a counted Davis--Kahan result (such as norm, scalar, dimension, or unbounded scope) and must be matched by its Lean evidence.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **scope / counted_result_scope** — Gap intervals may be half-infinite and the remaining spectra unbounded.
  - Counted result support: `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta`
  - Boundary rationale: This atom records printed scope shared by a counted Davis--Kahan result (such as norm, scalar, dimension, or unbounded scope) and must be matched by its Lean evidence.
### `DK-3.1-def`

- `DK-3.1-def.s0-s1-singular-values` — **assertion / section_setup_not_result** — S0 and S1 have the same nonzero singular values, with the stated possible initial unit singular values from unequal C0 nullities.
  - Counted result support: none
  - Boundary rationale: This atom is section-level setup used to formulate or prove later named results; it is not itself inside a counted result statement.
- `DK-3.1-def.direct-rotation-definition` — **definition / definition_not_result** — A direct rotation is a unitary intertwiner with C0,C1 positive and S1=S0*.
  - Counted result support: none
  - Boundary rationale: This atom is definitional/setup material. It is retained for source fidelity and notation, but definitions are not counted Davis--Kahan result obligations.
- `DK-3.1-def.u-notation` — **definition / definition_not_result** — The paper reserves U for direct rotations.
  - Counted result support: none
  - Boundary rationale: This atom is definitional/setup material. It is retained for source fidelity and notation, but definitions are not counted Davis--Kahan result obligations.
- `DK-3.1-def.eq-3-1` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (3.1) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-3.1-def.eq-3-2` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (3.2) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-3.1-def.eq-3-3` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (3.3) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-3.1-def.eq-3-4` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (3.4) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-3.2-def`

- `DK-3.2-def.acute-case-definition` — **definition / definition_not_result** — The acute case is exactly the vanishing of the two crossing intersections.
  - Counted result support: none
  - Boundary rationale: This atom is definitional/setup material. It is retained for source fidelity and notation, but definitions are not counted Davis--Kahan result obligations.
### `DK-3.1-prop`

- `DK-3.1-prop.existence` — **theorem / counted_result_statement** — In the acute case a direct rotation exists.
  - Counted result support: `DK-3.1-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.1-prop.uniqueness` — **theorem / counted_result_statement** — In the acute case the direct rotation is unique.
  - Counted result support: `DK-3.1-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.1-prop.positive-diagonal-characterization` — **theorem / counted_result_statement** — Positivity of C0,C1 characterizes the direct rotation among unitary intertwiners in the acute case.
  - Counted result support: `DK-3.1-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-3.2-prop`

- `DK-3.2-prop.existence-iff-crossing-dimensions` — **theorem / counted_result_statement** — Outside the acute case, direct rotation existence is equivalent to equality of the crossing dimensions.
  - Counted result support: `DK-3.2-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.2-prop.nonuniqueness` — **theorem / counted_result_statement** — When it exists outside the acute case it need not be unique.
  - Counted result support: `DK-3.2-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.2-prop.crossing-square-minus-one` — **theorem / proof_detail_not_in_printed_statement** — On the crossing subspaces U^2 x=-x.
  - Counted result support: none
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
- `DK-3.2-prop.finite-crossing-automatic` — **scope / post_result_scope_remark_not_in_printed_statement** — Under the assumed (1.5), condition (3.5) holds automatically whenever either dim P-space or dim P-perp-space is finite.
  - Counted result support: none
  - Boundary rationale: A scope remark attached to Proposition 3.2 rather than part of its printed statement. It records exactly when the crossed-defect condition is automatic, and therefore delimits the configurations in which the Section 2 ambient tangent reading is at issue at all.
  - Nonlocal interpretation support for `S2-tan-theta` (`automatic_case`): Shows the interpretive difficulty is genuinely infinite-dimensional: with either summand finite-dimensional, (1.5) already gives (3.5).
- `DK-3.2-prop.bilateral-shift-counterexample` — **counterexample / remark_or_example_not_result** — The bilateral-shift example on two-sided square-summable sequences satisfies (1.5) with nested P-space and Q-space, has crossing subspaces of dimensions 1 and 0, and therefore fails (3.5): the matching-dimension conditions do not imply the crossing-dimension condition in infinite dimension.
  - Counted result support: none
  - Boundary rationale: The bilateral-shift example demonstrates that the matching-dimension conditions (1.5) do not imply the crossed-dimension condition (3.5) in infinite dimension. It is a remark/example attached to Proposition 3.2 rather than a designated result. It is not a counterexample to any counted result; its role in this repository is to show that the qualification omitted from the printed Section 2 tangent statement is mathematically substantive.
  - Nonlocal interpretation support for `S2-tan-theta` (`scope_separating_example`): Proves that (1.5) does not imply (3.5) in infinite dimension, hence that the omitted qualification is substantive rather than cosmetic.
- `DK-3.2-prop.eq-3-5` — **numbered-equation / counted_result_statement** — Exact mathematical content of source equation (3.5) as reconstructed in the distributable TeX.
  - Counted result support: `DK-3.2-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
  - Nonlocal interpretation support for `S2-tan-theta` (`omitted_qualification`): Equation (3.5) is exactly the equality of the two crossing-subspace dimensions, i.e. of the right-angle parts of Theta_0 and Theta_1. It is the qualification the Section 2 statement does not carry.
### `S3-standing-scope`

- `S3-standing-scope.crossed-dimension-standing-assumption` — **scope / counted_result_scope** — Standing convention: (3.5) is assumed as well as (1.5) for the remainder of the paper, except where the contrary is explicitly stated, so a direct rotation always exists and the development uses its direct special case (3.6).
  - Counted result support: `DK-3.4-prop`, `DK-8.2-thm`
  - Boundary rationale: This atom records a standing source-scope convention, not a result. It is linked to the counted results whose printed reading needs it: Theorem 8.2, whose printed conclusion is the AMBIENT Theta < pi/4 obtained from a directed estimate, and Proposition 3.4, whose source block reads "under the same direct-rotation setup" instead of restating the dimension conditions. It is NOT linked to counted results that restate the conditions in their own printed statement (Theorem 3.1 and, through it, Corollary 3.1), to results that do not involve the pair (P,Q) at all (Sections 5 and 6 lemmas and the Sylvester theorems), or to Theorem 8.1, whose ambient quarter-angle characterization is proved with no dimension or crossed-defect hypothesis at all.
  - Nonlocal interpretation support for `S2-tan-theta` (`later_standing_assumption`): From immediately after Proposition 3.2 onward, (3.5) as well as (1.5) is assumed except where the contrary is stated; the Section 6 proof of the printed tangent theorem is inside that scope.
### `DK-3.3-prop`

- `DK-3.3-prop.reflection-conjugacy` — **identity / pre_result_setup_not_in_printed_statement** — With X=P-Pperp and Q_-=XQX, U^{-1}=XUX.
  - Counted result support: none
  - Boundary rationale: This atom appears immediately before the named result as setup, identity, or motivation; it is outside the printed theorem/proposition statement.
- `DK-3.3-prop.principal-square-root` — **theorem / counted_result_statement** — Every direct rotation is the principal unitary square root of the product of the two reflections.
  - Counted result support: `DK-3.3-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.3-prop.square-root-converse` — **theorem / counted_result_statement** — A principal square root is a direct rotation when it maps the two crossing subspaces appropriately.
  - Counted result support: `DK-3.3-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.3-prop.eq-3-6` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (3.6) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-3.3-prop.eq-3-7` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (3.7) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-3.3-prop.eq-3-8` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (3.8) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-3.4-prop`

- `DK-3.4-prop.u-square-direct-rotation` — **theorem / counted_result_statement** — If C0^2>=1/2, then U^2 is the direct rotation from Q_- to Q.
  - Counted result support: `DK-3.4-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-3.1-thm`

- `DK-3.1-thm.angle-operator-partial-isometry` — **construction / pre_result_setup_not_in_printed_statement** — For the direct rotation, Theta_j = arccos C_j, the two angle operators are isometric-equivalent apart from the dimensionalities of their null spaces, and the polar resolution S_0 = J_0 sin Theta_0 gives a partial isometry J_0 of the closed range of Theta_0 onto that of Theta_1 with J_0 Theta_0 = Theta_1 J_0.
  - Counted result support: none
  - Boundary rationale: Section 3 setup preceding the printed Theorem 3.1 statement rather than part of it. It is recorded because the Section 6 ambient tangent proof compares its two corners through exactly this J_0, which exists as described only in the direct-rotation setting fixed by the standing (3.5).
  - Nonlocal interpretation support for `S2-tan-theta` (`proof_context_dependency`): The equinormality of the two ambient tangent corners is a property of the direct-rotation partial isometry J_0, constructed under the standing crossed-defect convention.
- `DK-3.1-thm.complete-invariant` — **theorem / counted_result_statement** — Spectral multiplicity functions of Theta0,Theta1 completely classify the pair under the stated dimension hypotheses.
  - Counted result support: `DK-3.1-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.1-thm.converse-angle-data` — **theorem / counted_result_statement** — Conversely the angle operators may be arbitrary positive contractions in [0,pi/2] with matching spectral multiplicities away from zero and the stated dimensions.
  - Counted result support: `DK-3.1-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.1-thm.reconstruction` — **construction / proof_detail_not_in_printed_statement** — The pair is reconstructed from the angle data and J0.
  - Counted result support: none
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
### `DK-3.1-cor`

- `DK-3.1-cor.compact-complete-invariants` — **theorem / counted_result_statement** — If PQperpP is compact, the eigenvalues of Theta0,Theta1 counted with multiplicity are complete invariants.
  - Counted result support: `DK-3.1-cor`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.1-cor.allowed-angle-sequence` — **theorem / counted_result_statement** — Theta0 eigenvalues may be any decreasing sequence in [0,pi/2] tending to zero plus possible zero eigenspace.
  - Counted result support: `DK-3.1-cor`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.1-cor.theta1-match` — **theorem / counted_result_statement** — Theta1 has the same nonzero eigenvalues and may differ only in zero multiplicity.
  - Counted result support: `DK-3.1-cor`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-3.5-prop`

- `DK-3.5-prop.commutation` — **theorem / counted_result_statement** — Theta commutes with P,Q,J,U.
  - Counted result support: `DK-3.5-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.5-prop.direct-rotation-exponential` — **identity / pre_result_setup_not_in_printed_statement** — U=exp(J Theta).
  - Counted result support: none
  - Boundary rationale: This atom appears immediately before the named result as setup, identity, or motivation; it is outside the printed theorem/proposition statement.
- `DK-3.5-prop.cos-square-projector` — **identity / pre_result_setup_not_in_printed_statement** — cos^2 Theta=PQP+Pperp Qperp Pperp.
  - Counted result support: none
  - Boundary rationale: This atom appears immediately before the named result as setup, identity, or motivation; it is outside the printed theorem/proposition statement.
- `DK-3.5-prop.eigenvector-rotation-angle` — **theorem / counted_result_statement** — If Theta x=theta x then angle(x,Ux)=theta.
  - Counted result support: `DK-3.5-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-3.5-prop.acute-maximal-characterization` — **theorem / counted_result_statement** — In the acute case each theta-eigenspace is the unique maximal P/Q-reducing subspace with the stated constant-angle properties.
  - Counted result support: `DK-3.5-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-3.2-cor`

- `DK-3.2-cor.swap-invariance` — **theorem / counted_result_statement** — Swapping P and Q leaves Theta unchanged and sends J to -J.
  - Counted result support: `DK-3.2-cor`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-4.1-prop`

- `DK-4.1-prop.vz-factorization` — **construction / section_setup_not_result** — Every unitary V carrying P to Q is written V=UZ with Z block diagonal in the Section 4 setup.
  - Counted result support: none
  - Boundary rationale: This atom is section-level setup used to formulate or prove later named results; it is not itself inside a counted result statement.
- `DK-4.1-prop.orthonormal-angle-lower-bounds` — **theorem / counted_result_statement** — For every such V there are orthonormal v_k in P with angle(v_k,Vv_k)>=theta_k.
  - Counted result support: `DK-4.1-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-4.1-prop.singular-value-minimality` — **theorem / counted_result_statement** — Each singular value of (1-V)|P is minimized at V=U with value 2 sin(theta_k/2).
  - Counted result support: `DK-4.1-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-4.1-prop.closest-q-vector-proof-step` — **proof-claim / proof_or_derivation_not_result** — The pointwise comparison uses Qx/||Qx|| as the closest unit vector in Q-space.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.1-prop.eq-4-1` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (4.1) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.1-prop.eq-4-2` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (4.2) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-4.1-cor`

- `DK-4.1-cor.ui-minimality-on-p` — **theorem / counted_result_statement** — For every UI norm, ||(1-V)P|| is minimized at V=U.
  - Counted result support: `DK-4.1-cor`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-4.2-prop`

- `DK-4.2-prop.basis-sine-square-lower-bound` — **theorem / counted_result_statement** — For every orthonormal basis of P, sum sin^2 angle(v_k,Vv_k) >= sum sin^2 theta_k, including infinite RHS.
  - Counted result support: `DK-4.2-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-4.2-prop.trace-identification` — **proof-claim / proof_or_derivation_not_result** — The lower bound is identified with tr(S0* S0).
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-4.3-prop`

- `DK-4.3-prop.plane-parameterization` — **construction / proof_detail_not_in_printed_statement** — On each principal two-plane V has the displayed a_j,b_j parameterization.
  - Counted result support: none
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
- `DK-4.3-prop.squared-displacement-global-minimum` — **theorem / counted_result_statement** — ||(1-V*)(1-V)|| is minimized by U for every UI norm.
  - Counted result support: `DK-4.3-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-4.3-prop.operator-norm-displacement-minimum` — **consequence / post_result_consequence_not_in_printed_statement** — The operator norm of 1-V is minimized by U.
  - Counted result support: none
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
- `DK-4.3-prop.hilbert-schmidt-displacement-minimum` — **consequence / post_result_consequence_not_in_printed_statement** — The Hilbert--Schmidt norm of 1-V is minimized by U.
  - Counted result support: none
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
- `DK-4.3-prop.arbitrary-ui-displacement-warning` — **counterclaim / post_result_consequence_not_in_printed_statement** — Arbitrary UI norms of 1-V need not be minimized by U.
  - Counted result support: none
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
- `DK-4.3-prop.eq-4-3` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (4.3) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.3-prop.eq-4-4` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (4.4) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.3-prop.eq-4-5` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (4.5) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.3-prop.eq-4-6` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (4.6) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-4.4-prop`

- `DK-4.4-prop.example4-1-real-reflection` — **counterexample / remark_or_example_not_result** — Example 4.1 gives a real reflection with singular values 2,0 versus two equal direct-rotation singular values and defeats the Ky Fan 2 norm for theta>pi/3.
  - Counted result support: none
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-4.4-prop.example4-2-complex-phase` — **counterexample / remark_or_example_not_result** — Example 4.2 uses V=e^{i delta}U and shows the full-displacement UI minimum can fail in complex space.
  - Counted result support: none
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-4.4-prop.printed-proposition4-4` — **source-assertion / counted_result_statement** — The paper asserts that in real space with Theta<=pi/3, U minimizes ||1-V|| for every UI norm.
  - Counted result support: `DK-4.4-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-4.4-prop.printed-sharp-threshold` — **source-assertion / sharpness_commentary_not_designated_result** — The paper asserts the pi/3 threshold is sharp in view of the examples.
  - Counted result support: none
  - Boundary rationale: This is sharpness/equality commentary outside a designated result statement. It remains visible for fidelity but does not create an additional result obligation.
### `DK-5.1-thm`

- `DK-5.1-thm.banach-hypotheses` — **hypothesis / counted_result_hypothesis** — Banach-space theorem with ||B||<=alpha and ||A^{-1}||<=(alpha+delta)^{-1}, compatible cross norm.
  - Counted result support: `DK-5.1-thm`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `DK-5.1-thm.sylvester-lower-bound` — **theorem / counted_result_statement** — AX-XB=C implies ||C||>=delta||X||.
  - Counted result support: `DK-5.1-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-5.1-thm.roles-interchange` — **scope / post_result_scope_remark_not_in_printed_statement** — A and B roles/hypotheses may be interchanged.
  - Counted result support: none
  - Boundary rationale: This atom is a scope/extension remark stated after the named result, not part of the printed result environment; it is retained for fidelity without enlarging the result denominator.
- `DK-5.1-thm.one-sided-unbounded-extension` — **scope / post_result_scope_remark_not_in_printed_statement** — The proof covers densely-defined unbounded A with bounded inverse hypothesis while B,X remain bounded.
  - Counted result support: none
  - Boundary rationale: This atom is a scope/extension remark stated after the named result, not part of the printed result environment; it is retained for fidelity without enlarging the result denominator.
### `DK-5-hermitian-inequalities`

- `DK-5-hermitian-inequalities.pairwise-gap-hypothesis` — **hypothesis / background_theory_not_designated_result** — Hermitian A,B have pairwise spectral distance at least delta.
  - Counted result support: none
  - Boundary rationale: This is background/auxiliary theory discussed outside a designated Davis--Kahan result environment; it is not part of the 29-result denominator.
- `DK-5-hermitian-inequalities.operator-norm-constant-one-fails` — **counterclaim / background_theory_not_designated_result** — The operator-norm analogue with constant 1 can fail.
  - Counted result support: none
  - Boundary rationale: This is background/auxiliary theory discussed outside a designated Davis--Kahan result environment; it is not part of the 29-result denominator.
- `DK-5-hermitian-inequalities.rank-factor-not-best` — **sharpness / sharpness_commentary_not_designated_result** — Equation (5.2) is not best possible unless rank C<=1.
  - Counted result support: none
  - Boundary rationale: This is sharpness/equality commentary outside a designated result statement. It remains visible for fidelity but does not create an additional result obligation.
- `DK-5-hermitian-inequalities.universal-constant-question` — **open-question / open_question** — The source asks whether the rank factor can be replaced by a universal constant.
  - Counted result support: none
  - Boundary rationale: The paper explicitly leaves this as an open question; it is inventoried but is not a formalization obligation.
- `DK-5-hermitian-inequalities.constant-one-explicit-counterexample` — **counterexample / remark_or_example_not_result** — The displayed 2x2 A,B,X example rules out universal constant 1.
  - Counted result support: none
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-5-hermitian-inequalities.eq-5-1` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (5.1) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-5-hermitian-inequalities.eq-5-2` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (5.2) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-5.2-thm`

- `DK-5.2-thm.hilbert-unbounded-hypotheses` — **hypothesis / counted_result_hypothesis** — Theorem 5.2 gives the Hilbert-space unbounded Sylvester setup with separated spectra and domain/core hypotheses.
  - Counted result support: `DK-5.2-thm`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `DK-5.2-thm.hilbert-unbounded-conclusion` — **theorem / counted_result_statement** — The corresponding delta||X|| lower bound holds in the stated UI/ideal norm scope.
  - Counted result support: `DK-5.2-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-5.1-lem`

- `DK-5.1-lem.strong-cutoff-convergence` — **lemma / counted_result_statement** — The spectral-cutoff approximants converge strongly in the manner stated and support the unbounded proof.
  - Counted result support: `DK-5.1-lem`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-6.1-lem`

- `DK-6.1-lem.ordered-sylvester-forward` — **lemma / counted_result_statement** — The ordered spectral separation implies the stated Sylvester/UI-norm lower bound.
  - Counted result support: `DK-6.1-lem`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-6.1-lem.ordered-sylvester-converse` — **lemma / counted_result_statement** — The source includes the converse characterization used in the single-angle proof.
  - Counted result support: `DK-6.1-lem`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-6.2-lem`

- `DK-6.2-lem.pinching-contraction` — **lemma / counted_result_statement** — The reflection/pinching operation contracts every unitary-invariant norm in the stated setup.
  - Counted result support: `DK-6.2-lem`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-6.1-prop`

- `DK-6.1-prop.sine-proof-residual-identity` — **identity / proof_detail_not_in_printed_statement** — The symmetric sine proof rewrites the relevant off-diagonal block as the Sylvester residual identity.
  - Counted result support: none
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
- `DK-6.1-prop.symmetric-sine-theorem` — **theorem / counted_result_statement** — Proposition 6.1 gives the symmetric sine-theta conclusion under two-sided spectral placement.
  - Counted result support: `DK-6.1-prop`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-6.1-prop.source-counterexample-need-two-sided` — **counterexample / remark_or_example_not_result** — The source exhibits the failure of the ambient/symmetric conclusion when the needed two-sided placement is dropped.
  - Counted result support: none
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-6.1-prop.eq-6-1` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.1) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-6.1-thm`

- `DK-6.1-thm.generalized-sine-hypotheses` — **hypothesis / counted_result_hypothesis** — The generalized sine theorem allows nonisometric E0 with E0*E0 >= epsilon^2 and the stated spectral separation.
  - Counted result support: `DK-6.1-thm`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `DK-6.1-thm.generalized-sine-conclusion` — **theorem / counted_result_statement** — delta epsilon ||sin Theta0|| <= ||R||.
  - Counted result support: `DK-6.1-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-6.1-thm.unequal-dimension-scope` — **scope / counted_result_scope** — The generalized theorem allows unequal-dimensional comparison subspaces as stated.
  - Counted result support: `DK-6.1-thm`
  - Boundary rationale: This atom records printed scope shared by a counted Davis--Kahan result (such as norm, scalar, dimension, or unbounded scope) and must be matched by its Lean evidence.
### `DK-6.2-thm`

- `DK-6.2-thm.second-generalized-sine` — **theorem / counted_result_statement** — The second generalized sine theorem gives the Hilbert--Schmidt estimate under pairwise spectral separation.
  - Counted result support: `DK-6.2-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-6.2-thm.rank-corrected-operator-consequence` — **consequence / post_result_consequence_not_in_printed_statement** — The stated rank-corrected operator-norm consequence follows.
  - Counted result support: none
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
### `DK-6.3-thm`

- `DK-6.3-thm.tangent-setup-identities` — **proof-claim / proof_or_derivation_not_result** — Equations (6.2)--(6.6) provide the block identities used in the generalized tangent proof.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.tangent-proof-temporary-boundedness` — **proof-claim / proof_or_derivation_not_result** — The Section 6 tangent proof temporarily supposes that all operators are bounded and that S_0 is compact, and defers the removal of both restrictions to the Appendix to Section 6.
  - Counted result support: none
  - Boundary rationale: A temporary proof-technical restriction inside the Section 6 argument, not a hypothesis of the printed Section 2 theorem. It is part of the inherited proof context under which the printed tangent statement is actually settled.
  - Nonlocal interpretation support for `S2-tan-theta` (`proof_context_dependency`): Records that the printed statement is proved under successively relaxed working assumptions supplied outside Section 2.
- `DK-6.3-thm.ambient-wholeSpace-assembly` — **proof-claim / proof_or_derivation_not_result** — The ambient conclusion is assembled from the directed one: tan Theta has the two-corner block form built from J_0, tan Theta_0 and tan Theta_1, the two corners have equal unitarily invariant norms through J_0, and Lemmas 6.1 and 6.2 then give delta ||tan Theta|| <= ||H||.
  - Counted result support: none
  - Boundary rationale: The proof of the counted ambient conclusion rather than an additional printed result. It is recorded separately because it is the exact place where the Section 2 statement inherits the direct-rotation geometry available only under the later standing conditions.
  - Nonlocal interpretation support for `S2-tan-theta` (`proof_context_dependency`): The proof of the printed ambient conclusion runs in Section 6, where (3.5) has been standing since Section 3, and it uses the direct-rotation corner comparison rather than the Section 2 hypotheses alone.
- `DK-6.3-thm.example6-1` — **counterexample / remark_or_example_not_result** — Example 6.1 gives the explicit 2x2 counterexample showing one-sided placement is essential for the tangent conclusion.
  - Counted result support: none
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-6.3-thm.generalized-tangent-theorem` — **theorem / counted_result_statement** — Theorem 6.3 gives the generalized tangent residual bound with its exact source hypotheses.
  - Counted result support: `DK-6.3-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-6.3-thm.eq-6-2` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.2) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-3` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.3) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-4` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.4) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-5` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.5) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-6` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.6) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-6-appendix`

- `DK-6-appendix.unbounded-sine-extension` — **scope / expository_commentary_not_result** — The sine theorem extends to unbounded operators via bounded residual/common-domain hypotheses.
  - Counted result support: none
  - Boundary rationale: This atom is explanatory/source-scope commentary rather than a counted Davis--Kahan result statement.
- `DK-6-appendix.unbounded-tangent-extension` — **scope / counted_result_scope** — The Appendix states the tan theta theorem in the general ordered case A0 <= alpha and Lambda1 >= alpha + delta and explicitly allows both A0 and Lambda1 to be unbounded, while the residual used by the norm estimate remains bounded.
  - Counted result support: `S2-tan-theta`
  - Boundary rationale: This is an explicit source-scope extension of the counted Section 2 tan theta theorem. Full-scope formalization must therefore cover the case where the Ritz compression A0 itself is a genuinely unbounded self-adjoint operator, not merely an unbounded ambient operator with bounded compression.
- `DK-6-appendix.appendix-approximation-chain` — **proof-claim / proof_or_derivation_not_result** — Equations (6.7)--(6.11) form the approximation chain controlling singular directions and passing to all UI norms.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6-appendix.appendix-all-ui-limit` — **proof-claim / proof_or_derivation_not_result** — The epsilon-to-zero argument completes the bound-norm case and then all UI norms.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6-appendix.eq-6-7` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.7) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6-appendix.eq-6-8` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.8) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6-appendix.eq-6-9` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.9) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6-appendix.eq-6-10` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.10) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6-appendix.eq-6-11` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (6.11) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-6.3-lem`

- `DK-6.3-lem.approximation-number-leakage` — **lemma / counted_result_statement** — Lemma 6.3 controls the approximation/singular-number leakage used in the Appendix, including the stated finite and real forms.
  - Counted result support: `DK-6.3-lem`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
### `DK-7-sin2-proof`

- `DK-7-sin2-proof.reflection-setup` — **proof-claim / proof_or_derivation_not_result** — The reflection construction converts the double-angle geometry into a single-angle comparison.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-7-sin2-proof.ambient-sin2` — **theorem / restatement_of_counted_result** — The Section 7 proof derives the ambient sin2Theta perturbation estimate.
  - Counted result support: none
  - Boundary rationale: This passage rederives, reapplies, or restates a result already counted at its source theorem statement. It is retained for source fidelity and is not counted a second time.
- `DK-7-sin2-proof.directed-sin2` — **theorem / restatement_of_counted_result** — It separately derives the directed sin2Theta0 residual estimate.
  - Counted result support: none
  - Boundary rationale: This passage rederives, reapplies, or restates a result already counted at its source theorem statement. It is retained for source fidelity and is not counted a second time.
- `DK-7-sin2-proof.factor-one-directed-residual-refinement` — **proof-claim / proof_or_derivation_not_result** — The directed block residual estimate has the source factor-one intermediate bound before the headline factor 2 form.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-7-sin2-proof.swap-asymmetry` — **scope / expository_commentary_not_result** — The source records the asymmetry involved in swapping the two operators/subspaces in the residual form.
  - Counted result support: none
  - Boundary rationale: This atom is explanatory/source-scope commentary rather than a counted Davis--Kahan result statement.
- `DK-7-sin2-proof.eq-7-1` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (7.1) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-7-sin2-proof.eq-7-2` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (7.2) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-7-sin2-proof.eq-7-3` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (7.3) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-7-sin2-proof.eq-7-4` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (7.4) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-7-sin2-proof.eq-7-5` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (7.5) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-7-tan2-proof`

- `DK-7-tan2-proof.tan2-block-identity` — **proof-claim / proof_or_derivation_not_result** — Equation (7.6) gives the decisive tangent double-angle block identity.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-7-tan2-proof.cos2-pole-exclusion` — **proof-claim / proof_or_derivation_not_result** — The singular-vector argument proves the relevant cos(2 theta_j) factors do not vanish from the source hypotheses.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-7-tan2-proof.ambient-tan2` — **theorem / restatement_of_counted_result** — The proof yields the ambient tan2Theta perturbation estimate.
  - Counted result support: none
  - Boundary rationale: This passage rederives, reapplies, or restates a result already counted at its source theorem statement. It is retained for source fidelity and is not counted a second time.
- `DK-7-tan2-proof.directed-tan2` — **theorem / restatement_of_counted_result** — The proof yields the directed tan2Theta0 residual estimate.
  - Counted result support: none
  - Boundary rationale: This passage rederives, reapplies, or restates a result already counted at its source theorem statement. It is retained for source fidelity and is not counted a second time.
- `DK-7-tan2-proof.eq-7-6` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (7.6) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-8.1-thm`

- `DK-8.1-thm.branch-problem` — **scope / pre_result_motivation_not_result** — Small double-angle trigonometric quantities alone do not select angles near zero; the chosen reducing subspace matters.
  - Counted result support: none
  - Boundary rationale: This atom motivates the following counted result but is outside its printed statement.
- `DK-8.1-thm.acute-iff-spectral-placement` — **theorem / counted_result_statement** — Theta<=pi/4 iff the chosen perturbed reducing blocks lie on the corresponding sides of the gap.
  - Counted result support: `DK-8.1-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-8.1-thm.existence-correct-q` — **theorem / counted_result_statement** — A reducing spectral projector Q with the required placement exists and is unique in the stated sense.
  - Counted result support: `DK-8.1-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-8.1-thm.part-i-compression` — **theorem / counted_result_statement** — The upper/lower block compression inequalities of part (i).
  - Counted result support: `DK-8.1-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-8.1-thm.part-ii-eigenvalue` — **theorem / counted_result_statement** — The finite-dimensional eigenvalue displacement inequalities of part (ii), with natural infinite-dimensional extensions.
  - Counted result support: `DK-8.1-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-8.1-thm.part-iii-gauge` — **theorem / counted_result_statement** — The symmetric-gauge majorization inequalities of part (iii).
  - Counted result support: `DK-8.1-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-8.1-thm.exclude-pi-over-four` — **proof-claim / proof_or_derivation_not_result** — Equations (8.1)--(8.2) exclude theta=pi/4 and then theta>pi/4 under the selected placement.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.1-thm.spectral-repulsion-interpretation` — **consequence / post_result_interpretation_not_result** — Strong off-diagonal eigenvector rotation forces definite eigenvalue displacement as described.
  - Counted result support: none
  - Boundary rationale: This atom interprets a counted result after its statement/proof; it is not an additional result obligation.
- `DK-8.1-thm.eq-8-1` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (8.1) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.1-thm.eq-8-2` — **numbered-equation / proof_or_derivation_not_result** — Exact mathematical content of source equation (8.2) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
### `DK-8.2-thm`

- `DK-8.2-thm.smallness-alternative` — **hypothesis / counted_result_hypothesis** — The theorem assumes either ||H||_1<delta/2 or ||R||_1<delta/2 plus the stated A0 interval.
  - Counted result support: `DK-8.2-thm`
  - Boundary rationale: This atom is a printed hypothesis of a counted Davis--Kahan result and is part of the exact statement boundary that Lean must match.
- `DK-8.2-thm.double-angle-bound-retained` — **theorem / counted_result_statement** — The corresponding sin2 double-angle estimate remains valid.
  - Counted result support: `DK-8.2-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-8.2-thm.acute-branch-conclusion` — **theorem / counted_result_statement** — Theta<pi/4.
  - Counted result support: `DK-8.2-thm`
  - Boundary rationale: This atom is part of the printed statement/conclusion of a counted Davis--Kahan result and supports that result in the 29-result denominator.
- `DK-8.2-thm.homotopy-proof` — **proof-claim / proof_or_derivation_not_result** — The perturbation proof uses the continuous spectral-projector homotopy and the displayed arcsine bound.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.2-thm.residual-reduction` — **proof-claim / proof_or_derivation_not_result** — The residual form is reduced by changing the complementary perturbation block while preserving the residual/spectral data.
  - Counted result support: none
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.2-thm.sin2-unequal-dimension-extension` — **scope / post_result_scope_remark_not_in_printed_statement** — The source states a sin2 extension to unequal comparison dimensions.
  - Counted result support: none
  - Boundary rationale: This atom is a scope/extension remark stated after the named result, not part of the printed result environment; it is retained for fidelity without enlarging the result denominator.
- `DK-8.2-thm.no-tan2-unequal-dimension-extension-known` — **knowledge-state / historical_knowledge_state** — No analogous tan2 extension was known.
  - Counted result support: none
  - Boundary rationale: This atom records the paper's historical knowledge state rather than a Davis--Kahan result established in the paper.
### `DK-9-model`

- `DK-9-model.real-l2-model` — **definition / definition_not_result** — The numerical model is real L2(0,1) with the free-end fourth-derivative self-adjoint closure and multiplication perturbation epsilon t.
  - Counted result support: none
  - Boundary rationale: This atom is definitional/setup material. It is retained for source fidelity and notation, but definitions are not counted Davis--Kahan result obligations.
- `DK-9-model.perturbed-eigenproblem` — **definition / definition_not_result** — The displayed fourth-order perturbed boundary-value eigenproblem.
  - Counted result support: none
  - Boundary rationale: This atom is definitional/setup material. It is retained for source fidelity and notation, but definitions are not counted Davis--Kahan result obligations.
- `DK-9-model.unperturbed-strict-eigenvalue-order` — **assertion / section9_worked_example_not_result** — The source orders alpha1=0=alpha2<alpha3<alpha4<... with multiplicity.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-model.positive-root-equation` — **assertion / section9_worked_example_not_result** — For k>2, alpha_k are the positive roots of cos(alpha_k^(1/4)) cosh(alpha_k^(1/4))=1.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-model.positive-spectrum-over-500` — **assertion / section9_worked_example_not_result** — All positive alpha_k exceed 500.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-model.zero-eigenfunctions` — **construction / section9_worked_example_not_result** — The displayed w1,w2 are orthonormal linear eigenfunctions for the zero eigenvalue.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-model.lambda3-lower-bound` — **assertion / section9_worked_example_not_result** — H>=0 implies lambda3>=alpha3>500.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-model.initial-residual-formula` — **identity / section9_worked_example_not_result** — For A0=0, R=HE0 with the displayed residual functions r_k.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-model.residual-gram` — **identity / section9_worked_example_not_result** — The displayed 2x2 R*R matrix.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-model.residual-gram-eigenvalues` — **assertion / section9_worked_example_not_result** — R*R has eigenvalues epsilon^2(11+-sqrt76)/30.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
### `DK-9.1-9.4`

- `DK-9.1-9.4.sin-bound-comparison` — **consequence / section9_worked_example_not_result** — The paper notes (9.1) is sharper than the easy sin2 bound (9.2).
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.1-9.4.kyfan-two-term-scope` — **scope / section9_worked_example_not_result** — Equations (9.3)--(9.4) use the two-term Ky Fan norm to estimate both principal angles simultaneously.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.1-9.4.eq-9-1` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.1) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.1-9.4.eq-9-2` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.2) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.1-9.4.eq-9-3` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.3) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.1-9.4.eq-9-4` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.4) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
### `DK-9.5-9.7`

- `DK-9.5-9.7.rayleigh-ritz-matrix` — **identity / section9_worked_example_not_result** — The displayed Rayleigh--Ritz matrix is E0*(A+H)E0.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.5-9.7.refined-residual-gram` — **identity / section9_worked_example_not_result** — The displayed refined residual Gram matrix and its one/two-term norm equal epsilon/sqrt15.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.5-9.7.tangent-gap` — **assertion / section9_worked_example_not_result** — The tangent gap may be taken as 500-0.7887 epsilon.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.5-9.7.kyfan-tan-bound` — **consequence / section9_worked_example_not_result** — The same RHS as (9.6) bounds tan theta1+tan theta2 in the two-term Ky Fan norm.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.5-9.7.offdiagonal-complement-choice` — **construction / section9_worked_example_not_result** — For tan2 the complementary block is chosen as E1*(A+H)E1>500 to obtain an off-diagonal comparison.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.5-9.7.kyfan-tan2-bound` — **consequence / section9_worked_example_not_result** — The same RHS as (9.7) bounds tan2theta1+tan2theta2 in the two-term Ky Fan norm.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.5-9.7.eq-9-5` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.5) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.5-9.7.eq-9-6` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.6) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.5-9.7.eq-9-7` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.7) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
### `DK-9.8`

- `DK-9.8.weinberger-sine-square` — **external-result / external_result_not_dk_result** — Weinberger method gives the displayed sine-square estimate from Ritz upper/lower bounds and the 500 separation.
  - Counted result support: none
  - Boundary rationale: This atom records a result or comparison attributed to other work/methods rather than a Davis--Kahan result established as part of the project denominator.
- `DK-9.8.lehmann-best-lower-bounds` — **external-result / external_result_not_dk_result** — The best lower bounds deducible from the stated 2+1 data are the two lower eigenvalues of the displayed 3x3 matrix.
  - Counted result support: none
  - Boundary rationale: This atom records a result or comparison attributed to other work/methods rather than a Davis--Kahan result established as part of the project denominator.
- `DK-9.8.lower-bound-asymptotic` — **external-result / external_result_not_dk_result** — The source records the strict inequality and O(epsilon^4) asymptotic for alpha_hat-alpha_check.
  - Counted result support: none
  - Boundary rationale: This atom records a result or comparison attributed to other work/methods rather than a Davis--Kahan result established as part of the project denominator.
- `DK-9.8.angle-meaning-distinction` — **assertion / section9_worked_example_not_result** — phi_k are individual trial-vector-to-subspace angles whereas theta1 is the largest subspace angle.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.8.sine-square-sum-identity` — **identity / section9_worked_example_not_result** — sin^2 phi1+sin^2 phi2 = sin^2 theta1+sin^2 theta2.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.8.direct-one-vector-sharper-bounds` — **consequence / section9_worked_example_not_result** — Theorem 6.3 applied to each trial vector gives the displayed sharper tan phi_k bounds.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.8.methods-complementary` — **assertion / section9_worked_example_not_result** — The source concludes the two methods are complementary rather than one supplanting the other.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.8.eq-9-8` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.8) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
### `DK-9-infinite-residual-counterexample`

- `DK-9-infinite-residual-counterexample.l2-geometric-vector-example` — **counterexample / section9_worked_example_not_result** — The geometric sequence e and diagonal operator give a trial vector just outside the operator domain.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-infinite-residual-counterexample.arbitrarily-small-domain-repair` — **assertion / section9_worked_example_not_result** — The source asserts an arbitrarily small modification repairs the domain defect.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-infinite-residual-counterexample.rayleigh-quotient` — **identity / section9_worked_example_not_result** — The formal Rayleigh quotient is 1+mu.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-infinite-residual-counterexample.residual-infinite` — **counterexample / section9_worked_example_not_result** — The residual has infinite norm so the paper residual theorems give no estimate.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-infinite-residual-counterexample.weinberger-still-applies` — **consequence / section9_worked_example_not_result** — Independent lower eigenvalue bounds still allow the displayed Weinberger estimate.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9-infinite-residual-counterexample.best-lower-bound-result` — **consequence / section9_worked_example_not_result** — At the best lower bounds the true sin theta=mu satisfies mu<=mu/sqrt(1-mu).
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
### `DK-9.9-9.11`

- `DK-9.9-9.11.angle-factorization` — **identity / section9_worked_example_not_result** — cos omega_k=cos eta_k cos psi_k and omega_k^2<=psi_k^2+eta_k^2.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.9-9.11.schur-correction-bound` — **assertion / section9_worked_example_not_result** — The Schur correction is bounded by the displayed off-diagonal 2x2 matrix and operator inequalities.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.9-9.11.tan2-psi-bound` — **consequence / section9_worked_example_not_result** — The tan2 theorem yields the displayed bound for psi_k.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.9-9.11.acute-psi-selection` — **consequence / section9_worked_example_not_result** — Theorem 8.1 selects 0<=psi_k<pi/4 and yields the stated arctan bound.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.9-9.11.eta-bound` — **consequence / section9_worked_example_not_result** — Equation (9.10) yields the displayed tan eta_k bound.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.9-9.11.final-omega-bounds` — **consequence / section9_worked_example_not_result** — Combining psi_k and eta_k yields the two final omega_k bounds.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.9-9.11.best-possible-3x3-claim` — **source-assertion / deferred_unproved_claim** — The source says the best possible bound from the stated data is the coordinate/eigenvector angle of the 3x3 comparison matrix.
  - Counted result support: none
  - Boundary rationale: The paper states this claim but explicitly leaves its proof unresolved or defers it to an open question. By project policy it is fidelity material, not a completion obligation.
- `DK-9.9-9.11.best-possible-proof-deferred` — **knowledge-state / deferred_unproved_claim** — Proof of that best-possible assertion is deferred to the unresolved three-way-subspace Question 10.2.
  - Counted result support: none
  - Boundary rationale: The paper states this claim but explicitly leaves its proof unresolved or defers it to an open question. By project policy it is fidelity material, not a completion obligation.
- `DK-9.9-9.11.eq-9-9` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.9) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.9-9.11.eq-9-10` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.10) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
- `DK-9.9-9.11.eq-9-11` — **numbered-equation / section9_worked_example_not_result** — Exact mathematical content of source equation (9.11) as reconstructed in the distributable TeX.
  - Counted result support: none
  - Boundary rationale: This atom belongs to Section 9's worked numerical example/application. The section is fully inventoried for fidelity, but it is not a named/headline Davis--Kahan result in the 29-result denominator.
### `DK-10.1`

- `DK-10.1.question` — **open-question / open_question** — With only pairwise spectral distance delta, how sharply can Theta0 be bounded in terms of R?
  - Counted result support: none
  - Boundary rationale: The paper explicitly leaves this as an open question; it is inventoried but is not a formalization obligation.
### `DK-10.2`

- `DK-10.2.three-way-setup` — **definition / definition_not_result** — Three-way orthogonal decompositions are encoded by the 3x3 block matrix E_i*F_j.
  - Counted result support: none
  - Boundary rationale: This atom is definitional/setup material. It is retained for source fidelity and notation, but definitions are not counted Davis--Kahan result obligations.
- `DK-10.2.question` — **open-question / open_question** — Can nearby reducing three-way decompositions be estimated through off-diagonal blocks analogously to the two-way theory?
  - Counted result support: none
  - Boundary rationale: The paper explicitly leaves this as an open question; it is inventoried but is not a formalization obligation.
### `DK-10.3`

- `DK-10.3.question` — **open-question / open_question** — Find best possible bounds combining eigenvalue and eigenvector changes.
  - Counted result support: none
  - Boundary rationale: The paper explicitly leaves this as an open question; it is inventoried but is not a formalization obligation.
### `DK-10.4`

- `DK-10.4.spectral-functional-calculus` — **definition / definition_not_result** — The source recalls f(A) from the spectral resolution of self-adjoint A.
  - Counted result support: none
  - Boundary rationale: This atom is definitional/setup material. It is retained for source fidelity and notation, but definitions are not counted Davis--Kahan result obligations.
- `DK-10.4.step-function-specialization` — **construction / section10_motivation_not_result** — For the gap step function under tan2 hypotheses, f(A)=P, f(A+H)=Q, f(A0)=I.
  - Counted result support: none
  - Boundary rationale: This atom occurs in Section 10 as motivating/special-case mathematics surrounding an open question, not as a new counted Davis--Kahan result.
- `DK-10.4.ambient-functional-change` — **identity / section10_motivation_not_result** — ||f(A+H)-f(A)||=||Q-P||=||sin Theta||.
  - Counted result support: none
  - Boundary rationale: This atom occurs in Section 10 as motivating/special-case mathematics surrounding an open question, not as a new counted Davis--Kahan result.
- `DK-10.4.ambient-tan2-bound` — **theorem / restatement_of_counted_result** — delta||tan 2Theta||<=2||H||.
  - Counted result support: none
  - Boundary rationale: This passage rederives, reapplies, or restates a result already counted at its source theorem statement. It is retained for source fidelity and is not counted a second time.
- `DK-10.4.directed-functional-change` — **identity / section10_motivation_not_result** — ||(f(A+H)-f(A))E0||=||Qperp E0||=||sin Theta0||.
  - Counted result support: none
  - Boundary rationale: This atom occurs in Section 10 as motivating/special-case mathematics surrounding an open question, not as a new counted Davis--Kahan result.
- `DK-10.4.directed-tan2-bound` — **theorem / restatement_of_counted_result** — delta||tan 2Theta0||<=2||R||.
  - Counted result support: none
  - Boundary rationale: This passage rederives, reapplies, or restates a result already counted at its source theorem statement. It is retained for source fidelity and is not counted a second time.
- `DK-10.4.question` — **open-question / open_question** — Seek analogous perturbation bounds for more general functions f.
  - Counted result support: none
  - Boundary rationale: The paper explicitly leaves this as an open question; it is inventoried but is not a formalization obligation.
