# Davis--Kahan 1970 independent result audit packet

## Claim boundary presented to the reviewer

The repository does **not** claim that every mathematical sentence, proof equation, worked example, historical comparison, or open question in the paper is separately formalized as a Lean theorem. It claims exact formal coverage of every result that Davis and Kahan actually establish in the paper.

The two accounting layers are deliberately both visible:

- **Source fidelity:** `dev/davis-kahan-1970-source-atom-inventory.json` contains **266 atoms** in paper order, including all **64 numbered equations**. Every atom has an explicit result-boundary reason code and names any counted result(s) it supports.
- **Formalization denominator:** `dev/davis-kahan-1970-formalization-result-inventory.json` contains exactly **29 counted results**: the four Section 2 headline theorems plus every named theorem, proposition, lemma, and corollary Davis--Kahan actually establish.
- Section 10 questions, explicitly deferred/unproved claims, definitions, proof-only derivations, examples, numerical working, historical/external results, and theorem-adjacent remarks remain visible in source fidelity but do not enlarge the denominator.
- A false counted result remains in the denominator and requires exact formal refutation plus the repository's separate best-effort repair disposition.

Current result-level status: **28/29 terminal**, **1 awaiting semantic closure**.
Result-selection/boundary review: **accepted** under policy `dk_established_results_only`.

A hostile reviewer should challenge both layers independently: (1) whether the fidelity inventory omitted source material or misclassified an exclusion, and (2) whether each of the 29 counted result statements is represented exactly in Lean.

## Authoritative checked-in materials

- Distributable source specification: `prose/distilled_literature/DavisKahan1970_part_III.tex`
- Source-fidelity inventory: `dev/davis-kahan-1970-source-atom-inventory.json`
- Formalization-result inventory: `dev/davis-kahan-1970-formalization-result-inventory.json`
- Source census: `dev/davis-kahan-1970-full-source-census.json`
- Organizational statement map: `dev/davis-kahan-1970-statement-map.json`
- Compiler certificate: **not supplied**; theorem types below are placeholders.

## Result-level verdict vocabulary

Use one of: **PASS exact**, **PASS refuted + repair**, **FAIL boundary**, **FAIL scope**, **FAIL conclusion**, **FAIL missing clause**, **FAIL evidence**, or **UNCERTAIN**.

## 1. S2-sin-theta — Single-angle sine theorem

- **Counted result kind:** `unnumbered_theorem`
- **Exact source anchor:** Section 2, sin theta theorem
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `8e5e36e64c718f1cdb002dd3c5a191c8919fa22bad64020bdbf8f22adb6a3f72`

### Atoms inside the counted printed result

- `S2-sin-theta.ui-norm-scope` — **counted_result_scope** — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
- `S2-sin-theta.gap-hypothesis` — **counted_result_hypothesis** — The sine theorem uses interval/exterior separation, allowing the A0 and Lambda1 roles to be interchanged.
- `S2-sin-theta.directed-conclusion` — **counted_result_statement** — delta ||sin Theta0|| <= ||R||.
- `S2-unbounded-scope.infinite-dimensional-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply in infinite as well as finite dimension.
- `S2-unbounded-scope.arbitrary-ui-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply to arbitrary UI norms.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **counted_result_scope** *(shared/cross-block scope)* — The results extend to unbounded self-adjoint A under the stated domain condition.
- `S2-unbounded-scope.bounded-residual-needed` — **counted_result_scope** *(shared/cross-block scope)* — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **counted_result_scope** *(shared/cross-block scope)* — Gap intervals may be half-infinite and the remaining spectra unbounded.

### Same-block material explicitly outside the counted result

- `S2-sin-theta.family-distinctness` — **expository_commentary_not_result** — The four Section 2 theorem families are distinct rather than mere restatements.
  - Boundary rationale: This atom is explanatory/source-scope commentary rather than a counted Davis--Kahan result statement.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
The four Section~2 statements are distinct theorem families; the source does not present them as cosmetic reformulations of one another.  Every displayed norm in these theorem statements is an arbitrary unitary-invariant norm in the source sense.

Assume that for some interval $[\beta,\alpha]$ and $\delta>0$, either
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\cap(\beta-\delta,\alpha+\delta)=\varnothing,
\]
or the same condition with $A_0$ and $\Lambda_1$ interchanged.  Then, for every unitary-invariant norm,
\[
 \boxed{\delta\norm{\sin\Theta_0}\le\norm{R}.}
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.sinTheta`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:53`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTheta_real_exactPaper`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:98`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.generalizedSinTheta`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/GeneralSinTheta.lean:40`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.generalizedSinTheta_real_exactPaper`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:109`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 2. S2-tan-theta — Single-angle tangent theorem

- **Counted result kind:** `unnumbered_theorem`
- **Exact source anchor:** Section 2, tan theta theorem
- **Result disposition:** `pending_result_only_review`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `pending_result_only_review`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `c85f8a2839187dd9ae4d020608816821c3b1f30e401eb5e52d4cbce093e82b3c`

### Atoms inside the counted printed result

- `S2-sin-theta.ui-norm-scope` — **counted_result_scope** *(shared/cross-block scope)* — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
- `S2-tan-theta.ordered-gap-hypothesis` — **counted_result_hypothesis** — The tangent theorem assumes A0 below Lambda1 by delta.
- `S2-tan-theta.rayleigh-ritz-hypothesis` — **counted_result_hypothesis** — The tangent theorem assumes H0=0, equivalently the Rayleigh--Ritz block choice.
- `S2-tan-theta.directed-conclusion` — **counted_result_statement** — delta ||tan Theta0|| <= ||R||.
- `S2-tan-theta.ambient-conclusion` — **counted_result_statement** — delta ||tan Theta|| <= ||H||.
- `S2-unbounded-scope.infinite-dimensional-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply in infinite as well as finite dimension.
- `S2-unbounded-scope.arbitrary-ui-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply to arbitrary UI norms.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **counted_result_scope** *(shared/cross-block scope)* — The results extend to unbounded self-adjoint A under the stated domain condition.
- `S2-unbounded-scope.bounded-residual-needed` — **counted_result_scope** *(shared/cross-block scope)* — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **counted_result_scope** *(shared/cross-block scope)* — Gap intervals may be half-infinite and the remaining spectra unbounded.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assume
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\subset[\alpha+\delta,\infty),
 \qquad \delta>0,
\]
and impose the Rayleigh--Ritz/off-diagonal condition $H_0=0$ (equivalently $A_0=E_0^*(A+H)E_0$ in this setup).  Then for every unitary-invariant norm both conclusions hold:
\[
 \boxed{\delta\norm{\tan\Theta_0}\le\norm{R}},
 \qquad
 \boxed{\delta\norm{\tan\Theta}\le\norm{H}}.
\]
The first is directed and residual-based; the second uses the ambient angle and the full perturbation.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/PartIII.lean:119`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Section2.theorem6_3_perturbation_infiniteTrial`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section2TanThetaPerturbation.lean:175`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1186`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:210`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_wholeSpace_paperUINorm_of_crossedDefectsEquivalent`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:320`, `DavisKahan/Sources/DavisKahan1970/TanThetaWholeSpace.lean:1275`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_unbounded_ambient_paperUINorm_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanThetaUnboundedAmbient.lean:268`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 3. S2-sin-two-theta — Double-angle sine theorem

- **Counted result kind:** `unnumbered_theorem`
- **Exact source anchor:** Section 2, sin 2 theta theorem
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `7da711fdbd912b64b5aa6f2efc5c4255bcbe796831a18b99c92712024b81c70b`

### Atoms inside the counted printed result

- `S2-sin-theta.ui-norm-scope` — **counted_result_scope** *(shared/cross-block scope)* — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
- `S2-sin-two-theta.gap-hypothesis` — **counted_result_hypothesis** — The double-sine theorem separates Lambda0 from Lambda1 by an interval/exterior gap.
- `S2-sin-two-theta.directed-conclusion` — **counted_result_statement** — delta ||sin(2 Theta0)|| <= 2||R||.
- `S2-sin-two-theta.ambient-conclusion` — **counted_result_statement** — delta ||sin(2 Theta)|| <= 2||H||.
- `S2-unbounded-scope.infinite-dimensional-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply in infinite as well as finite dimension.
- `S2-unbounded-scope.arbitrary-ui-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply to arbitrary UI norms.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **counted_result_scope** *(shared/cross-block scope)* — The results extend to unbounded self-adjoint A under the stated domain condition.
- `S2-unbounded-scope.bounded-residual-needed` — **counted_result_scope** *(shared/cross-block scope)* — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **counted_result_scope** *(shared/cross-block scope)* — Gap intervals may be half-infinite and the remaining spectra unbounded.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assume that for some $[\beta,\alpha]$ and $\delta>0$,
\[
 \spec(\Lambda_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\cap(\beta-\delta,\alpha+\delta)=\varnothing.
\]
Then for every unitary-invariant norm,
\[
 \boxed{\delta\norm{\sin(2\Theta_0)}\le2\norm{R}},
 \qquad
 \boxed{\delta\norm{\sin(2\Theta)}\le2\norm{H}}.
\]
Again the source distinguishes the directed residual statement from the ambient perturbation statement.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:390`, `DavisKahan/Sources/DavisKahan1970/SinTwoThetaWholeSpace.lean:723`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.sinTwoTheta_wholeSpace_paperUINorm_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:252`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:166`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:254`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_uiNorm_representative_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:344`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.unbounded_sinTwoTheta_residual_uiNorm_representative_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/SinTwoTheta.lean:404`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 4. S2-tan-two-theta — Double-angle tangent theorem

- **Counted result kind:** `unnumbered_theorem`
- **Exact source anchor:** Section 2, tan 2 theta theorem
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `5c5b96c1cc563a42d13b8b4e06989c19ff82ec8ed6958f3da78d67dc9b2b7830`

### Atoms inside the counted printed result

- `S2-sin-theta.ui-norm-scope` — **counted_result_scope** *(shared/cross-block scope)* — Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm.
- `S2-tan-two-theta.ordered-gap-hypothesis` — **counted_result_hypothesis** — The double-tangent theorem assumes A0 below A1 by delta.
- `S2-tan-two-theta.strong-offdiagonal-hypothesis` — **counted_result_hypothesis** — The double-tangent theorem assumes H0=H1=0.
- `S2-tan-two-theta.no-extra-pole-hypothesis` — **counted_result_scope** — The printed theorem has no independent tan-pole exclusion or perturbed-block spectral-placement hypothesis.
- `S2-tan-two-theta.directed-conclusion` — **counted_result_statement** — delta ||tan(2 Theta0)|| <= 2||R||.
- `S2-tan-two-theta.ambient-conclusion` — **counted_result_statement** — delta ||tan(2 Theta)|| <= 2||H||.
- `S2-unbounded-scope.infinite-dimensional-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply in infinite as well as finite dimension.
- `S2-unbounded-scope.arbitrary-ui-scope` — **counted_result_scope** *(shared/cross-block scope)* — All four main results apply to arbitrary UI norms.
- `S2-unbounded-scope.unbounded-selfadjoint-scope` — **counted_result_scope** *(shared/cross-block scope)* — The results extend to unbounded self-adjoint A under the stated domain condition.
- `S2-unbounded-scope.bounded-residual-needed` — **counted_result_scope** *(shared/cross-block scope)* — Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly.
- `S2-unbounded-scope.half-infinite-gap-intervals` — **counted_result_scope** *(shared/cross-block scope)* — Gap intervals may be half-infinite and the remaining spectra unbounded.

### Same-block material explicitly outside the counted result

- `S2-tan-two-theta.pole-exclusion-derived` — **proof_or_derivation_not_result** — Section 7 derives the needed nonvanishing cosine factors from the printed hypotheses.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assume the ordered gap
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(A_1)\subset[\alpha+\delta,\infty),
 \qquad \delta>0,
\]
and the strong off-diagonal hypothesis
\[
 H_0=H_1=0.
\]
No independent hypothesis excluding the poles of $\tan(2\Theta)$, and no spectral placement hypothesis on the perturbed $Q$-blocks $\Lambda_0,\Lambda_1$, is part of the printed theorem.  For every unitary-invariant norm the two conclusions are
\[
 \boxed{\delta\norm{\tan(2\Theta_0)}\le2\norm{R}},
 \qquad
 \boxed{\delta\norm{\tan(2\Theta)}\le2\norm{H}}.
\]
Section~7 derives the nonvanishing of the relevant $\cos(2\theta_j)$ factors from these hypotheses during the proof rather than assuming it.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_exact`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:441`, `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1160`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_directedCorner_residual_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:362`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_exact`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:531`, `DavisKahan/Sources/DavisKahan1970/TanTwoThetaReflectionAmbient.lean:1297`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_wholeSpace_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/WholeSpaceReal.lean:433`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExact.lean:77`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_directedResidual_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:194`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedAmbientExact.lean:258`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTwoTheta_unbounded_ambient_paperUINorm_real_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedExactReal.lean:342`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 5. DK-3.1-prop — Acute direct rotation existence and uniqueness

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `ff945cb6247987becf0eec9e3c5fd945ba2df2d2b8756cea6df2c7ebd00213d4`

### Atoms inside the counted printed result

- `DK-3.1-prop.existence` — **counted_result_statement** — In the acute case a direct rotation exists.
- `DK-3.1-prop.uniqueness` — **counted_result_statement** — In the acute case the direct rotation is unique.
- `DK-3.1-prop.positive-diagonal-characterization` — **counted_result_statement** — Positivity of C0,C1 characterizes the direct rotation among unitary intertwiners in the acute case.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
In the acute case, a direct rotation exists and is unique.  Moreover positivity of the diagonal blocks, $C_0,C_1\ge0$, already characterizes it among unitaries carrying $P\Hsp$ onto $Q\Hsp$: the polar-decomposition relations force the off-diagonal condition $S_1=S_0^*$ because the relevant kernels vanish in the acute case.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.proposition3_1_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3AcuteDirectRotation.lean:169`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 6. DK-3.2-prop — Nonacute existence criterion

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `3824155c8b919c0b61e9eb7bdc7b822214fbb6d6abfa95f7e7eb5eac2a73c09a`

### Atoms inside the counted printed result

- `DK-3.2-prop.existence-iff-crossing-dimensions` — **counted_result_statement** — Outside the acute case, direct rotation existence is equivalent to equality of the crossing dimensions.
- `DK-3.2-prop.nonuniqueness` — **counted_result_statement** — When it exists outside the acute case it need not be unique.
- `DK-3.2-prop.eq-3-5` — **counted_result_statement** — Exact mathematical content of source equation (3.5) as reconstructed in the distributable TeX.

### Same-block material explicitly outside the counted result

- `DK-3.2-prop.crossing-square-minus-one` — **proof_detail_not_in_printed_statement** — On the crossing subspaces U^2 x=-x.
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
- `DK-3.2-prop.bilateral-shift-counterexample` — **remark_or_example_not_result** — The bilateral-shift example shows the basic P/Q dimension conditions do not imply the crossing-dimension condition.
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Outside the acute case a direct rotation exists iff the two crossing subspaces have the same dimension:
\begin{equation}
 \dim(P\Hsp\cap Q^\perp\Hsp)
 =\dim(P^\perp\Hsp\cap Q\Hsp).
 \tag{3.5}
\end{equation}
When it exists it need not be unique.  On the two crossing subspaces a direct rotation satisfies $U^2x=-x$.  The source also gives an infinite-dimensional bilateral-shift example showing that the equal-dimension conditions (1.5) for $P,Q$ do not by themselves imply (3.5).
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2038`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_not_unique`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2092`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_exists_iff_crossedDefectsEquivalent_real`

Source location candidates: `DavisKahan/Frontier/Section3.lean:3330`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_2_not_unique_real`

Source location candidates: `DavisKahan/Frontier/Section3.lean:3354`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 7. DK-3.3-prop — Principal square-root characterization

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.3
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `dbc77fc4c71873dbd8c706d68f5bb4ea28064a4d930ccb58c91c2640ab7bf382`

### Atoms inside the counted printed result

- `DK-3.3-prop.principal-square-root` — **counted_result_statement** — Every direct rotation is the principal unitary square root of the product of the two reflections.
- `DK-3.3-prop.square-root-converse` — **counted_result_statement** — A principal square root is a direct rotation when it maps the two crossing subspaces appropriately.

### Same-block material explicitly outside the counted result

- `DK-3.3-prop.reflection-conjugacy` — **pre_result_setup_not_in_printed_statement** — With X=P-Pperp and Q_-=XQX, U^{-1}=XUX.
  - Boundary rationale: This atom appears immediately before the named result as setup, identity, or motivation; it is outside the printed theorem/proposition statement.
- `DK-3.3-prop.eq-3-6` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (3.6) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-3.3-prop.eq-3-7` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (3.7) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-3.3-prop.eq-3-8` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (3.8) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assuming both the matching-dimension condition (1.5) and the crossing-dimension condition (3.5), write the direct rotation as
\begin{equation}
 U\sim\begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix},
 \qquad C_j\ge0.
 \tag{3.6}
\end{equation}
The corresponding projector has the block representation
\begin{equation}
 Q=UPU^{-1}
 \sim
 \binom{C_0}{S_0}(C_0\ \ S_0^*)
 =\begin{pmatrix}
 C_0^2&C_0S_0^*\\
 S_0C_0&S_0S_0^*
 \end{pmatrix}.
 \tag{3.7}
\end{equation}
With the reflection $X=P-P^\perp$ and $Q_-=XQX$ one has $U^{-1}=XUX$.  In particular,
\begin{equation}
 U^2=(Q-Q^\perp)(P-P^\perp).
 \tag{3.8}
\end{equation}
Every direct rotation is therefore the principal unitary square root of $(Q-Q^\perp)(P-P^\perp)$, with spectrum in the closed right half-plane.  Conversely, a principal square root of that product is a direct rotation provided it sends $P\Hsp\cap Q^\perp\Hsp$ onto $P^\perp\Hsp\cap Q\Hsp$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.proposition3_3_complex_forward_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean:112`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_3_complex_converse_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean:135`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_3_real_forward_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean:257`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_3_real_converse_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean:299`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 8. DK-3.4-prop — Square as a direct rotation

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.4
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `a4914037fecd9b2f6193105f137f3a59d160e47ca70747bb4a6c430477038990`

### Atoms inside the counted printed result

- `DK-3.4-prop.u-square-direct-rotation` — **counted_result_statement** — If C0^2>=1/2, then U^2 is the direct rotation from Q_- to Q.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Under the same direct-rotation setup, if
\[
 C_0^2\ge\tfrac12
\]
(equivalently, the relevant principal angles do not exceed $\pi/4$), then $U^2$ is itself the direct rotation carrying $Q_-\Hsp$ onto $Q\Hsp$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_full`

Source location candidates: `DavisKahan/Frontier/Section3.lean:1830`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.proposition3_4_source_eq_directRotation`

Source location candidates: `DavisKahan/Frontier/Section3.lean:1981`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_4_source_full_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition34Real.lean:188`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 9. DK-3.1-thm — Classification of pairs of subspaces

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 3.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `c596c36a00cab2889d9af204a420d6746d77273cc66e9a3268dc91891902987f`

### Atoms inside the counted printed result

- `DK-3.1-thm.complete-invariant` — **counted_result_statement** — Spectral multiplicity functions of Theta0,Theta1 completely classify the pair under the stated dimension hypotheses.
- `DK-3.1-thm.converse-angle-data` — **counted_result_statement** — Conversely the angle operators may be arbitrary positive contractions in [0,pi/2] with matching spectral multiplicities away from zero and the stated dimensions.

### Same-block material explicitly outside the counted result

- `DK-3.1-thm.reconstruction` — **proof_detail_not_in_printed_statement** — The pair is reconstructed from the angle data and J0.
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assume
\[
 \dim P\Hsp=\dim Q\Hsp,
 \qquad
 \dim(P\Hsp\cap Q^\perp\Hsp)=\dim(P^\perp\Hsp\cap Q\Hsp).
\]
A complete invariant of the pair $(P\Hsp,Q\Hsp)$ under isometric equivalence is given by the spectral multiplicity functions of $\Theta_0$ and $\Theta_1$.  Conversely, the angle operators may be arbitrary Hermitian operators satisfying
\[
 0\le\Theta_j\le\pi/2,
\]
their domain dimensions sum to $\dim\Hsp$, and their spectral multiplicity functions agree except possibly at the eigenvalue/spectral point $0$.  The proof reconstructs the pair from these angle data and the corresponding partial isometry $J_0$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2636`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_realization`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2722`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.theorem3_1_spectralMultiplicity_classification_real`

Source location candidates: `DavisKahan/Frontier/Section3Real.lean:132`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 10. DK-3.1-cor — Compact classification by angle eigenvalues

- **Counted result kind:** `corollary`
- **Exact source anchor:** Corollary 3.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `2661dd05c08e61c06c54ce50c66032413a3c958bb7cda1b28638548253e30d2c`

### Atoms inside the counted printed result

- `DK-3.1-cor.compact-complete-invariants` — **counted_result_statement** — If PQperpP is compact, the eigenvalues of Theta0,Theta1 counted with multiplicity are complete invariants.
- `DK-3.1-cor.allowed-angle-sequence` — **counted_result_statement** — Theta0 eigenvalues may be any decreasing sequence in [0,pi/2] tending to zero plus possible zero eigenspace.
- `DK-3.1-cor.theta1-match` — **counted_result_statement** — Theta1 has the same nonzero eigenvalues and may differ only in zero multiplicity.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Under the hypotheses of Theorem~3.1, if $PQ^\perp P$ is compact, the complete invariants reduce to the eigenvalues of $\Theta_0,\Theta_1$, counted with multiplicity.  The eigenvalues of $\Theta_0$ may be any sequence
\[
 \pi/2\ge\theta_1\ge\theta_2\ge\cdots\to0,
\]
together with a possible eigenvalue $0$; $\Theta_1$ has the same nonzero eigenvalues and may differ only in the multiplicity of $0$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_defectBlock_angleList_classification`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2464`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_compact_classification_real`

Source location candidates: `DavisKahan/Frontier/Section3.lean:3210`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.corollary3_1_realization`

Source location candidates: `DavisKahan/Frontier/Section3.lean:2895`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 11. DK-3.5-prop — Angle commutation and eigenspace geometry

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 3.5
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `bdabc4530ed8ad8040dfe34d4a1071b2b52d3563d3e0e5bb9de9868287999a4e`

### Atoms inside the counted printed result

- `DK-3.5-prop.commutation` — **counted_result_statement** — Theta commutes with P,Q,J,U.
- `DK-3.5-prop.eigenvector-rotation-angle` — **counted_result_statement** — If Theta x=theta x then angle(x,Ux)=theta.
- `DK-3.5-prop.acute-maximal-characterization` — **counted_result_statement** — In the acute case each theta-eigenspace is the unique maximal P/Q-reducing subspace with the stated constant-angle properties.

### Same-block material explicitly outside the counted result

- `DK-3.5-prop.direct-rotation-exponential` — **pre_result_setup_not_in_printed_statement** — U=exp(J Theta).
  - Boundary rationale: This atom appears immediately before the named result as setup, identity, or motivation; it is outside the printed theorem/proposition statement.
- `DK-3.5-prop.cos-square-projector` — **pre_result_setup_not_in_printed_statement** — cos^2 Theta=PQP+Pperp Qperp Pperp.
  - Boundary rationale: This atom appears immediately before the named result as setup, identity, or motivation; it is outside the printed theorem/proposition statement.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
The angle operator $\Theta$ commutes with $P,Q,J,$ and $U$, and the direct rotation has $U=e^{J\Theta}$.  The source also records
\[
 \cos^2\Theta=PQP+P^\perp Q^\perp P^\perp.
\]
If $\Theta x=\theta x$, then
\[
 \angle(x,Ux)=\theta.
\]
In the acute case the $\theta$-eigenspace of $\Theta$ is the unique maximal subspace which reduces both $P$ and $Q$ and on which every nonzero $x\in P\Hsp$ has angle $\theta$ from $Qx$, while every nonzero $x\in P^\perp\Hsp$ has angle $\theta$ from $Q^\perp x$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.proposition3_5_commutations`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:235`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_eigenvector_angle`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:249`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_eq_fixedCosineSubspace`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:257`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.proposition3_5_angleEigenspace_uniqueMaximal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:268`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 12. DK-3.2-cor — Reversal symmetry

- **Counted result kind:** `corollary`
- **Exact source anchor:** Corollary 3.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `6ef3d66483655d6bf428a2422d4d26494455fe9cba09939d61a2092809e68a9d`

### Atoms inside the counted printed result

- `DK-3.2-cor.swap-invariance` — **counted_result_statement** — Swapping P and Q leaves Theta unchanged and sends J to -J.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Interchanging the roles of $P$ and $Q$ leaves the angle operator $\Theta$ unchanged and replaces $J$ by $-J$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.corollary3_2_source`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:200`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.corollary3_2_paperQuarterTurn_symm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:170`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.corollary3_2_nonacute_directRotation_resolution`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section3Proposition35.lean:152`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.complex_directRotation_reversal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:132`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.real_directRotation_reversal`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:247`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section3.corollary3_2_reversal_source_form`

Source location candidates: `DavisKahan/Frontier/Section3.lean:1448`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 13. DK-4.1-prop — Pointwise and singular-value extremality of the direct rotation

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 4.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `2b3c6a4dc471284a2f9e4f7e4f091d30fd00d0c04ef03648ee469d6e9e110cb3`

### Atoms inside the counted printed result

- `DK-4.1-prop.orthonormal-angle-lower-bounds` — **counted_result_statement** — For every such V there are orthonormal v_k in P with angle(v_k,Vv_k)>=theta_k.
- `DK-4.1-prop.singular-value-minimality` — **counted_result_statement** — Each singular value of (1-V)|P is minimized at V=U with value 2 sin(theta_k/2).

### Same-block material explicitly outside the counted result

- `DK-4.1-prop.vz-factorization` — **section_setup_not_result** — Every unitary V carrying P to Q is written V=UZ with Z block diagonal in the Section 4 setup.
  - Boundary rationale: This atom is section-level setup used to formulate or prove later named results; it is not itself inside a counted result statement.
- `DK-4.1-prop.closest-q-vector-proof-step` — **proof_or_derivation_not_result** — The pointwise comparison uses Qx/||Qx|| as the closest unit vector in Q-space.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.1-prop.eq-4-1` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.1) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.1-prop.eq-4-2` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.2) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
This section is logically independent of the later perturbation proofs.  Under the compact/classification setup, every unitary carrying $P\Hsp$ onto $Q\Hsp$ is written $V=UZ$ with $Z$ block diagonal relative to $P\oplus P^\perp$, and the principal angles are ordered $\theta_1\ge\theta_2\ge\cdots$.

For any such unitary $V$, there are orthonormal vectors $v_k\in P\Hsp$ such that
\[
 \angle(v_k,Vv_k)\ge\theta_k\qquad\text{for every }k.
\]
Equivalently, if $\lambda_1\ge\lambda_2\ge\cdots$ are the singular values of $(1-V)|_{P\Hsp}$, then each $\lambda_k$ is minimized by the direct rotation $V=U$, with minimum
\[
 \lambda_k=2\sin(\theta_k/2).
\]
The singular values admit the minimax description
\begin{equation}
 \lambda_k
 =\inf_{\substack{\mathcal Y\subset P\Hsp\\\dim\mathcal Y=k-1}}
   \ \sup_{\substack{x\in P\Hsp\ominus\mathcal Y\\\norm{x}=1}}
   \norm{(1-V)x},
 \tag{4.1}
\end{equation}
and the proof selects a corresponding unit vector $x$ for which
\begin{equation}
 \angle(x,Vx)\ge\theta_k=\angle(u_k,Uu_k).
 \tag{4.2}
\end{equation}
The latter follows by comparing $Vx$ with the closest unit vector in $Q\Hsp$ and using the block formula (3.7).
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:310`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1255`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_directRotationValues`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:242`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_1_compact_nonacute_directRotationValues_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1177`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 14. DK-4.1-cor — UI-norm minimality of direct rotation displacement

- **Counted result kind:** `corollary`
- **Exact source anchor:** Corollary 4.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `73cd6caf9a976a811e4836d656d566a66b0f57c7504ff38365d6891b3d75b9ba`

### Atoms inside the counted printed result

- `DK-4.1-cor.ui-minimality-on-p` — **counted_result_statement** — For every UI norm, ||(1-V)P|| is minimized at V=U.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
For every unitary-invariant norm,
\[
 \norm{(1-V)P}
\]
is minimized among unitaries carrying $P\Hsp$ onto $Q\Hsp$ by the direct rotation $V=U$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:341`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Corollary4_1_compact_nonacute_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1282`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Corollary4_1_infiniteDimensional_nonacute`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:372`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 15. DK-4.2-prop — Basis-angle square-sum extremality

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 4.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `a1d36230f960f5b48427a6c4fce26c28327cc9fdff714575e4261c76ae92c4f4`

### Atoms inside the counted printed result

- `DK-4.2-prop.basis-sine-square-lower-bound` — **counted_result_statement** — For every orthonormal basis of P, sum sin^2 angle(v_k,Vv_k) >= sum sin^2 theta_k, including infinite RHS.

### Same-block material explicitly outside the counted result

- `DK-4.2-prop.trace-identification` — **proof_or_derivation_not_result** — The lower bound is identified with tr(S0* S0).
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
For every unitary $V$ carrying $P\Hsp$ onto $Q\Hsp$ and every orthonormal basis $\{v_k\}$ of $P\Hsp$,
\[
 \sum_{k=1}^{\infty}\sin^2\angle(v_k,Vv_k)
 \ge
 \sum_{k=1}^{\infty}\sin^2\theta_k,
\]
with the inequality also valid when the right-hand side is infinite.  The proof identifies the lower bound with $\operatorname{tr}(S_0^*S_0)$.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Proposition4_2_infiniteDimensional`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:395`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tsum_displacementAngleSineSqR_ge_tsum_sq_sin_principalAngleSequence`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:784`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 16. DK-4.3-prop — Squared displacement UI-norm minimality

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 4.3
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `efb61fbf15adb18ac47572bb82096f44ac2bd356072eaa15cd006cec8cc14dac`

### Atoms inside the counted printed result

- `DK-4.3-prop.squared-displacement-global-minimum` — **counted_result_statement** — ||(1-V*)(1-V)|| is minimized by U for every UI norm.

### Same-block material explicitly outside the counted result

- `DK-4.3-prop.plane-parameterization` — **proof_detail_not_in_printed_statement** — On each principal two-plane V has the displayed a_j,b_j parameterization.
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
- `DK-4.3-prop.operator-norm-displacement-minimum` — **post_result_consequence_not_in_printed_statement** — The operator norm of 1-V is minimized by U.
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
- `DK-4.3-prop.hilbert-schmidt-displacement-minimum` — **post_result_consequence_not_in_printed_statement** — The Hilbert--Schmidt norm of 1-V is minimized by U.
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
- `DK-4.3-prop.arbitrary-ui-displacement-warning` — **post_result_consequence_not_in_printed_statement** — Arbitrary UI norms of 1-V need not be minimized by U.
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.
- `DK-4.3-prop.eq-4-3` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.3) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.3-prop.eq-4-4` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.4) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.3-prop.eq-4-5` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.5) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-4.3-prop.eq-4-6` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (4.6) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
The source next studies the full operator $1-V$.  For the two-dimensional reducing planes $\Omega_k\Hsp=[u_k,Ju_k]$, its Ky Fan comparisons specialize to
\begin{equation}
\begin{aligned}
 \norm{K}_{\nu}&\ge\sum_{k=1}^{\nu/2}\norm{K\Omega_k}_2,
 &&\nu\text{ even},\\
 \norm{K}_{\nu}&\ge\sum_{k=1}^{\lfloor\nu/2\rfloor}\norm{K\Omega_k}_2
 +\norm{K\Omega_{(\nu+1)/2}}_1,
 &&\nu\text{ odd},
\end{aligned}
\tag{4.3}
\end{equation}
and, after compressing on both sides,
\begin{equation}
\begin{aligned}
 \norm{K}_{\nu}&\ge\sum_{k=1}^{\nu/2}\norm{\Omega_kK\Omega_k}_2,
 &&\nu\text{ even},\\
 \norm{K}_{\nu}&\ge\sum_{k=1}^{\lfloor\nu/2\rfloor}\norm{\Omega_kK\Omega_k}_2
 +\norm{\Omega_{(\nu+1)/2}K\Omega_{(\nu+1)/2}}_1,
 &&\nu\text{ odd}.
\end{aligned}
\tag{4.4}
\end{equation}
For one such plane write
\[
 Vu=a_0Uu+b_0w,
 \qquad
 VJu=a_1UJu+b_1x,
 \qquad |a_j|^2+|b_j|^2=1,
\]
with $w,x$ orthogonal to that plane in the appropriate $Q$ and $Q^\perp$ subspaces.  If $\mu_1\ge\mu_2$ are the singular values of $(1-V)\Omega$, and
\[
 a_0+a_1=2c+2ie,
 \qquad
 a_0-a_1=2d-2if,
\]
then
\begin{equation}
\begin{aligned}
 1-\mu_1^2/2&=c\cos\theta-\sqrt{d^2+e^2\sin^2\theta},\\
 1-\mu_2^2/2&=c\cos\theta+\sqrt{d^2+e^2\sin^2\theta},
\end{aligned}
\tag{4.5}
\end{equation}
while unitarity implies
\begin{equation}
 (c+d)^2+(e-f)^2\le1,
 \qquad
 (c-d)^2+(e+f)^2\le1.
 \tag{4.6}
\end{equation}
These formulas show term by term that the squared displacement has the source's global extremal property:
\[
 \boxed{\norm{(1-V^*)(1-V)}\ \text{is minimized when }V=U}
\]
for every unitary-invariant norm.  They also imply minimality of the operator norm and Hilbert--Schmidt norm of $1-V$, but the source warns that arbitrary unitary-invariant norms of $1-V$ need not be minimized by the direct rotation.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_idealGauge`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4.lean:486`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition4_3_compact_nonacute_real_idealGauge`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section4Real.lean:1297`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 17. DK-4.4-prop — Full-displacement counterexamples and Proposition 4.4 as printed

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 4.4
- **Result disposition:** `refuted_as_transcribed`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `1896dfda86994261bd007a6aeaf1fcd46b1b47e60a197caa7313cc5025ac1194`

### Atoms inside the counted printed result

- `DK-4.4-prop.printed-proposition4-4` — **counted_result_statement** — The paper asserts that in real space with Theta<=pi/3, U minimizes ||1-V|| for every UI norm.

### Same-block material explicitly outside the counted result

- `DK-4.4-prop.example4-1-real-reflection` — **remark_or_example_not_result** — Example 4.1 gives a real reflection with singular values 2,0 versus two equal direct-rotation singular values and defeats the Ky Fan 2 norm for theta>pi/3.
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-4.4-prop.example4-2-complex-phase` — **remark_or_example_not_result** — Example 4.2 uses V=e^{i delta}U and shows the full-displacement UI minimum can fail in complex space.
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-4.4-prop.printed-sharp-threshold` — **sharpness_commentary_not_designated_result** — The paper asserts the pi/3 threshold is sharp in view of the examples.
  - Boundary rationale: This is sharpness/equality commentary outside a designated result statement. It remains visible for fidelity but does not create an additional result obligation.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
The source exhibits failures of unrestricted full-displacement minimality.  In a real two-plane, a competing reflection has singular values $2,0$, whereas the direct rotation has both singular values $2\sin(\theta/2)$; the two-term Ky Fan comparison defeats the direct rotation once $\theta>\pi/3$.  In complex space, the competitors $V=e^{i\delta}U$ have singular values
\[
 2\sin\frac{\theta+\delta}{2},\qquad
 2\sin\frac{\theta-\delta}{2},
\]
and their sum is $4\sin(\theta/2)\cos(\delta/2)$, so the direct rotation is not generally minimizing.

After these examples the paper prints Proposition~4.4: if $\Hsp$ is real, $V$ is a unitary carrying $P\Hsp$ onto $Q\Hsp$, and
\[
 \Theta\le\pi/3,
\]
then $\norm{1-V}$ is asserted to be minimized by $V=U$ for every unitary-invariant norm.  The paper states the $\pi/3$ threshold is sharp in view of the examples.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahanTheory.DavisKahanProposition4_4_Finite`

Source location candidates: `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:639`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahanTheory.not_davisKahanProposition4_4_Finite`

Source location candidates: `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:663`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahanTheory.shortRotation_fullDisplacement_refuted`

Source location candidates: `DavisKahan/FiniteDimensional/DirectRotation/ShortRotationCounterexample.lean:610`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### False-source repair disposition

- **Repair status:** `proved`
- **Repair declarations:** `TauCeti.DavisKahanTheory.directRotation_fullDisplacement_qnorm`
- **Repair notes:** The printed real-space every-UI-norm full-displacement minimization claim is refuted exactly. The natural surviving Q-norm minimization theorem is proved by directRotation_fullDisplacement_qnorm.

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 18. DK-5.1-thm — Banach-space Sylvester lower bound

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 5.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `38590318e770b1eddea8bb6e6a45126b57c9652588f5e1c6991078f3dd8a6c4a`

### Atoms inside the counted printed result

- `DK-5.1-thm.banach-hypotheses` — **counted_result_hypothesis** — Banach-space theorem with ||B||<=alpha and ||A^{-1}||<=(alpha+delta)^{-1}, compatible cross norm.
- `DK-5.1-thm.sylvester-lower-bound` — **counted_result_statement** — AX-XB=C implies ||C||>=delta||X||.

### Same-block material explicitly outside the counted result

- `DK-5.1-thm.roles-interchange` — **post_result_scope_remark_not_in_printed_statement** — A and B roles/hypotheses may be interchanged.
  - Boundary rationale: This atom is a scope/extension remark stated after the named result, not part of the printed result environment; it is retained for fidelity without enlarging the result denominator.
- `DK-5.1-thm.one-sided-unbounded-extension` — **post_result_scope_remark_not_in_printed_statement** — The proof covers densely-defined unbounded A with bounded inverse hypothesis while B,X remain bounded.
  - Boundary rationale: This atom is a scope/extension remark stated after the named result, not part of the printed result environment; it is retained for fidelity without enlarging the result denominator.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Let $\mathcal X,\mathcal Y$ be Banach spaces.  Let $B$ be an operator on $\mathcal X$ and $A$ an operator on $\mathcal Y$ satisfying, in their bound norms,
\[
 \norm{B}\le\alpha,
 \qquad
 \norm{A^{-1}}\le(\alpha+\delta)^{-1},
 \qquad \alpha\ge0,\ \delta>0.
\]
For maps $\mathcal X\to\mathcal Y$, use any norm compatible with those bound norms.  If
\[
 AX-XB=C,
\]
then
\[
 \boxed{\norm{C}\ge\delta\norm{X}.}
\]
The roles and hypotheses of $A$ and $B$ may be interchanged.  The same proof also covers densely-defined unbounded $A$ provided the inverse hypothesis is meaningful/bounded while $B$ and $X$ remain bounded; the source then proceeds to a separate result allowing unbounded behavior on both sides in the Hilbert-space setting.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_uiNorm`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:266`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.banach_sylvester_lower_bound_exact`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullPartIII.lean:269`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 19. DK-5.2-thm — Semibounded self-adjoint Sylvester theorem

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 5.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `2078bb97672c50ca247554b198c575e381bd776725924f1333057a2a10fc3d8c`

### Atoms inside the counted printed result

- `DK-5.2-thm.hilbert-unbounded-hypotheses` — **counted_result_hypothesis** — Theorem 5.2 gives the Hilbert-space unbounded Sylvester setup with separated spectra and domain/core hypotheses.
- `DK-5.2-thm.hilbert-unbounded-conclusion` — **counted_result_statement** — The corresponding delta||X|| lower bound holds in the stated UI/ideal norm scope.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Let $\mathcal X,\mathcal Y$ be Hilbert spaces and let $A$ on $\mathcal Y$, $B$ on $\mathcal X$ be semibounded self-adjoint operators satisfying
\[
 A\ge\gamma+\delta>\gamma\ge B.
\]
If $X,C:\mathcal X\to\mathcal Y$ are bounded and
\[
 AX=XB+C,
\]
then for every unitary-invariant norm
\[
 \boxed{\norm{C}\ge\delta\norm{X}.}
\]
This is the source's main Sylvester tool for the unbounded self-adjoint passages.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Theorem5_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section5.lean:51`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.ExactSinTheta.davisKahan1970_sylvester_real`

Source location candidates: `DavisKahan/Sylvester/RealUnbounded.lean:76`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 20. DK-5.1-lem — Strong-cutoff convergence of singular values

- **Counted result kind:** `lemma`
- **Exact source anchor:** Lemma 5.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `4154e65f1eb46629c33da85de5866a2751ce9b5e21d9fa3956d2d6d0e677ecbd`

### Atoms inside the counted printed result

- `DK-5.1-lem.strong-cutoff-convergence` — **counted_result_statement** — The spectral-cutoff approximants converge strongly in the manner stated and support the unbounded proof.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
If orthogonal projectors $\Omega(\tau)$ converge strongly to the identity and $\kappa_\nu,\kappa_\nu(\tau)$ are the $\nu$th singular values of $K$ and $K\Omega(\tau)$, respectively, then
\[
 \kappa_\nu(\tau)\longrightarrow\kappa_\nu.
\]
This cutoff lemma lets finite spectral truncations recover the Ky Fan data required in the unbounded arguments.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Lemma5_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section5.lean:35`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 21. DK-6.1-lem — Direct-sum UI-norm comparison and converse

- **Counted result kind:** `lemma`
- **Exact source anchor:** Lemma 6.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `3fcdb9152000100900fc421874565b2defe8ccb6cc2a8574154d146c509eb2d5`

### Atoms inside the counted printed result

- `DK-6.1-lem.ordered-sylvester-forward` — **counted_result_statement** — The ordered spectral separation implies the stated Sylvester/UI-norm lower bound.
- `DK-6.1-lem.ordered-sylvester-converse` — **counted_result_statement** — The source includes the converse characterization used in the single-angle proof.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Let $\Omega,\Upsilon$ be orthogonal projectors.  If, for every unitary-invariant norm,
\[
 \norm{\Omega K\Upsilon}\le\norm{\Omega L\Upsilon},
 \qquad
 \norm{\Omega^\perp K\Upsilon^\perp}\le\norm{\Omega^\perp L\Upsilon^\perp},
\]
then
\[
 \norm{\Omega K\Upsilon+\Omega^\perp K\Upsilon^\perp}
 \le
 \norm{\Omega L\Upsilon+\Omega^\perp L\Upsilon^\perp}
\]
for every unitary-invariant norm.  The converse holds when the two diagonal blocks of $K$ are equisingular and the two diagonal blocks of $L$ are equisingular.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.lemma6_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:77`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.lemma6_1_converse`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:78`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 22. DK-6.2-lem — Reflection-pinch contraction

- **Counted result kind:** `lemma`
- **Exact source anchor:** Lemma 6.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `fefd468fd43df7f2d9ecb643c21a78aa0f8471b3b3909472925d347e6aa26f63`

### Atoms inside the counted printed result

- `DK-6.2-lem.pinching-contraction` — **counted_result_statement** — The reflection/pinching operation contracts every unitary-invariant norm in the stated setup.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
For orthogonal projectors $\Omega,\Upsilon$ and every unitary-invariant norm,
\[
 \boxed{\norm{\Omega K\Upsilon+\Omega^\perp K\Upsilon^\perp}\le\norm{K}.}
\]
The proof is the reflection/pinching contraction obtained by averaging $K$ with suitable unitary reflections.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.lemma6_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:79`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 23. DK-6.1-prop — Sine proof, ambient limitation, and symmetric sine theorem

- **Counted result kind:** `proposition`
- **Exact source anchor:** Proposition 6.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `ec802eefcfa341b4268ff3fd35bdb06d38211ec9cf5c72138d53e1ffdf5d11ce`

### Atoms inside the counted printed result

- `DK-6.1-prop.symmetric-sine-theorem` — **counted_result_statement** — Proposition 6.1 gives the symmetric sine-theta conclusion under two-sided spectral placement.

### Same-block material explicitly outside the counted result

- `DK-6.1-prop.sine-proof-residual-identity` — **proof_detail_not_in_printed_statement** — The symmetric sine proof rewrites the relevant off-diagonal block as the Sylvester residual identity.
  - Boundary rationale: This atom is established or used inside the proof of the neighboring named result, but is not part of that result's printed statement.
- `DK-6.1-prop.source-counterexample-need-two-sided` — **remark_or_example_not_result** — The source exhibits the failure of the ambient/symmetric conclusion when the needed two-sided placement is dropped.
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-6.1-prop.eq-6-1` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.1) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Projecting the residual relation onto the complementary exact subspace gives the Sylvester equation
\[
 R^*F_1=E_0^*F_1\Lambda_1-A_0E_0^*F_1.
\]
Under the interval/exterior gap of the $\sin\theta$ theorem, Theorem~5.1/5.2 yields
\begin{equation}
 \norm{R^*F_1}\ge\delta\norm{E_0^*F_1},
 \tag{6.1}
\end{equation}
whose singular values are the directed sines, proving $\delta\norm{\sin\Theta_0}\le\norm{R}$.

The source explicitly warns that the same one-sided hypotheses do \emph{not} imply $\delta\norm{\sin\Theta}\le\norm{H}$ for every unitary-invariant norm.  A $2\times2$ example has $\delta=2$, $\theta=\pi/4$, and
\[
 \delta\norm{\sin\Theta}_{\mathrm{sq}}=2>\sqrt3=\norm{H}_{\mathrm{sq}}.
\]

The symmetric replacement is Proposition~6.1: if the $A_0$--$\Lambda_1$ spectra satisfy the sine-theorem separation of width $\delta$ and the $A_1$--$\Lambda_0$ spectra satisfy the analogous separation, then for every unitary-invariant norm
\[
 \boxed{\delta\norm{\sin\Theta}\le\norm{H}.}
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Proposition6_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:115`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Proposition6_1_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:127`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 24. DK-6.1-thm — Generalized sine theorem

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 6.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `13e2036a72aaec0c5094f6014d3bfe1933167f1a43cf79f77716d5d7bf9726c7`

### Atoms inside the counted printed result

- `DK-6.1-thm.generalized-sine-hypotheses` — **counted_result_hypothesis** — The generalized sine theorem allows nonisometric E0 with E0*E0 >= epsilon^2 and the stated spectral separation.
- `DK-6.1-thm.generalized-sine-conclusion` — **counted_result_statement** — delta epsilon ||sin Theta0|| <= ||R||.
- `DK-6.1-thm.unequal-dimension-scope` — **counted_result_scope** — The generalized theorem allows unequal-dimensional comparison subspaces as stated.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Assume $A+H$ has the reducing decomposition (1.3) with exhaustive isometries $F_0,F_1$, and define $R$ by (1.8).  The trial map $E_0$ need not be isometric; assume only
\[
 E_0^*E_0\ge\varepsilon^2 I\qquad(\varepsilon>0).
\]
Let $P,Q$ be the projectors onto $\operatorname{Ran}(E_0)$ and $\operatorname{Ran}(F_0)$, with no equality-of-dimension hypothesis, and let $\sin\Theta_0$ be any operator having the same singular values as $PQ^\perp$.

If one of $A_0,\Lambda_1$ has spectrum in $[\beta,\alpha]$ and the other has spectrum outside $(\beta-\delta,\alpha+\delta)$, then for every unitary-invariant norm
\[
 \boxed{\delta\varepsilon\norm{\sin\Theta_0}\le\norm{R}.}
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Theorem6_1`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:102`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:105`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real_commonDomain`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:200`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_1_real_commonCore`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:221`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 25. DK-6.2-thm — Pairwise-gap square-norm sine theorem

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 6.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `3d339a183924f39cbfd71c81f3745c69442b26a631b3a25921093e05277bb58d`

### Atoms inside the counted printed result

- `DK-6.2-thm.second-generalized-sine` — **counted_result_statement** — The second generalized sine theorem gives the Hilbert--Schmidt estimate under pairwise spectral separation.

### Same-block material explicitly outside the counted result

- `DK-6.2-thm.rank-corrected-operator-consequence` — **post_result_consequence_not_in_printed_statement** — The stated rank-corrected operator-norm consequence follows.
  - Boundary rationale: This atom is an immediate consequence or interpretation stated after the named result; it is outside the printed result statement and is not counted separately.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Under the same lower-frame and range assumptions as Theorem~6.1, replace the interval/exterior separation by only the pairwise distance condition
\[
 |\lambda-a|\ge\delta>0
 \quad\text{for every }\lambda\in\spec(\Lambda_1),\ a\in\spec(A_0).
\]
Then the guaranteed norm is the Hilbert--Schmidt norm:
\[
 \boxed{\delta\varepsilon\norm{\sin\Theta_0}_{\mathrm{sq}}
 \le\norm{R}_{\mathrm{sq}}.}
\]
Combining this with (5.2) also yields the rank-corrected operator-norm estimate
\[
 \delta\varepsilon\norm{\sin\Theta_0}_1
 \le\norm{R}_1\sqrt{\operatorname{rank}R}.
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Theorem6_2`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:142`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Theorem6_2_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/FullSineTheta.lean:146`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 26. DK-6.3-thm — Tangent proof machinery, Example 6.1, and generalized tangent theorem

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 6.3
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `ca0097fc54e1567d7129b6da2a912399a2cb516b3ba5ddc306bf4ab65b746505`

### Atoms inside the counted printed result

- `DK-6.3-thm.generalized-tangent-theorem` — **counted_result_statement** — Theorem 6.3 gives the generalized tangent residual bound with its exact source hypotheses.

### Same-block material explicitly outside the counted result

- `DK-6.3-thm.tangent-setup-identities` — **proof_or_derivation_not_result** — Equations (6.2)--(6.6) provide the block identities used in the generalized tangent proof.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.example6-1` — **remark_or_example_not_result** — Example 6.1 gives the explicit 2x2 counterexample showing one-sided placement is essential for the tangent conclusion.
  - Boundary rationale: This atom belongs to a remark, example, or counterexample outside a counted result statement. It is retained for fidelity but is not a separate result obligation.
- `DK-6.3-thm.eq-6-2` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.2) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-3` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.3) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-4` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.4) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-5` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.5) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-6.3-thm.eq-6-6` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (6.6) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Restore the Section~1--2 hypotheses and write the direct rotation as
\begin{equation}
 U\sim
 \begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}
 =
 \begin{pmatrix}
 \cos\Theta_0&-J_0^*\sin\Theta_1\\
 J_0\sin\Theta_0&\cos\Theta_1
 \end{pmatrix},
 \qquad J_0\Theta_0=\Theta_1J_0,
 \quad C_j\ge0.
 \tag{6.2}
\end{equation}
The two reducing representations are related by
\begin{equation}
 \begin{pmatrix}A_0+H_0&B^*\\B&A_1+H_1\end{pmatrix}
 \begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}
 =
 \begin{pmatrix}C_0&-S_0^*\\S_0&C_1\end{pmatrix}
 \begin{pmatrix}\Lambda_0&0\\0&\Lambda_1\end{pmatrix},
 \tag{6.3}
\end{equation}
so in particular
\begin{equation}
 (A_0+H_0)(-S_0^*)+B^*C_1=-S_0^*\Lambda_1.
 \tag{6.4}
\end{equation}
Under $A_0\le\alpha$, $\Lambda_1\ge\alpha+\delta$, and $H_0=0$, transposing (6.4) gives
\begin{equation}
 C_1B=S_0A_0-\Lambda_1S_0.
 \tag{6.5}
\end{equation}
Under $A_0\le\alpha$, $\Lambda_1\ge\alpha+\delta$, and $H_0=0$, singular vectors for $S_0$ give the scalar estimate
\begin{equation}
 \cos\theta_j\,|y_j^*Bx_j|\ge\delta\sin\theta_j,
 \tag{6.6}
\end{equation}
so the relevant cosines are positive and Ky Fan/Fan dominance gives the tangent theorem.  The source then gives Example~6.1 showing the one-sided placement of $\Lambda_1$ is essential: a finite matrix example has $\delta=1$ and tangent quantity $1$ while the residual is only $1/\sqrt2$ if spectral mass is allowed on the wrong side.

The generalized theorem retains exact Rayleigh--Ritz trial data.  Assume $E_0,E_1,F_0,F_1$ are exhaustive isometries whose ranges reduce $A$ and $A+H$, respectively, but allow
\[
 \dim\mathcal X(E_0)<\dim\mathcal X(F_0).
\]
Set $A_0=E_0^*(A+H)E_0$, define $R$ by (1.8), and let the directed sine data have the singular values of $E_0^*F_1$.  If
\[
 \spec(A_0)\subset[\beta,\alpha],
 \qquad
 \spec(\Lambda_1)\subset[\alpha+\delta,\infty),
\]
then the corresponding directed tangent operator satisfies, for every unitary-invariant norm,
\[
 \boxed{\delta\norm{\tan\Theta_0}\le\norm{R}.}
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan.ExactTanTheta.theorem6_3_unbounded_infiniteTrial_ideal_exists`

Source location candidates: `DavisKahan/TanTheta/Theorem63UnboundedInfiniteTrial.lean:640`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.theorem6_3_unbounded_infiniteTrial_ideal_exists_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean:534`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_spectral`

Source location candidates: `Challenge/DavisKahan1970/Conformance.lean:297`, `DavisKahan/Sources/DavisKahan1970/Directed.lean:122`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.tanTheta_directed_paperUINorm_real_spectral`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/DirectedReal.lean:492`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 27. DK-6.3-lem — Finite-rank near-maximizer leakage estimate

- **Counted result kind:** `lemma`
- **Exact source anchor:** Lemma 6.3
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `6709c9fbf240ea7fc10d68b73cd0c746c59536127a66d13108ba14d114d52a45`

### Atoms inside the counted printed result

- `DK-6.3-lem.approximation-number-leakage` — **counted_result_statement** — Lemma 6.3 controls the approximation/singular-number leakage used in the Appendix, including the stated finite and real forms.

### Same-block material explicitly outside the counted result

- *(none; the primary source block contains only atoms belonging to the counted result statement)*

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Let $K$ have singular values $\kappa_1\ge\kappa_2\ge\cdots$, let $\Gamma,\Psi$ be rank-$\nu$ projectors with $K\Psi=\Gamma K\Psi$, and let the singular values of $K\Psi$ be $\mu_1\ge\cdots\ge\mu_\nu$.  If
\[
 \sum_{k=1}^{\nu}\mu_k^2
 >\sum_{k=1}^{\nu}\kappa_k^2-\eta^2,
\]
then the leakage outside $\Psi$ obeys
\[
 \boxed{\norm{\Gamma K\Psi^\perp}_1\le\eta.}
\]
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean:352`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_singularValue_leakage`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakage.lean:372`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section6Appendix.lemma6_3_approximationNumber_leakage_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section6AppendixLeakageReal.lean:114`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 28. DK-8.1-thm — Branch selection and spectral repulsion

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 8.1
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `ca616396d0bee7b303c7da3ad0904053b80ad6da1a13a172bbec402be84f7c57`

### Atoms inside the counted printed result

- `DK-8.1-thm.acute-iff-spectral-placement` — **counted_result_statement** — Theta<=pi/4 iff the chosen perturbed reducing blocks lie on the corresponding sides of the gap.
- `DK-8.1-thm.existence-correct-q` — **counted_result_statement** — A reducing spectral projector Q with the required placement exists and is unique in the stated sense.
- `DK-8.1-thm.part-i-compression` — **counted_result_statement** — The upper/lower block compression inequalities of part (i).
- `DK-8.1-thm.part-ii-eigenvalue` — **counted_result_statement** — The finite-dimensional eigenvalue displacement inequalities of part (ii), with natural infinite-dimensional extensions.
- `DK-8.1-thm.part-iii-gauge` — **counted_result_statement** — The symmetric-gauge majorization inequalities of part (iii).

### Same-block material explicitly outside the counted result

- `DK-8.1-thm.branch-problem` — **pre_result_motivation_not_result** — Small double-angle trigonometric quantities alone do not select angles near zero; the chosen reducing subspace matters.
  - Boundary rationale: This atom motivates the following counted result but is outside its printed statement.
- `DK-8.1-thm.exclude-pi-over-four` — **proof_or_derivation_not_result** — Equations (8.1)--(8.2) exclude theta=pi/4 and then theta>pi/4 under the selected placement.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.1-thm.spectral-repulsion-interpretation` — **post_result_interpretation_not_result** — Strong off-diagonal eigenvector rotation forces definite eigenvalue displacement as described.
  - Boundary rationale: This atom interprets a counted result after its statement/proof; it is not an additional result obligation.
- `DK-8.1-thm.eq-8-1` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (8.1) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.1-thm.eq-8-2` — **proof_or_derivation_not_result** — Exact mathematical content of source equation (8.2) as reconstructed in the distributable TeX.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Small $\sin2\Theta$ or $\tan2\Theta$ does not by itself force all principal angles near $0$: some may lie near $\pi/2$.  The reason is that the double-angle theorems initially impose no distinguished choice of the reducing subspace $Q\Hsp$ of $A+H$; even when $H=0$, a poorly matched reducing subspace can require rotations near $\pi/2$.  Section~8 identifies the spectrally corresponding acute branch.

Assume the hypotheses of the $\tan2\theta$ theorem.  Then
\[
 \Theta\le\pi/4
\]
if and only if the chosen reducing blocks of $A+H$ satisfy
\[
 \Lambda_1\ge\alpha+\delta,
 \qquad
 \Lambda_0\le\alpha.
\]
For fixed $A,P,H$ there exists a reducing projector $Q$ with these properties (take the spectral projector of $A+H$ on the appropriate side of $\alpha$).  For this $Q$:
\begin{enumerate}[label=(\roman*)]
\item the upper block obeys
\[
 A_1-\alpha\le C_1(\Lambda_1-\alpha)C_1,
\]
with the analogous lower-block inequality;
\item in finite dimensions, if $\lambda_k$ are the ordered eigenvalues of $\Lambda_1$ and $\alpha_k$ those of $A_1$,
\[
 \alpha_k-\alpha\le\norm{C_1}_1^2(\lambda_k-\alpha),
\]
with the analogous lower-block statement and natural infinite-dimensional extensions;
\item for every symmetric gauge function $\Phi$ in finite dimensions,
\[
 \Phi(\alpha_1-\alpha,\ldots,\alpha_n-\alpha)
 \le
 \Phi((\lambda_1-\alpha)\cos^2\theta_1,\ldots,
      (\lambda_n-\alpha)\cos^2\theta_n),
\]
again with the analogous lower-block relation.
\end{enumerate}
The branch proof uses the two representations
\begin{equation}
 x_0^*\Lambda_0x_0
 =x_0^*A_0x_0+\tan\theta\,x_0^*B^*y_1
 =\cot\theta\,y_1^*Bx_0+y_1^*A_1y_1
 \tag{8.1}
\end{equation}
and hence
\begin{equation}
 x_0^*B^*y_1(\tan\theta-\cot\theta)
 =y_1^*A_1y_1-x_0^*A_0x_0\ge\delta>0.
 \tag{8.2}
\end{equation}
These exclude $\theta=\pi/4$ and then $\theta>\pi/4$ under the chosen spectral placement.  The source interprets parts (ii)--(iii) as quantitative spectral repulsion: an off-diagonal perturbation that rotates all relevant eigenvectors strongly must also move eigenvalues by a definite amount.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean:249`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81.lean:494`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_canonicalBranch_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81Real.lean:78`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_maximalAngle_le_iff_spectrumIn_real`

Source location candidates: `DavisKahan/Sources/DavisKahan1970/Section8/SourceTheorem81Real.lean:240`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_source`

Source location candidates: `DavisKahan/Frontier/Section8.lean:1015`, `DavisKahan/Frontier/Section8SourceSurface.lean:96`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_source`

Source location candidates: `DavisKahan/Frontier/Section8.lean:1063`, `DavisKahan/Frontier/Section8SourceSurface.lean:101`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_real`

Source location candidates: `DavisKahan/Frontier/Section8PartIIReal.lean:341`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_real`

Source location candidates: `DavisKahan/Frontier/Section8PartIIReal.lean:404`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_source`

Source location candidates: `DavisKahan/Frontier/Section8PartII.lean:419`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_source`

Source location candidates: `DavisKahan/Frontier/Section8PartII.lean:548`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperApproximationRepulsion_real`

Source location candidates: `DavisKahan/Frontier/Section8PartIIReal.lean:536`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerApproximationRepulsion_real`

Source location candidates: `DavisKahan/Frontier/Section8PartIIReal.lean:622`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.approximationNumber_eq_eigenvalues_of_isPositive`

Source location candidates: `DavisKahan/Frontier/Section8SourceDictionary.lean:147`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_source`

Source location candidates: `DavisKahan/Frontier/Section8SourceDictionary.lean:437`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_source`

Source location candidates: `DavisKahan/Frontier/Section8SourceDictionary.lean:490`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real`

Source location candidates: `DavisKahan/Frontier/Section8SourceDictionary.lean:715`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_real`

Source location candidates: `DavisKahan/Frontier/Section8SourceDictionary.lean:770`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

## 29. DK-8.2-thm — Smallness selects the acute branch

- **Counted result kind:** `theorem`
- **Exact source anchor:** Theorem 8.2
- **Result disposition:** `proved_exact`
- **Compiler verification:** `proved_in_build`
- **Hostile semantic certification:** `accepted`
- **Boundary review:** `accepted`
- **Organizational source-block hash:** `8af6a38667dbf398e65e1b4460763ab627b559607ac519214c35402797c1b48e`

### Atoms inside the counted printed result

- `DK-8.2-thm.smallness-alternative` — **counted_result_hypothesis** — The theorem assumes either ||H||_1<delta/2 or ||R||_1<delta/2 plus the stated A0 interval.
- `DK-8.2-thm.double-angle-bound-retained` — **counted_result_statement** — The corresponding sin2 double-angle estimate remains valid.
- `DK-8.2-thm.acute-branch-conclusion` — **counted_result_statement** — Theta<pi/4.

### Same-block material explicitly outside the counted result

- `DK-8.2-thm.homotopy-proof` — **proof_or_derivation_not_result** — The perturbation proof uses the continuous spectral-projector homotopy and the displayed arcsine bound.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.2-thm.residual-reduction` — **proof_or_derivation_not_result** — The residual form is reduced by changing the complementary perturbation block while preserving the residual/spectral data.
  - Boundary rationale: This atom occurs in a proof, derivation, or proof-only equation rather than in a counted result statement. Source fidelity preserves it, but 100% does not require a separate Lean theorem for it.
- `DK-8.2-thm.sin2-unequal-dimension-extension` — **post_result_scope_remark_not_in_printed_statement** — The source states a sin2 extension to unequal comparison dimensions.
  - Boundary rationale: This atom is a scope/extension remark stated after the named result, not part of the printed result environment; it is retained for fidelity without enlarging the result denominator.
- `DK-8.2-thm.no-tan2-unequal-dimension-extension-known` — **historical_knowledge_state** — No analogous tan2 extension was known.
  - Boundary rationale: This atom records the paper's historical knowledge state rather than a Davis--Kahan result established in the paper.

Boundary method: Compared the printed result environment with the source-fidelity atoms; included only hypotheses, conclusions, and scope belonging to the counted result, and explicitly classified all adjacent same-block material outside the statement.

### Full registered source block (for context and boundary challenge)

~~~~tex
Add to the hypotheses of the $\sin2\theta$ theorem either
\[
 \norm{H}_1<\delta/2
 \quad\text{or}\quad
 \norm{R}_1<\delta/2,
\]
and assume
\[
 \spec(A_0)\subset[\beta-\delta/2,\alpha+\delta/2].
\]
Then the corresponding double-angle estimate remains valid,
\[
 \delta\norm{\sin2\Theta}\le2\norm H
 \quad\text{or}\quad
 \delta\norm{\sin2\Theta_0}\le2\norm R,
\]
and in addition the comparison is on the acute branch:
\[
 \boxed{\Theta<\pi/4.}
\]
For the perturbation form, the proof follows the homotopy $A(\sigma)=A+H-\sigma H$ and the continuously varying spectral projector $Q(\sigma)$.  If $\gamma=\norm H_1<\delta/2$, every ``close'' parameter satisfies
\[
 \theta(\sigma)
 \le\tfrac12\arcsin(2\sigma\gamma/\delta)
 \le\frac{\pi}{2}\frac{\sigma\gamma}{\delta}
 <\pi/4,
\]
which propagates closeness from $\sigma=0$ to $1$.  The residual case is reduced to this by changing $H_1$ without changing the relevant residual or spectral blocks and choosing the replacement with $\norm H_1=\norm R_1$.

The source closes Section~8 by stating that the $\sin2\theta$ theorem extends to $\dim\mathcal X(E_0)<\dim\mathcal X(F_0)$ analogously to Theorems~6.1 and~6.3, while no corresponding extension of the $\tan2\theta$ theorem was known.
~~~~

### Source-facing Lean declarations

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:123`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_paperUINorm`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:207`, `DavisKahan/Frontier/Section8SourceTheorem82.lean:431`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_residual_source_paperUINorm`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:216`, `DavisKahan/Frontier/Section8SourceTheorem82.lean:507`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_branch_source_directed_real`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:251`, `DavisKahan/Frontier/Section8SourceTheorem82Real.lean:319`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan1970.Section8.theorem8_2_sinTwoTheta_perturbation_source_real_paperUINorm`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:284`, `DavisKahan/Frontier/Section8SourceTheorem82Real.lean:553`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

#### `TauCeti.DavisKahan.Frontier.Section8.theorem8_2_sinTwoTheta_residual_source_real_paperUINorm`

Source location candidates: `DavisKahan/Frontier/Section8SourceSurface.lean:290`, `DavisKahan/Frontier/Section8SourceTheorem82Real.lean:608`

Compiler-printed type: *inserted when a compiler certificate is supplied.*

### Independent result audit checklist

- [ ] The selected source atoms are exactly the hypotheses, conclusions, and scope of the printed result statement.
- [ ] Every same-block atom excluded by the boundary review is genuinely outside the printed result statement.
- [ ] The source hypotheses are all represented, with no stronger hidden hypothesis used as a substitute.
- [ ] The Lean conclusion matches every conclusion of the counted result.
- [ ] Real/complex scalar scope matches the source, including field-independent statements.
- [ ] Finite-dimensional versus arbitrary/separable Hilbert-space scope matches the source.
- [ ] Compactness, finite-rank, spectral-gap, domain, and bounded/unbounded assumptions match the source.
- [ ] Acute/nonacute, crossed-defect, branch, and direct-rotation existence hypotheses match the source.
- [ ] Existence/uniqueness assertions and quantifier order match the source rather than only a derived inequality.
- [ ] Indexing, eigenvalue/singular-value multiplicity, and finite-versus-infinite sequence semantics match the source.
- [ ] Norm class, constants, strictness, signs, interval orientation, and directed/ambient distinctions match exactly.
- [ ] If the result is refuted, the counterexample satisfies all printed hypotheses and the separate repair record is terminal.

### Auditor verdict

- **Verdict:** _fill in_
- **Boundary challenge:** _confirm or identify an atom wrongly included/excluded_
- **Source/Lean mismatch:** _fill in_
- **Additional Lean declaration(s) needed, if any:** _fill in_

---

# Appendix A — complete source-fidelity classification

Every source atom remains visible here even when it is outside the 29-result denominator. This table is the project's explicit limitation statement: an excluded item is not hidden; it has a reason code that the reviewer may challenge.

## Classification totals

- `background_theory_not_designated_result`: **2**
- `counted_result_hypothesis`: **10**
- `counted_result_scope`: **8**
- `counted_result_statement`: **49**
- `deferred_unproved_claim`: **2**
- `definition_not_result`: **9**
- `expository_commentary_not_result`: **4**
- `external_result_not_dk_result`: **3**
- `historical_knowledge_state`: **1**
- `introductory_background_not_designated_result`: **26**
- `open_question`: **5**
- `post_result_consequence_not_in_printed_statement`: **4**
- `post_result_interpretation_not_result`: **1**
- `post_result_scope_remark_not_in_printed_statement`: **3**
- `pre_result_motivation_not_result`: **1**
- `pre_result_setup_not_in_printed_statement`: **3**
- `proof_detail_not_in_printed_statement`: **4**
- `proof_or_derivation_not_result`: **65**
- `remark_or_example_not_result`: **6**
- `restatement_of_counted_result`: **6**
- `section10_motivation_not_result`: **3**
- `section9_worked_example_not_result`: **43**
- `section_setup_not_result`: **2**
- `sharpness_commentary_not_designated_result`: **6**

## All source atoms in paper order

| # | Atom | Parent block | Boundary classification | Counted result support | Source-fidelity summary |
|---:|---|---|---|---|---|
| 1 | `S1-block-residual.setup-hilbert-scope` | `S1-block-residual` | `introductory_background_not_designated_result` | — | Separable real or complex Hilbert space; bounded main setting with stated unbounded extension. |
| 2 | `S1-block-residual.reducing-projector-setup` | `S1-block-residual` | `introductory_background_not_designated_result` | — | P reduces A and E0,E1 are isometries onto the two reducing summands. |
| 3 | `S1-block-residual.q-reduces-perturbed` | `S1-block-residual` | `introductory_background_not_designated_result` | — | Q reduces A+H and F0,F1 give its reducing decomposition. |
| 4 | `S1-block-residual.no-spectral-projector-assumption` | `S1-block-residual` | `introductory_background_not_designated_result` | — | P and Q need not be spectral projectors and the diagonal spectral sets may overlap. |
| 5 | `S1-block-residual.unitary-intertwiner-dimension-criterion` | `S1-block-residual` | `introductory_background_not_designated_result` | — | A unitary carrying P-space to Q-space exists precisely with the two matching dimension conditions. |
| 6 | `S1-block-residual.within-subspace-coordinate-freedom` | `S1-block-residual` | `introductory_background_not_designated_result` | — | Changing the intertwining unitary changes only the within-subspace unitary coordinates W0,W1. |
| 7 | `S1-block-residual.residual-inherited-block` | `S1-block-residual` | `introductory_background_not_designated_result` | — | When A0 is inherited from A, R=H E0 and is the first block column of H. |
| 8 | `S1-block-residual.rayleigh-ritz-h0-zero` | `S1-block-residual` | `introductory_background_not_designated_result` | — | The Rayleigh--Ritz choice A0=E0*(A+H)E0 is equivalent here to H0=0. |
| 9 | `S1-block-residual.residual-gram-split` | `S1-block-residual` | `introductory_background_not_designated_result` | — | R*R=H0^2+B*B. |
| 10 | `S1-block-residual.rayleigh-ritz-minimizes-residual` | `S1-block-residual` | `introductory_background_not_designated_result` | — | The Rayleigh--Ritz choice minimizes residual size among the block choices under discussion. |
| 11 | `S1-block-residual.one-sided-vs-strong-offdiagonal` | `S1-block-residual` | `introductory_background_not_designated_result` | — | H0=0 is distinguished from the stronger H0=H1=0 condition. |
| 12 | `S1-block-residual.residual-eigenvalue-sum` | `S1-block-residual` | `introductory_background_not_designated_result` | — | There is an ordering of m exact eigenvalues with sum_j (alpha_j-lambda_j)^2 <= \|\|R\|\|_sq^2. |
| 13 | `S1-block-residual.residual-eigenvalue-pointwise` | `S1-block-residual` | `introductory_background_not_designated_result` | — | The same ordering satisfies \|alpha_j-lambda_j\| <= \|\|R\|\|_1. |
| 14 | `S1-block-residual.eq-1-1` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.1) as reconstructed in the distributable TeX. |
| 15 | `S1-block-residual.eq-1-2` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.2) as reconstructed in the distributable TeX. |
| 16 | `S1-block-residual.eq-1-3` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.3) as reconstructed in the distributable TeX. |
| 17 | `S1-block-residual.eq-1-4` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.4) as reconstructed in the distributable TeX. |
| 18 | `S1-block-residual.eq-1-5` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.5) as reconstructed in the distributable TeX. |
| 19 | `S1-block-residual.eq-1-6` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.6) as reconstructed in the distributable TeX. |
| 20 | `S1-block-residual.eq-1-7` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.7) as reconstructed in the distributable TeX. |
| 21 | `S1-block-residual.eq-1-8` | `S1-block-residual` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.8) as reconstructed in the distributable TeX. |
| 22 | `S1-ui-norms.ui-rank-one-normalization` | `S1-ui-norms` | `definition_not_result` | — | Rank-one operators satisfy the normalized unitary-invariant norm convention. |
| 23 | `S1-ui-norms.ui-contraction-monotonicity` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | Left and right multiplication by contractions cannot increase a unitary-invariant norm. |
| 24 | `S1-ui-norms.singular-minimax-noncompact-scope` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The singular-value minimax expression extends to bounded noncompact operators, with spectral-multiplicity cautions. |
| 25 | `S1-ui-norms.hilbert-schmidt-identity` | `S1-ui-norms` | `definition_not_result` | — | The Hilbert--Schmidt norm is the square root of the sum of squared singular values and trace K*K. |
| 26 | `S1-ui-norms.fan-dominance` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | All-unitary-invariant-norm comparison is equivalent to comparison in every Ky Fan norm. |
| 27 | `S1-ui-norms.eq1-13-variational` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The Ky Fan norm also equals the supremum of the real sum of y_k* K x_k over orthonormal tuples. |
| 28 | `S1-ui-norms.cosine-law` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The vector-angle convention satisfies \|\|x+y\|\|^2=\|\|x\|\|^2+\|\|y\|\|^2+2\|\|x\|\|\|\|y\|\|cos angle(x,y). |
| 29 | `S1-ui-norms.s0-singular-values` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The singular values of S0 are sin(theta_k) for the principal-angle data. |
| 30 | `S1-ui-norms.ambient-angle-doubling` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | Nonzero angle data of the ambient angle operator occur twice, once from each side. |
| 31 | `S1-ui-norms.directed-sine-norm` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | \|\|Q^perp P\|\|=\|\|Q^perp E0\|\|=\|\|sin Theta0\|\| for every UI norm. |
| 32 | `S1-ui-norms.ambient-sine-norm` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | \|\|P-Q\|\|=\|\|sin Theta\|\| for every UI norm. |
| 33 | `S1-ui-norms.operator-largest-one-sided-distance` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | In operator norm the largest one-sided distance is \|\|sin Theta\|\|_1. |
| 34 | `S1-ui-norms.closest-unit-vector-distance` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The closest-unit-vector distance is 2\|\|sin(Theta/2)\|\|_1. |
| 35 | `S1-ui-norms.j-block-form` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | Section 3 constructs the skew block partial isometry J from J0. |
| 36 | `S1-ui-norms.direct-rotation-exponential` | `S1-ui-norms` | `introductory_background_not_designated_result` | — | The distinguished direct rotation satisfies U=exp(J Theta)=cos Theta+J sin Theta with the displayed block form. |
| 37 | `S1-ui-norms.eq-1-9` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.9) as reconstructed in the distributable TeX. |
| 38 | `S1-ui-norms.eq-1-10` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.10) as reconstructed in the distributable TeX. |
| 39 | `S1-ui-norms.eq-1-11` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.11) as reconstructed in the distributable TeX. |
| 40 | `S1-ui-norms.eq-1-12` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.12) as reconstructed in the distributable TeX. |
| 41 | `S1-ui-norms.eq-1-13` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.13) as reconstructed in the distributable TeX. |
| 42 | `S1-ui-norms.eq-1-14` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.14) as reconstructed in the distributable TeX. |
| 43 | `S1-ui-norms.eq-1-15` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.15) as reconstructed in the distributable TeX. |
| 44 | `S1-ui-norms.eq-1-16` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.16) as reconstructed in the distributable TeX. |
| 45 | `S1-ui-norms.eq-1-17` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.17) as reconstructed in the distributable TeX. |
| 46 | `S1-ui-norms.eq-1-18` | `S1-ui-norms` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (1.18) as reconstructed in the distributable TeX. |
| 47 | `S2-sin-theta.family-distinctness` | `S2-sin-theta` | `expository_commentary_not_result` | — | The four Section 2 theorem families are distinct rather than mere restatements. |
| 48 | `S2-sin-theta.ui-norm-scope` | `S2-sin-theta` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | Every norm in the four headline theorem statements is an arbitrary unitary-invariant norm. |
| 49 | `S2-sin-theta.gap-hypothesis` | `S2-sin-theta` | `counted_result_hypothesis` | `S2-sin-theta` | The sine theorem uses interval/exterior separation, allowing the A0 and Lambda1 roles to be interchanged. |
| 50 | `S2-sin-theta.directed-conclusion` | `S2-sin-theta` | `counted_result_statement` | `S2-sin-theta` | delta \|\|sin Theta0\|\| <= \|\|R\|\|. |
| 51 | `S2-tan-theta.ordered-gap-hypothesis` | `S2-tan-theta` | `counted_result_hypothesis` | `S2-tan-theta` | The tangent theorem assumes A0 below Lambda1 by delta. |
| 52 | `S2-tan-theta.rayleigh-ritz-hypothesis` | `S2-tan-theta` | `counted_result_hypothesis` | `S2-tan-theta` | The tangent theorem assumes H0=0, equivalently the Rayleigh--Ritz block choice. |
| 53 | `S2-tan-theta.directed-conclusion` | `S2-tan-theta` | `counted_result_statement` | `S2-tan-theta` | delta \|\|tan Theta0\|\| <= \|\|R\|\|. |
| 54 | `S2-tan-theta.ambient-conclusion` | `S2-tan-theta` | `counted_result_statement` | `S2-tan-theta` | delta \|\|tan Theta\|\| <= \|\|H\|\|. |
| 55 | `S2-sin-two-theta.gap-hypothesis` | `S2-sin-two-theta` | `counted_result_hypothesis` | `S2-sin-two-theta` | The double-sine theorem separates Lambda0 from Lambda1 by an interval/exterior gap. |
| 56 | `S2-sin-two-theta.directed-conclusion` | `S2-sin-two-theta` | `counted_result_statement` | `S2-sin-two-theta` | delta \|\|sin(2 Theta0)\|\| <= 2\|\|R\|\|. |
| 57 | `S2-sin-two-theta.ambient-conclusion` | `S2-sin-two-theta` | `counted_result_statement` | `S2-sin-two-theta` | delta \|\|sin(2 Theta)\|\| <= 2\|\|H\|\|. |
| 58 | `S2-tan-two-theta.ordered-gap-hypothesis` | `S2-tan-two-theta` | `counted_result_hypothesis` | `S2-tan-two-theta` | The double-tangent theorem assumes A0 below A1 by delta. |
| 59 | `S2-tan-two-theta.strong-offdiagonal-hypothesis` | `S2-tan-two-theta` | `counted_result_hypothesis` | `S2-tan-two-theta` | The double-tangent theorem assumes H0=H1=0. |
| 60 | `S2-tan-two-theta.no-extra-pole-hypothesis` | `S2-tan-two-theta` | `counted_result_scope` | `S2-tan-two-theta` | The printed theorem has no independent tan-pole exclusion or perturbed-block spectral-placement hypothesis. |
| 61 | `S2-tan-two-theta.directed-conclusion` | `S2-tan-two-theta` | `counted_result_statement` | `S2-tan-two-theta` | delta \|\|tan(2 Theta0)\|\| <= 2\|\|R\|\|. |
| 62 | `S2-tan-two-theta.ambient-conclusion` | `S2-tan-two-theta` | `counted_result_statement` | `S2-tan-two-theta` | delta \|\|tan(2 Theta)\|\| <= 2\|\|H\|\|. |
| 63 | `S2-tan-two-theta.pole-exclusion-derived` | `S2-tan-two-theta` | `proof_or_derivation_not_result` | — | Section 7 derives the needed nonvanishing cosine factors from the printed hypotheses. |
| 64 | `S2-sharpness.constants-best-possible` | `S2-sharpness` | `sharpness_commentary_not_designated_result` | — | The constants in all four theorem families are best possible. |
| 65 | `S2-sharpness.two-dimensional-equality` | `S2-sharpness` | `sharpness_commentary_not_designated_result` | — | Two-dimensional examples attain the constants. |
| 66 | `S2-sharpness.direct-sum-simultaneous-equality` | `S2-sharpness` | `sharpness_commentary_not_designated_result` | — | Orthogonal sums give simultaneous equality for all UI norms. |
| 67 | `S2-sharpness.first-order-asymptotic` | `S2-sharpness` | `sharpness_commentary_not_designated_result` | — | All four estimates share the stated first-order epsilon asymptotics. |
| 68 | `S2-unbounded-scope.infinite-dimensional-scope` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | All four main results apply in infinite as well as finite dimension. |
| 69 | `S2-unbounded-scope.arbitrary-ui-scope` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | All four main results apply to arbitrary UI norms. |
| 70 | `S2-unbounded-scope.unbounded-selfadjoint-scope` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | The results extend to unbounded self-adjoint A under the stated domain condition. |
| 71 | `S2-unbounded-scope.bounded-residual-needed` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | Useful unbounded conclusions require the pertinent perturbation or residual to extend boundedly. |
| 72 | `S2-unbounded-scope.half-infinite-gap-intervals` | `S2-unbounded-scope` | `counted_result_scope` | `S2-sin-theta`, `S2-tan-theta`, `S2-sin-two-theta`, `S2-tan-two-theta` | Gap intervals may be half-infinite and the remaining spectra unbounded. |
| 73 | `DK-3.1-def.s0-s1-singular-values` | `DK-3.1-def` | `section_setup_not_result` | — | S0 and S1 have the same nonzero singular values, with the stated possible initial unit singular values from unequal C0 nullities. |
| 74 | `DK-3.1-def.direct-rotation-definition` | `DK-3.1-def` | `definition_not_result` | — | A direct rotation is a unitary intertwiner with C0,C1 positive and S1=S0*. |
| 75 | `DK-3.1-def.u-notation` | `DK-3.1-def` | `definition_not_result` | — | The paper reserves U for direct rotations. |
| 76 | `DK-3.1-def.eq-3-1` | `DK-3.1-def` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.1) as reconstructed in the distributable TeX. |
| 77 | `DK-3.1-def.eq-3-2` | `DK-3.1-def` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.2) as reconstructed in the distributable TeX. |
| 78 | `DK-3.1-def.eq-3-3` | `DK-3.1-def` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.3) as reconstructed in the distributable TeX. |
| 79 | `DK-3.1-def.eq-3-4` | `DK-3.1-def` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.4) as reconstructed in the distributable TeX. |
| 80 | `DK-3.2-def.acute-case-definition` | `DK-3.2-def` | `definition_not_result` | — | The acute case is exactly the vanishing of the two crossing intersections. |
| 81 | `DK-3.1-prop.existence` | `DK-3.1-prop` | `counted_result_statement` | `DK-3.1-prop` | In the acute case a direct rotation exists. |
| 82 | `DK-3.1-prop.uniqueness` | `DK-3.1-prop` | `counted_result_statement` | `DK-3.1-prop` | In the acute case the direct rotation is unique. |
| 83 | `DK-3.1-prop.positive-diagonal-characterization` | `DK-3.1-prop` | `counted_result_statement` | `DK-3.1-prop` | Positivity of C0,C1 characterizes the direct rotation among unitary intertwiners in the acute case. |
| 84 | `DK-3.2-prop.existence-iff-crossing-dimensions` | `DK-3.2-prop` | `counted_result_statement` | `DK-3.2-prop` | Outside the acute case, direct rotation existence is equivalent to equality of the crossing dimensions. |
| 85 | `DK-3.2-prop.nonuniqueness` | `DK-3.2-prop` | `counted_result_statement` | `DK-3.2-prop` | When it exists outside the acute case it need not be unique. |
| 86 | `DK-3.2-prop.crossing-square-minus-one` | `DK-3.2-prop` | `proof_detail_not_in_printed_statement` | — | On the crossing subspaces U^2 x=-x. |
| 87 | `DK-3.2-prop.bilateral-shift-counterexample` | `DK-3.2-prop` | `remark_or_example_not_result` | — | The bilateral-shift example shows the basic P/Q dimension conditions do not imply the crossing-dimension condition. |
| 88 | `DK-3.2-prop.eq-3-5` | `DK-3.2-prop` | `counted_result_statement` | `DK-3.2-prop` | Exact mathematical content of source equation (3.5) as reconstructed in the distributable TeX. |
| 89 | `DK-3.3-prop.reflection-conjugacy` | `DK-3.3-prop` | `pre_result_setup_not_in_printed_statement` | — | With X=P-Pperp and Q_-=XQX, U^{-1}=XUX. |
| 90 | `DK-3.3-prop.principal-square-root` | `DK-3.3-prop` | `counted_result_statement` | `DK-3.3-prop` | Every direct rotation is the principal unitary square root of the product of the two reflections. |
| 91 | `DK-3.3-prop.square-root-converse` | `DK-3.3-prop` | `counted_result_statement` | `DK-3.3-prop` | A principal square root is a direct rotation when it maps the two crossing subspaces appropriately. |
| 92 | `DK-3.3-prop.eq-3-6` | `DK-3.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.6) as reconstructed in the distributable TeX. |
| 93 | `DK-3.3-prop.eq-3-7` | `DK-3.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.7) as reconstructed in the distributable TeX. |
| 94 | `DK-3.3-prop.eq-3-8` | `DK-3.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (3.8) as reconstructed in the distributable TeX. |
| 95 | `DK-3.4-prop.u-square-direct-rotation` | `DK-3.4-prop` | `counted_result_statement` | `DK-3.4-prop` | If C0^2>=1/2, then U^2 is the direct rotation from Q_- to Q. |
| 96 | `DK-3.1-thm.complete-invariant` | `DK-3.1-thm` | `counted_result_statement` | `DK-3.1-thm` | Spectral multiplicity functions of Theta0,Theta1 completely classify the pair under the stated dimension hypotheses. |
| 97 | `DK-3.1-thm.converse-angle-data` | `DK-3.1-thm` | `counted_result_statement` | `DK-3.1-thm` | Conversely the angle operators may be arbitrary positive contractions in [0,pi/2] with matching spectral multiplicities away from zero and the stated dimensions. |
| 98 | `DK-3.1-thm.reconstruction` | `DK-3.1-thm` | `proof_detail_not_in_printed_statement` | — | The pair is reconstructed from the angle data and J0. |
| 99 | `DK-3.1-cor.compact-complete-invariants` | `DK-3.1-cor` | `counted_result_statement` | `DK-3.1-cor` | If PQperpP is compact, the eigenvalues of Theta0,Theta1 counted with multiplicity are complete invariants. |
| 100 | `DK-3.1-cor.allowed-angle-sequence` | `DK-3.1-cor` | `counted_result_statement` | `DK-3.1-cor` | Theta0 eigenvalues may be any decreasing sequence in [0,pi/2] tending to zero plus possible zero eigenspace. |
| 101 | `DK-3.1-cor.theta1-match` | `DK-3.1-cor` | `counted_result_statement` | `DK-3.1-cor` | Theta1 has the same nonzero eigenvalues and may differ only in zero multiplicity. |
| 102 | `DK-3.5-prop.commutation` | `DK-3.5-prop` | `counted_result_statement` | `DK-3.5-prop` | Theta commutes with P,Q,J,U. |
| 103 | `DK-3.5-prop.direct-rotation-exponential` | `DK-3.5-prop` | `pre_result_setup_not_in_printed_statement` | — | U=exp(J Theta). |
| 104 | `DK-3.5-prop.cos-square-projector` | `DK-3.5-prop` | `pre_result_setup_not_in_printed_statement` | — | cos^2 Theta=PQP+Pperp Qperp Pperp. |
| 105 | `DK-3.5-prop.eigenvector-rotation-angle` | `DK-3.5-prop` | `counted_result_statement` | `DK-3.5-prop` | If Theta x=theta x then angle(x,Ux)=theta. |
| 106 | `DK-3.5-prop.acute-maximal-characterization` | `DK-3.5-prop` | `counted_result_statement` | `DK-3.5-prop` | In the acute case each theta-eigenspace is the unique maximal P/Q-reducing subspace with the stated constant-angle properties. |
| 107 | `DK-3.2-cor.swap-invariance` | `DK-3.2-cor` | `counted_result_statement` | `DK-3.2-cor` | Swapping P and Q leaves Theta unchanged and sends J to -J. |
| 108 | `DK-4.1-prop.vz-factorization` | `DK-4.1-prop` | `section_setup_not_result` | — | Every unitary V carrying P to Q is written V=UZ with Z block diagonal in the Section 4 setup. |
| 109 | `DK-4.1-prop.orthonormal-angle-lower-bounds` | `DK-4.1-prop` | `counted_result_statement` | `DK-4.1-prop` | For every such V there are orthonormal v_k in P with angle(v_k,Vv_k)>=theta_k. |
| 110 | `DK-4.1-prop.singular-value-minimality` | `DK-4.1-prop` | `counted_result_statement` | `DK-4.1-prop` | Each singular value of (1-V)\|P is minimized at V=U with value 2 sin(theta_k/2). |
| 111 | `DK-4.1-prop.closest-q-vector-proof-step` | `DK-4.1-prop` | `proof_or_derivation_not_result` | — | The pointwise comparison uses Qx/\|\|Qx\|\| as the closest unit vector in Q-space. |
| 112 | `DK-4.1-prop.eq-4-1` | `DK-4.1-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.1) as reconstructed in the distributable TeX. |
| 113 | `DK-4.1-prop.eq-4-2` | `DK-4.1-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.2) as reconstructed in the distributable TeX. |
| 114 | `DK-4.1-cor.ui-minimality-on-p` | `DK-4.1-cor` | `counted_result_statement` | `DK-4.1-cor` | For every UI norm, \|\|(1-V)P\|\| is minimized at V=U. |
| 115 | `DK-4.2-prop.basis-sine-square-lower-bound` | `DK-4.2-prop` | `counted_result_statement` | `DK-4.2-prop` | For every orthonormal basis of P, sum sin^2 angle(v_k,Vv_k) >= sum sin^2 theta_k, including infinite RHS. |
| 116 | `DK-4.2-prop.trace-identification` | `DK-4.2-prop` | `proof_or_derivation_not_result` | — | The lower bound is identified with tr(S0* S0). |
| 117 | `DK-4.3-prop.plane-parameterization` | `DK-4.3-prop` | `proof_detail_not_in_printed_statement` | — | On each principal two-plane V has the displayed a_j,b_j parameterization. |
| 118 | `DK-4.3-prop.squared-displacement-global-minimum` | `DK-4.3-prop` | `counted_result_statement` | `DK-4.3-prop` | \|\|(1-V*)(1-V)\|\| is minimized by U for every UI norm. |
| 119 | `DK-4.3-prop.operator-norm-displacement-minimum` | `DK-4.3-prop` | `post_result_consequence_not_in_printed_statement` | — | The operator norm of 1-V is minimized by U. |
| 120 | `DK-4.3-prop.hilbert-schmidt-displacement-minimum` | `DK-4.3-prop` | `post_result_consequence_not_in_printed_statement` | — | The Hilbert--Schmidt norm of 1-V is minimized by U. |
| 121 | `DK-4.3-prop.arbitrary-ui-displacement-warning` | `DK-4.3-prop` | `post_result_consequence_not_in_printed_statement` | — | Arbitrary UI norms of 1-V need not be minimized by U. |
| 122 | `DK-4.3-prop.eq-4-3` | `DK-4.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.3) as reconstructed in the distributable TeX. |
| 123 | `DK-4.3-prop.eq-4-4` | `DK-4.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.4) as reconstructed in the distributable TeX. |
| 124 | `DK-4.3-prop.eq-4-5` | `DK-4.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.5) as reconstructed in the distributable TeX. |
| 125 | `DK-4.3-prop.eq-4-6` | `DK-4.3-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (4.6) as reconstructed in the distributable TeX. |
| 126 | `DK-4.4-prop.example4-1-real-reflection` | `DK-4.4-prop` | `remark_or_example_not_result` | — | Example 4.1 gives a real reflection with singular values 2,0 versus two equal direct-rotation singular values and defeats the Ky Fan 2 norm for theta>pi/3. |
| 127 | `DK-4.4-prop.example4-2-complex-phase` | `DK-4.4-prop` | `remark_or_example_not_result` | — | Example 4.2 uses V=e^{i delta}U and shows the full-displacement UI minimum can fail in complex space. |
| 128 | `DK-4.4-prop.printed-proposition4-4` | `DK-4.4-prop` | `counted_result_statement` | `DK-4.4-prop` | The paper asserts that in real space with Theta<=pi/3, U minimizes \|\|1-V\|\| for every UI norm. |
| 129 | `DK-4.4-prop.printed-sharp-threshold` | `DK-4.4-prop` | `sharpness_commentary_not_designated_result` | — | The paper asserts the pi/3 threshold is sharp in view of the examples. |
| 130 | `DK-5.1-thm.banach-hypotheses` | `DK-5.1-thm` | `counted_result_hypothesis` | `DK-5.1-thm` | Banach-space theorem with \|\|B\|\|<=alpha and \|\|A^{-1}\|\|<=(alpha+delta)^{-1}, compatible cross norm. |
| 131 | `DK-5.1-thm.sylvester-lower-bound` | `DK-5.1-thm` | `counted_result_statement` | `DK-5.1-thm` | AX-XB=C implies \|\|C\|\|>=delta\|\|X\|\|. |
| 132 | `DK-5.1-thm.roles-interchange` | `DK-5.1-thm` | `post_result_scope_remark_not_in_printed_statement` | — | A and B roles/hypotheses may be interchanged. |
| 133 | `DK-5.1-thm.one-sided-unbounded-extension` | `DK-5.1-thm` | `post_result_scope_remark_not_in_printed_statement` | — | The proof covers densely-defined unbounded A with bounded inverse hypothesis while B,X remain bounded. |
| 134 | `DK-5-hermitian-inequalities.pairwise-gap-hypothesis` | `DK-5-hermitian-inequalities` | `background_theory_not_designated_result` | — | Hermitian A,B have pairwise spectral distance at least delta. |
| 135 | `DK-5-hermitian-inequalities.operator-norm-constant-one-fails` | `DK-5-hermitian-inequalities` | `background_theory_not_designated_result` | — | The operator-norm analogue with constant 1 can fail. |
| 136 | `DK-5-hermitian-inequalities.rank-factor-not-best` | `DK-5-hermitian-inequalities` | `sharpness_commentary_not_designated_result` | — | Equation (5.2) is not best possible unless rank C<=1. |
| 137 | `DK-5-hermitian-inequalities.universal-constant-question` | `DK-5-hermitian-inequalities` | `open_question` | — | The source asks whether the rank factor can be replaced by a universal constant. |
| 138 | `DK-5-hermitian-inequalities.constant-one-explicit-counterexample` | `DK-5-hermitian-inequalities` | `remark_or_example_not_result` | — | The displayed 2x2 A,B,X example rules out universal constant 1. |
| 139 | `DK-5-hermitian-inequalities.eq-5-1` | `DK-5-hermitian-inequalities` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (5.1) as reconstructed in the distributable TeX. |
| 140 | `DK-5-hermitian-inequalities.eq-5-2` | `DK-5-hermitian-inequalities` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (5.2) as reconstructed in the distributable TeX. |
| 141 | `DK-5.2-thm.hilbert-unbounded-hypotheses` | `DK-5.2-thm` | `counted_result_hypothesis` | `DK-5.2-thm` | Theorem 5.2 gives the Hilbert-space unbounded Sylvester setup with separated spectra and domain/core hypotheses. |
| 142 | `DK-5.2-thm.hilbert-unbounded-conclusion` | `DK-5.2-thm` | `counted_result_statement` | `DK-5.2-thm` | The corresponding delta\|\|X\|\| lower bound holds in the stated UI/ideal norm scope. |
| 143 | `DK-5.1-lem.strong-cutoff-convergence` | `DK-5.1-lem` | `counted_result_statement` | `DK-5.1-lem` | The spectral-cutoff approximants converge strongly in the manner stated and support the unbounded proof. |
| 144 | `DK-6.1-lem.ordered-sylvester-forward` | `DK-6.1-lem` | `counted_result_statement` | `DK-6.1-lem` | The ordered spectral separation implies the stated Sylvester/UI-norm lower bound. |
| 145 | `DK-6.1-lem.ordered-sylvester-converse` | `DK-6.1-lem` | `counted_result_statement` | `DK-6.1-lem` | The source includes the converse characterization used in the single-angle proof. |
| 146 | `DK-6.2-lem.pinching-contraction` | `DK-6.2-lem` | `counted_result_statement` | `DK-6.2-lem` | The reflection/pinching operation contracts every unitary-invariant norm in the stated setup. |
| 147 | `DK-6.1-prop.sine-proof-residual-identity` | `DK-6.1-prop` | `proof_detail_not_in_printed_statement` | — | The symmetric sine proof rewrites the relevant off-diagonal block as the Sylvester residual identity. |
| 148 | `DK-6.1-prop.symmetric-sine-theorem` | `DK-6.1-prop` | `counted_result_statement` | `DK-6.1-prop` | Proposition 6.1 gives the symmetric sine-theta conclusion under two-sided spectral placement. |
| 149 | `DK-6.1-prop.source-counterexample-need-two-sided` | `DK-6.1-prop` | `remark_or_example_not_result` | — | The source exhibits the failure of the ambient/symmetric conclusion when the needed two-sided placement is dropped. |
| 150 | `DK-6.1-prop.eq-6-1` | `DK-6.1-prop` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.1) as reconstructed in the distributable TeX. |
| 151 | `DK-6.1-thm.generalized-sine-hypotheses` | `DK-6.1-thm` | `counted_result_hypothesis` | `DK-6.1-thm` | The generalized sine theorem allows nonisometric E0 with E0*E0 >= epsilon^2 and the stated spectral separation. |
| 152 | `DK-6.1-thm.generalized-sine-conclusion` | `DK-6.1-thm` | `counted_result_statement` | `DK-6.1-thm` | delta epsilon \|\|sin Theta0\|\| <= \|\|R\|\|. |
| 153 | `DK-6.1-thm.unequal-dimension-scope` | `DK-6.1-thm` | `counted_result_scope` | `DK-6.1-thm` | The generalized theorem allows unequal-dimensional comparison subspaces as stated. |
| 154 | `DK-6.2-thm.second-generalized-sine` | `DK-6.2-thm` | `counted_result_statement` | `DK-6.2-thm` | The second generalized sine theorem gives the Hilbert--Schmidt estimate under pairwise spectral separation. |
| 155 | `DK-6.2-thm.rank-corrected-operator-consequence` | `DK-6.2-thm` | `post_result_consequence_not_in_printed_statement` | — | The stated rank-corrected operator-norm consequence follows. |
| 156 | `DK-6.3-thm.tangent-setup-identities` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Equations (6.2)--(6.6) provide the block identities used in the generalized tangent proof. |
| 157 | `DK-6.3-thm.example6-1` | `DK-6.3-thm` | `remark_or_example_not_result` | — | Example 6.1 gives the explicit 2x2 counterexample showing one-sided placement is essential for the tangent conclusion. |
| 158 | `DK-6.3-thm.generalized-tangent-theorem` | `DK-6.3-thm` | `counted_result_statement` | `DK-6.3-thm` | Theorem 6.3 gives the generalized tangent residual bound with its exact source hypotheses. |
| 159 | `DK-6.3-thm.eq-6-2` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.2) as reconstructed in the distributable TeX. |
| 160 | `DK-6.3-thm.eq-6-3` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.3) as reconstructed in the distributable TeX. |
| 161 | `DK-6.3-thm.eq-6-4` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.4) as reconstructed in the distributable TeX. |
| 162 | `DK-6.3-thm.eq-6-5` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.5) as reconstructed in the distributable TeX. |
| 163 | `DK-6.3-thm.eq-6-6` | `DK-6.3-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.6) as reconstructed in the distributable TeX. |
| 164 | `DK-6-appendix.unbounded-sine-extension` | `DK-6-appendix` | `expository_commentary_not_result` | — | The sine theorem extends to unbounded operators via bounded residual/common-domain hypotheses. |
| 165 | `DK-6-appendix.unbounded-tangent-extension` | `DK-6-appendix` | `expository_commentary_not_result` | — | The tangent theorem requires the stronger approximation argument recorded in the Appendix. |
| 166 | `DK-6-appendix.appendix-approximation-chain` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Equations (6.7)--(6.11) form the approximation chain controlling singular directions and passing to all UI norms. |
| 167 | `DK-6-appendix.appendix-all-ui-limit` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | The epsilon-to-zero argument completes the bound-norm case and then all UI norms. |
| 168 | `DK-6-appendix.eq-6-7` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.7) as reconstructed in the distributable TeX. |
| 169 | `DK-6-appendix.eq-6-8` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.8) as reconstructed in the distributable TeX. |
| 170 | `DK-6-appendix.eq-6-9` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.9) as reconstructed in the distributable TeX. |
| 171 | `DK-6-appendix.eq-6-10` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.10) as reconstructed in the distributable TeX. |
| 172 | `DK-6-appendix.eq-6-11` | `DK-6-appendix` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (6.11) as reconstructed in the distributable TeX. |
| 173 | `DK-6.3-lem.approximation-number-leakage` | `DK-6.3-lem` | `counted_result_statement` | `DK-6.3-lem` | Lemma 6.3 controls the approximation/singular-number leakage used in the Appendix, including the stated finite and real forms. |
| 174 | `DK-7-sin2-proof.reflection-setup` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | The reflection construction converts the double-angle geometry into a single-angle comparison. |
| 175 | `DK-7-sin2-proof.ambient-sin2` | `DK-7-sin2-proof` | `restatement_of_counted_result` | — | The Section 7 proof derives the ambient sin2Theta perturbation estimate. |
| 176 | `DK-7-sin2-proof.directed-sin2` | `DK-7-sin2-proof` | `restatement_of_counted_result` | — | It separately derives the directed sin2Theta0 residual estimate. |
| 177 | `DK-7-sin2-proof.factor-one-directed-residual-refinement` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | The directed block residual estimate has the source factor-one intermediate bound before the headline factor 2 form. |
| 178 | `DK-7-sin2-proof.swap-asymmetry` | `DK-7-sin2-proof` | `expository_commentary_not_result` | — | The source records the asymmetry involved in swapping the two operators/subspaces in the residual form. |
| 179 | `DK-7-sin2-proof.eq-7-1` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.1) as reconstructed in the distributable TeX. |
| 180 | `DK-7-sin2-proof.eq-7-2` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.2) as reconstructed in the distributable TeX. |
| 181 | `DK-7-sin2-proof.eq-7-3` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.3) as reconstructed in the distributable TeX. |
| 182 | `DK-7-sin2-proof.eq-7-4` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.4) as reconstructed in the distributable TeX. |
| 183 | `DK-7-sin2-proof.eq-7-5` | `DK-7-sin2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.5) as reconstructed in the distributable TeX. |
| 184 | `DK-7-tan2-proof.tan2-block-identity` | `DK-7-tan2-proof` | `proof_or_derivation_not_result` | — | Equation (7.6) gives the decisive tangent double-angle block identity. |
| 185 | `DK-7-tan2-proof.cos2-pole-exclusion` | `DK-7-tan2-proof` | `proof_or_derivation_not_result` | — | The singular-vector argument proves the relevant cos(2 theta_j) factors do not vanish from the source hypotheses. |
| 186 | `DK-7-tan2-proof.ambient-tan2` | `DK-7-tan2-proof` | `restatement_of_counted_result` | — | The proof yields the ambient tan2Theta perturbation estimate. |
| 187 | `DK-7-tan2-proof.directed-tan2` | `DK-7-tan2-proof` | `restatement_of_counted_result` | — | The proof yields the directed tan2Theta0 residual estimate. |
| 188 | `DK-7-tan2-proof.eq-7-6` | `DK-7-tan2-proof` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (7.6) as reconstructed in the distributable TeX. |
| 189 | `DK-8.1-thm.branch-problem` | `DK-8.1-thm` | `pre_result_motivation_not_result` | — | Small double-angle trigonometric quantities alone do not select angles near zero; the chosen reducing subspace matters. |
| 190 | `DK-8.1-thm.acute-iff-spectral-placement` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | Theta<=pi/4 iff the chosen perturbed reducing blocks lie on the corresponding sides of the gap. |
| 191 | `DK-8.1-thm.existence-correct-q` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | A reducing spectral projector Q with the required placement exists and is unique in the stated sense. |
| 192 | `DK-8.1-thm.part-i-compression` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | The upper/lower block compression inequalities of part (i). |
| 193 | `DK-8.1-thm.part-ii-eigenvalue` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | The finite-dimensional eigenvalue displacement inequalities of part (ii), with natural infinite-dimensional extensions. |
| 194 | `DK-8.1-thm.part-iii-gauge` | `DK-8.1-thm` | `counted_result_statement` | `DK-8.1-thm` | The symmetric-gauge majorization inequalities of part (iii). |
| 195 | `DK-8.1-thm.exclude-pi-over-four` | `DK-8.1-thm` | `proof_or_derivation_not_result` | — | Equations (8.1)--(8.2) exclude theta=pi/4 and then theta>pi/4 under the selected placement. |
| 196 | `DK-8.1-thm.spectral-repulsion-interpretation` | `DK-8.1-thm` | `post_result_interpretation_not_result` | — | Strong off-diagonal eigenvector rotation forces definite eigenvalue displacement as described. |
| 197 | `DK-8.1-thm.eq-8-1` | `DK-8.1-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (8.1) as reconstructed in the distributable TeX. |
| 198 | `DK-8.1-thm.eq-8-2` | `DK-8.1-thm` | `proof_or_derivation_not_result` | — | Exact mathematical content of source equation (8.2) as reconstructed in the distributable TeX. |
| 199 | `DK-8.2-thm.smallness-alternative` | `DK-8.2-thm` | `counted_result_hypothesis` | `DK-8.2-thm` | The theorem assumes either \|\|H\|\|_1<delta/2 or \|\|R\|\|_1<delta/2 plus the stated A0 interval. |
| 200 | `DK-8.2-thm.double-angle-bound-retained` | `DK-8.2-thm` | `counted_result_statement` | `DK-8.2-thm` | The corresponding sin2 double-angle estimate remains valid. |
| 201 | `DK-8.2-thm.acute-branch-conclusion` | `DK-8.2-thm` | `counted_result_statement` | `DK-8.2-thm` | Theta<pi/4. |
| 202 | `DK-8.2-thm.homotopy-proof` | `DK-8.2-thm` | `proof_or_derivation_not_result` | — | The perturbation proof uses the continuous spectral-projector homotopy and the displayed arcsine bound. |
| 203 | `DK-8.2-thm.residual-reduction` | `DK-8.2-thm` | `proof_or_derivation_not_result` | — | The residual form is reduced by changing the complementary perturbation block while preserving the residual/spectral data. |
| 204 | `DK-8.2-thm.sin2-unequal-dimension-extension` | `DK-8.2-thm` | `post_result_scope_remark_not_in_printed_statement` | — | The source states a sin2 extension to unequal comparison dimensions. |
| 205 | `DK-8.2-thm.no-tan2-unequal-dimension-extension-known` | `DK-8.2-thm` | `historical_knowledge_state` | — | No analogous tan2 extension was known. |
| 206 | `DK-9-model.real-l2-model` | `DK-9-model` | `definition_not_result` | — | The numerical model is real L2(0,1) with the free-end fourth-derivative self-adjoint closure and multiplication perturbation epsilon t. |
| 207 | `DK-9-model.perturbed-eigenproblem` | `DK-9-model` | `definition_not_result` | — | The displayed fourth-order perturbed boundary-value eigenproblem. |
| 208 | `DK-9-model.unperturbed-strict-eigenvalue-order` | `DK-9-model` | `section9_worked_example_not_result` | — | The source orders alpha1=0=alpha2<alpha3<alpha4<... with multiplicity. |
| 209 | `DK-9-model.positive-root-equation` | `DK-9-model` | `section9_worked_example_not_result` | — | For k>2, alpha_k are the positive roots of cos(alpha_k^(1/4)) cosh(alpha_k^(1/4))=1. |
| 210 | `DK-9-model.positive-spectrum-over-500` | `DK-9-model` | `section9_worked_example_not_result` | — | All positive alpha_k exceed 500. |
| 211 | `DK-9-model.zero-eigenfunctions` | `DK-9-model` | `section9_worked_example_not_result` | — | The displayed w1,w2 are orthonormal linear eigenfunctions for the zero eigenvalue. |
| 212 | `DK-9-model.lambda3-lower-bound` | `DK-9-model` | `section9_worked_example_not_result` | — | H>=0 implies lambda3>=alpha3>500. |
| 213 | `DK-9-model.initial-residual-formula` | `DK-9-model` | `section9_worked_example_not_result` | — | For A0=0, R=HE0 with the displayed residual functions r_k. |
| 214 | `DK-9-model.residual-gram` | `DK-9-model` | `section9_worked_example_not_result` | — | The displayed 2x2 R*R matrix. |
| 215 | `DK-9-model.residual-gram-eigenvalues` | `DK-9-model` | `section9_worked_example_not_result` | — | R*R has eigenvalues epsilon^2(11+-sqrt76)/30. |
| 216 | `DK-9.1-9.4.sin-bound-comparison` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | The paper notes (9.1) is sharper than the easy sin2 bound (9.2). |
| 217 | `DK-9.1-9.4.kyfan-two-term-scope` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Equations (9.3)--(9.4) use the two-term Ky Fan norm to estimate both principal angles simultaneously. |
| 218 | `DK-9.1-9.4.eq-9-1` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.1) as reconstructed in the distributable TeX. |
| 219 | `DK-9.1-9.4.eq-9-2` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.2) as reconstructed in the distributable TeX. |
| 220 | `DK-9.1-9.4.eq-9-3` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.3) as reconstructed in the distributable TeX. |
| 221 | `DK-9.1-9.4.eq-9-4` | `DK-9.1-9.4` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.4) as reconstructed in the distributable TeX. |
| 222 | `DK-9.5-9.7.rayleigh-ritz-matrix` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The displayed Rayleigh--Ritz matrix is E0*(A+H)E0. |
| 223 | `DK-9.5-9.7.refined-residual-gram` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The displayed refined residual Gram matrix and its one/two-term norm equal epsilon/sqrt15. |
| 224 | `DK-9.5-9.7.tangent-gap` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The tangent gap may be taken as 500-0.7887 epsilon. |
| 225 | `DK-9.5-9.7.kyfan-tan-bound` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The same RHS as (9.6) bounds tan theta1+tan theta2 in the two-term Ky Fan norm. |
| 226 | `DK-9.5-9.7.offdiagonal-complement-choice` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | For tan2 the complementary block is chosen as E1*(A+H)E1>500 to obtain an off-diagonal comparison. |
| 227 | `DK-9.5-9.7.kyfan-tan2-bound` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | The same RHS as (9.7) bounds tan2theta1+tan2theta2 in the two-term Ky Fan norm. |
| 228 | `DK-9.5-9.7.eq-9-5` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.5) as reconstructed in the distributable TeX. |
| 229 | `DK-9.5-9.7.eq-9-6` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.6) as reconstructed in the distributable TeX. |
| 230 | `DK-9.5-9.7.eq-9-7` | `DK-9.5-9.7` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.7) as reconstructed in the distributable TeX. |
| 231 | `DK-9.8.weinberger-sine-square` | `DK-9.8` | `external_result_not_dk_result` | — | Weinberger method gives the displayed sine-square estimate from Ritz upper/lower bounds and the 500 separation. |
| 232 | `DK-9.8.lehmann-best-lower-bounds` | `DK-9.8` | `external_result_not_dk_result` | — | The best lower bounds deducible from the stated 2+1 data are the two lower eigenvalues of the displayed 3x3 matrix. |
| 233 | `DK-9.8.lower-bound-asymptotic` | `DK-9.8` | `external_result_not_dk_result` | — | The source records the strict inequality and O(epsilon^4) asymptotic for alpha_hat-alpha_check. |
| 234 | `DK-9.8.angle-meaning-distinction` | `DK-9.8` | `section9_worked_example_not_result` | — | phi_k are individual trial-vector-to-subspace angles whereas theta1 is the largest subspace angle. |
| 235 | `DK-9.8.sine-square-sum-identity` | `DK-9.8` | `section9_worked_example_not_result` | — | sin^2 phi1+sin^2 phi2 = sin^2 theta1+sin^2 theta2. |
| 236 | `DK-9.8.direct-one-vector-sharper-bounds` | `DK-9.8` | `section9_worked_example_not_result` | — | Theorem 6.3 applied to each trial vector gives the displayed sharper tan phi_k bounds. |
| 237 | `DK-9.8.methods-complementary` | `DK-9.8` | `section9_worked_example_not_result` | — | The source concludes the two methods are complementary rather than one supplanting the other. |
| 238 | `DK-9.8.eq-9-8` | `DK-9.8` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.8) as reconstructed in the distributable TeX. |
| 239 | `DK-9-infinite-residual-counterexample.l2-geometric-vector-example` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | The geometric sequence e and diagonal operator give a trial vector just outside the operator domain. |
| 240 | `DK-9-infinite-residual-counterexample.arbitrarily-small-domain-repair` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | The source asserts an arbitrarily small modification repairs the domain defect. |
| 241 | `DK-9-infinite-residual-counterexample.rayleigh-quotient` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | The formal Rayleigh quotient is 1+mu. |
| 242 | `DK-9-infinite-residual-counterexample.residual-infinite` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | The residual has infinite norm so the paper residual theorems give no estimate. |
| 243 | `DK-9-infinite-residual-counterexample.weinberger-still-applies` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | Independent lower eigenvalue bounds still allow the displayed Weinberger estimate. |
| 244 | `DK-9-infinite-residual-counterexample.best-lower-bound-result` | `DK-9-infinite-residual-counterexample` | `section9_worked_example_not_result` | — | At the best lower bounds the true sin theta=mu satisfies mu<=mu/sqrt(1-mu). |
| 245 | `DK-9.9-9.11.angle-factorization` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | cos omega_k=cos eta_k cos psi_k and omega_k^2<=psi_k^2+eta_k^2. |
| 246 | `DK-9.9-9.11.schur-correction-bound` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | The Schur correction is bounded by the displayed off-diagonal 2x2 matrix and operator inequalities. |
| 247 | `DK-9.9-9.11.tan2-psi-bound` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | The tan2 theorem yields the displayed bound for psi_k. |
| 248 | `DK-9.9-9.11.acute-psi-selection` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Theorem 8.1 selects 0<=psi_k<pi/4 and yields the stated arctan bound. |
| 249 | `DK-9.9-9.11.eta-bound` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Equation (9.10) yields the displayed tan eta_k bound. |
| 250 | `DK-9.9-9.11.final-omega-bounds` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Combining psi_k and eta_k yields the two final omega_k bounds. |
| 251 | `DK-9.9-9.11.best-possible-3x3-claim` | `DK-9.9-9.11` | `deferred_unproved_claim` | — | The source says the best possible bound from the stated data is the coordinate/eigenvector angle of the 3x3 comparison matrix. |
| 252 | `DK-9.9-9.11.best-possible-proof-deferred` | `DK-9.9-9.11` | `deferred_unproved_claim` | — | Proof of that best-possible assertion is deferred to the unresolved three-way-subspace Question 10.2. |
| 253 | `DK-9.9-9.11.eq-9-9` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.9) as reconstructed in the distributable TeX. |
| 254 | `DK-9.9-9.11.eq-9-10` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.10) as reconstructed in the distributable TeX. |
| 255 | `DK-9.9-9.11.eq-9-11` | `DK-9.9-9.11` | `section9_worked_example_not_result` | — | Exact mathematical content of source equation (9.11) as reconstructed in the distributable TeX. |
| 256 | `DK-10.1.question` | `DK-10.1` | `open_question` | — | With only pairwise spectral distance delta, how sharply can Theta0 be bounded in terms of R? |
| 257 | `DK-10.2.three-way-setup` | `DK-10.2` | `definition_not_result` | — | Three-way orthogonal decompositions are encoded by the 3x3 block matrix E_i*F_j. |
| 258 | `DK-10.2.question` | `DK-10.2` | `open_question` | — | Can nearby reducing three-way decompositions be estimated through off-diagonal blocks analogously to the two-way theory? |
| 259 | `DK-10.3.question` | `DK-10.3` | `open_question` | — | Find best possible bounds combining eigenvalue and eigenvector changes. |
| 260 | `DK-10.4.spectral-functional-calculus` | `DK-10.4` | `definition_not_result` | — | The source recalls f(A) from the spectral resolution of self-adjoint A. |
| 261 | `DK-10.4.step-function-specialization` | `DK-10.4` | `section10_motivation_not_result` | — | For the gap step function under tan2 hypotheses, f(A)=P, f(A+H)=Q, f(A0)=I. |
| 262 | `DK-10.4.ambient-functional-change` | `DK-10.4` | `section10_motivation_not_result` | — | \|\|f(A+H)-f(A)\|\|=\|\|Q-P\|\|=\|\|sin Theta\|\|. |
| 263 | `DK-10.4.ambient-tan2-bound` | `DK-10.4` | `restatement_of_counted_result` | — | delta\|\|tan 2Theta\|\|<=2\|\|H\|\|. |
| 264 | `DK-10.4.directed-functional-change` | `DK-10.4` | `section10_motivation_not_result` | — | \|\|(f(A+H)-f(A))E0\|\|=\|\|Qperp E0\|\|=\|\|sin Theta0\|\|. |
| 265 | `DK-10.4.directed-tan2-bound` | `DK-10.4` | `restatement_of_counted_result` | — | delta\|\|tan 2Theta0\|\|<=2\|\|R\|\|. |
| 266 | `DK-10.4.question` | `DK-10.4` | `open_question` | — | Seek analogous perturbation bounds for more general functions f. |

# Final independent conclusion

- **All 266 source-fidelity atoms reviewed for omission/classification:** yes / no
- **All 29 counted DK-established results reviewed against their exact printed boundaries:** yes / no
- **28 currently terminal results independently reconfirmed:** yes / no
- **1 currently nonterminal/pending results resolved by this audit:** yes / no
- **Any excluded fidelity atom that actually belongs to a counted result statement:** yes / no
- **Any Davis--Kahan-established named/headline result missing from the 29-result inventory:** yes / no
- **Any non-established/open/deferred material incorrectly included in the denominator:** yes / no
- **Compiler certificate clean and complete:** yes / no
- **Is the repository's explicitly limited claim of 100% result-level Davis--Kahan 1970 formalization justified?** yes / no / uncertain

## Findings requiring action

1. _none recorded yet_
