# Davis--Kahan 1970 full source census

Base commit: `7463ca25c64a46c48411a2769b47714889974a97`.

This is the public, independently worded theorem-by-theorem ledger for the
full paper. The maintained modernized transcription is used only as a local
comparison source and is intentionally not distributed. The JSON file is
authoritative; this Markdown file is generated from it.

## Status summary

| Status | Count |
| --- | ---: |
| `compiled_exact` | 7 |
| `compiled_specialization` | 2 |
| `compiled_general_infrastructure` | 7 |
| `candidate_under_repair` | 13 |
| `partial_or_wrapper_missing` | 5 |
| `not_represented` | 3 |
| `not_started` | 6 |
| `resolved_by_modern_development` | 1 |
| `not_a_completion_obligation` | 3 |
| `refuted_as_transcribed` | 1 |

## Status meanings

- **`compiled_exact`** -- An exact source-facing theorem or construction is compiled on the base.
- **`compiled_specialization`** -- A useful compiled specialization exists, but not the full source scope.
- **`compiled_general_infrastructure`** -- The mathematics exists in a general reusable form, though a source-numbered wrapper may be absent.
- **`candidate_under_repair`** -- A statement/candidate exists in the full Part III repair campaign but is not compiler-certified on this base.
- **`partial_or_wrapper_missing`** -- Substantial ingredients exist, but the exact source theorem is not represented or audited.
- **`not_represented`** -- No matching declaration was found.
- **`not_started`** -- The source artifact has no formalization campaign yet.
- **`resolved_by_modern_development`** -- An open source question has a partial or norm-specific modern resolution in the repository.
- **`not_a_completion_obligation`** -- An open question or exposition item should be documented but is not proof debt.
- **`refuted_as_transcribed`** -- The transcribed statement is disproved by a compiled Lean counterexample; the census row records the refutation pending a re-audit of the printed source text.

## Source ledger

### Section 1

#### Section 1, equations (1.1)–(1.8): Two reducing decompositions and the residual

- **Kind:** `construction`
- **Status:** `compiled_general_infrastructure`
- **Mathematics:** Block decompositions for A and A+H, trial and exact coordinate maps, and R = (A+H)E0 - E0 A0.
- **Current Lean references:** `ForMathlib.DavisKahan1970.PaperTheorem61Data`, `ForMathlib.DavisKahan1970.UnboundedSinThetaData`
- **Assessment:** The exact notation is distributed across the Section 6 source data records rather than exposed as a Section 1 facade.
- **Next action:** Add source-facing construction aliases only if useful for the full-paper facade.

#### Section 1, equations (1.9)–(1.13): Unitary-invariant norms and Fan dominance

- **Kind:** `framework`
- **Status:** `compiled_general_infrastructure`
- **Mathematics:** Norms determined by singular values, contraction laws, Ky Fan prefix norms, and dominance by all prefixes.
- **Current Lean references:** `ForMathlib.DavisKahan1970.PaperUnitaryInvariantNorm`, `ForMathlib.DavisKahan1970.PaperUnitaryInvariantNorm.prefixGauge_le_of_all_kyFan_le_hetero`
- **Assessment:** The source norm correspondence is part of the clean Section 6 surface.
- **Next action:** Retain as shared prerequisite; no new mathematics required.

### Section 2

#### Section 2, sin theta theorem: Single-angle sine theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_exact`
- **Mathematics:** Interval/exterior spectral separation gives delta times the directed sine norm bounded by the residual norm for every source unitary-invariant norm.
- **Current Lean references:** `ForMathlib.DavisKahan1970.sinTheta`, `ForMathlib.DavisKahan1970.generalizedSinTheta`
- **Assessment:** The definitive source form is Theorem 6.1; real, complex, bounded, unbounded, and arbitrary-representative forms are present.
- **Next action:** No mathematical gap. Keep the source audit synchronized.

#### Section 2, tan theta theorem: Single-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `candidate_under_repair`
- **Mathematics:** One-sided spectral separation plus the Rayleigh–Ritz/off-diagonal condition gives residual and perturbation tangent bounds in every unitary-invariant norm.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`, `ForMathlib.DavisKahanTheory.tanTheta_genuineSpectrum`
- **Assessment:** The finite arbitrary-UI-norm theorem is compiled. General Hilbert-space and exact source wrappers are in the Part III repair campaign.
- **Next action:** Certify the Hilbert-space source wrapper and exact perturbation companion.

#### Section 2, sin 2 theta theorem: Double-angle sine theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `candidate_under_repair`
- **Mathematics:** A spectral gap between the two exact blocks yields residual and perturbation bounds for sin(2 Theta), with sharp factor two.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.partIII_sinTwoTheta_uiNorm`, `ForMathlib.DavisKahan.sinTwoTheta_addBounded_of_spectrum_gap`
- **Assessment:** Finite arbitrary-UI-norm forms are compiled; general Hilbert-space source forms are under repair.
- **Next action:** Certify source-general residual and perturbation forms.

#### Section 2, tan 2 theta theorem: Double-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `candidate_under_repair`
- **Mathematics:** Fully off-diagonal perturbations across an ordered gap give residual and perturbation tan(2 Theta) bounds with factor two.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.partIII_tanTwoTheta_opNorm`, `ForMathlib.DavisKahanExt.tanTwoTheta_offDiagonalC_of_weighted_sine`
- **Assessment:** The finite operator-norm theorem is compiled. The source arbitrary-UI-norm Hilbert-space endpoint and branch selection are not yet certified.
- **Next action:** Complete the general UI-norm source theorem and its selected acute branch.

#### Section 2, paragraph after four theorems: Best constants and simultaneous equality

- **Kind:** `source_claim`
- **Status:** `candidate_under_repair`
- **Mathematics:** All four constants are optimal in two dimensions, and finite direct sums realize equality simultaneously for all unitary-invariant norms.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.sinTheta_constant_optimal`, `ForMathlib.DavisKahanTheory.sinTwoTheta_constant_optimal`, `ForMathlib.DavisKahanTheory.single_double_sine_tangent_ratios_tendsto_one`
- **Assessment:** Sine sharpness and finite multiplicity are compiled; full quartet simultaneous equality remains in the Part III campaign.
- **Next action:** Audit tangent and double-angle equality models against the exact source claim.

#### Section 2, final paragraphs: Unbounded self-adjoint scope

- **Kind:** `scope_claim`
- **Status:** `partial_or_wrapper_missing`
- **Mathematics:** The four theorem families extend to unbounded self-adjoint operators under bounded perturbation or residual assumptions, with analytic work concentrated in Theorem 5.2 and the Section 6 appendix.
- **Current Lean references:** `ForMathlib.DavisKahan1970.canonical_generalizedSinTheta`, `ForMathlib.DavisKahan1970.unbounded_sinTheta_opNorm`
- **Assessment:** The sine family is complete in source scope. Other theorem families have partial unbounded APIs but no full source audit.
- **Next action:** Track unbounded tangent and double-angle source coverage separately.

### Section 3

#### Definition 3.1: Direct rotation

- **Kind:** `definition`
- **Status:** `candidate_under_repair`
- **Mathematics:** A unitary intertwining the two projections whose diagonal cosine blocks are positive and whose off-diagonal sine blocks are adjoints.
- **Current Lean references:** `ForMathlib.DavisKahan1970.complex_directRotation`, `ForMathlib.DavisKahan.spectraCanonicalIntertwiner`
- **Assessment:** Acute complex and finite constructions exist; exact nonacute source scope is not yet unified.
- **Next action:** Add a source-facing definition covering the source existence regimes.

#### Definition 3.2: Acute case

- **Kind:** `definition`
- **Status:** `compiled_general_infrastructure`
- **Mathematics:** Both crossed intersections P ∩ Q-perp and P-perp ∩ Q vanish.
- **Current Lean references:** `ForMathlib.IsAcute`
- **Assessment:** The predicate is broadly used but lacks a numbered source alias.
- **Next action:** Add a source alias only if the facade benefits.

#### Proposition 3.1: Acute direct rotation existence and uniqueness

- **Kind:** `proposition`
- **Status:** `candidate_under_repair`
- **Mathematics:** In the acute case the direct rotation exists, is unique, and positivity of its diagonal blocks characterizes it.
- **Current Lean references:** `ForMathlib.DavisKahan1970.complex_directRotation`, `ForMathlib.DavisKahan1970.complex_directRotation_unique`
- **Assessment:** The main acute construction and uniqueness are present; the exact characterization by positivity needs source-level verification.
- **Next action:** Prove or wrap the positivity characterization explicitly.

#### Proposition 3.2: Nonacute existence criterion

- **Kind:** `proposition`
- **Status:** `not_represented`
- **Mathematics:** A direct rotation exists exactly when the two crossed intersections have equal dimension; it is then nonunique.
- **Current Lean references:** none identified
- **Assessment:** No exact general Hilbert-space declaration was found.
- **Next action:** State the cardinal/dimension-balanced existence theorem conservatively; finite and infinite cases may need separate APIs.

#### Proposition 3.3: Principal square-root characterization

- **Kind:** `proposition`
- **Status:** `partial_or_wrapper_missing`
- **Mathematics:** Every direct rotation is a principal square root of the product of the two reflections; conversely a suitable principal square root is a direct rotation.
- **Current Lean references:** `ForMathlib.DavisKahan1970.complex_directRotation_sq`
- **Assessment:** The square identity and acute spectral branch exist; the source converse with the crossed-intersection mapping condition is not exposed.
- **Next action:** Add the converse or record the exact missing nonacute hypothesis.

#### Proposition 3.4: Square as a direct rotation

- **Kind:** `proposition`
- **Status:** `candidate_under_repair`
- **Mathematics:** When the cosine block squared is at least one half, U squared is the direct rotation from the reflected subspace to the target subspace.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.directRotation_sq`, `ForMathlib.DavisKahan1970.complex_directRotation_sq`
- **Assessment:** Square identities exist; exact source mapping between Q-minus and Q needs verification.
- **Next action:** Add an exact source wrapper after the direct-rotation repair lands.

#### Theorem 3.1: Classification of pairs of subspaces

- **Kind:** `theorem`
- **Status:** `not_represented`
- **Mathematics:** Spectral multiplicity functions of the two angle operators classify dimension-compatible subspace pairs up to isometric equivalence.
- **Current Lean references:** none identified
- **Assessment:** The current angle API does not provide this full classification theorem.
- **Next action:** Develop a two-projection canonical-decomposition classification, likely using Spectra/Halmos infrastructure.

#### Corollary 3.1: Compact classification by angle eigenvalues

- **Kind:** `corollary`
- **Status:** `not_represented`
- **Mathematics:** When the cross projection is compact, the decreasing angle eigenvalue lists, including possible zero multiplicity, classify the pair.
- **Current Lean references:** none identified
- **Assessment:** Depends on Theorem 3.1 plus compact spectral classification.
- **Next action:** Defer until the general classification and compact spectral multiplicity bridge exist.

#### Proposition 3.5: Angle commutation and eigenspace geometry

- **Kind:** `proposition`
- **Status:** `partial_or_wrapper_missing`
- **Mathematics:** The full angle commutes with both projections, the quarter-turn and direct rotation; its eigenspaces are maximal reducing constant-angle subspaces in the acute case.
- **Current Lean references:** `ForMathlib.DavisKahan1970.bounded_angle_commute`, `ForMathlib.DavisKahan1970.bounded_sinAngleOperatorC_norm`
- **Assessment:** Commutation identities are present, but the maximal eigenspace characterization is not represented.
- **Next action:** Separate the reusable commutation theorem from the source-specific maximality result.

#### Corollary 3.2: Reversal symmetry

- **Kind:** `corollary`
- **Status:** `candidate_under_repair`
- **Mathematics:** Swapping P and Q leaves the angle operator unchanged and reverses the quarter-turn operator.
- **Current Lean references:** `ForMathlib.DavisKahan1970.complex_directRotation_reversal`, `ForMathlib.DavisKahanTheory.directRotation_symm`
- **Assessment:** Direct-rotation reversal is represented; the exact angle/J statement needs a source wrapper.
- **Next action:** Add the source-facing angle and quarter-turn reversal theorem.

### Section 4

#### Proposition 4.1: Pointwise and singular-value extremality of the direct rotation

- **Kind:** `proposition`
- **Status:** `compiled_general_infrastructure`
- **Mathematics:** For any unitary carrying P to Q, an orthonormal sequence experiences angles at least the principal angles; equivalently the singular values of (1-V)|P are minimized by the direct rotation and equal 2 sin(theta_k/2).
- **Current Lean references:** `ForMathlib.DavisKahanTheory.singularValues_restrictedDisplacement_le`, `ForMathlib.DavisKahanTheory.singularValues_restrictedDisplacement_directRotation`
- **Assessment:** The finite pointwise singular-value theorem is compiled: every singular value of the restricted displacement (1-V)P is minimized by the direct rotation, whose values are the doubled half-angle sines 2 sin(theta_k/2).  A source-numbered wrapper and the infinite-dimensional scope remain open.
- **Next action:** Add a DavisKahan1970 source wrapper and audit the infinite-dimensional statement.

#### Corollary 4.1: UI-norm minimality of direct rotation displacement

- **Kind:** `corollary`
- **Status:** `compiled_general_infrastructure`
- **Mathematics:** The direct rotation minimizes the norm of (1-V)P for every unitary-invariant norm.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.uiNorm_restrictedDisplacement_le`, `ForMathlib.DavisKahanTheory.directRotation_minimizes_restrictedDisplacement_uiNorm`
- **Assessment:** Compiled without any angle restriction, for every unitarily invariant norm, over every RCLike field (finite dimension).  The earlier note conflating this row with Proposition 4.4 is resolved: the corollary concerns the restricted displacement and needs no angle hypothesis.
- **Next action:** Add a DavisKahan1970 source wrapper and audit the infinite-dimensional statement.

#### Proposition 4.2: Basis-angle square-sum extremality

- **Kind:** `proposition`
- **Status:** `compiled_specialization`
- **Mathematics:** For every orthonormal basis of P, the sum of squared displacement sines under V dominates the sum of squared principal sines.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles`
- **Assessment:** The finite orthonormal-basis displacement-energy extremality is compiled via the nuclear-norm specialization of the displacement-square majorization.
- **Next action:** Determine the exact infinite-dimensional summability convention of the source statement.

#### Proposition 4.3: Squared displacement UI-norm minimality

- **Kind:** `proposition`
- **Status:** `compiled_general_infrastructure`
- **Mathematics:** The direct rotation minimizes the UI norm of (1-V*) (1-V).
- **Current Lean references:** `ForMathlib.DavisKahanTheory.directRotation_displacementSquare_kyFan`, `ForMathlib.DavisKahanTheory.directRotation_displacementSquare_uiNorm`, `ForMathlib.DavisKahanTheory.directRotation_minimizes_displacementSquare_uiNorm`
- **Assessment:** Compiled for every unitarily invariant norm over every RCLike field (finite dimension), via Fan-Hoffman majorization of the pinched competitor and two-block pinching contraction.
- **Next action:** Add a DavisKahan1970 source wrapper and audit the infinite-dimensional statement.

#### Proposition 4.4: Real-space full displacement minimality below pi/3

- **Kind:** `proposition`
- **Status:** `refuted`
- **Mathematics:** In a real Hilbert space, if the maximal angle is at most pi/3, the direct rotation minimizes every UI norm of 1-V.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.shortRotation_fullDisplacement_refuted`, `ForMathlib.DavisKahanTheory.DavisKahanProposition4_4_Finite`, `ForMathlib.DavisKahanTheory.not_davisKahanProposition4_4_Finite`
- **Assessment:** The transcribed claim is false: a compiled R^4 counterexample exhibits an acute pair with both principal angles pi/4 and a competitor unitary carrying P to Q whose full displacement 1-V has trace norm 2 sqrt 2, strictly below the direct rotation value 4 sqrt(2 - sqrt 2).  The competitor mixes the equal-angle multiplicity space (rotation angles 0 and pi/2), an obstruction available at every angle threshold; the same family refutes the closing conjecture of Davis 1958.  Operator-norm and squared-displacement consequences survive via 4.1/4.3.
- **Next action:** None outstanding.  The source re-audit is done: the printed Proposition 4.4 carries no hypothesis restricting the competitor class, excluding multiplicity mixing, or replacing the full displacement, so the refutation applies to the claim as printed.  The defect is localized to equation (4.3), whose derivation from (1.12) needs superadditivity of the Ky Fan sum across an orthogonal decomposition of the domain; range orthogonality fails.  The block-level claim the printed proof body establishes (each `||K Omega_k||_2` minimized at V=U, via the pi/3 trigonometry) remains true in the counterexample.  `not_davisKahanProposition4_4_Finite` now refutes the claim in its "every UI norm" form, instantiating N at `(RectangularUnitarilyInvariantNorm.kyFan 4).toSquare`.

### Section 5

#### Theorem 5.1: Banach-space Sylvester lower bound

- **Kind:** `theorem`
- **Status:** `partial_or_wrapper_missing`
- **Mathematics:** Under a norm bound on B and an inverse norm bound on A, AX-XB=C implies ||C|| >= delta ||X|| for any compatible operator norm.
- **Current Lean references:** `ForMathlib.DavisKahan1970.bounded_sylvester_neumann_solution`
- **Assessment:** The repository has Neumann and ordered-gap engines, but no explicit audited source wrapper for this Banach-space theorem.
- **Next action:** Add the exact Banach-space statement and derive it from the geometric-series proof.

#### Theorem 5.2: Semibounded self-adjoint Sylvester theorem

- **Kind:** `theorem`
- **Status:** `candidate_under_repair`
- **Mathematics:** For A >= gamma+delta > gamma >= B, a bounded solution of AX=XB+C satisfies the sharp UI-norm inequality.
- **Current Lean references:** `ForMathlib.DavisKahan.directGenuineOrderedSylvesterEngine_lowerUpper`, `ForMathlib.DavisKahan1970.unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`
- **Assessment:** The completed Section 6 route contains the needed constant-one engines, while the exact source theorem alias is still in the full Part III repair campaign.
- **Next action:** Expose an exact Theorem 5.2 wrapper and include it in the full-paper audit.

#### Lemma 5.1: Strong-cutoff convergence of singular values

- **Kind:** `lemma`
- **Status:** `compiled_general_infrastructure`
- **Mathematics:** If projections converge strongly to one, each singular value of K composed with the projection converges to the corresponding singular value of K.
- **Current Lean references:** `ForMathlib.approximationSingularValue_comp_strongProjection_tendsto`
- **Assessment:** The modern approximation-number theorem is stronger and scalar-generic.
- **Next action:** Add a source-numbered wrapper if needed by the full-paper facade.

### Section 6

#### Lemma 6.1: Direct-sum UI-norm comparison and converse

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Mathematics:** Two diagonal block inequalities imply the direct-sum inequality; under equisingularity of paired blocks the converse holds.
- **Current Lean references:** `ForMathlib.DavisKahan1970.lemma6_1`, `ForMathlib.DavisKahan1970.lemma6_1_converse`
- **Assessment:** Both directions are proved; the converse should be added to the exact audit manifest.
- **Next action:** Harden the audit, not the mathematics.

#### Lemma 6.2: Reflection-pinch contraction

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Mathematics:** The sum of the two diagonal projection blocks of an operator is no larger than the operator in every source unitary-invariant norm.
- **Current Lean references:** `ForMathlib.DavisKahan1970.lemma6_2`
- **Assessment:** Part of the clean Section 6 surface.
- **Next action:** No mathematical gap.

#### Proposition 6.1: Symmetric sine theorem

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Mathematics:** Two complementary source gap hypotheses give the full sine-angle inequality with perturbation H.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Proposition6_1`
- **Assessment:** Complex and real source forms are compiled.
- **Next action:** No mathematical gap.

#### Theorem 6.1: Generalized sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Mathematics:** A lower frame bound on the trial map and interval/exterior separation give delta epsilon times any equisingular sine representative bounded by the residual.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Theorem6_1`
- **Assessment:** This is the canonical source-general sine theorem.
- **Next action:** No mathematical gap.

#### Theorem 6.2: Pairwise-gap square-norm sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Mathematics:** Arbitrary pairwise spectral distance gives the sharp Hilbert–Schmidt/square-norm residual bound.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Theorem6_2`
- **Assessment:** The defect-first pairwise tensor proof is compiled.
- **Next action:** No mathematical gap.

#### Theorem 6.3: Generalized tangent theorem

- **Kind:** `theorem`
- **Status:** `compiled_specialization`
- **Mathematics:** A strict-lower-rank trial space, Rayleigh–Ritz residual, and one-sided gap give the source UI-norm tangent bound.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.partIII_generalizedTanTheta_ritzResidual_uiNorm`
- **Assessment:** The finite arbitrary-UI-norm specialization is compiled; the source Hilbert-space theorem remains under Part III repair.
- **Next action:** Certify the general Hilbert-space statement and exact dimension/cardinality formulation.

### Section 6 appendix

#### Appendix to Section 6, equations (6.7)–(6.11): Unbounded-operator passage

- **Kind:** `appendix`
- **Status:** `compiled_exact`
- **Mathematics:** Domain invariance, bounded residual, spectral cutoffs, and limiting arguments extend the single-angle theorems to unbounded self-adjoint operators.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Theorem6_1_commonDomain`, `ForMathlib.DavisKahan1970.Theorem6_1_commonCore`
- **Assessment:** The main common-domain and graph-core source forms are compiled.
- **Next action:** Audit every displayed appendix identity, not only the headline theorem.

#### Lemma 6.3: Finite-rank near-maximizer leakage estimate

- **Kind:** `lemma`
- **Status:** `partial_or_wrapper_missing`
- **Mathematics:** A nearly Ky-Fan-optimal finite-rank compression has small off-block trace norm.
- **Current Lean references:** none identified
- **Assessment:** The surrounding approximation-number infrastructure exists, but no exact source declaration was found.
- **Next action:** State and prove the source lemma; it may be useful independently for cutoff passages.

### Section 7

#### Section 7, equations (7.1)–(7.5): Reflection proof of the sine double-angle theorem

- **Kind:** `proof_package`
- **Status:** `candidate_under_repair`
- **Mathematics:** Reflect the perturbation by 2P-1, identify U squared and sin(2 Theta), and reduce the result to the symmetric sine theorem.
- **Current Lean references:** `ForMathlib.DavisKahan.reflectionDefect_eq_perturbationDefect`, `ForMathlib.DavisKahan.sinTwoTheta_reflectionResidual_of_spectrum_gap`
- **Assessment:** The reflection identities and finite theorem exist; the exact full proof package is under repair.
- **Next action:** Add a source wrapper preserving both residual and perturbation conclusions.

#### Section 7, equation (7.6) and following argument: Singular-vector proof of the tangent double-angle theorem

- **Kind:** `proof_package`
- **Status:** `candidate_under_repair`
- **Mathematics:** The off-diagonal block equation and paired singular vectors yield Ky Fan and UI-norm bounds for tan(2 Theta).
- **Current Lean references:** `ForMathlib.DavisKahanExt.tanTwoTheta_offDiagonalC_of_weighted_sine`
- **Assessment:** The operator-norm theorem is compiled in finite dimensions; the arbitrary UI-norm singular-vector argument remains uncertified.
- **Next action:** Complete the exact source norm scope and infinite-dimensional approximation passage.

### Section 8

#### Theorem 8.1: Branch selection and spectral repulsion

- **Kind:** `theorem`
- **Status:** `candidate_under_repair`
- **Mathematics:** Under tan(2 Theta) hypotheses, the acute branch is equivalent to the selected spectral ordering; a canonical reducing subspace exists and satisfies operator, eigenvalue, and symmetric-gauge repulsion inequalities.
- **Current Lean references:** `ForMathlib.DavisKahanExt.quarterAcuteAngularCoordinate_sharp_bound_of_orderedSpectraSeparated`
- **Assessment:** Several finite and continuation components exist, but all three source conclusions are not yet source-audited together.
- **Next action:** Compile the continuation-selected branch and separate parts (i), (ii), and (iii) into explicit source declarations.

#### Theorem 8.2: Smallness selects the acute branch

- **Kind:** `theorem`
- **Status:** `candidate_under_repair`
- **Mathematics:** If the perturbation or residual norm is below half the gap, the sine double-angle estimate is accompanied by Theta < pi/4.
- **Current Lean references:** `ForMathlib.DavisKahanExt.norm_selectedEndpointAngularOperator_le_div`
- **Assessment:** A priori angle bounds and continuation machinery exist; exact source hypotheses and both alternatives require audit.
- **Next action:** Add the exact two-alternative source theorem.

### Section 9

#### Section 9, problem setup: Fourth-derivative Rayleigh–Ritz model

- **Kind:** `numerical_model`
- **Status:** `not_started`
- **Mathematics:** The free-beam fourth derivative on L2(0,1), perturbed by multiplication by epsilon t, with the two-dimensional linear trial eigenspace.
- **Current Lean references:** none identified
- **Assessment:** No source module formalizes the differential operator, boundary conditions, trial basis, or spectral gap alpha3 > 500.
- **Next action:** Choose whether to formalize the analytic operator or a certified finite-data surrogate reproducing the paper computations.

#### Equations (9.1)–(9.4): Initial sine and sine-double-angle bounds

- **Kind:** `numerical_claims`
- **Status:** `not_started`
- **Mathematics:** Compute R*R and derive the operator- and two-singular-value bounds for sin Theta and sin(2 Theta).
- **Current Lean references:** none identified
- **Assessment:** The general theorems exist, but the concrete residual matrix and numerical constants are not formalized.
- **Next action:** Formalize exact radical inequalities first, with decimals as derived corollaries.

#### Equations (9.5)–(9.7): Rayleigh–Ritz tangent refinements

- **Kind:** `numerical_claims`
- **Status:** `not_started`
- **Mathematics:** Use the compressed trial operator and orthogonal residual to obtain sharper tan Theta and tan(2 Theta) bounds.
- **Current Lean references:** none identified
- **Assessment:** Requires exact 2x2 matrix computations and application of Theorems 6.3 and the tan-double-angle theorem.
- **Next action:** Build a finite-dimensional exact arithmetic model independent of the unbounded differential-operator construction.

#### Equation (9.8): Comparison with Weinberger bounds

- **Kind:** `comparison_claim`
- **Status:** `not_started`
- **Mathematics:** Derive lower-eigenvalue estimates from a 3x3 comparison matrix and compare individual-vector angle bounds.
- **Current Lean references:** none identified
- **Assessment:** This imports an external theorem and asymptotic O(epsilon^4) discussion not currently distilled into Lean-ready statements.
- **Next action:** Separate exact matrix eigenvalue inequalities from the historical comparison narrative.

#### Section 9, l2 example after (9.8): Residual-infinite limitation example

- **Kind:** `example`
- **Status:** `not_started`
- **Mathematics:** An l2 trial vector has a useful Rayleigh quotient but lies outside the perturbed operator domain, so residual-based theorems do not apply while lower-bound methods still do.
- **Current Lean references:** none identified
- **Assessment:** This is an instructive domain counterexample and independently useful.
- **Next action:** Formalize a corrected nearby domain example rather than the intentionally non-domain vector itself.

#### Equations (9.9)–(9.11) and final bounds: Individual eigenvector identification inside a cluster

- **Kind:** `numerical_claims`
- **Status:** `not_started`
- **Mathematics:** Reduce the full eigenproblem to a two-dimensional Schur complement, then combine tan(2 Theta) and tan Theta bounds to control each eigenvector angle omega_k.
- **Current Lean references:** none identified
- **Assessment:** No current module represents the Schur-complement reduction or final constants.
- **Next action:** Formalize as a standalone finite block-operator theorem, then instantiate the numerical data.

### Section 10

#### Question 10.1: Sine bounds under arbitrary pairwise spectral distance

- **Kind:** `open_question`
- **Status:** `resolved_by_modern_development`
- **Mathematics:** Ask for the best UI-norm sine-angle estimate when the two relevant spectra are only known to be at distance delta.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Theorem6_2`
- **Assessment:** The paper resolves the square norm; the repository has the sharp pairwise Hilbert–Schmidt theorem. The all-UI-norm version remains a distinct question.
- **Next action:** Record precisely which norm classes are resolved and which remain open.

#### Question 10.2: Three-way subspace decompositions

- **Kind:** `open_question`
- **Status:** `not_a_completion_obligation`
- **Mathematics:** Seek perturbation estimates for two decompositions into three reducing subspaces using off-diagonal coordinate blocks.
- **Current Lean references:** none identified
- **Assessment:** This is explicitly an open research direction, not a theorem required to formalize the 1970 paper.
- **Next action:** Preserve as a documented research question; do not count as proof debt.

#### Question 10.3: Joint eigenvalue–eigenvector bounds

- **Kind:** `open_question`
- **Status:** `not_a_completion_obligation`
- **Mathematics:** Seek optimal estimates coupling changes in eigenvalues and eigenvectors.
- **Current Lean references:** none identified
- **Assessment:** Open research question.
- **Next action:** Document only.

#### Question 10.4: Perturbation bounds for functional calculus

- **Kind:** `open_question`
- **Status:** `not_a_completion_obligation`
- **Mathematics:** Seek bounds on f(A+H)-f(A) for broader functions, with spectral projections as the motivating discontinuous case.
- **Current Lean references:** none identified
- **Assessment:** Open research question; modern operator-Lipschitz theory is outside the paper-completion target.
- **Next action:** Document connections but do not treat as missing proof.

## Completion interpretation

The completed Section 6 sine-theta surface is not the same as completion of
the whole paper. The largest definite source gaps are the Section 3
classification and nonacute direct-rotation results, exact source wrappers
for Sections 4--5 and 7--8, and the complete Section 9 numerical example.
The Section 10 questions are part of the source record but are not proof
obligations for a faithful formalization of what the paper proves.
