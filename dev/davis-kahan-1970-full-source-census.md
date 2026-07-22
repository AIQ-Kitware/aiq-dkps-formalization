# Davis--Kahan 1970 full source census

Base commit: `3975f7b0397c64d12e47e1937f4d273e832bfa12`.

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
| `candidate_under_repair` | 19 |
| `partial_or_wrapper_missing` | 5 |
| `not_represented` | 3 |
| `not_started` | 0 |
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

## Verification summary

`status` above is the mathematical judgement against the printed
source. `verification` below is what the Lean build certifies, and is
checkable: run `python3 scripts/probe_census_declarations.py --verify`
to confirm every row still matches the build. The default build carries
no `sorry` and no `axiom`, so a declaration reachable from
`DavisKahan.All` is genuinely proved.

| Verification | Count |
| --- | ---: |
| `proved_in_build` | 34 |
| `proved_conditional` | 5 |
| `partially_in_build` | 0 |
| `proved_outside_build` | 0 |
| `not_compiling` | 2 |
| `absent` | 4 |
| `not_applicable` | 3 |

## Verification meanings

- **`proved_in_build`** -- Every declaration resolves against DavisKahan.All. The default build carries no sorry and no axiom, so this is a proof, continuously re-checked by CI.
- **`proved_conditional`** -- Declarations resolve against DavisKahan.All and are proved, but the source conclusion is stated relative to a hypothesis record that no value is ever constructed for, so the paper's claim is assumed rather than derived.
- **`partially_in_build`** -- Some declarations resolve against DavisKahan.All and some do not, so the row's source claim is only partly guarded by CI. `declarations_outside_build` lists the unguarded ones.
- **`proved_outside_build`** -- Declarations compile, but only under DavisKahan/Experimental, which no default target builds. The mathematics is done; it is not guarded against regression and is not reachable from the source facade.
- **`not_compiling`** -- Declarations are written but their package does not compile, so nothing is certified.
- **`absent`** -- No declaration exists.
- **`not_applicable`** -- A documented research question or exposition item. No formalization is intended, so the row is not proof debt and must not be counted as a gap.

## Frontier

Every row that still owes work, grouped by the obstruction standing
in front of it. This includes rows that are already
`proved_in_build`: the mathematics can be proved and CI-guarded while
the source-numbered wrapper is still missing. Obstructions marked
`mechanical` need only wiring or a restatement; `hard_math` needs new
mathematics.

### `contour-integration-library` -- hard_math

**Operator-valued contour integration and Riesz projections**

DavisKahan/Experimental/InfiniteDimensional/Sylvester/Resolvent.lean calls Contour.integral, Contour.IsClosed, Contour.Rectifiable, Contour.index and Contour.cauchyIndicatorFormula. None of these is defined in this repository, in Mathlib, or in vendored Spectra: the module was written against an API that was never implemented. This is the single largest remaining item. Resolvent sits on the critical path via Sylvester.Basic, so the other three never-compiled Experimental modules (Core.CompatibilitySinTwoTheta, Ideals.Symmetric, GraphSubspace) unblock nothing on their own.

Gates: DK-8.1-thm (not_compiling), DK-8.2-thm (not_compiling)

### `free-beam-closed-operator` -- hard_math

**Free-beam closed fourth-derivative operator on L2(0,1)**

Section 9's numerical example needs the analytic model itself: the closed fourth-derivative operator with the source's boundary conditions, as an unbounded self-adjoint operator.

Gates: DK-9-model (proved_conditional)

### `free-beam-third-eigenvalue` -- hard_math

**The spectral bound alpha_3 > 500**

A concrete transcendental eigenvalue estimate for the free-beam model. Together with free-beam-closed-operator this is what a FreeBeamFiniteDataCertificate would have to supply.

Gates: DK-9-model (proved_conditional), DK-9.8 (proved_conditional)

### `two-subspace-classification` -- hard_math

**Two-projection canonical decomposition and multiplicity theory**

Section 3's classification results need the Halmos two-subspace canonical form together with spectral multiplicity functions, and the infinite-dimensional existence statement needs cardinal-valued dimension bookkeeping rather than a finite-rank stand-in.

Gates: DK-3.2-prop (absent), DK-3.1-thm (absent), DK-3.1-cor (absent)

### `section9-certificate-discharge` -- mixed

**Construct the Section 9 certificates**

Section 9 compiles, but every source conclusion is stated relative to FreeBeamFiniteDataCertificate (Section9/ExactData.lean) or TheoremOutputCertificate (Section9/FullExample.lean), and no value of either type is ever constructed. The certificate fields are the paper's numerical claims. Discharging the analytic ones needs free-beam-closed-operator and free-beam-third-eigenvalue; the rest is instantiating theorems the repository already proves.

Gates: DK-9-model (proved_conditional), DK-9.1-9.4 (proved_conditional), DK-9.5-9.7 (proved_conditional), DK-9.8 (proved_conditional), DK-9.9-9.11 (proved_conditional)

### `exact-source-wrappers` -- mechanical

**Source-numbered wrappers over already-proved general theorems**

The mathematics is in the build in a more general form; what is missing is a statement carrying the paper's numbering, scope and hypotheses, so the facade can cite it.

Gates: S1-block-residual (proved_in_build), S2-sin-two-theta (proved_in_build), S2-tan-two-theta (proved_in_build), S2-unbounded-scope (proved_in_build), DK-3.1-def (proved_in_build), DK-3.2-def (proved_in_build), DK-3.1-prop (proved_in_build), DK-3.3-prop (proved_in_build), DK-3.4-prop (proved_in_build), DK-3.5-prop (proved_in_build), DK-4.1-prop (proved_in_build), DK-5.1-thm (proved_in_build), DK-5.2-thm (proved_in_build), DK-5.1-lem (proved_in_build), DK-6.3-thm (proved_in_build), DK-7-sin2-proof (proved_in_build), DK-7-tan2-proof (proved_in_build)

### Not attributed to a blocker

DK-6.3-lem (absent)


## Source ledger

### Section 1

#### Section 1, equations (1.1)–(1.8): Two reducing decompositions and the residual

- **Kind:** `construction`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Block decompositions for A and A+H, trial and exact coordinate maps, and R = (A+H)E0 - E0 A0.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan.Experimental.ExactSinTheta.PaperTheorem61Data`, `ForMathlib.DavisKahan.Experimental.ExactSinTheta.UnboundedSinThetaData`
- **Assessment:** The exact notation is distributed across the Section 6 source data records rather than exposed as a Section 1 facade.
- **Next action:** Add source-facing construction aliases only if useful for the full-paper facade.

#### Section 1, equations (1.9)–(1.13): Unitary-invariant norms and Fan dominance

- **Kind:** `framework`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Norms determined by singular values, contraction laws, Ky Fan prefix norms, and dominance by all prefixes.
- **Current Lean references:** `ForMathlib.DavisKahan.Experimental.ExactSinTheta.PaperUnitaryInvariantNorm`, `ForMathlib.DavisKahan.Experimental.ExactSinTheta.PaperUnitaryInvariantNorm.prefixGauge_le_of_all_kyFan_le_hetero`
- **Assessment:** The source norm correspondence is part of the clean Section 6 surface.
- **Next action:** Retain as shared prerequisite; no new mathematics required.

### Section 2

#### Section 2, sin theta theorem: Single-angle sine theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Interval/exterior spectral separation gives delta times the directed sine norm bounded by the residual norm for every source unitary-invariant norm.
- **Current Lean references:** `ForMathlib.DavisKahan1970.sinTheta`, `ForMathlib.DavisKahan1970.generalizedSinTheta`
- **Assessment:** The definitive source form is Theorem 6.1; real, complex, bounded, unbounded, and arbitrary-representative forms are present.
- **Next action:** No mathematical gap. Keep the source audit synchronized.

#### Section 2, tan theta theorem: Single-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** One-sided spectral separation plus the Rayleigh–Ritz/off-diagonal condition gives residual and perturbation tangent bounds in every unitary-invariant norm.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.partIII_tanTheta_ritzResidual_uiNorm`, `ForMathlib.DavisKahanExt.tanTheta_genuineSpectrum`
- **Assessment:** The finite arbitrary-UI-norm theorem is compiled. General Hilbert-space and exact source wrappers are in the Part III repair campaign.
- **Next action:** Certify the Hilbert-space source wrapper and exact perturbation companion.

#### Section 2, sin 2 theta theorem: Double-angle sine theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** A spectral gap between the two exact blocks yields residual and perturbation bounds for sin(2 Theta), with sharp factor two.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahanTheory.partIII_sinTwoTheta_uiNorm`, `ForMathlib.DavisKahan.Experimental.SpectraBridge.sinTwoTheta_addBounded_of_spectrum_gap`
- **Assessment:** Finite arbitrary-UI-norm forms are compiled; general Hilbert-space source forms are under repair.
- **Next action:** Certify source-general residual and perturbation forms.

#### Section 2, tan 2 theta theorem: Double-angle tangent theorem

- **Kind:** `unnumbered_theorem`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** Fully off-diagonal perturbations across an ordered gap give residual and perturbation tan(2 Theta) bounds with factor two.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahanTheory.partIII_tanTwoTheta_opNorm`, `ForMathlib.DavisKahanExt.tanTwoTheta_offDiagonalC_of_weighted_sine`
- **Assessment:** The finite operator-norm theorem is compiled. The source arbitrary-UI-norm Hilbert-space endpoint and branch selection are not yet certified.
- **Next action:** Complete the general UI-norm source theorem and its selected acute branch.

#### Section 2, paragraph after four theorems: Best constants and simultaneous equality

- **Kind:** `source_claim`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** All four constants are optimal in two dimensions, and finite direct sums realize equality simultaneously for all unitary-invariant norms.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.sinTheta_constant_optimal`, `ForMathlib.DavisKahanTheory.sinTwoTheta_constant_optimal`, `ForMathlib.DavisKahanTheory.single_double_sine_tangent_ratios_tendsto_one`
- **Assessment:** Sine sharpness and finite multiplicity are compiled; full quartet simultaneous equality remains in the Part III campaign.
- **Next action:** Proved. The constant-optimality and ratio-limit witnesses compile under DavisKahan/Experimental/FiniteDimensional/Sharpness.lean; promote them into the build, then audit the equality models against the exact source claim.

#### Section 2, final paragraphs: Unbounded self-adjoint scope

- **Kind:** `scope_claim`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** The four theorem families extend to unbounded self-adjoint operators under bounded perturbation or residual assumptions, with analytic work concentrated in Theorem 5.2 and the Section 6 appendix.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan1970.canonical_generalizedSinTheta`, `ForMathlib.DavisKahan1970.unbounded_sinTheta_opNorm`
- **Assessment:** The sine family is complete in source scope. Other theorem families have partial unbounded APIs but no full source audit.
- **Next action:** Track unbounded tangent and double-angle source coverage separately.

### Section 3

#### Definition 3.1: Direct rotation

- **Kind:** `definition`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** A unitary intertwining the two projections whose diagonal cosine blocks are positive and whose off-diagonal sine blocks are adjoints.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan1970.complex_directRotation`, `ForMathlib.DavisKahan.Experimental.SpectraBridge.spectraCanonicalIntertwiner`
- **Assessment:** Acute complex and finite constructions exist; exact nonacute source scope is not yet unified.
- **Next action:** Add a source-facing definition covering the source existence regimes.

#### Definition 3.2: Acute case

- **Kind:** `definition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** Both crossed intersections P ∩ Q-perp and P-perp ∩ Q vanish.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan.IsAcute`
- **Assessment:** The predicate is broadly used but lacks a numbered source alias.
- **Next action:** Add a source alias only if the facade benefits.

#### Proposition 3.1: Acute direct rotation existence and uniqueness

- **Kind:** `proposition`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** In the acute case the direct rotation exists, is unique, and positivity of its diagonal blocks characterizes it.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan1970.complex_directRotation`, `ForMathlib.DavisKahan1970.complex_directRotation_unique`
- **Assessment:** The main acute construction and uniqueness are present; the exact characterization by positivity needs source-level verification.
- **Next action:** Prove or wrap the positivity characterization explicitly.

#### Proposition 3.2: Nonacute existence criterion

- **Kind:** `proposition`
- **Status:** `not_represented`
- **Verification:** `absent`
- **Mathematics:** A direct rotation exists exactly when the two crossed intersections have equal dimension; it is then nonunique.
- **Blocked by:** `two-subspace-classification`
- **Current Lean references:** none identified
- **Assessment:** No exact general Hilbert-space declaration was found.
- **Next action:** State the cardinal/dimension-balanced existence theorem conservatively; finite and infinite cases may need separate APIs.

#### Proposition 3.3: Principal square-root characterization

- **Kind:** `proposition`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** Every direct rotation is a principal square root of the product of the two reflections; conversely a suitable principal square root is a direct rotation.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan1970.complex_directRotation_sq`
- **Assessment:** The square identity and acute spectral branch exist; the source converse with the crossed-intersection mapping condition is not exposed.
- **Next action:** Add the converse or record the exact missing nonacute hypothesis.

#### Proposition 3.4: Square as a direct rotation

- **Kind:** `proposition`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** When the cosine block squared is at least one half, U squared is the direct rotation from the reflected subspace to the target subspace.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahanTheory.directRotation_sq`, `ForMathlib.DavisKahan1970.complex_directRotation_sq`
- **Assessment:** Square identities exist; exact source mapping between Q-minus and Q needs verification.
- **Next action:** Add an exact source wrapper after the direct-rotation repair lands.

#### Theorem 3.1: Classification of pairs of subspaces

- **Kind:** `theorem`
- **Status:** `not_represented`
- **Verification:** `absent`
- **Mathematics:** Spectral multiplicity functions of the two angle operators classify dimension-compatible subspace pairs up to isometric equivalence.
- **Blocked by:** `two-subspace-classification`
- **Current Lean references:** none identified
- **Assessment:** The current angle API does not provide this full classification theorem.
- **Next action:** Develop a two-projection canonical-decomposition classification, likely using Spectra/Halmos infrastructure.

#### Corollary 3.1: Compact classification by angle eigenvalues

- **Kind:** `corollary`
- **Status:** `not_represented`
- **Verification:** `absent`
- **Mathematics:** When the cross projection is compact, the decreasing angle eigenvalue lists, including possible zero multiplicity, classify the pair.
- **Blocked by:** `two-subspace-classification`
- **Current Lean references:** none identified
- **Assessment:** Depends on Theorem 3.1 plus compact spectral classification.
- **Next action:** Defer until the general classification and compact spectral multiplicity bridge exist.

#### Proposition 3.5: Angle commutation and eigenspace geometry

- **Kind:** `proposition`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** The full angle commutes with both projections, the quarter-turn and direct rotation; its eigenspaces are maximal reducing constant-angle subspaces in the acute case.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan1970.bounded_angle_commute`, `ForMathlib.DavisKahan1970.bounded_sinAngleOperatorC_norm`
- **Assessment:** Commutation identities are present, but the maximal eigenspace characterization is not represented.
- **Next action:** Separate the reusable commutation theorem from the source-specific maximality result.

#### Corollary 3.2: Reversal symmetry

- **Kind:** `corollary`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** Swapping P and Q leaves the angle operator unchanged and reverses the quarter-turn operator.
- **Current Lean references:** `ForMathlib.DavisKahan1970.complex_directRotation_reversal`, `ForMathlib.DavisKahanTheory.directRotation_symm`
- **Assessment:** Direct-rotation reversal is represented; the exact angle/J statement needs a source wrapper.
- **Next action:** The reversal theorem compiles under DavisKahan/Experimental/FiniteDimensional/DirectRotation.lean. Promote it into DavisKahan/FiniteDimensional so CI guards it, then add the source-facing angle and quarter-turn statement.

### Section 4

#### Proposition 4.1: Pointwise and singular-value extremality of the direct rotation

- **Kind:** `proposition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** For any unitary carrying P to Q, an orthonormal sequence experiences angles at least the principal angles; equivalently the singular values of (1-V)|P are minimized by the direct rotation and equal 2 sin(theta_k/2).
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahanTheory.singularValues_restrictedDisplacement_le`, `ForMathlib.DavisKahanTheory.singularValues_restrictedDisplacement_directRotation`
- **Assessment:** The finite pointwise singular-value theorem is compiled: every singular value of the restricted displacement (1-V)P is minimized by the direct rotation, whose values are the doubled half-angle sines 2 sin(theta_k/2).  A source-numbered wrapper and the infinite-dimensional scope remain open.
- **Next action:** Add a DavisKahan1970 source wrapper and audit the infinite-dimensional statement.

#### Corollary 4.1: UI-norm minimality of direct rotation displacement

- **Kind:** `corollary`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** The direct rotation minimizes the norm of (1-V)P for every unitary-invariant norm.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.uiNorm_restrictedDisplacement_le`, `ForMathlib.DavisKahanTheory.directRotation_minimizes_restrictedDisplacement_uiNorm`
- **Assessment:** Compiled without any angle restriction, for every unitarily invariant norm, over every RCLike field (finite dimension).  The earlier note conflating this row with Proposition 4.4 is resolved: the corollary concerns the restricted displacement and needs no angle hypothesis.
- **Next action:** Proved. directRotation_minimizes_restrictedDisplacement_uiNorm compiles but only under DavisKahan/Experimental; promote it into the build, then add a DavisKahan1970 source wrapper and audit the infinite-dimensional statement.

#### Proposition 4.2: Basis-angle square-sum extremality

- **Kind:** `proposition`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** For every orthonormal basis of P, the sum of squared displacement sines under V dominates the sum of squared principal sines.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.directRotation_minimizes_sum_sq_basis_angles`
- **Assessment:** The finite orthonormal-basis displacement-energy extremality is compiled via the nuclear-norm specialization of the displacement-square majorization.
- **Next action:** Proved. directRotation_minimizes_sum_sq_basis_angles compiles but only under DavisKahan/Experimental; promote it into the build, then settle the exact infinite-dimensional summability convention of the source statement.

#### Proposition 4.3: Squared displacement UI-norm minimality

- **Kind:** `proposition`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** The direct rotation minimizes the UI norm of (1-V*) (1-V).
- **Current Lean references:** `ForMathlib.DavisKahanTheory.directRotation_displacementSquare_kyFan`, `ForMathlib.DavisKahanTheory.directRotation_displacementSquare_uiNorm`, `ForMathlib.DavisKahanTheory.directRotation_minimizes_displacementSquare_uiNorm`
- **Assessment:** Compiled for every unitarily invariant norm over every RCLike field (finite dimension), via Fan-Hoffman majorization of the pinched competitor and two-block pinching contraction.
- **Next action:** Proved. directRotation_minimizes_displacementSquare_uiNorm compiles but only under DavisKahan/Experimental; promote it into the build, then add a DavisKahan1970 source wrapper.

#### Proposition 4.4: Real-space full displacement minimality below pi/3

- **Kind:** `proposition`
- **Status:** `refuted_as_transcribed`
- **Verification:** `proved_in_build`
- **Mathematics:** In a real Hilbert space, if the maximal angle is at most pi/3, the direct rotation minimizes every UI norm of 1-V.
- **Current Lean references:** `ForMathlib.DavisKahanTheory.shortRotation_fullDisplacement_refuted`, `ForMathlib.DavisKahanTheory.DavisKahanProposition4_4_Finite`, `ForMathlib.DavisKahanTheory.not_davisKahanProposition4_4_Finite`
- **Assessment:** The transcribed claim is false: a compiled R^4 counterexample exhibits an acute pair with both principal angles pi/4 and a competitor unitary carrying P to Q whose full displacement 1-V has trace norm 2 sqrt 2, strictly below the direct rotation value 4 sqrt(2 - sqrt 2).  The competitor mixes the equal-angle multiplicity space (rotation angles 0 and pi/2), an obstruction available at every angle threshold; the same family refutes the closing conjecture of Davis 1958.  Operator-norm and squared-displacement consequences survive via 4.1/4.3.
- **Next action:** None outstanding.  The source re-audit is done: the printed Proposition 4.4 carries no hypothesis restricting the competitor class, excluding multiplicity mixing, or replacing the full displacement, so the refutation applies to the claim as printed.  The defect is localized to equation (4.3), whose derivation from (1.12) needs superadditivity of the Ky Fan sum across an orthogonal decomposition of the domain; range orthogonality fails.  The block-level claim the printed proof body establishes (each `||K Omega_k||_2` minimized at V=U, via the pi/3 trigonometry) remains true in the counterexample.  `not_davisKahanProposition4_4_Finite` now refutes the claim in its "every UI norm" form, instantiating N at `(RectangularUnitarilyInvariantNorm.kyFan 4).toSquare`.

### Section 5

#### Theorem 5.1: Banach-space Sylvester lower bound

- **Kind:** `theorem`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `proved_in_build`
- **Mathematics:** Under a norm bound on B and an inverse norm bound on A, AX-XB=C implies ||C|| >= delta ||X|| for any compatible operator norm.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan1970.bounded_sylvester_neumann_solution`
- **Assessment:** The repository has Neumann and ordered-gap engines, but no explicit audited source wrapper for this Banach-space theorem.
- **Next action:** Add the exact Banach-space statement and derive it from the geometric-series proof.

#### Theorem 5.2: Semibounded self-adjoint Sylvester theorem

- **Kind:** `theorem`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** For A >= gamma+delta > gamma >= B, a bounded solution of AX=XB+C satisfies the sharp UI-norm inequality.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan.Experimental.ExactSinTheta.directGenuineOrderedSylvesterEngine_lowerUpper`, `ForMathlib.DavisKahan1970.unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`
- **Assessment:** The completed Section 6 route contains the needed constant-one engines, while the exact source theorem alias is still in the full Part III repair campaign.
- **Next action:** Expose an exact Theorem 5.2 wrapper and include it in the full-paper audit.

#### Lemma 5.1: Strong-cutoff convergence of singular values

- **Kind:** `lemma`
- **Status:** `compiled_general_infrastructure`
- **Verification:** `proved_in_build`
- **Mathematics:** If projections converge strongly to one, each singular value of K composed with the projection converges to the corresponding singular value of K.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan.Experimental.ExactSinTheta.approximationSingularValue_comp_strongProjection_tendsto`
- **Assessment:** The modern approximation-number theorem is stronger and scalar-generic.
- **Next action:** Add a source-numbered wrapper if needed by the full-paper facade.

### Section 6

#### Lemma 6.1: Direct-sum UI-norm comparison and converse

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Two diagonal block inequalities imply the direct-sum inequality; under equisingularity of paired blocks the converse holds.
- **Current Lean references:** `ForMathlib.DavisKahan1970.lemma6_1`, `ForMathlib.DavisKahan1970.lemma6_1_converse`
- **Assessment:** Both directions are proved; the converse should be added to the exact audit manifest.
- **Next action:** Harden the audit, not the mathematics.

#### Lemma 6.2: Reflection-pinch contraction

- **Kind:** `lemma`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** The sum of the two diagonal projection blocks of an operator is no larger than the operator in every source unitary-invariant norm.
- **Current Lean references:** `ForMathlib.DavisKahan1970.lemma6_2`
- **Assessment:** Part of the clean Section 6 surface.
- **Next action:** No mathematical gap.

#### Proposition 6.1: Symmetric sine theorem

- **Kind:** `proposition`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Two complementary source gap hypotheses give the full sine-angle inequality with perturbation H.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Proposition6_1`
- **Assessment:** Complex and real source forms are compiled.
- **Next action:** No mathematical gap.

#### Theorem 6.1: Generalized sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** A lower frame bound on the trial map and interval/exterior separation give delta epsilon times any equisingular sine representative bounded by the residual.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Theorem6_1`
- **Assessment:** This is the canonical source-general sine theorem.
- **Next action:** No mathematical gap.

#### Theorem 6.2: Pairwise-gap square-norm sine theorem

- **Kind:** `theorem`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Arbitrary pairwise spectral distance gives the sharp Hilbert–Schmidt/square-norm residual bound.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Theorem6_2`
- **Assessment:** The defect-first pairwise tensor proof is compiled.
- **Next action:** No mathematical gap.

#### Theorem 6.3: Generalized tangent theorem

- **Kind:** `theorem`
- **Status:** `compiled_specialization`
- **Verification:** `proved_in_build`
- **Mathematics:** A strict-lower-rank trial space, Rayleigh–Ritz residual, and one-sided gap give the source UI-norm tangent bound.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahanTheory.partIII_generalizedTanTheta_ritzResidual_uiNorm`
- **Assessment:** The finite arbitrary-UI-norm specialization is compiled; the source Hilbert-space theorem remains under Part III repair.
- **Next action:** Certify the general Hilbert-space statement and exact dimension/cardinality formulation.

### Section 6 appendix

#### Appendix to Section 6, equations (6.7)–(6.11): Unbounded-operator passage

- **Kind:** `appendix`
- **Status:** `compiled_exact`
- **Verification:** `proved_in_build`
- **Mathematics:** Domain invariance, bounded residual, spectral cutoffs, and limiting arguments extend the single-angle theorems to unbounded self-adjoint operators.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Theorem6_1_commonDomain`, `ForMathlib.DavisKahan1970.Theorem6_1_commonCore`
- **Assessment:** The main common-domain and graph-core source forms are compiled.
- **Next action:** Audit every displayed appendix identity, not only the headline theorem.

#### Lemma 6.3: Finite-rank near-maximizer leakage estimate

- **Kind:** `lemma`
- **Status:** `partial_or_wrapper_missing`
- **Verification:** `absent`
- **Mathematics:** A nearly Ky-Fan-optimal finite-rank compression has small off-block trace norm.
- **Current Lean references:** none identified
- **Assessment:** The surrounding approximation-number infrastructure exists, but no exact source declaration was found.
- **Next action:** State and prove the source lemma; it may be useful independently for cutoff passages.

### Section 7

#### Section 7, equations (7.1)–(7.5): Reflection proof of the sine double-angle theorem

- **Kind:** `proof_package`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** Reflect the perturbation by 2P-1, identify U squared and sin(2 Theta), and reduce the result to the symmetric sine theorem.
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahan.reflectionDefect_eq_perturbationDefect`, `ForMathlib.DavisKahan.Experimental.SpectraBridge.sinTwoTheta_reflectionResidual_of_spectrum_gap`
- **Assessment:** The reflection identities and finite theorem exist; the exact full proof package is under repair.
- **Next action:** Add a source wrapper preserving both residual and perturbation conclusions.

#### Section 7, equation (7.6) and following argument: Singular-vector proof of the tangent double-angle theorem

- **Kind:** `proof_package`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** The off-diagonal block equation and paired singular vectors yield Ky Fan and UI-norm bounds for tan(2 Theta).
- **Blocked by:** `exact-source-wrappers`
- **Current Lean references:** `ForMathlib.DavisKahanExt.tanTwoTheta_offDiagonalC_of_weighted_sine`
- **Assessment:** The operator-norm theorem is compiled in finite dimensions; the arbitrary UI-norm singular-vector argument remains uncertified.
- **Next action:** Complete the exact source norm scope and infinite-dimensional approximation passage.

### Section 8

#### Theorem 8.1: Branch selection and spectral repulsion

- **Kind:** `theorem`
- **Status:** `candidate_under_repair`
- **Verification:** `not_compiling`
- **Mathematics:** Under tan(2 Theta) hypotheses, the acute branch is equivalent to the selected spectral ordering; a canonical reducing subspace exists and satisfies operator, eigenvalue, and symmetric-gauge repulsion inequalities.
- **Blocked by:** `contour-integration-library`
- **Current Lean references:** `ForMathlib.DavisKahan1970.Section8.maximalAngle_selectedSpectralSubspaces_lt_pi_div_four`, `ForMathlib.DavisKahan1970.Section8.orientedSpectralRepulsionConclusion`, `ForMathlib.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData`, `ForMathlib.DavisKahan1970.Section8.theorem8_1_selectedBranch_and_spectralRepulsion`, `ForMathlib.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_of_rotatedBlockData`
- **Not reachable from `DavisKahan.All`:** `ForMathlib.DavisKahan1970.Section8.maximalAngle_selectedSpectralSubspaces_lt_pi_div_four`, `ForMathlib.DavisKahan1970.Section8.orientedSpectralRepulsionConclusion`, `ForMathlib.DavisKahan1970.Section8.theorem8_1_lowerCompressionRepulsion_of_rotatedBlockData`, `ForMathlib.DavisKahan1970.Section8.theorem8_1_selectedBranch_and_spectralRepulsion`, `ForMathlib.DavisKahan1970.Section8.theorem8_1_upperCompressionRepulsion_of_rotatedBlockData`
- **Assessment:** A source-facing candidate assembles the continuation-selected reducing branch, unitary transport, strict quarter-acuteness, full-spectrum gap exclusion, and restricted-spectrum separation.  The exact quadratic-form algebra behind part (i) is also proved from an abstract rotated-block decomposition and sine/cosine Pythagoras certificate.  The unrestricted construction from the exact tan(2 Theta) hypotheses, the converse branch characterization, the concrete direct-rotation instantiation of part (i), and parts (ii)--(iii) remain open.
- **Next action:** Blocked, not merely unfinished. The package does not compile: it needs the operator-valued contour integration API (see blockers). Four named theorems were never written -- see planned_declarations. Only then instantiate the compression certificates with concrete direct-rotation blocks.

#### Theorem 8.2: Smallness selects the acute branch

- **Kind:** `theorem`
- **Status:** `candidate_under_repair`
- **Verification:** `not_compiling`
- **Mathematics:** If the perturbation or residual norm is below half the gap, the sine double-angle estimate is accompanied by Theta < pi/4.
- **Blocked by:** `contour-integration-library`
- **Current Lean references:** `ForMathlib.DavisKahan1970.Section8.PerturbationHalfGapBridge`, `ForMathlib.DavisKahan1970.Section8.ResidualHalfGapBridge`, `ForMathlib.DavisKahan1970.Section8.theorem82_branch_of_residualHalfGapBridge`, `ForMathlib.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_selectedBranch`
- **Not reachable from `DavisKahan.All`:** `ForMathlib.DavisKahan1970.Section8.PerturbationHalfGapBridge`, `ForMathlib.DavisKahan1970.Section8.ResidualHalfGapBridge`, `ForMathlib.DavisKahan1970.Section8.theorem82_branch_of_residualHalfGapBridge`, `ForMathlib.DavisKahan1970.Section8.theorem8_2_perturbationHalfGap_selectedBranch`
- **Assessment:** The strict selected-branch conclusion is now exposed under explicit perturbation and residual half-gap bridge records. The general continuation machinery behind the conclusion is admission-free. Constructing those bridges from the exact printed half-gap hypotheses, and the Krein replacement step for the residual alternative, remain open.
- **Next action:** Blocked on the same contour-integration API. Then prove the half-gap spectral enclosure / common-contour constructor and formalize the Krein residual-to-perturbation replacement.

### Section 9

#### Section 9, problem setup: Fourth-derivative Rayleigh–Ritz model

- **Kind:** `numerical_model`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_conditional`
- **Mathematics:** The free-beam fourth derivative on L2(0,1), perturbed by multiplication by epsilon t, with the two-dimensional linear trial eigenspace.
- **Blocked by:** `section9-certificate-discharge`, `free-beam-closed-operator`, `free-beam-third-eigenvalue`
- **Current Lean references:** `ForMathlib.DavisKahan1970.Section9.CenteredAffine`, `ForMathlib.DavisKahan1970.Section9.ritz_matrix_from_affine_moments`, `ForMathlib.DavisKahan1970.Section9.FreeBeamFiniteDataCertificate`
- **Assessment:** A source-facing candidate now reconstructs the affine trial basis through exact unit-interval moments and packages the remaining free-beam analytic facts behind an explicit certificate. The closed fourth-derivative operator and the bound alpha_3 > 500 are not yet proved.
- **Next action:** The finite-moment layer compiles. Remaining is the analytic model itself: construct the free-beam closed fourth-derivative operator on L2(0,1) with the source's boundary conditions, discharge alpha_3 > 500, and build a FreeBeamFiniteDataCertificate. Until such a value exists the Section 9 conclusions are assumed, not derived.

#### Equations (9.1)–(9.4): Initial sine and sine-double-angle bounds

- **Kind:** `numerical_claims`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_conditional`
- **Mathematics:** Compute R*R and derive the operator- and two-singular-value bounds for sin Theta and sin(2 Theta).
- **Blocked by:** `section9-certificate-discharge`
- **Current Lean references:** `ForMathlib.DavisKahan1970.Section9.initial_residual_gram_from_affine_moments`, `ForMathlib.DavisKahan1970.Section9.residualGram_eigenvalueHigh_charAt`, `ForMathlib.DavisKahan1970.Section9.equation_9_1`, `ForMathlib.DavisKahan1970.Section9.equation_9_4`
- **Assessment:** The residual Gram matrix, its two characteristic roots, exact radical bounds, and the printed rational relaxations are represented. The actual sine and double-angle theorem outputs are still bridge hypotheses pending integration with the maintained theorem APIs.
- **Next action:** The arithmetic compiles. Remaining is to replace the TheoremOutputCertificate fields by applications of the source-facing sine and tangent theorems, so the printed conclusions are derived rather than assumed.

#### Equations (9.5)–(9.7): Rayleigh–Ritz tangent refinements

- **Kind:** `numerical_claims`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_conditional`
- **Mathematics:** Use the compressed trial operator and orthogonal residual to obtain sharper tan Theta and tan(2 Theta) bounds.
- **Blocked by:** `section9-certificate-discharge`
- **Current Lean references:** `ForMathlib.DavisKahan1970.Section9.recentered_residual_gram_from_affine_moments`, `ForMathlib.DavisKahan1970.Section9.equation_9_5_low`, `ForMathlib.DavisKahan1970.Section9.equation_9_6`, `ForMathlib.DavisKahan1970.Section9.equation_9_7`
- **Assessment:** The Ritz compression, rank-one recentered residual, singular-value scalars, exact tangent envelopes, and decimal corollaries are present as a candidate. The unbounded tan-theta and tan-two-theta instantiations remain to be connected.
- **Next action:** The exact radical arithmetic compiles. Remaining is to instantiate the strongest correct tangent and double-angle theorems in place of the corresponding certificate fields.

#### Equation (9.8): Comparison with Weinberger bounds

- **Kind:** `comparison_claim`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_conditional`
- **Mathematics:** Derive lower-eigenvalue estimates from a 3x3 comparison matrix and compare individual-vector angle bounds.
- **Blocked by:** `section9-certificate-discharge`, `free-beam-third-eigenvalue`
- **Current Lean references:** `ForMathlib.DavisKahan1970.Section9.ArrowheadThreeByThree`, `ForMathlib.DavisKahan1970.Section9.tangent_sq_le_of_weinberger_sine_sq`, `ForMathlib.DavisKahan1970.Section9.equation_9_8_lower`, `ForMathlib.DavisKahan1970.Section9.equation_9_8_upper`
- **Assessment:** The exact arrowhead characteristic polynomial and the algebraic conversion of Weinberger sine-square bounds to tangent bounds are represented. The historical lower-root theorem is deliberately an explicit certificate rather than an informal O(epsilon^4) assertion.
- **Next action:** The arrowhead algebra compiles. Remaining is the root inequality, which needs the alpha_3 > 500 spectral bound.

#### Section 9, l2 example after (9.8): Residual-infinite limitation example

- **Kind:** `example`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_in_build`
- **Mathematics:** An l2 trial vector has a useful Rayleigh quotient but lies outside the perturbed operator domain, so residual-based theorems do not apply while lower-bound methods still do.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Section9.rawDiagonalImage_eq_one`, `ForMathlib.DavisKahan1970.Section9.rawDiagonalImage_partial_energy`, `ForMathlib.DavisKahan1970.Section9.truncatedDiagonalImage_energy`
- **Assessment:** The pointwise constant image and divergent finite partial energies are formalized algebraically, together with an explicit finite-support truncation repair that agrees on arbitrary prescribed prefixes.
- **Next action:** The sequence lemmas compile and are unconditional. Optionally lift them from coordinate sequences to the abstract operator setting.

#### Equations (9.9)–(9.11) and final bounds: Individual eigenvector identification inside a cluster

- **Kind:** `numerical_claims`
- **Status:** `candidate_under_repair`
- **Verification:** `proved_conditional`
- **Mathematics:** Reduce the full eigenproblem to a two-dimensional Schur complement, then combine tan(2 Theta) and tan Theta bounds to control each eigenvector angle omega_k.
- **Blocked by:** `section9-certificate-discharge`
- **Current Lean references:** `ForMathlib.DavisKahan1970.Section9.half_tanTwoPsi_ratio_lt_of_eigenvalue_upper`, `ForMathlib.DavisKahan1970.Section9.block_eigenproblem_iff`, `ForMathlib.DavisKahan1970.Section9.schur_complement_reduction`, `ForMathlib.DavisKahan1970.Section9.individual_angle_le_exact_envelope`, `ForMathlib.DavisKahan1970.Section9.final_lower_individual_angle_bound`, `ForMathlib.DavisKahan1970.Section9.NumericalExampleCertificate`
- **Assessment:** Equation (9.9) is represented as an explicit block linear map, and equations (9.10)-(9.11) by a generic Schur reduction. The rank-one correction is decomposed into its shifted diagonal and off-diagonal parts, with the exact sqrt(3)/30 coefficient. The final scalar combination producing sqrt(7)/10 and the printed bounds is present. The operator-order resolvent sandwich and actual angle identifications remain certificate fields.
- **Next action:** The block reduction compiles. Remaining is the rank-one resolvent order argument, replacing the last certificate fields.

### Section 10

#### Question 10.1: Sine bounds under arbitrary pairwise spectral distance

- **Kind:** `open_question`
- **Status:** `resolved_by_modern_development`
- **Verification:** `proved_in_build`
- **Mathematics:** Ask for the best UI-norm sine-angle estimate when the two relevant spectra are only known to be at distance delta.
- **Current Lean references:** `ForMathlib.DavisKahan1970.Theorem6_2`
- **Assessment:** The paper resolves the square norm; the repository has the sharp pairwise Hilbert–Schmidt theorem. The all-UI-norm version remains a distinct question.
- **Next action:** Record precisely which norm classes are resolved and which remain open.

#### Question 10.2: Three-way subspace decompositions

- **Kind:** `open_question`
- **Status:** `not_a_completion_obligation`
- **Verification:** `not_applicable`
- **Mathematics:** Seek perturbation estimates for two decompositions into three reducing subspaces using off-diagonal coordinate blocks.
- **Current Lean references:** none identified
- **Assessment:** This is explicitly an open research direction, not a theorem required to formalize the 1970 paper.
- **Next action:** Preserve as a documented research question; do not count as proof debt.

#### Question 10.3: Joint eigenvalue–eigenvector bounds

- **Kind:** `open_question`
- **Status:** `not_a_completion_obligation`
- **Verification:** `not_applicable`
- **Mathematics:** Seek optimal estimates coupling changes in eigenvalues and eigenvectors.
- **Current Lean references:** none identified
- **Assessment:** Open research question.
- **Next action:** Document only.

#### Question 10.4: Perturbation bounds for functional calculus

- **Kind:** `open_question`
- **Status:** `not_a_completion_obligation`
- **Verification:** `not_applicable`
- **Mathematics:** Seek bounds on f(A+H)-f(A) for broader functions, with spectral projections as the motivating discontinuous case.
- **Current Lean references:** none identified
- **Assessment:** Open research question; modern operator-Lipschitz theory is outside the paper-completion target.
- **Next action:** Document connections but do not treat as missing proof.

## Completion interpretation

The completed Section 6 sine-theta surface is not the same as completion of
the whole paper, but the remaining distance is smaller than a raw count of
outstanding rows suggests, and it is not uniform.

A zero `sorry` count is not evidence of completion here. Because the tree is
both sorry-free and axiom-free, unfinished work cannot show up as a `sorry`;
it shows up in exactly three places, which the `verification` axis separates:
a package that does not compile (`not_compiling`), a conclusion stated
relative to a hypothesis record nobody constructs (`proved_conditional`), and
a statement nobody wrote (`absent`). Rows marked `proved_outside_build` and
`partially_in_build` are a fourth, much cheaper case: the mathematics is
already proved and merely sits outside the default build target.

The genuinely hard remainder is Section 8, which is blocked on an
operator-valued contour-integration API that exists nowhere, the Section 9
analytic model, and the Section 3 classification results. The Section 10
questions are part of the source record but are not proof obligations for a
faithful formalization of what the paper proves.
