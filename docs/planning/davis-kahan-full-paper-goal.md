# Davis--Kahan 1970: full-paper formalization goal

## Default objective

The default objective is a skeptical-expert-quality formalization of Chandler
Davis and W. M. Kahan, *The Rotation of Eigenvectors by a Perturbation. III*
(1970), in the scope in which the paper states its results.

The finite-dimensional theory is important and should be preserved. It is not
the terminal definition of success unless a task explicitly asks for a
finite-only result.

## Source-verified ambient scope

The maintained modernized transcription states that:

- the ambient space is a separable Hilbert space;
- the subject throughout the main development is a bounded Hermitian operator
  `A` and a modified Hermitian operator `A + H`;
- the results and proofs also apply to unbounded self-adjoint `A` when the
  domain of `H` contains the domain of `A`, with useful conclusions requiring
  the relevant perturbation or residual to be bounded;
- all four headline theorems apply in infinite as well as finite dimensions;
- all four are stated for arbitrary unitary-invariant norms;
- the complications needed to remove inessential boundedness restrictions are
  concentrated in Theorem 5.2 and the Appendix to Section 6.

The source therefore has one canonical theorem family with nested
specializations:

1. unbounded self-adjoint operators with explicit domains and bounded residuals;
2. bounded operators on arbitrary Hilbert spaces as full-domain corollaries;
3. finite-dimensional and matrix forms as further specializations or
   independent weaker-foundation alternatives.

The source exposition may introduce the bounded case first. The formalization
API must not turn that expository order into a loss of theorem generality.

## Status vocabulary

Use scope-qualified claims:

- **finite specialization complete**: a theorem is proved using finite spectra,
  finite singular-value lists, or finite-dimensional UI norms;
- **bounded Hilbert-space theorem complete**: the theorem is proved for bounded
  self-adjoint operators without a finite-dimensional assumption;
- **source norm scope complete**: the theorem supports the unitary-invariant
  norm scope asserted by the paper, with an honest operator-ideal/domain API in
  infinite dimensions;
- **unbounded extension complete**: the source domain assumptions and limiting
  arguments are formalized;
- **paper theorem complete**: the exact source statement, hypotheses,
  orientation, constants, branch conditions, and norm scope are proved;
- **paper complete**: every numbered theorem, proposition, corollary, lemma,
  direct-rotation result, Section 8 selection result, sharpness/equality claim,
  numerical example claim intended for formalization, and unbounded passage has
  been audited and either formalized or explicitly classified as expository.

Do not abbreviate the first status to “Davis--Kahan complete.”

## Role of the finite theory

`DavisKahan/FiniteDimensional/` is retained because it provides:

- arbitrary rectangular UI norms through finite singular-value lists;
- computational and matrix-facing statements;
- weaker-foundation proofs that do not require the infinite-dimensional
  analytic stack;
- explicit equality models and regression tests;
- applications to DKPS, statistics, Ritz methods, and singular subspaces;
- alternative proofs suitable for cherry-picking.

When finite work is undertaken by default, it should close a named seam needed
by the Hilbert-space theorem or be clearly labeled as an alternative endpoint.

## Canonical roadmap

### General single-angle root

The first source theorem to own an unqualified API is the generalized
unbounded `sin Theta` theorem. Its dependency ladder is maintained in
`davis-kahan-general-sin-theta-roadmap.md` and consists of:

- densely defined closed self-adjoint operators and domain-aware compositions;
- unbounded spectral projections, cutoffs, and bounded truncations;
- the Section 5 Sylvester estimate for the source gap configurations;
- bounded residual block identities on explicit domains;
- rectangular UI-norm ideals and the Ky Fan dominance passage;
- lower-frame factorization and exact directed-angle identification.

Bounded and finite forms are then derived or retained as scoped alternatives.

### Remaining theorem families

- source-faithful two-subspace geometry and operator angles;
- direct rotation, existence, uniqueness, formulas, and extremality;
- graph/transversality machinery and `tan Theta`;
- reflection theory, `sin 2 Theta`, and `tan 2 Theta`;
- Section 8 continuation, branch selection, canonical spectral subspaces,
  uniqueness, and spectral repulsion;
- unbounded forms of every source result for which the paper supplies them.

### Unitary-invariant norm scope

The finite `RectangularUnitarilyInvariantNorm` API cannot simply be reused for
all bounded operators. The infinite-dimensional theory needs honest domains of
finiteness, such as compact/symmetric norm ideals, approximation numbers, Ky
Fan norms, Hilbert--Schmidt and Schatten classes, and the relevant ideal and
unitary-invariance laws.

### Unbounded passages

- densely defined self-adjoint operators and domain-aware compositions;
- spectral cutoffs and convergence;
- Theorem 5.2 in its source scope;
- the Appendix to Section 6;
- bounded residual/perturbation hypotheses and passage from cutoffs to the
  unbounded operator.

## Source audit discipline

The local modernized transcription is the authority for source wording and
numbering. Committed distilled notes are independent mathematical summaries;
they may quote only short anchors and should record:

- source section/theorem/equation;
- ambient operator and space assumptions;
- bounded versus unbounded status;
- norm scope and finiteness conventions;
- residual versus perturbation form;
- directed angle convention;
- branch or transversality conclusion;
- exact current Lean declaration and its narrower or broader scope;
- remaining gap before the source statement is represented.

## Current high-level status

The finite-dimensional library contains a strong and valuable package,
including arbitrary rectangular UI-norm sine and tangent results and stable
double-angle endpoints. The bounded branch contains meaningful operator-norm
foundations. Neither is the canonical completion boundary. The immediate
controlling goal is the generalized unbounded single-angle theorem in
`Experimental/InfiniteDimensional/SinTheta/Canonical.lean`; the remaining
four-theorem package, direct-rotation extremal theory, Section 8 package, and
full source audit follow from that foundation.

### Progress note (2026-07-15, easy-ladder closure session)

Fully proved and axiom-clean: the total resolvent interface with both
resolvent identities and Neumann resolvent-set stability
(`Sylvester/Resolvent`); `graphSubspace` as the closure of the parametrized
graph range with an unconditional projection instance and
`graphSubspace_eq_range` for angular operators (`GraphSubspace`); the bounded
and unbounded block-operator constructions on the Hilbert direct sum with the
unbounded block-graph projection instance (`Riccati/Bounded`,
`Riccati/Unbounded`); the Hermitian dilation and its self-adjointness
(`Ideals/CompactAndSingular`); and the explicit planar extremizer
constructions for the `sin Θ`, `sin 2Θ`, and `tan 2Θ` sharpness models (both
`Sharpness` files).

Structurally assembled on top of documented open black boxes:
`sylvester_unique`, `sinTheta_symmetric`, `existsUnique_angularOperator`,
`continuedProjection_eq_spectralProjection`, `schatten_sinTheta`,
`covariance_subspace_sinTheta`, and `tanTwoTheta_spectralSubspace_le`.

**Statement-soundness repair (2026-07-15).** The former
`Core/AbstractSpectrum.lean` predicates were point-spectrum based and therefore
vacuous for continuous-spectrum self-adjoint operators such as multiplication
by `t` on `L²(0,1)`.  The repaired layer now defines `realSpectrum` by pulling the native
`RCLike` Banach-algebra spectrum back to real scalars and defines
`restrictedSpectrum A U` from `spectrum 𝕜 (A.restrict hU)` for an invariant
subspace.  `SpectrumIn`,
`SpectraSeparated`, `OrderedSpectraSeparated`, and all derived gap predicates
also carry invariance explicitly.  This removes the counterexample that made
the Sylvester, `sin Θ`, ideal, off-diagonal, and Riccati declarations false as
stated.  Those declarations remain open proof obligations: the next analytic
step is to connect these actual restriction spectra to the existing coercive
bounds, using the complex spectral-order bridge first and a real bridge or
complexification transport afterward.

**General sine-theta architecture push (2026-07-15).** The unbounded
closed-operator equation now has an explicit domain-transport field; bounded
operators embed into the same model through `ClosedOperator.ofBounded`; the
unified unbounded Sylvester theorem is assembled by cases from the
interval/exterior and two semibounded orientations; the generalized and
isometric unbounded sine endpoints are reduced to the residual block identity,
Sylvester engine, ideal contraction, lower-frame transport, and exact-angle
identification. `SinTheta/Canonical.lean` now bundles the intended source
problem and reserves the unqualified source role for the generalized unbounded
result. Compiler feedback is expected to drive repair of the newly exposed
seams.

### Progress note (2026-07-16, genuine-spectrum sin Θ session)

The honest layer answering the vacuity finding now exists and its headline is
fully proved (axiom audit: `propext, Classical.choice, Quot.sound` on every
declaration):

- `ForMathlib/Analysis/CStarAlgebra/SelfAdjointGapInverse.lean`: for a
  self-adjoint element of a unital C*-algebra, `‖a‖ ≤ r` when the real
  spectrum lies in `[-r, r]`, and a two-sided inverse of norm at most `r⁻¹`
  when the spectrum avoids `(-r, r)` — both by the isometric continuous
  functional calculus.
- `DavisKahan/Experimental/InfiniteDimensional/Sylvester/GenuineSpectrum.lean`:
  `norm_sylvester_le_of_spectrum_intervalExterior`, the **constant-one
  interval/exterior Sylvester estimate** with genuine Banach-algebra spectra
  (shift-and-invert argument, no splitting, no `π/2` loss), and
  `sinTheta_genuineSpectrum`, the **fully general bounded operator-norm
  Davis--Kahan `sin Θ` theorem**: `U` reducing self-adjoint `A` with
  `spectrum ℝ (A|_U) ⊆ [a, b]`, `V` reducing self-adjoint `B` with
  `spectrum ℝ (B|_{Vᗮ})` outside `(a-d, b+d)` give
  `d · directedGap U V ≤ ‖B - A‖`.  Supporting API: `compressOperator`
  (honest restriction to a reducing subspace), its self-adjointness, the
  cross-block Sylvester equation, and the norm identification of the
  cross-block compression with the directed projection composition.

Scope status: this makes the classical `sin Θ` theorem **bounded
Hilbert-space theorem complete** (complex scalars, operator norm, genuine
spectra).  Remaining for "paper theorem complete": the symmetric/two-sided
form (maximum of the two directed gaps, as in `sinTheta_symmetric`), the
UI-norm/ideal scope, real scalars via complexification, and the unbounded
extension.

### Progress note (2026-07-16, unbounded sin Θ session)

The unbounded extension now has its honest operator-norm layer, fully proved
at `RCLike` generality (axiom audit clean on every declaration) in
`SinTheta/GenuineUnbounded.lean`:

- `ClosedOperator.norm_shift_apply_le_of_form_bounds`: a symmetric closed
  operator with quadratic form in `[β, α]` satisfies
  `‖B y - c y‖ ≤ r ‖y‖` on its domain (`c` center, `r` radius), by
  polarization and density — the unbounded numerical-radius-to-norm bridge.
- `norm_closedSylvester_le_of_intervalExterior` and
  `norm_closedSylvester_le_of_exteriorInterval`: constant-one estimates
  `δ ‖X‖ ≤ ‖C‖` for the domain-aware `ClosedSylvesterEquation`, in both
  orientations, with the exterior block carried by a proof-carrying bounded
  shifted inverse (`LeftShiftedInverseBound` /
  `TwoSidedShiftedInverseBound` — the resolvent reformulation of spectral
  exteriority, to be discharged later by an unbounded spectral theorem).
- `sinTheta_unbounded_opNorm`: **the unbounded Davis--Kahan `sin Θ`
  theorem in operator norm** — for the paper-shaped `UnboundedSinThetaData`
  with the trial block's form in `[β, α]` and the complementary block's
  shifted resolvent bounded by `((α-β)/2 + δ)⁻¹`, the conclusion
  `δ ‖X⋆ ∘ F₁‖ ≤ ‖R⋆ ∘ F₁‖`, through the proved adjoint residual block
  identity.

This lands Davis--Kahan Theorem 5.2 at operator-norm scope with honest
hypotheses.  The paper's full UI-norm scope for 5.2 remains open in
`Sylvester/Unbounded.lean` (Ky Fan cutoff route and the ideal-gauge
interval/exterior route, which additionally needs a gauge-closedness or
Neumann-series argument for ideal membership of the solution).  Elaboration notes for future waves: statements over
`[CStarAlgebra A]` applied to `E →L[ℂ] E` need
`import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`; the
`...ContinuousFunctionalCalculus.Basic` import is required for the base
`ℂ`/`IsStarNormal` instance; and `norm_nonneg`/`add_le_add_left` underscores
against CLM operator-norm goals can send the unifier into whnf timeouts —
use `ContinuousLinearMap.opNorm_nonneg` and `add_le_add le_rfl` instead.

### Progress note (2026-07-16, Spectra activation session)

Three gaps toward "paper theorem complete" closed (axiom audit clean on every
new declaration):

- `sinTheta_genuineSpectrum_symmetric` (`Sylvester/GenuineSpectrum.lean`): the
  **symmetric two-sided genuine-spectrum `sin Θ` theorem** — both directed
  spectral configurations give `d * subspaceGap U V ≤ ‖B - A‖` through the
  max-of-directed-gaps projector identity.
- `sylvester_mem_and_gauge_le_of_unbounded_bound_inverse`
  (`Core/UnboundedSpectral.lean`): the **one-unbounded ideal-gauge Sylvester
  engine**.  The solution is identified as the ideal-gauge limit of the
  Neumann iteration `X = Σ Jⁿ⁺¹ C Bⁿ` (contraction factor `ρ/(ρ+δ) < 1`),
  membership comes from the `gauge_complete` field plus operator-norm limit
  uniqueness, and the estimate `δ · gauge X ≤ gauge C` follows by absorption.
  This is the first fully proved UI-norm-scope Sylvester estimate with an
  unbounded block — the ideal-membership half of Theorem 5.2's
  interval/exterior case at ordinary rectangular-ideal generality.
  (The index universe of `finset_sum_mem`/`gauge_finset_sum_le` in
  `Ideals/Rectangular.lean` was generalized to `Type*` for the ℕ-indexed
  iteration.)
- **Spectra activation and the spectral-theorem discharge**
  (`SpectraBridge/GapResolvent.lean`).  The Stone/spectral-calculus import
  cone of the `external/Spectra` library was repaired for the root
  Lean/Mathlib pin (eight files, mechanical fixes: `map_sub`/`map_add`/
  `map_smul` through subtype mks instead of `convert using 1/2`;
  `convert`-generated instance-path congruence goals closed with `rfl`;
  beta-unreduced `Pi.neg_apply` patterns normalized before `rw`;
  ℂ-coerced scalar measurability in `AEStronglyMeasurable.smul`).  On top of
  it, written Spectra-idiomatically for upstreaming:
  `spectralProjection_eq_zero_of_forall_mem_resolventSet` (pointwise
  resolvent membership kills spectral mass, by second countability),
  `exists_norm_le_two_sided_shifted_inverse_of_spectralProjection_Ioo_eq_zero`
  (the quantitative gap resolvent `‖(A - c)⁻¹‖ ≤ s⁻¹` via the truncated
  symbol and the sharp calculus norm bound), and
  `exists_norm_le_two_sided_shifted_inverse_of_spectrum_gap` for self-adjoint
  `LinearPMap`s.  The DK-side corollaries discharge
  `TwoSidedShiftedInverseBound` from genuine spectrum avoidance
  (`twoSidedShiftedInverseBound_of_spectrum_gap`) and produce
  **`sinTheta_unbounded_opNorm_of_spectrum_gap`: the unbounded `sin Θ`
  theorem whose only spectral hypotheses are the trial block's form bounds
  and genuine (resolvent-set) spectrum avoidance of the complementary
  block** — the resolvent predicate is no longer an undischarged input.
  `SpectraBridge.All` is now registered in the
  `Experimental/InfiniteDimensional` tree.

### Progress note (2026-07-16, UI-norm unbounded sin Θ session)

The paper's unitary-invariant norm scope for the unbounded `sin Θ` theorem
is now proved (`SinTheta/GenuineUnboundedGauge.lean`, all axiom-clean,
`RCLike`-generic):

- `exists_bounded_shift_extension`: a symmetric closed operator with form
  in `[β, α]` has a bounded extension of its centered shift with norm at
  most the radius — `ContinuousLinearMap.extend` along the dense domain
  embedding, with `norm_shift_apply_le_of_form_bounds` as the bound.
- `mem_and_gauge_le_of_boundedLeft_exteriorRight`: the ideal-gauge
  constant-one Sylvester estimate in the `sin Θ` orientation.  The key
  observation: with the interval block realized bounded (`S`) and the
  exterior block carried by a shifted right inverse `J`, the domain-aware
  equation collapses to the everywhere-defined fixed point
  `Y = S Y J - C J`, and the Neumann argument runs entirely on the bounded
  side — no unbounded adjoints, no spectral cutoffs.
- `sinTheta_unbounded_gauge`: `δ · gauge (X⋆F₁) ≤ gauge (R⋆F₁)` with
  ideal membership of `X⋆F₁` — **Davis--Kahan Theorem 5.2's `sin Θ`
  passage at the paper's unitary-invariant norm scope** over any
  `RectangularSymmetricIdealFamily`.
- `SpectraBridge/GapResolvent.lean` adds the genuine-spectrum versions at
  `ℂ`: `sinTheta_unbounded_opNorm_of_spectrum_gap` and
  `sinTheta_unbounded_gauge_of_spectrum_gap`, whose only spectral inputs
  are form bounds and Spectra resolvent-set spectrum avoidance.
- `FullPartIII` aliases: `bounded_sinTheta_genuineSpectrum_symmetric`,
  `unbounded_sinTheta_uiNorm`, `unbounded_sinTheta_opNorm_genuineSpectrum`,
  `unbounded_sinTheta_uiNorm_genuineSpectrum`.

The bounded branch received the same upgrade
(`Sylvester/GenuineSpectrum.lean`):
`mem_and_gauge_sylvester_le_of_spectrum_intervalExterior` (the ideal-gauge
interval/exterior Sylvester estimate with genuine Banach-algebra spectra,
by feeding the CFC shift-and-invert data into the Neumann ideal engine
through `ClosedOperator.ofBounded`), and `sinTheta_genuineSpectrum_gauge`:
**the bounded `sin Θ` theorem at unitary-invariant ideal scope with
genuine spectra** — `B - A` in the family gives
`d · gauge (P_{Vᗮ} P_U) ≤ gauge (B - A)` with membership of the directed
projection composition.  `FullPartIII` aliases:
`bounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`,
`bounded_sinTheta_uiNorm_genuineSpectrum`.

**`sin Θ` scope summary after this session**: genuine spectra + operator
norm + UI norm, at bounded and unbounded scope, directed and (bounded)
symmetric two-sided forms — every combination proved and axiom-clean.
The symmetric two-sided form also holds at UI scope
(`sinTheta_genuineSpectrum_gauge_symmetric`, constant `2`, via the
projector-difference decomposition
`P_U - P_V = P_{Vᗮ}P_U - (P_{Uᗮ}P_V)⋆` proved in
`starProjection_sub_eq_cross_sub_cross_adjoint`; the constant-one version
would need UI direct-sum/singular-value-union laws not yet in the family
API).  Alias: `bounded_sinTheta_uiNorm_genuineSpectrum_symmetric`.

The unbounded interval/exterior Sylvester estimate now also holds at ideal
scope in **both orientations**
(`closedSylvesterEquation_boundedRealization` +
`mem_and_gauge_le_of_exteriorLeft_intervalRight` in
`SinTheta/GenuineUnboundedGauge.lean`): the form-bounded block is realized
bounded through its shift extension, the domain-aware equation extends to
the whole space by density and the closed graph of the exterior block, and
the shifted configuration feeds the Neumann ideal engine.  `FullPartIII`
aliases: `unbounded_sylvester_intervalExterior_uiNorm`,
`unbounded_sylvester_exteriorInterval_uiNorm`.  This is the honest
replacement for the `realSpectrum`-based
`unbounded_sylvester_mem_and_gauge_le_of_intervalExteriorGap` obligation.

Remaining for "paper theorem complete" on the `sin Θ` family: the Ky Fan
cutoff route for the two semibounded orientations of Theorem 5.2
(`Sylvester/Unbounded.lean`, needs unbounded spectral cutoffs — now within
reach through `spectralProjection`/`spectralCalculus` of the activated
Spectra cone), and real scalars via complexification.  Note the sin Θ
endpoint no longer waits on those: the interval/exterior configuration the
paper uses for the residual bound is fully covered at both operator-norm
and UI-norm scope.

Controlling blocker identified for the two-projection calculus at source
scalar generality: an `RCLike`-generic positive operator square root
(`operatorAbsoluteValue`) is unavailable in Mathlib (operator CFC is
`ℂ`-only) and the repo's `IsPositive.sqrt` is finite-dimensional. The whole
`Core/OperatorAngle` ladder (`sinAngleOperator`, `cosAngleOperator`,
`angleOperator`, and their norm identities) waits on a route decision:
norm-preserving complexification transfer versus a direct order-theoretic
construction, or specializing the infinite-dimensional angle calculus to `ℂ`
with a real-scalar bridge afterward.

**Route decision taken (2026-07-16): specialize to `ℂ`**, consistent with
the genuine-spectrum layer, real bridge by complexification later.  First
rungs proved and axiom-clean:
`ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean` defines
`operatorAbs T = (T⋆T)^(1/2)` via `CFC.sqrt` with the Loewner/StarOrder
instances from `Mathlib.Analysis.InnerProductSpace.StarOrder`, proving
nonnegativity, self-adjointness, the defining square identity, uniqueness,
`‖|T|‖ = ‖T‖`, and the pointwise isometry `‖|T|x‖ = ‖Tx‖`.
`Core/OperatorAngleComplex.lean` then defines
`sinAngleOperatorC U V = |P_U - P_V|` and proves
`‖sinAngleOperatorC U V‖ = subspaceGap U V` — the honest `ℂ` counterparts
of the blocked `sinAngleOperator`/`norm_sinAngleOperator` obligations.
Next rungs: the Halmos two-projection decomposition for
`cosAngleOperatorC`/`sinTwoAngleOperatorC` (`2 sin cos`), then the genuine
`sin 2Θ` theorems.

### Progress note (2026-07-17, the sharp reflection-defect estimate)

Toward the residual `sin 2Θ` form (all axiom-clean):
`reflectionDefect_eq_neg_two_smul_offdiag`
(`J_V A J_V - A = -2 (P_{Vᗮ} A P_V + P_V A P_{Vᗮ})`) and the **sharp
estimate** `norm_reflectionDefect_le_two_mul_norm_cross`:
`‖J_V A J_V - A‖ ≤ 2 ‖P_{Vᗮ} A P_V‖` for self-adjoint `A`, with **no
reduction hypothesis on `V`** — the two off-diagonal blocks are mutually
adjoint and have orthogonal input/output splittings, so their sum is
bounded by the larger block.  Aliases:
`bounded_reflectionDefect_offdiag`, `bounded_reflectionDefect_le_cross`.
The residual `sin 2Θ` theorem now needs only: `V := closed range of the
isometric trial embedding`, the bound `‖P_{Vᗮ} A P_V‖ ≤ ‖residual‖`
(pointwise on the range, by the residual identity), and the reflected-pair
`sin Θ` argument of `sinTwoTheta_genuineSpectrum`.

### Progress note (2026-07-17, the residual `sin 2Θ` theorem)

The residual form is proved (all axiom-clean), closing the
"residual (approximate-invariant-pair) form" gap in the `sin 2Θ` family:

- `sinTwoTheta_genuineSpectrum_defect`: the reflected-pair core
  `d * subspaceGap U (J_V U) ≤ ‖reflectionDefect V A‖`, factored out of
  `sinTwoTheta_genuineSpectrum` so both the reduced-comparison and the
  residual forms consume it (the comparison form is now a three-line
  corollary);
- `norm_cross_le_norm_residual`: if `V` is the range of an isometric
  embedding `X` and `R = A X - X M`, then `‖P_{Vᗮ} A P_V‖ ≤ ‖R‖` — on
  `v = X u`, `(1 - P_V) A v = (1 - P_V) (R u)` since `X (M u) ∈ V`, and
  the isometry converts `‖u‖` back to `‖P_V z‖`;
- **`sinTwoTheta_genuineSpectrum_residual`**: for self-adjoint `A` with
  the genuine internal configuration at the reducing `U`, trial subspace
  `V = range X`, and *arbitrary* comparison operator `M` on the trial
  space, `d * subspaceGap U (J_V U) ≤ 2 ‖A X - X M‖` — the paper's
  residual `sin 2Θ` bound, with no reduction or self-adjointness
  hypothesis on the comparison pair, by chaining the defect core with
  `norm_reflectionDefect_le_two_mul_norm_cross` and the cross-residual
  bound.

Aliases: `bounded_sinTwoTheta_genuineSpectrum_defect`,
`bounded_cross_le_residual`, `bounded_sinTwoTheta_genuineSpectrum_residual`.

### Progress note (2026-07-17, the double-angle identification)

The `sin 2Θ` family is now closed at the operator level (all axiom-clean),
without the Halmos two-projection decomposition — pure C⋆-norm algebra
substitutes for it:

- `ForMathlib.norm_operatorAbs_mul` / `norm_mul_operatorAbs`: the
  C⋆-composition identities `‖|S| D‖ = ‖S D‖` (from
  `(|S|D)⋆(|S|D) = D⋆(S⋆S)D = (SD)⋆(SD)`) and `‖D |T|‖ = ‖D T⋆‖`;
- `norm_sinTwoAngleOperatorC`: the exact norm
  `‖sin 2Θ(U, V)‖ = 2 ‖P_{Vᗮ} P_U P_V‖` — the absolute values drop out
  of `2 ‖sin Θ_d · cos Θ‖` by the two identities, leaving the compressed
  cross block;
- `norm_offdiag_add_eq`: `‖P_{Vᗮ} A P_V + P_V A P_{Vᗮ}‖ = ‖P_{Vᗮ} A P_V‖`
  for self-adjoint `A` (`≤` from the sharp defect estimate, `≥` by
  restriction to `V`);
- `starProjection_map_reflection` / `subspaceGap_map_reflection`:
  `P_{J_V U} = J_V P_U J_V`, hence
  `subspaceGap U (J_V U) = ‖reflectionDefect V P_U‖`;
- **`subspaceGap_map_reflection_eq_norm_sinTwoAngle`**: the double-angle
  identification `subspaceGap U (J_V U) = ‖sinTwoAngleOperatorC U V‖` —
  both sides equal `2 ‖P_{Vᗮ} P_U P_V‖`;
- **`sinTwoTheta_genuineSpectrum_operator`** and
  **`sinTwoTheta_genuineSpectrum_residual_operator`**: the exact operator
  forms `d * ‖sin 2Θ(U, V)‖ ≤ 2 ‖B - A‖` and
  `d * ‖sin 2Θ(U, V)‖ ≤ 2 ‖A X - X M‖` — the paper's `sin 2Θ` theorems
  stated on the functional-calculus double-angle sine operator.

Aliases: `bounded_sinTwoAngle_norm_eq`,
`bounded_sinTwoAngle_gap_identification`,
`bounded_sinTwoTheta_genuineSpectrum_operator`,
`bounded_sinTwoTheta_genuineSpectrum_residual_operator`.

### Progress note (2026-07-17, boundedness from a bounded spectrum)

New Spectra-backed seam for the fully unbounded Theorem 5.2
(`SpectraBridge/BoundedFromSpectrum.lean`, axiom-clean):
**`exists_boundedRealization_of_spectrum_subset_Icc`** — a closed densely
defined self-adjoint operator with `Spectra.Resolvent.spectrum ⊆ [β, α]`
admits a `BoundedRealization` on the whole space with
`‖A - (β+α)/2‖ ≤ (α-β)/2`.  Assembled from four Spectra bricks
transported along `generator_genToGroup`: the spectral projection
vanishes off the spectrum (`E([β,α]ᶜ) = 0`), complementation
(`E([β,α]) = 1`), spectrally bounded vectors lie in the generator's
domain (so the domain is everything), and the centered norm bound
`generator_sub_smul_norm_le_Icc`.  Alias:
`unbounded_boundedRealization_of_spectrum_Icc`.  This discharges the
honest content of the scaffold obligations
`boundedRealization_of_spectrumIn_Icc`/`boundedRealization_of_spectrumIcc`
(whose `realSpectrum` is still a placeholder definition) and is the
missing interval-block step for the interval/exterior orientation of
Theorem 5.2 with a genuinely unbounded exterior block: the interval
block is secretly bounded, after which the proved mixed orientations
(`mem_and_gauge_le_of_exteriorLeft_intervalRight`,
`mem_and_gauge_le_of_boundedLeft_exteriorRight`) apply.  Next rung: the
assembly of that reduction (transport the closed Sylvester equation
across the bounded realization).

### Progress note (2026-07-17, Theorem 5.2 interval/exterior with genuine spectra)

The assembly is done (`SpectraBridge/UnboundedIntervalExterior.lean`, all
axiom-clean).  Both orientations of the Theorem 5.2 interval/exterior
configuration are now proved with **both blocks genuinely closed
self-adjoint operators** and all spectral hypotheses phrased through the
Spectra spectrum:

- `semibounded_of_spectrum_subset_Icc`: spectral inclusion in `[β, α]`
  gives the matching quadratic-form bounds, through the bounded
  realization and the centered norm estimate (`|re ⟪(B - c)x, x⟫| ≤
  ρ ‖x‖²`);
- **`unbounded_sylvester_mem_and_gauge_le_of_spectra_exteriorLeft_intervalRight`**:
  `A X - X B = C` with `σ(B) ⊆ [β, α]` and `σ(A) ∩ (β-δ, α+δ) = ∅` gives
  `X ∈ N` and `δ · gauge X ≤ gauge C` — through the form bounds and the
  Spectra-backed two-sided shifted inverse;
- **`unbounded_sylvester_mem_and_gauge_le_of_spectra_intervalLeft_exteriorRight`**:
  the opposite orientation, replacing the interval block by its bounded
  realization and feeding the transported equation to the bounded-left
  Neumann engine.

Aliases: `unbounded_semibounded_of_spectrum_Icc`,
`unbounded_sylvester_exteriorInterval_uiNorm_genuineSpectrum`,
`unbounded_sylvester_intervalExterior_uiNorm_genuineSpectrum`.  With
these, the interval/exterior branch of Theorem 5.2 is closed at
genuine-spectrum scope; the remaining Theorem 5.2 branch is the ordered
(two-semibounded) configuration, whose documented route is the Ky Fan
spectral-cutoff argument.

### Progress note (2026-07-17, tangent norm bounds)

Angle ladder, eighth rung (all axiom-clean): the inverse-norm estimate
`norm_cosAngleExtendedCEquiv_symm_apply_le`
(`‖(cos Θ + P_{Uᗮ})⁻¹ y‖ ≤ c⁻¹ ‖y‖` from coercivity) and
**`norm_tanAngleOperatorC_le`**:
`‖tan Θ(U,V)‖ ≤ directedGap · (min (√(1-g²)) 1)⁻¹` — the inequality half
of `‖tan Θ‖ = tan θ_max`.  Alias: `bounded_tanAngle_norm_le`.

### Progress note (2026-07-17, the double-angle tangent)

Angle ladder, seventh rung (all axiom-clean): **`tanTwoAngleOperatorC`
exists.**  Two general helpers were extracted:
`ker_bot_range_top_of_isSelfAdjoint_of_bounded_below` (a self-adjoint
operator bounded below in norm is boundedly invertible — kernel, closed
range, self-adjoint density) and
`norm_add_starProjection_orthogonal_apply_ge` (coercivity of a
`U`-supported operator extended by the identity on `Uᗮ`).  On top:
`cosTwoAngleOperatorC = cos² - sin²` with self-adjointness, support,
invariance, and **quarter-acute coercivity**
`‖cos 2Θ x‖ ≥ (1 - 2 g²)‖x‖` on `U` (quadratic form + Cauchy--Schwarz);
the extended `cos 2Θ + P_{Uᗮ}` is invertible in the quarter-acute regime,
and `tanTwoAngleOperatorC := sin 2Θ · (cos 2Θ + P_{Uᗮ})⁻¹` carries its
defining identity.  `FullPartIII` aliases:
`bounded_cosTwoAngleOperatorC`, `bounded_cosTwoAngle_coercive`,
`bounded_cosTwoAngleExtended_invertible`, `bounded_tanTwoAngleOperatorC`,
`bounded_tanTwoAngle_defining_identity`.  All four operator constructions
of the paper's angle calculus (sin, cos, sin 2Θ, tan Θ, cos 2Θ, tan 2Θ)
now exist at `ℂ` with their defining algebra proved.

### Progress note (2026-07-17, the tangent operator)

Angle ladder, sixth rung (all axiom-clean): **`tanAngleOperatorC` exists.**
`commute_cosAngleOperatorC_starProjection` and `cosAngleOperatorC_apply_mem`
(the cosine commutes with `P_U` and preserves `U`, by nonneg CFC
commutation), the extended cosine `cosAngleExtendedC = cos Θ + P_{Uᗮ}`
with self-adjointness and **global coercivity**
`min (√(1 - g²)) 1 · ‖x‖ ≤ ‖(cos Θ + P_{Uᗮ}) x‖` (orthogonal
decomposition + acute coercivity on the source), and
`cosAngleExtendedC_ker_bot_range_top`: in the acute regime the extended
cosine is **boundedly invertible** — trivial kernel from coercivity,
closed range by the antilipschitz bound, full range by self-adjointness
(`orthogonal_eq_bot_iff`).  `cosAngleExtendedCEquiv` packages the
`ContinuousLinearEquiv` (open mapping via `ofBijective`), and
`tanAngleOperatorC := sin Θ_directed ∘ (cos Θ + P_{Uᗮ})⁻¹` with the
defining identity `tan Θ ∘ (cos Θ + P_{Uᗮ}) = sin Θ_directed`.
`FullPartIII` aliases: `bounded_cosAngleExtended_invertible`,
`bounded_tanAngleOperatorC`, `bounded_tanAngle_defining_identity`.
Next: the tan Θ theorem (`d·‖tan Θ‖ ≤ ‖R‖` under the one-sided spectral
configuration, via the Sylvester engine against the graph/angular-operator
representation), and `tanTwoAngleOperatorC` by the same extended-inverse
pattern at the quarter-acute threshold.

### Progress note (2026-07-17, acute coercivity of the cosine)

Angle ladder, fifth rung (all axiom-clean):
`operatorAbs_apply_eq_zero_iff` (the absolute value vanishes exactly where
the operator does, from the pointwise isometry),
`cosAngleOperatorC_apply_eq_zero_of_mem_orthogonal` (the directed cosine
is supported on the source subspace), and **acute coercivity**
`norm_cosAngleOperatorC_apply_ge`:
`‖cos Θ(U,V) x‖ ≥ √(1 - directedGap²) ‖x‖` on `U`, by the pointwise
Pythagoras — with the corollary that in the acute regime the cosine is
injective on the source (`cosAngleOperatorC_eq_zero_imp_of_acute`).
`FullPartIII` aliases: `bounded_cosAngle_coercive`,
`bounded_cosAngle_injective_of_acute`.  This is the quantitative input for
the bounded inverse of the cosine on `U` (hence `tanAngleOperatorC`): what
remains for the tangent is packaging the coercive positive operator
`cos + P_{Uᗮ}` as invertible and forming `sin · (cos + P_{Uᗮ})⁻¹`.

### Progress note (2026-07-17, commutation and the double-angle operator)

Angle ladder, fourth rung (all axiom-clean): the ForMathlib absolute-value
commutation law `operatorAbs_commute_operatorAbs` (commuting squares give
commuting absolute values, through `Commute.cfcₙ_nnreal` twice), the
compressed-square commutation `commute_cross_sq` (via the square Pythagoras
`cross_sq_add_cross_sq` and `commute_compress_starProjection` — a
compression by `P_U` commutes with `P_U`), hence **the directed sine and
cosine operators commute**
(`commute_sinAngleOperatorDirectedC_cosAngleOperatorC`).  On top of it,
`sinTwoAngleOperatorC := 2 • (sin Θ_directed · cos Θ)` is defined with
self-adjointness and `‖sin 2Θ‖ ≤ 2 · directedGap`.  `FullPartIII` aliases:
`bounded_angle_commute`, `bounded_sinTwoAngleOperatorC`,
`bounded_sinTwoAngleOperatorC_norm_le`.  The remaining Halmos content is
now localized to spectral-mapping statements (norms and spectra of the
commuting pair on the generic block), the tan operators (needing the
inverse of the cosine in the acute regime), and the identification of
`sinTwoAngleOperatorC` with the reflected-image gap proved in
`DoubleAngleGenuine.lean`.

### Progress note (2026-07-17, Spectra vendoring + operator Pythagoras)

Upstream integration change (pulled): Spectra is now **vendored** at
`vendor/Spectra` (pristine upstream snapshot `8dbaaf6` plus the committed
compatibility patch under `vendor/patches/Spectra/`); `external/Spectra`
is a read-only reference submodule and the build must not depend on it
(see the AGENTS.md Spectra collaboration policy).  All `Spectra.*` imports
in this repo now resolve to the vendored snapshot; the full build is green
against it.

Angle ladder, third rung: `sinAngleOperatorDirectedC U V = |P_{Vᗮ} P_U|`
with `‖·‖ = directedGap U V`, the cross-block square identity
`(P_W P_U)⋆(P_W P_U) = P_U P_W P_U`, and the **operator-level Pythagoras**
`sinAngleOperatorDirectedC² + cosAngleOperatorC² = P_U` — pure projection
algebra through the absolute-value square law.  `FullPartIII` aliases:
`bounded_sinAngleOperatorC_norm`, `bounded_sinAngleOperatorDirectedC_norm`,
`bounded_angle_pythagoras`.

### Progress note (2026-07-16, cosine rung)

`Core/OperatorAngleComplex.lean` gains the second angle-ladder rung:
`cosAngleOperatorC U V = |P_V P_U|` with nonnegativity, self-adjointness,
`‖cos Θ‖ = ‖P_V P_U‖`, contractivity, and the pointwise Pythagoras law
`sq_norm_sin_add_sq_norm_cos` (`‖P_{Vᗮ}x‖² + ‖P_V x‖² = ‖x‖²` on `U`) —
the vector-level `sin² + cos² = 1`.  Remaining for the full Halmos ladder:
the operator-level `sin² + cos² = 1` on the generic block, commutation of
the sine and cosine operators, and `sinTwoAngleOperatorC = 2 sin cos`.

### Progress note (2026-07-16, direct-rotation scalar core)

`principalHalfPhase_displacement_minimal_scalar`
(`SpectraBridge/DirectRotationSquare.lean`) is proved — without the
`Real.Angle` halving API the route note anticipated: any unit `w` with
`w² = z` factors as `(w - phz)(w + phz) = 0` against the proved square
identity, and the principal branch's nonnegative real part
(`re ((1+z)/‖1+z‖) ≥ 0`) makes its displacement from `1` the smaller of
the two roots'.  This is the per-fiber analytic core of the
direct-rotation extremality (Section 7); the remaining two obligations in
that file (`spectraDirectRotation_unique`, `spectraDirectRotation_minimal`)
are the genuine two-projection-decomposition/multiplicity passages.

### Progress note (2026-07-16, real spectral bridge session)

**The real-scalar gap for the bounded `sin Θ` theorem is closed** — without
complexification, by the direct Rayleigh-shift route the bridge file
recorded: `upperFormBoundOn_top_of_spectrum_subset_Iic`
(`Core/RealSpectralBridge.lean`, now sorry-free and axiom-clean) shifts by
`m = ‖A‖ + 1`, transports the spectrum with `spectrum.add_singleton_eq`,
derives spectral positivity and the `c + m` upper bound from
`spectrum.norm_le_norm_of_mem`, converts the spectral radius through
`ContinuousLinearMap.spectralRadius_eq_nnnorm` (nonemptiness of the shifted
spectrum by contradiction through the radius identity), and finishes with
the Rayleigh estimate.  Consequently
`opNorm_starProjection_sub_le_of_restriction_spectra` — **the real
Hilbert-space Davis--Kahan theorem with genuine restriction spectra**
(`‖P_U - P_W‖ ≤ ‖B - A‖ / g` from `Ici`/`Iic` spectra of the actual
restrictions) — is fully proved.  `FullPartIII` aliases:
`real_sinTheta_symmetric_genuineSpectrum`,
`real_upperFormBound_of_spectrum`.

### Progress note (2026-07-16, genuine sin 2Θ session)

**The genuine-spectrum `sin 2Θ` theorem is proved**
(`DoubleAngleGenuine.lean`, all axiom-clean, complex scalars), without
waiting on the Halmos decomposition, by the reflection argument:

- upstream-candidate transport layer: `ContinuousLinearEquiv.conjAlgEquiv`
  (conjugation as an algebra equivalence of endomorphism algebras),
  `conjByIsometryEquiv` with transport of self-adjointness, reducing
  subspaces (`Reduces.map_isometryEquiv`, via
  `Submodule.map_orthogonal_equiv`), compressions
  (`compressOperator_map`, via `Submodule.starProjection_map_apply` and the
  isometric restriction `submoduleMapIsometry`), and **real spectra**
  (`spectrum_compressOperator_map`, via `AlgEquiv.spectrum_eq` after scalar
  restriction);
- `sinTwoTheta_genuineSpectrum`: for self-adjoint `A` with genuine internal
  configuration at the reducing `U` (compression to `U` in `[a, b]`,
  compression to `Uᗮ` outside `(a-d, b+d)`) and any `B` reduced by `V`,
  `d * subspaceGap U (J_V U) ≤ 2 ‖B - A‖` where `J_V U` is the reflected
  image — the gap to the reflected image is `‖sin 2Θ(U, V)‖`; also phrased
  through `sinAngleOperatorC` (`sinTwoTheta_genuineSpectrum_sinAngle`).
  Route: apply `sinTheta_genuineSpectrum_symmetric` to the pair
  `(A, J A J)` — the conjugate has the *same* genuine compression spectra —
  and bound `‖J A J - A‖ = ‖reflectionDefect V A‖ ≤ 2‖B - A‖` by the
  proved defect estimate.  `FullPartIII` aliases:
  `bounded_sinTwoTheta_genuineSpectrum`,
  `bounded_sinTwoTheta_genuineSpectrum_sinAngle`.

This replaces the `FiniteGapConfiguration`-gated `sinTwoTheta_perturbation`
obligation with an honest statement.  The UI-norm scope is also proved:
`sinTwoTheta_genuineSpectrum_gauge` gives ideal membership of the directed
cross block to the reflected image with
`d · gauge ≤ 2 · gauge (B - A)`, using
`reflectionDefect_eq_perturbationDefect` and reflection-conjugation
contractivity of the gauge (alias
`bounded_sinTwoTheta_uiNorm_genuineSpectrum`).  The residual
(approximate-invariant-pair) form is now proved
(`sinTwoTheta_genuineSpectrum_residual`; see the residual progress note),
and the identification with the functional-calculus
`sinTwoAngleOperatorC` is also proved
(`subspaceGap_map_reflection_eq_norm_sinTwoAngle`; see the double-angle
identification progress note) — the `sin 2Θ` family is closed at the
operator level. See `dev/sorry-difficulty-ranking.md` for the evolving proof-obligation ranking; verify its totals against the source tree before using them in status claims.

### Progress note (2026-07-17, the infinite-dimensional `tan Θ` theorem)

The per-vector, pole-free Davis--Kahan `tan Θ` theorem is proved on
infinite-dimensional Hilbert spaces
(`Experimental/InfiniteDimensional/TanTheta/Vector.lean`, all axiom-clean):
**`tan_theta_le'`** — `T` symmetric on a complete space, `V` a
`T`-invariant subspace with the complementary quadratic form in the strip
`[α, β]`, `Z` a test subspace whose compression is coercive at distance
`(β-α)/2 + δ` from the midpoint, `ρ` a columnwise residual bound over
`Z`; then `δ ‖x - P_V x‖ ≤ ρ ‖P_V x‖` for every `x ∈ Z` — the per-vector
form of `tan ∠(Z, V) ≤ ρ/δ`, forcing `Z ∩ Vᗮ = 0`, with no dimension
comparison between `Z` and `V`.  This is the infinite-dimensional form of
the finite theorem in `FiniteDimensional/TanTheta/Vector.lean`: the
finite proof's compact-sphere maximizer is replaced by the operator norm
`κ` of the compressed projection `P_Z|_{Vᗮ}` and an approximate-supremum
limit — near-maximizing vectors from
`ContinuousLinearMap.exists_lt_apply_of_lt_opNorm` give
`(e+δ)(κ-ε) ≤ κe + ρ√(1-(κ-ε)²)` for all small `ε > 0`, and continuity
in `ε` (`ge_of_tendsto` along `𝓝[Ioo 0 κ] 0`) yields the exact
`δκ ≤ ρ√(1-κ²)`; the strip bound uses Hellinger--Toeplitz
(`IsSymmetric.continuous`) in place of finite-dimensional automatic
continuity.  Supporting lemmas `norm_map_sub_midpoint_smul_le'` and
`norm_starProjection_map_le_of_mem_orthogonal'` are ported at full
generality.  Alias: `bounded_tanTheta_perVector`.  The `tan Θ` family now
has: the constructed operator `tanAngleOperatorC` with defining identity
and norm bound, and the per-vector theorem at infinite-dimensional
scope; still open are the UI-norm Ritz-residual forms (the
`principalTangents` route of `FiniteDimensional/TanTheta/RitzResidual`)
and the `tan θ_max = ‖angular operator‖` identification.

### Progress note (2026-07-17, `tan Θ` with genuine spectra)

The bounded genuine-spectrum `tan Θ` theorem is proved
(`Experimental/InfiniteDimensional/TanTheta/GenuineSpectrum.lean`, all
axiom-clean): **`tanTheta_genuineSpectrum`** — for self-adjoint `T`, a
`T`-invariant subspace `V` with `σ(T|_{Vᗮ}) ⊆ [α, β]` (Banach-algebra
spectrum of the compression), and a test subspace `Z` whose compression
spectrum avoids `(α - δ, β + δ)`, a columnwise residual bound `ρ` over
`Z` gives `δ ‖x - P_V x‖ ≤ ρ ‖P_V x‖` on `Z`.  Two reusable spectral
bridges feed the per-vector theorem:
`formBounds_of_compress_spectrum_subset_Icc` (interval compression
spectrum gives the quadratic-form strip, through
`IsSelfAdjoint.norm_le_of_spectrum_subset_Icc` on the centered
compression) and `coercive_of_compress_spectrum_exterior` (exterior
compression spectrum gives midpoint coercivity, through
`IsSelfAdjoint.exists_two_sided_inverse_of_spectrum_gap`).
Proof-engineering note: `IsSelfAdjoint.sub`/C⋆-lemma applications on
compressions over subtype spaces need the algebra given explicitly
(`(R := ↥W →L[ℂ] ↥W)`, `(A := ...)`) plus `maxHeartbeats 1600000` for
the star-instance defeq checks — same pattern as
`Sylvester/GenuineSpectrum`.  Aliases: `bounded_tanTheta_genuineSpectrum`,
`bounded_formBounds_of_spectrum_Icc`,
`bounded_coercive_of_spectrum_exterior`.  The `tan Θ` family is now
bounded-Hilbert-space complete in per-vector form with honest spectral
hypotheses; still open are the UI-norm Ritz-residual forms and the
`tan θ_max = ‖angular operator‖` identification.

### Progress note (2026-07-17, graph projection formula)

The graph projection formula is defined and proved
(`Experimental/InfiniteDimensional/GraphSubspace.lean`, axiom-clean):
**`graphProjectionFormula`** is now the closed operator expression
`A N⁻¹ A⋆` with `A = P_U + X P_U` the graph parametrization and
`N = 1 + (X P_U)⋆ (X P_U)` the normal-equation operator (`Ring.inverse`
keeps the definition total in `X`), and
**`projection_graphSubspace_formula`** shows it equals
`projection (graphSubspace U X)` for every angular operator, at fully
`RCLike`-generic scalars.  No functional-calculus square roots are
needed: angularity gives the algebra `A⋆ A = N P_U`, `P_U N = N P_U`,
and `A⋆ (A N⁻¹ A⋆) = A⋆`, so `A N⁻¹ A⋆ z` lies on the graph while
`z - A N⁻¹ A⋆ z` is orthogonal to it, and
`Submodule.eq_starProjection_of_mem_of_inner_eq_zero` closes the proof.
Invertibility of `N` comes from a new upstreamable operator
Lax--Milgram lemma `ForMathlib.ContinuousLinearMap.isUnit_of_coercive`
(`ForMathlib/Analysis/InnerProductSpace/CoerciveUnit.lean`): a
uniformly coercive bounded operator on a Hilbert space is a unit —
coercivity alone forces injectivity, closed range (antilipschitz), and
trivial orthogonal complement of the range, with no self-adjointness
hypothesis.  Aliases: `graph_projection_operator`,
`graph_projection_formula` (now proved), `bounded_coercive_isUnit`.
Still open in the graph arc are the
`tan θ_max = ‖angular operator‖` identification and the contractivity
criterion `norm_angularOperator_lt_one_iff`, both of which reduce to
the gap computation `‖P_U - P_V‖ = ‖X‖ / √(1 + ‖X‖²)` now reachable
through the proved projection formula.

### Progress note (2026-07-17, tan of the maximal angle)

The graph-subspace arc is closed (`GraphSubspace.lean` now has no open
obligations; all results axiom-clean at `RCLike`-generic scalars):
**`norm_projection_sub_projection_graphSubspace`** /
**`subspaceGap_graphSubspace`** give the exact gap
`‖P_U - P_V‖ = ‖X‖ / √(1 + ‖X‖²)` for the graph `V` of an angular
operator `X`, **`tan_maximalAngle_eq_norm_angularOperator`** derives
`tan θ_max = ‖X‖`, and **`norm_angularOperator_lt_one_iff`** identifies
contractive angular operators with maximal angle below `π/4`.  No
functional calculus is used anywhere: through the wave-25 projection
formula the blocks `P (1 - Q)` and `(1 - P) Q` satisfy
`T T⋆ = 1 - (1 + B)⁻¹` with `B = X⋆X` and `B = X X⋆` (the latter through
the intertwining `X (1 + X⋆X)⁻¹ = (1 + X X⋆)⁻¹ X`), and the new
`ForMathlib` brick **`norm_one_sub_inverse_one_add`**
(`CoerciveUnit.lean`) evaluates `‖1 - (1 + B)⁻¹‖ = ‖B‖/(1 + ‖B‖)`
exactly for positive `B` — upper bound by the quadratic form along the
substitution `z = (1 + B) y` with the positive-operator Cauchy–Schwarz
inequality `norm_apply_sq_le_of_positive` (also new, proved by
evaluating the form at `y - ‖B‖⁻¹ B y`), lower bound from
near-maximizers of `‖B‖` and a small-`ε` limit.  A `U`-blockwise
Pythagoras estimate pins `‖P_U - P_V‖` at the common block value.  Also
added `isUnit_one_add_star_mul_self`.  Proof-engineering note: rewrite
against C⋆-lemmas (`CStarRing.norm_star_mul_self`, `norm_star`) through
locally restated `have`s — the library statements carry a different
star-instance path and fail as `rw` patterns on `E →L[𝕜] E`.  Aliases:
`graph_gap_value`, `graph_subspaceGap`, `graph_tan_maximalAngle`,
`graph_contractive_iff_quarterAcute`, `bounded_inverse_defect_norm`,
`bounded_positive_cauchy_schwarz`, `bounded_one_add_star_mul_self_isUnit`.


### Progress note (2026-07-18, real operator-angle complexification)

The independent real-angle bridge is now implemented without touching the
approximation-number or Ky Fan layers. `Core/ComplexificationSubspace.lean`
complexifies real subspaces coordinatewise and proves exact transport of
orthogonal complements, orthogonal projections, symmetric and directed gaps,
acuteness thresholds, and reducing-subspace data. In particular, the
projection onto the complexified subspace is identified exactly with
the complexification of the original real projection.

`Core/OperatorAngleReal.lean` then applies the completed complex operator-angle
calculus to those complexified subspaces. It supplies real-subspace wrappers
for sine, directed sine, cosine, double-angle sine, tangent, and double-angle
tangent, with exact real gap norm identities, operator Pythagoras, commutation,
and the acute/quarter-acute tangent defining identities. The remaining descent
seam is narrower: prove the conjugation-invariant angle operators preserve the
canonical real copy when an actual real-valued angle operator is required.
