/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.TanTwoTheta
import ForMathlib.Analysis.InnerProductSpace.DavisKahanTheory.FrameFactorization

/-!
# Generalized finite-dimensional Davis--Kahan theorems

This file records the finite-dimensional forms of the generalizations stated
after the four headline theorems in Davis--Kahan (1970).

Literature map:

* `ForMathlib/prose/Davis-Kahan-1970-part-III-core-arguments.tex`,
  Sections 5--11.
* Davis--Kahan (1970), Theorems 6.1--6.3 and 8.2.

The important extra features are non-orthonormal trial vectors, comparison of
subspaces of unequal dimension, the square-norm fallback under arbitrary
spectral separation, and the continuation argument selecting the acute branch
of a double-angle estimate.  These are kept separate from the sharp clean API
so their conditioning losses are visible in theorem statements.
-/


/-! ## Construction status

The shared injective-trial-map coordinate layer now lives in
`DavisKahanTheory.FrameFactorization`.  It provides the canonical rectangular
polar factorization `X = Q T`, proves that `Q` is isometric with
`range Q = range X`, and packages the positive Gram square root `T` as a
linear equivalence.  It also proves `‖T⁻¹‖ ≤ ε⁻¹`, the corresponding
right-ideal estimate for every rectangular UI norm, and the assembled
frame-to-sine transport inequality
`ε * N (P_{Vᗮ} Q) ≤ N (P_{Vᗮ} X)`.

Theorem 6.1 is assembled below from this coordinate layer and the raw
projected Sylvester identity.  The source-complete endpoints accept either
interval/exterior orientation, derive injectivity from either the positive
lower frame bound or the paper's Gram-operator inequality, and keep coordinate
operators such as `M` in their original self-adjoint coordinates throughout.
The final wrapper also accepts any `sin Θ₀` operator with the canonical complete
singular-value sequence.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators Topology
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Symmetric compression after whitening a full-column-rank trial map.

If `X = Q G^{1/2}` is the polar/whitening factorization, this is `Q⋆ A Q`.
The coordinate Rayleigh quotient `(X⋆X)⁻¹ X⋆ A X` is similar to this operator
but is generally only self-adjoint for the Gram inner product. -/
noncomputable def generalizedCompression (A : E →ₗ[𝕜] E)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X) : F →ₗ[𝕜] F :=
  compression A (orthonormalizedEmbedding X hX)

/-- The whitened generalized compression is symmetric for a symmetric
ambient operator.

Lean proof route for a weaker agent:

1. Unfold `generalizedCompression`.
2. Apply `isSymmetric_compression hA` to the isometric factor
   `orthonormalizedEmbedding X hX`.
3. Keep any future theorem about `(X⋆X)⁻¹ X⋆ A X` separate and formulate it as
   Gram-self-adjointness or similarity to this compression.

Signature audit: Valid because the public compression is now the whitened
ordinary-self-adjoint operator.
-/
theorem isSymmetric_generalizedCompression {A : E →ₗ[𝕜] E}
    (hA : A.IsSymmetric) (X : F →ₗ[𝕜] E) (hX : Function.Injective X) :
    (generalizedCompression A X hX).IsSymmetric := by
  exact isSymmetric_compression hA (orthonormalizedEmbedding X hX)

/-- The interval/exterior spectral hypothesis for a generalized trial pair,
in either orientation.

The first branch places the coordinate spectrum of `M` in `[a,b]` and the
unwanted exact spectrum of `A` on `Vᗮ` outside the enlarged interval.  The
second branch reverses those roles, as allowed in Davis--Kahan Theorem 6.1. -/
def TrialComplementIntervalGap (M : F →ₗ[𝕜] F) (A : E →ₗ[𝕜] E)
    (V : Submodule 𝕜 E) (a b δ : ℝ) : Prop :=
  (SpectrumIn M ⊤ (Set.Icc a b) ∧
      SpectrumIn A Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) ∨
    (SpectrumIn A Vᗮ (Set.Icc a b) ∧
      SpectrumIn M ⊤ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)})

/-- **Raw generalized sine-block residual estimate, every UI norm.**

For an arbitrary trial map `X`, the complementary block `P_{Vᗮ} X` satisfies
the sharp interval/exterior Sylvester estimate in either spectral orientation.
No injectivity or lower frame bound is needed at this stage. -/
theorem complementaryTrialBlock_residual_le_of_intervalGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hgap : TrialComplementIntervalGap M A V a b δ) :
    δ * N (complementaryTrialBlock V X) ≤ N (generalResidual A X M) := by
  have hVperp : Reduces A Vᗮ := reduces_orthogonal_of_isSymmetric hA hV
  let AV : Vᗮ →ₗ[𝕜] Vᗮ := A.restrict hVperp
  let Y : F →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ X
  let C : F →ₗ[𝕜] Vᗮ :=
    Vᗮ.orthogonalProjectionOnto.toLinearMap ∘ₗ generalResidual A X M
  let NV : RectangularUnitarilyInvariantNorm 𝕜 F Vᗮ :=
    N.codomainIsometryTransport Vᗮ.subtypeₗᵢ
  have hAV : AV.IsSymmetric := isSymmetric_restrict hA hVperp
  have hgap' : UnorderedIntervalSylvesterGap AV M a b δ := by
    rcases hgap with hforward | hreverse
    · exact Or.inl ⟨hforward.1,
        (spectrumIn_restrict_iff A hVperp _).2 hforward.2⟩
    · exact Or.inr ⟨
        (spectrumIn_restrict_iff A hVperp _).2 hreverse.1,
        hreverse.2⟩
  have hEq : AV ∘ₗ Y - Y ∘ₗ M = C := by
    ext x
    have hx := LinearMap.congr_fun
      (sylvester_complementaryTrialBlock_eq_projectedGeneralResidual hA hV X M) x
    simpa [AV, Y, C, complementaryTrialBlock, complementaryProjection, projection,
      LinearMap.comp_apply] using hx
  have hY : NV Y = N (complementaryTrialBlock V X) := by
    change N (Vᗮ.subtypeₗᵢ.toLinearMap ∘ₗ Y) =
      N (complementaryTrialBlock V X)
    congr 1
  have hC : NV C =
      N (complementaryProjection V ∘ₗ generalResidual A X M) := by
    change N (Vᗮ.subtypeₗᵢ.toLinearMap ∘ₗ C) =
      N (complementaryProjection V ∘ₗ generalResidual A X M)
    congr 1
  have hproj : ‖(complementaryProjection V).toContinuousLinearMap‖ ≤ 1 := by
    refine (complementaryProjection V).toContinuousLinearMap.opNorm_le_bound
      zero_le_one fun x => ?_
    change ‖Vᗮ.starProjection x‖ ≤ 1 * ‖x‖
    simpa using Vᗮ.norm_starProjection_apply_le x
  have hC_le : NV C ≤ N (generalResidual A X M) := by
    rw [hC]
    calc
      N (complementaryProjection V ∘ₗ generalResidual A X M)
          ≤ ‖(complementaryProjection V).toContinuousLinearMap‖ *
              N (generalResidual A X M) :=
        N.comp_le_opNorm_mul _ _
      _ ≤ 1 * N (generalResidual A X M) :=
        mul_le_mul_of_nonneg_right hproj (N.nonneg _)
      _ = N (generalResidual A X M) := one_mul _
  have hSylvester :=
    uiNorm_sylvester_le_of_unorderedIntervalGap NV hAV hM hδ hgap' hEq
  rw [hY] at hSylvester
  exact hSylvester.trans hC_le

/-- **Davis--Kahan Theorem 6.1, source-complete interval/exterior form.**

A positive lower frame bound supplies injectivity automatically.  The theorem
allows either interval/exterior orientation and compares subspaces of unequal
dimension through the directed sine block. -/
theorem generalizedSinTheta_residual_le_of_intervalGap
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : TrialComplementIntervalGap M A V a b δ) :
    δ * ε * N (sinThetaEmbedding V
      (orthonormalizedEmbedding X (hframe.injective hε))) ≤
      N (generalResidual A X M) := by
  have htransport := lowerFrame_mul_uiNorm_sinTheta_le_complementaryTrialBlock
    N V X (hframe.injective hε) hframe hε
  have hraw := complementaryTrialBlock_residual_le_of_intervalGap
    N hA hV X hM hδ hgap
  calc
    δ * ε * N (sinThetaEmbedding V
        (orthonormalizedEmbedding X (hframe.injective hε))) =
        δ * (ε * N (sinThetaEmbedding V
          (orthonormalizedEmbedding X (hframe.injective hε)))) := by ring
    _ ≤ δ * N (complementaryTrialBlock V X) :=
      mul_le_mul_of_nonneg_left htransport hδ.le
    _ ≤ N (generalResidual A X M) := hraw

/-- **Davis--Kahan Theorem 6.1 with the paper's Gram hypothesis.**

This source-facing wrapper accepts the operator inequality
`X⋆ X ≥ ε² I` through `GramLowerBound`, rather than requiring callers to
translate it into a pointwise norm bound. -/
theorem generalizedSinTheta_residual_le_of_gramLowerBound
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hgram : GramLowerBound X ε)
    (hgap : TrialComplementIntervalGap M A V a b δ) :
    δ * ε * N (sinThetaEmbedding V
      (orthonormalizedEmbedding X (hgram.injective hε))) ≤
      N (generalResidual A X M) := by
  exact generalizedSinTheta_residual_le_of_intervalGap
    N hA hV X hM hδ hε (hgram.lowerFrameBound hε.le) hgap

/-- **Davis--Kahan Theorem 6.1 in its permissive `sin Θ₀` form.**

The paper allows `sin Θ₀` to be any rectangular operator with the same complete
singular-value sequence as the canonical directed sine block.  Since every
rectangular unitarily invariant norm depends only on that sequence, the
canonical Gram-bound theorem transfers without loss. -/
theorem generalizedSinTheta0_residual_le_of_gramLowerBound
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hgram : GramLowerBound X ε)
    (hgap : TrialComplementIntervalGap M A V a b δ)
    (sinTheta0 : F →ₗ[𝕜] E)
    (hsin : sinTheta0.singularValues =
      (sinThetaEmbedding V
        (orthonormalizedEmbedding X (hgram.injective hε))).singularValues) :
    δ * ε * N sinTheta0 ≤ N (generalResidual A X M) := by
  have hcanonical := generalizedSinTheta_residual_le_of_gramLowerBound
    N hA hV X hM hδ hε hgram hgap
  have hnorm : N sinTheta0 = N (sinThetaEmbedding V
      (orthonormalizedEmbedding X (hgram.injective hε))) :=
    N.apply_eq_of_singularValues_eq hsin
  rw [hnorm]
  exact hcanonical

/-- Compatibility specialization of Theorem 6.1 with the coordinate spectrum
inside `[a,b]` and the unwanted exact spectrum outside the enlarged interval.

The explicit injectivity argument is retained for callers of the earlier API;
the source-complete theorem above derives it from the positive lower frame
bound. -/
theorem generalizedSinTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {a b δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hMspec : SpectrumIn M ⊤ (Set.Icc a b))
    (hAspec : SpectrumIn A Vᗮ {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    δ * ε * N (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      N (generalResidual A X M) := by
  have htransport := lowerFrame_mul_uiNorm_sinTheta_le_complementaryTrialBlock
    N V X hX hframe hε
  have hraw := complementaryTrialBlock_residual_le_of_intervalGap
    N hA hV X hM hδ (Or.inl ⟨hMspec, hAspec⟩)
  calc
    δ * ε * N (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) =
        δ * (ε * N (sinThetaEmbedding V (orthonormalizedEmbedding X hX))) := by ring
    _ ≤ δ * N (complementaryTrialBlock V X) :=
      mul_le_mul_of_nonneg_left htransport hδ.le
    _ ≤ N (generalResidual A X M) := hraw

/-- Davis--Kahan Theorem 6.2: under arbitrary spectral separation the sharp
all-UI conclusion is replaced by the Hilbert--Schmidt/square-norm estimate.

Lean proof route for a weaker agent:

1. Set `Q := orthonormalizedEmbedding X hX` and rewrite its range using `range_orthonormalizedEmbedding`.
2. Derive the rectangular Sylvester equation for `sinThetaEmbedding U Q` and apply the Frobenius separated-spectrum estimate entrywise.
3. Factor the whitened residual through the Gram inverse square root, use `hframe` to control that factor, and clear `ε` with `hε`.
-/
theorem generalizedSinTheta_frobenius_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : SpectraSeparated M ⊤ A Vᗮ δ) :
    δ * ε * RectangularUnitarilyInvariantNorm.frobenius
        (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      RectangularUnitarilyInvariantNorm.frobenius
        (generalResidual A X M) := by
  sorry

/-- Trace/nuclear fallback obtained from the square-norm estimate and rank.

Lean proof route for a weaker agent:

1. Apply `generalizedSinTheta_frobenius_le_of_spectralDistance` to obtain the Hilbert--Schmidt bound.
2. Use the finite singular-value inequality `nuclear ≤ sqrt(rank) * frobenius` for the rectangular sine map.
3. Bound its rank by `finrank 𝕜 F`, preserve all nonnegativity side conditions, and simplify the scalar factors.
-/
theorem generalizedSinTheta_nuclear_le_of_spectralDistance
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    (hframe : LowerFrameBound X ε)
    (hgap : SpectraSeparated M ⊤ A Vᗮ δ) :
    δ * ε * RectangularUnitarilyInvariantNorm.nuclear
        (sinThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      Real.sqrt (finrank 𝕜 F) *
        RectangularUnitarilyInvariantNorm.frobenius
          (generalResidual A X M) := by
  sorry

/-- Davis--Kahan Theorem 6.3: generalized `tan Θ`, allowing the exact target
subspace to have larger dimension than the trial space.

Lean proof route for a weaker agent:

1. Set `Q := orthonormalizedEmbedding X hX` and rewrite the range with
   `range_orthonormalizedEmbedding`.
2. Use `htrans` to construct the graph operator from `range Q` to `V`.
3. Derive the ordered tangent Sylvester equation for the Ritz pair
   `(Q, compression A Q)` and apply `tanTheta_residual_le`.
4. Simplify `generalizedCompression` and the residual definitions.

Signature audit: The theorem now uses the symmetric whitened compression and its matching
whitened residual.  The previous statement mixed whitened coordinates with the unwhitened
trial map.
-/
theorem generalizedTanTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection] (hV : Reduces A V)
    (X : F →ₗ[𝕜] E) (hX : Function.Injective X)
    (_hdim : finrank 𝕜 F ≤ finrank 𝕜 V)
    (_htrans : IsTransverse
      (approximateSubspace (orthonormalizedEmbedding X hX)) V)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap (generalizedCompression A X hX) ⊤ A Vᗮ δ) :
    δ * N (tanThetaEmbedding V (orthonormalizedEmbedding X hX)) ≤
      N (residual A (orthonormalizedEmbedding X hX)
        (generalizedCompression A X hX)) :=
  tanTheta_residual_le N hA hV (orthonormalizedEmbedding X hX)
    (isSymmetric_generalizedCompression hA X hX) rfl hδ hgap

/-- The unequal-dimensional `sin 2Θ` extension mentioned after Theorem 8.2.

Lean proof route for a weaker agent:

1. Form the reflection across `U` and rewrite the double-angle embedding as the corresponding off-diagonal reflection block.
2. Apply the finite rectangular reflection-defect/Sylvester estimate under `InternalGap A U δ`.
3. Use the residual equation for `(X,M)` and UI ideal inequalities to bound the reflection defect by twice `N (residual A X M)`; unequal dimensions require only zero-padding in the final singular-value identification.
-/
theorem generalizedSinTwoTheta_unequalFinrank
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) :=
  sinTwoTheta_residual_le N hA hU X hM hδ hgap

/-- Spectral projectors along the homotopy `A+tH` stay on one isolated branch.

Lean proof route for a weaker agent:

1. Use `hselected` and `houtside` to obtain one fixed interval/exterior contour with clearance
   `δ` for every `t ∈ [0,1]`.
2. Specialize the experimental continuation/Riesz-projection module to the path
   `t ↦ A + t • H` and this fixed contour.
3. Identify the finite Riesz projection with `spectralProjection` by diagonalizing each
   symmetric operator.
4. Transfer continuity through the linear-map/continuous-linear-map coercion.

Signature audit: The fixed interval and uniform exterior buffer prevent eigenvalues from
crossing the selection boundary; the former hypothesis was tautological.
-/
theorem spectralSubspace_path_continuous
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hselected : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      SpectrumIn (A + (t : 𝕜) • H)
        (spectralSubspace (A + (t : 𝕜) • H) (Set.Icc a b))
        (Set.Icc a b))
    (houtside : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      SpectrumIn (A + (t : 𝕜) • H)
        (spectralSubspace (A + (t : 𝕜) • H) (Set.Icc a b))ᗮ
        {lam | lam ∉ Set.Ioo (a - δ) (b + δ)}) :
    ContinuousOn (fun t : ℝ =>
      (spectralProjection (A + (t : 𝕜) • H) (Set.Icc a b)).toContinuousLinearMap)
      (Set.Icc 0 1) := by
  sorry

/-- Davis--Kahan Theorem 8.2: a quantitative half-gap bound selects the acute
branch of the `sin 2Θ` conclusion.

Lean proof route for a weaker agent:

1. Use the strengthened continuation theorem to keep the selected projector in the component of `U`, combine the half-gap perturbation bound with `‖P-Q‖ < 1`, and conclude `IsAcute`.
2. This should directly specialize the experimental bounded continuation layer.
-/
theorem sinTwoTheta_acute_of_small_perturbation
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hUcentral : SpectrumIn A U (Set.Icc (a - δ / 2) (b + δ / 2)))
    (hUoutside : SpectrumIn A Uᗮ
      {lam | lam ∉ Set.Ioo (a - δ) (b + δ)})
    (hsmall : ‖H.toContinuousLinearMap‖ < δ / 2) :
    IsAcute U (spectralSubspace (A + H) (Set.Icc (a - δ / 2) (b + δ / 2))) := by
  sorry

end DavisKahanTheory
end ForMathlib
