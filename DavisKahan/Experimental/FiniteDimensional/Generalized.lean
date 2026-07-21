/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.SinTheta.TrialMap
import DavisKahan.Experimental.FiniteDimensional.Residual.AngleEmbeddings
import DavisKahan.Experimental.FiniteDimensional.DoubleAngle.SinTheta

/-!
# Compatibility surface for unfinished generalized extensions

The completed generalized sine theorem moved to
`DavisKahan.FiniteDimensional.SinTheta.TrialMap`.
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
  classical
  let G := LinearMap.adjoint X ∘ₗ X
  let Gmhalf := positiveInverseSqrt G hX
  let Q := orthonormalizedEmbedding X hX
  have hQ : Q.toLinearMap = X ∘ₗ Gmhalf := orthonormalizedEmbedding_eq X hX
  have hQiso : LinearMap.adjoint Q.toLinearMap ∘ₗ Q.toLinearMap = LinearMap.id :=
    orthonormalizedEmbedding_adjoint_comp_self X hX
  have hres : residual A Q M = generalResidual A X M ∘ₗ Gmhalf := by
    ext y
    simp [residual, generalResidual, hQ, LinearMap.comp_apply, LinearMap.comp_assoc]
  have hsylv :
      compression A Vᗮ ∘ₗ sinThetaEmbedding V Q -
        sinThetaEmbedding V Q ∘ₗ M =
      complementaryProjection V ∘ₗ residual A Q M :=
    projectedResidual_sylvester hA hM hV Q
  have hHS := rectangular_frobenius_sylvester_le_of_spectraSeparated
    hA.compression hM hδ hgap (sinThetaEmbedding V Q)
      (complementaryProjection V ∘ₗ residual A Q M) hsylv
  have hGmhalf : ‖Gmhalf.toContinuousLinearMap‖ ≤ ε⁻¹ :=
    positiveInverseSqrt_norm_le_of_lowerFrameBound hframe hε
  have hR :
      RectangularUnitarilyInvariantNorm.frobenius (residual A Q M) ≤
        ε⁻¹ * RectangularUnitarilyInvariantNorm.frobenius
          (generalResidual A X M) := by
    rw [hres]
    exact RectangularUnitarilyInvariantNorm.frobenius_comp_le _ hGmhalf
  have hproj :
      RectangularUnitarilyInvariantNorm.frobenius
          (complementaryProjection V ∘ₗ residual A Q M) ≤
        RectangularUnitarilyInvariantNorm.frobenius (residual A Q M) :=
    RectangularUnitarilyInvariantNorm.frobenius_projection_comp_le _ _
  calc
    δ * ε * RectangularUnitarilyInvariantNorm.frobenius
        (sinThetaEmbedding V Q)
        ≤ ε * RectangularUnitarilyInvariantNorm.frobenius
            (complementaryProjection V ∘ₗ residual A Q M) := by
          nlinarith [hHS]
    _ ≤ ε * (ε⁻¹ * RectangularUnitarilyInvariantNorm.frobenius
          (generalResidual A X M)) := by gcongr; exact hproj.trans hR
    _ = RectangularUnitarilyInvariantNorm.frobenius
          (generalResidual A X M) := by
          field_simp [ne_of_gt hε]

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
  classical
  let S := sinThetaEmbedding V (orthonormalizedEmbedding X hX)
  have hHS := generalizedSinTheta_frobenius_le_of_spectralDistance
    hA hV X hX hM hδ hε hframe hgap
  have hrank : LinearMap.rank S ≤ finrank 𝕜 F := LinearMap.rank_le_domain S
  have hnuc : RectangularUnitarilyInvariantNorm.nuclear S ≤
      Real.sqrt (finrank 𝕜 F) *
        RectangularUnitarilyInvariantNorm.frobenius S := by
    exact nuclear_le_sqrt_rank_mul_frobenius S hrank
  have hδε : 0 ≤ δ * ε := mul_nonneg (le_of_lt hδ) (le_of_lt hε)
  calc
    δ * ε * RectangularUnitarilyInvariantNorm.nuclear S
        ≤ δ * ε * (Real.sqrt (finrank 𝕜 F) *
          RectangularUnitarilyInvariantNorm.frobenius S) :=
      mul_le_mul_of_nonneg_left hnuc hδε
    _ = Real.sqrt (finrank 𝕜 F) *
        (δ * ε * RectangularUnitarilyInvariantNorm.frobenius S) := by ring
    _ ≤ Real.sqrt (finrank 𝕜 F) *
        RectangularUnitarilyInvariantNorm.frobenius (generalResidual A X M) := by
      gcongr

/-- Davis--Kahan Theorem 6.3: generalized `tan Θ`, allowing the exact target
subspace to have larger dimension than the trial space.

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

/-- The unequal-dimensional ordered-gap `sin 2Θ` residual extension.

The spectral separation is between the trial coordinate operator `M` and the
unwanted exact spectrum on `Uᗮ`, as in the source-complete residual theorem.
An internal gap between the two blocks of `A` alone does not locate the trial
spectrum. -/
theorem generalizedSinTwoTheta_unequalFinrank
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) :=
  sinTwoTheta_residual_le_of_orderedGap N hA hU X hM hδ hgap

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
  classical
  let Γ := rectangleContour (a - δ / 2) (b + δ / 2)
    (uniformSpectralRadius A H)
  have hsep : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContourSeparatesSpectrum Γ (A + (t : 𝕜) • H) := by
    intro t ht
    exact contourSeparatesSpectrum_of_interval_buffer
      hδ (hselected t ht) (houtside t ht)
  have hpath : Continuous fun t : ℝ =>
      (A + (t : 𝕜) • H).toContinuousLinearMap := by
    fun_prop
  have hRiesz := continuousOn_rieszProjection hpath hsep
  simpa [rieszProjection_eq_spectralProjection hA hH hselected houtside]
    using hRiesz

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
  classical
  let I := Set.Icc (a - δ / 2) (b + δ / 2)
  let P := fun t : ℝ => spectralProjection (A + (t : 𝕜) • H) I
  have hselected : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      SpectrumIn (A + (t : 𝕜) • H)
        (spectralSubspace (A + (t : 𝕜) • H) I) I := by
    intro t ht
    exact spectralSubspace_spectrumIn (hA.add (hH.smul_ofReal t)) I
  have houtside : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      SpectrumIn (A + (t : 𝕜) • H)
        (spectralSubspace (A + (t : 𝕜) • H) I)ᗮ
        {lam | lam ∉ Set.Ioo (a - δ) (b + δ)} := by
    intro t ht
    exact spectral_stability_outside_buffer hA hH hU hUcentral hUoutside hsmall ht
  have hcont := spectralSubspace_path_continuous hA hH hδ hselected houtside
  have hP0 : P 0 = projection U := by
    simp [P, I, spectralProjection_eq_of_spectrum_split hA hU hUcentral hUoutside]
  have hcomponent : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖P t - P 0‖ < 1 := by
    exact continuous_projector_stays_in_component hcont
      (uniform_projector_boundary_exclusion hδ hsmall houtside)
  have h1 := hcomponent 1 (by simp)
  simpa [P, I, hP0, IsAcute, subspaceGap, norm_sub_rev] using h1

end DavisKahanTheory
end ForMathlib
