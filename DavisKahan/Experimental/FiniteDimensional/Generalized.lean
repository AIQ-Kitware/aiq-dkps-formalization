/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.SinTheta.TrialMap
import DavisKahan.Experimental.FiniteDimensional.DoubleAngle.TanTheta

/-!
# Generalized finite-dimensional Davis--Kahan theorems

The trial map is whitened by the inverse square root of its Gram operator.  The
resulting map is isometric and has the same range.  The residual equation then
reduces to the ordinary rectangular Sylvester equation.  Arbitrary spectral
separation gives the Hilbert--Schmidt estimate; the nuclear estimate follows
from `‖T‖₁ ≤ √rank(T) ‖T‖₂`.  The final two statements record the finite
continuation argument used to select an isolated spectral branch.
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

/-- Davis--Kahan Theorem 6.2 in Hilbert--Schmidt norm. -/
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

/-- Trace/nuclear fallback obtained from the Hilbert--Schmidt theorem and rank. -/
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

/-- Generalized `tan Θ` residual theorem in whitened coordinates. -/
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

/-- Unequal-dimensional `sin 2Θ` extension. -/
theorem generalizedSinTwoTheta_unequalFinrank
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    δ * N (sinTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) :=
  sinTwoTheta_residual_le N hA hU X hM hδ hgap

/-- Spectral projectors along `A+tH` vary continuously under a uniform fixed
spectral buffer. -/
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

/-- A perturbation smaller than half the buffer keeps the selected branch acute. -/
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
