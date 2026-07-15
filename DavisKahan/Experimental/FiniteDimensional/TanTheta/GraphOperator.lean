/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.FiniteDimensional.SinTheta.Perturbation
import DavisKahan.FiniteDimensional.TanTheta.Vector
import DavisKahan.Experimental.FiniteDimensional.Core.AngleOperators
import DavisKahan.Experimental.FiniteDimensional.Residual.AngleEmbeddings

/-!
# Finite-dimensional graph-operator `tan Θ` theory

When the trial subspace is transverse to `Uᗮ`, its cosine coordinate is
injective and the subspace is the graph of `S C⁺`, where `C=P_U X` and
`S=P_{Uᗮ}X`.  Its singular values are the principal tangents.  Projecting the
residual or reducing equation onto the two blocks yields an ordered Sylvester
equation for this graph operator, from which the UI-norm estimates follow.
-/

namespace ForMathlib
namespace DavisKahanTheory

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Totalized graph operator in trial coordinates. -/
noncomputable def graphOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E) : F →ₗ[𝕜] E :=
  tanThetaEmbedding U X

/-- The public graph operator and tangent embedding are definitionally equal. -/
theorem graphOperator_eq_tanThetaEmbedding (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (_htrans : IsTransverse (approximateSubspace X) U) :
    graphOperator U X = tanThetaEmbedding U X :=
  rfl

/-- Singular values of the graph operator are the principal tangents. -/
theorem singularValues_graphOperator (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (X : F →ₗᵢ[𝕜] E)
    (htrans : IsTransverse (approximateSubspace X) U) :
    (graphOperator U X).singularValues =
      principalTangents (approximateSubspace X) U := by
  classical
  funext i
  rw [graphOperator, singularValues_tanThetaEmbedding]
  · exact principalTangents_comm_index (approximateSubspace X) U i
  · simpa [IsTransverseEmbedding] using htrans

/-- A separated Ritz residual forces transversality. -/
theorem isTransverse_of_tanTheta_residual_gap
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    IsTransverse (approximateSubspace X) U := by
  classical
  rw [isTransverse_iff_cosThetaEmbedding_injective]
  intro y hy
  have hCy : cosThetaEmbedding U X y = 0 := hy
  have hSy : sinThetaEmbedding U X y = X y := by
    rw [← X.cos_add_sin U y, hCy, zero_add]
  have hresU : projection U (residual A X M y) = 0 := by
    rw [hGalerkin]
    exact galerkin_residual_orthogonal X A y
  have hhom :
      compression A Uᗮ (sinThetaEmbedding U X y) =
        sinThetaEmbedding U X (M y) := by
    have hblock := projectedResidual_sine_equation hA hU X M y
    simpa [hresU] using hblock
  have hy0 : y = 0 := by
    have hsep := orderedGap_vector_coercive hgap hδ y
      (sinThetaEmbedding U X y) hhom
    have hnormX : ‖X y‖ = ‖y‖ := X.norm_map y
    rw [hSy, hnormX] at hsep
    nlinarith [norm_nonneg y]
  exact hy0

/-- Residual `tan Θ` theorem for every rectangular UI norm. -/
theorem tanTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap M ⊤ A Uᗮ δ) :
    δ * N (tanThetaEmbedding U X) ≤ N (residual A X M) := by
  classical
  have htrans := isTransverse_of_tanTheta_residual_gap
    hA hU X hM hGalerkin hδ hgap
  let C := cosThetaEmbedding U X
  let S := sinThetaEmbedding U X
  let T := tanThetaEmbedding U X
  let R := residual A X M
  have hCinverse : C ∘ₗ inverseOnRange C htrans.cos_injective = LinearMap.id :=
    cosThetaEmbedding_inverseOnRange htrans
  have hgraph : S = T ∘ₗ C := by
    ext y
    simp [T, tanThetaEmbedding, C, S,
      moorePenroseInverse_eq_inverseOnRange htrans.cos_injective,
      LinearMap.comp_apply, hCinverse]
  have hsylv :
      compression A Uᗮ ∘ₗ T - T ∘ₗ M =
        complementaryProjection U ∘ₗ R ∘ₗ
          inverseOnRange C htrans.cos_injective := by
    ext y
    have hblock := projectedResidual_sine_equation hA hU X M
      (inverseOnRange C htrans.cos_injective y)
    simpa [T, R, C, S, hgraph, LinearMap.comp_apply, LinearMap.comp_assoc]
      using hblock
  have hsolve := rectangular_uiNorm_sylvester_le_of_orderedGap
    N hM (compression_isSymmetric hA) hδ hgap T
      (complementaryProjection U ∘ₗ R ∘ₗ
        inverseOnRange C htrans.cos_injective) hsylv
  have hrhs :
      N (complementaryProjection U ∘ₗ R ∘ₗ
        inverseOnRange C htrans.cos_injective) ≤ N R := by
    exact N.projection_comp_inverseCos_le htrans R
  exact hsolve.trans hrhs

/-- Perturbation `tan Θ` theorem for every square UI norm. -/
theorem tanTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (tanAngleOperator U V) ≤ N (B - A) := by
  classical
  let T := angularOperator U V hacute
  have hgraph : V = graphSubspace U T := graphSubspace_angularOperator U V hacute
  have hriccati :
      compression B Vᗮ ∘ₗ T - T ∘ₗ compression A U =
        complementaryProjection V ∘ₗ (B - A) ∘ₗ projection U := by
    exact tangentSylvesterEquation_of_reduces_zeroCompression
      hA hB hU hV hzero hacute
  have hsolve := uiNorm_sylvester_le_of_orderedGap
    N hA hB hδ hgap T
      (complementaryProjection V ∘ₗ (B - A) ∘ₗ projection U) hriccati
  have hrhs :
      N (complementaryProjection V ∘ₗ (B - A) ∘ₗ projection U) ≤ N (B - A) :=
    N.projection_comp_projection_le _
  have hsing : N T = N (tanAngleOperator U V) := by
    exact N.eq_of_same_singularValues
      (singularValues_angularOperator_eq_tanAngleOperator U V hacute)
  simpa [hsing] using hsolve.trans hrhs

/-- Cross-map version under the explicit transversality hypothesis. -/
theorem tanThetaMap_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (htrans : IsTransverse U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * N (tanThetaMap U V) ≤ N (B - A) := by
  classical
  let T := graphMapOfTransverse U V htrans
  have hriccati := tangentSylvesterEquation_of_transverse
    hA hB hU hV hzero htrans
  have hsolve := uiNorm_sylvester_le_of_orderedGap
    N hA hB hδ hgap T
      (complementaryProjection V ∘ₗ (B - A) ∘ₗ projection U) hriccati
  have hrhs := N.projection_comp_projection_le (B - A) Vᗮ U
  have hsame : N T = N (tanThetaMap U V) := by
    exact N.eq_of_same_singularValues
      (singularValues_graphMap_eq_tanThetaMap U V htrans)
  simpa [T, hsame] using hsolve.trans hrhs

/-- Canonical spectral-subspace specialization. -/
theorem tanTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {a b δ : ℝ} (hδ : 0 < δ)
    (hzero : HasZeroCompression (spectralSubspace A (Set.Icc a b)) (B - A))
    (hacute : IsAcute (spectralSubspace A (Set.Icc a b))
      (spectralSubspace B (Set.Icc a b)))
    (hgap : OrderedGap A (spectralSubspace A (Set.Icc a b))
      B (spectralSubspace B (Set.Icc a b))ᗮ δ) :
    δ * N (tanAngleOperator (spectralSubspace A (Set.Icc a b))
        (spectralSubspace B (Set.Icc a b))) ≤ N (B - A) :=
  tanTheta_perturbation_le N hA hB
    (reduces_spectralSubspace A (Set.Icc a b))
    (reduces_spectralSubspace B (Set.Icc a b))
    hzero hacute hδ hgap

/-- Pole-free vector form. -/
theorem tanTheta_vector_le
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hGalerkin : M = compression A X)
    {δ ρ : ℝ} (hδ : 0 < δ)
    (hgap : OrderedGap M ⊤ A Uᗮ δ)
    (hres : ∀ y, ‖residual A X M y‖ ≤ ρ * ‖y‖) :
    ∀ y, δ * ‖sinThetaEmbedding U X y‖ ≤
      ρ * ‖cosThetaEmbedding U X y‖ := by
  intro y
  have hblock := projectedResidual_sine_equation hA hU X M y
  have hsep := orderedGap_vector_tanTheta hM hA hδ hgap
    (cosThetaEmbedding U X y) (sinThetaEmbedding U X y) hblock
  have hproj : ‖complementaryProjection U (residual A X M y)‖ ≤
      ‖residual A X M y‖ := Uᗮ.norm_starProjection_apply_le _
  calc
    δ * ‖sinThetaEmbedding U X y‖
        ≤ ‖complementaryProjection U (residual A X M y)‖ *
            ‖cosThetaEmbedding U X y‖ := hsep
    _ ≤ (ρ * ‖y‖) * ‖cosThetaEmbedding U X y‖ := by
      gcongr
      exact hproj.trans (hres y)
    _ ≤ ρ * ‖cosThetaEmbedding U X y‖ := by
      have hC := cosThetaEmbedding_contraction U X y
      nlinarith [norm_nonneg y, norm_nonneg (cosThetaEmbedding U X y)]

/-- Operator-norm endpoint. -/
theorem opNorm_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * ‖(tanAngleOperator U V).toContinuousLinearMap‖ ≤
      ‖(B - A).toContinuousLinearMap‖ := by
  simpa using tanTheta_perturbation_le
    (UnitarilyInvariantNorm.opNorm 𝕜 E) hA hB hU hV hzero hacute hδ hgap

/-- Frobenius endpoint. -/
theorem frobenius_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) :
    δ * UnitarilyInvariantNorm.frobenius 𝕜 E (tanAngleOperator U V) ≤
      UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  exact tanTheta_perturbation_le
    (UnitarilyInvariantNorm.frobenius 𝕜 E) hA hB hU hV hzero hacute hδ hgap

/-- Ky Fan endpoint. -/
theorem kyFan_tanTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hzero : HasZeroCompression U (B - A))
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (hgap : OrderedGap A U B Vᗮ δ) (k : ℕ) :
    δ * kyFanSum k (tanAngleOperator U V) ≤ kyFanSum k (B - A) := by
  let NK : UnitarilyInvariantNorm 𝕜 E :=
    (RectangularUnitarilyInvariantNorm.kyFan
      (𝕜 := 𝕜) (E := E) (F := E) k).toSquare
  have h := tanTheta_perturbation_le NK hA hB hU hV hzero hacute hδ hgap
  simpa [NK, RectangularUnitarilyInvariantNorm.toSquare,
    RectangularUnitarilyInvariantNorm.kyFan_apply,
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum,
    kyFanSum_eq_sum_fin] using h

end DavisKahanTheory
end ForMathlib
