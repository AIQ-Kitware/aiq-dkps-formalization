/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.FiniteDimensional.DoubleAngle.SinTheta
import DavisKahan.FiniteDimensional.DoubleAngle.TanTheta

/-!
# Finite-dimensional `tan (2Θ)` theory and spectral repulsion

The raw theorem is obtained from the double-angle Riccati identity.  The
internal gap makes the double-angle cosine block injective, hence excludes a
quarter-turn and converts the identity to an estimate for `tan (2Θ)`.

For the canonical spectral subspace of `A+H`, the correct branch is selected by
continuation along `A+tH`.  The fixed gap stays free of spectrum; therefore the
spectral projector varies continuously and cannot cross the projection-gap
boundary.  The same graph calculation gives the spectral-repulsion part of
Davis--Kahan Theorem 8.1.
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

/-- Residual `tan 2Θ` theorem, before choosing an acute branch. -/
theorem tanTwoTheta_residual_le
    (N : RectangularUnitarilyInvariantNorm 𝕜 F E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (hU : Reduces A U)
    (X : F →ₗᵢ[𝕜] E) {M : F →ₗ[𝕜] F} (hM : M.IsSymmetric)
    (hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurnEmbedding U X ∧
      δ * N (tanTwoThetaEmbedding U X) ≤ 2 * N (residual A X M) := by
  classical
  let C₂ := FiniteDimensional.cosTwoThetaEmbedding U X
  let S₂ := sinTwoThetaEmbedding U X
  let R := residual A X M
  have hriccati :
      doubleAngleSylvesterOperator A U S₂ =
        doubleAngleResidual U X R :=
    doubleAngleRiccatiIdentity hA hB hM hU hBX hoff
  have hker : LinearMap.ker C₂ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x hx
    have hhom := doubleAngleHomogeneousEquation_of_cosTwo_apply_eq_zero
      hriccati hx
    exact internalGap_homogeneous_doubleAngle_injective hA hU hδ hgap hhom
  have havoid : AvoidsQuarterTurnEmbedding U X :=
    avoidsQuarterTurnEmbedding_iff_cosTwo_injective.mpr
      (LinearMap.ker_eq_bot.mp hker)
  have htan : tanTwoThetaEmbedding U X =
      S₂ ∘ₗ inverseOnRange C₂ (LinearMap.ker_eq_bot.mp hker) := by
    ext x
    simp [tanTwoThetaEmbedding, C₂, S₂,
      moorePenroseInverse_eq_inverse_of_injective]
  have hsolve := internalGap_doubleAngleTangent_uiNorm_le
    N hA hU hδ hgap hriccati hker
  have hres : N (doubleAngleResidual U X R) ≤ 2 * N R :=
    doubleAngleResidual_uiNorm_le N U X R
  refine ⟨havoid, ?_⟩
  simpa [htan, R] using (hsolve.trans hres)

/-- Perturbation form of the raw `tan 2Θ` theorem. -/
theorem tanTwoTheta_perturbation_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurn U V ∧
      δ * N (tanTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  classical
  let X := V.orthonormalBasis.isometryEquiv.rangeIsometry
  let M := compression B V
  have hBX : B ∘ₗ X.toLinearMap = X.toLinearMap ∘ₗ M :=
    reduces_compression_intertwines hB hV
  have hM : M.IsSymmetric := compression_isSymmetric hB
  have hraw := tanTwoTheta_residual_le
    (N.rectangularRestriction X) hA hB hU X hM hBX hoff hδ hgap
  have hR : residual A X M = (B - A) ∘ₗ X.toLinearMap := by
    ext x
    simp [residual, hBX, LinearMap.comp_apply]
  have hN : (N.rectangularRestriction X) ((B - A) ∘ₗ X.toLinearMap) ≤ N (B - A) :=
    N.comp_isometry_le _ X
  refine ⟨?_, ?_⟩
  · simpa [X, AvoidsQuarterTurnEmbedding, approximateSubspace_rangeIsometry] using hraw.1
  · have hident := tanTwoThetaEmbedding_identifies_angleOperator U V X
    rw [hident, hR] at hraw
    exact hraw.2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN zero_le_two)
      (le_of_lt hδ))

/-- The same-cut spectral branch of an off-diagonal perturbation remains acute. -/
theorem isAcute_canonical_tanTwoTheta
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    IsAcute U (spectralSubspace (A + H) (Set.Iic a)) := by
  classical
  let Apath : ℝ → E →ₗ[𝕜] E := fun t => A + (t : 𝕜) • H
  let P : ℝ → E →ₗ[𝕜] E := fun t =>
    projection (spectralSubspace (Apath t) (Set.Iic a))
  have hsymm : ∀ t, (Apath t).IsSymmetric := fun t =>
    hA.add (hH.smul_ofReal t)
  have hgap : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      spectrum 𝕜 (Apath t) ∩ ((Set.Ioo a b : Set ℝ) : Set 𝕜) = ∅ := by
    intro t ht
    exact offDiagonal_gap_repulsion_along_segment hA hH hU hoff hab hUa hUb ht
  have hcont : ContinuousOn P (Set.Icc (0 : ℝ) 1) :=
    spectralProjection_continuousOn_fixedGap hsymm hgap
  have hP0 : P 0 = projection U := by
    simp [P, Apath, spectralSubspace_eq_of_spectrum_split hA hU hUa hUb]
  let G := {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ ‖P t - projection U‖ < 1}
  have hGopen : IsOpenIn G (Set.Icc (0 : ℝ) 1) := by
    exact relativeOpen_norm_lt_one hcont
  have hGclosed : IsClosedIn G (Set.Icc (0 : ℝ) 1) := by
    intro t ht htn
    have hquarter := avoidsQuarterTurn_along_segment hA hH hU hoff hab hUa hUb ht
    exact projectionGap_component_closed hquarter htn
  have h0 : (0 : ℝ) ∈ G := by simp [G, hP0]
  have hG : G = Set.Icc (0 : ℝ) 1 :=
    connected_Icc.clopen_eq_univ hGopen hGclosed h0
  have h1 : ‖P 1 - projection U‖ < 1 := by
    have : (1 : ℝ) ∈ G := by rw [hG]; simp
    exact this.2
  simpa [P, Apath, IsAcute, subspaceGap, norm_sub_rev] using h1

/-- Canonical spectral-subspace `tan 2Θ` estimate. -/
theorem tanTwoTheta_spectralSubspace_le
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    let V := spectralSubspace (A + H) (Set.Iic a)
    IsAcute U V ∧
      (b - a) * N (tanTwoAngleOperator U V) ≤ 2 * N H := by
  classical
  let V := spectralSubspace (A + H) (Set.Iic a)
  have hδ : 0 < b - a := sub_pos.mpr hab
  have hgap : InternalGap A U (b - a) :=
    internalGap_of_spectrumIn_interval_sides hA hU hUa hUb hab
  have hV : Reduces (A + H) V := reduces_spectralSubspace (hA.add hH) _
  have hraw := tanTwoTheta_perturbation_le N hA (hA.add hH)
    hU hV (by simpa using hoff) hδ hgap
  have hacute := isAcute_canonical_tanTwoTheta hA hH hU hoff hab hUa hUb
  simpa [V] using And.intro hacute hraw.2

/-- The canonical reducing subspace in the preserved gap component exists and
is unique. -/
theorem existsUnique_reducingSubspace_preserving_gap
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    ∃! V : Submodule 𝕜 E,
      Reduces (A + H) V ∧
      SpectrumIn (A + H) V (Set.Iic a) ∧
      SpectrumIn (A + H) Vᗮ (Set.Ici b) ∧
      IsAcute U V := by
  classical
  let V := spectralSubspace (A + H) (Set.Iic a)
  have hrep := offDiagonal_spectral_repulsion hA hH hU hoff hab hUa hUb
  have hred : Reduces (A + H) V := reduces_spectralSubspace (hA.add hH) _
  have hlow : SpectrumIn (A + H) V (Set.Iic a) :=
    spectralSubspace_spectrumIn (hA.add hH) _
  have hupp : SpectrumIn (A + H) Vᗮ (Set.Ici b) := hrep.upper
  have hacute := isAcute_canonical_tanTwoTheta hA hH hU hoff hab hUa hUb
  refine ⟨V, ⟨hred, hlow, hupp, hacute⟩, ?_⟩
  intro W hW
  have hWspec : W = spectralSubspace (A + H) (Set.Iic a) :=
    reducingSubspace_eq_spectralSubspace_of_split
      (hA.add hH) hW.1 hW.2.1 hW.2.2.1 hab
  simpa [V] using hWspec

/-- Compression form of the spectral-repulsion theorem. -/
theorem spectral_repulsion_compression
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (horder : OrderedGap A U A Uᗮ δ) :
    SpectrumIn (A + H) Vᗮ
      {lam | ∃ μ ∈ restrictedSpectrum A Uᗮ, μ ≤ lam} := by
  classical
  let X := angularOperator U V hacute
  let C := positiveCosineEquiv U V hacute
  have hgraph : Vᗮ = graphSubspace Uᗮ (-LinearMap.adjoint X) :=
    orthogonal_graph_angularOperator U V hacute
  have hriccati := offDiagonal_Riccati_equation hA hH hU hV hoff hacute
  have hcompression :
      compression (A + H) Vᗮ =
        C.symm.toLinearMap ∘ₗ
          (compression A Uᗮ + positiveGraphCorrection A H U X) ∘ₗ
        C.toLinearMap :=
    graph_compression_formula hA hH hU hoff hriccati
  have hcorr : (positiveGraphCorrection A H U X).IsPositive :=
    graphCorrection_positive_of_orderedGap horder hriccati
  rw [hgraph, hcompression]
  exact spectrum_congruence_add_positive_above hA.compression hcorr

/-- Ordered-eigenvalue form of spectral repulsion. -/
theorem spectral_repulsion_eigenvalues
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (horder : OrderedGap A U A Uᗮ δ) :
    ∀ lam ∈ restrictedSpectrum (A + H) Vᗮ,
      ∃ μ ∈ restrictedSpectrum A Uᗮ, μ ≤ lam := by
  intro lam hlam
  exact spectral_repulsion_compression hA hH hU hV hoff hacute hδ horder hlam

/-- UI-norm form of spectral repulsion. -/
theorem spectral_repulsion_uiNorm
    (N : UnitarilyInvariantNorm 𝕜 E)
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U)
    (hV : Reduces (A + H) V) (hoff : IsOffDiagonal U H)
    (hacute : IsAcute U V)
    {δ : ℝ} (hδ : 0 < δ) (horder : OrderedGap A U A Uᗮ δ)
    {c : ℝ} :
    N (projection Vᗮ ∘ₗ ((A + H) - (c : 𝕜) • LinearMap.id) ∘ₗ projection Vᗮ) ≥
      N (cosThetaMap Uᗮ Vᗮ ∘ₗ
        (projection Uᗮ ∘ₗ (A - (c : 𝕜) • LinearMap.id) ∘ₗ projection Uᗮ)) := by
  classical
  have heig := spectral_repulsion_eigenvalues hA hH hU hV hoff hacute hδ horder
  have hprefix : ∀ k,
      kyFanSingularValueSum 𝕜
        (cosThetaMap Uᗮ Vᗮ ∘ₗ
          (projection Uᗮ ∘ₗ (A - (c : 𝕜) • LinearMap.id) ∘ₗ projection Uᗮ)) k ≤
      kyFanSingularValueSum 𝕜
        (projection Vᗮ ∘ₗ ((A + H) - (c : 𝕜) • LinearMap.id) ∘ₗ projection Vᗮ) k := by
    intro k
    exact minmax_cosine_compression_kyFan_dominance hA hH hU hV hacute heig k c
  exact N.le_of_kyFan_singular_dominance hprefix

/-- The canonical selected subspace has largest angle below `π/4`. -/
theorem largestPrincipalAngle_lt_pi_div_four
    {A H : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (hoff : IsOffDiagonal U H)
    {a b : ℝ} (hab : a < b)
    (hUa : SpectrumIn A U (Set.Iic a))
    (hUb : SpectrumIn A Uᗮ (Set.Ici b)) :
    principalAngles U (spectralSubspace (A + H) (Set.Iic a)) 0 <
      Real.pi / 4 := by
  classical
  let V := spectralSubspace (A + H) (Set.Iic a)
  have hacute := isAcute_canonical_tanTwoTheta hA hH hU hoff hab hUa hUb
  have hδ : 0 < b - a := sub_pos.mpr hab
  have hgap : InternalGap A U (b - a) :=
    internalGap_of_spectrumIn_interval_sides hA hU hUa hUb hab
  have hV : Reduces (A + H) V := reduces_spectralSubspace (hA.add hH) _
  have havoid := (tanTwoTheta_perturbation_le
    (UnitarilyInvariantNorm.opNorm 𝕜 E) hA (hA.add hH) hU hV
    (by simpa using hoff) hδ hgap).1
  have hconnected := principalAngles_continuous_along_offDiagonal_path
    hA hH hU hoff hab hUa hUb
  exact acute_avoidsQuarterTurn_continuation_selects_lower_branch
    hacute havoid hconnected

/-- Operator-norm endpoint. -/
theorem opNorm_tanTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurn U V ∧
      δ * ‖(tanTwoAngleOperator U V).toContinuousLinearMap‖ ≤
        2 * ‖(B - A).toContinuousLinearMap‖ := by
  simpa using tanTwoTheta_perturbation_le
    (UnitarilyInvariantNorm.opNorm 𝕜 E) hA hB hU hV hoff hδ hgap

/-- Frobenius endpoint. -/
theorem frobenius_tanTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ) :
    AvoidsQuarterTurn U V ∧
      δ * UnitarilyInvariantNorm.frobenius 𝕜 E (tanTwoAngleOperator U V) ≤
        2 * UnitarilyInvariantNorm.frobenius 𝕜 E (B - A) := by
  exact tanTwoTheta_perturbation_le
    (UnitarilyInvariantNorm.frobenius 𝕜 E) hA hB hU hV hoff hδ hgap

/-- Ky Fan endpoint. -/
theorem kyFan_tanTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : Reduces A U) (hV : Reduces B V)
    (hoff : IsOffDiagonal U (B - A))
    {δ : ℝ} (hδ : 0 < δ) (hgap : InternalGap A U δ)
    (k : ℕ) :
    AvoidsQuarterTurn U V ∧
      δ * kyFanSum k (tanTwoAngleOperator U V) ≤ 2 * kyFanSum k (B - A) := by
  let NK : UnitarilyInvariantNorm 𝕜 E :=
    (RectangularUnitarilyInvariantNorm.kyFan
      (𝕜 := 𝕜) (E := E) (F := E) k).toSquare
  have h := tanTwoTheta_perturbation_le NK hA hB hU hV hoff hδ hgap
  simpa [NK, RectangularUnitarilyInvariantNorm.toSquare,
    RectangularUnitarilyInvariantNorm.kyFan_apply,
    RectangularUnitarilyInvariantNorm.rectangularKyFanSum,
    kyFanSum_eq_sum_fin] using h

end DavisKahanTheory
end ForMathlib
