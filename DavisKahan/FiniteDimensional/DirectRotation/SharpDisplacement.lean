/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
import DavisKahan.FiniteDimensional.DirectRotation.ProjectionDisplacement
import DavisKahan.FiniteDimensional.DirectRotation.Exponential
import DavisKahan.FiniteDimensional.DirectRotation.PrincipalPlanes.Spectrum
import DavisKahan.FiniteDimensional.DirectRotation.TraceOptimality
import ForTauCeti.Analysis.InnerProductSpace.TwoDimensionalSingularValues

/-!
# Sharp comparison of canonical and projection displacements

We compare the *full* canonical displacement with the positive sine by
factoring their common Gram spectrum. This avoids constructing a new
principal-plane eigenbasis, and works for every unitarily invariant
seminorm over `RCLike`.

The scalar multiplier is `sqrt (2 / (1 + sqrt (1 - s^2)))`, evaluated on
the positive full-space sine operator. It is well defined also at `s=0`
and `s=1`. The operator Pythagorean theorem identifies the Gram operator
of the resulting product with the direct-displacement Gram operator.
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

private noncomputable def sharpTransferWeight (s : ℝ) : ℝ :=
  Real.sqrt (2 / (1 + Real.sqrt (1 - s ^ 2)))

private theorem sharpTransferWeight_nonneg (s : ℝ) :
    0 ≤ sharpTransferWeight s := Real.sqrt_nonneg _

/-- The scalar Gram identity behind the sharp transfer multiplier. -/
private theorem sharpTransferWeight_sq (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (sharpTransferWeight s * s) ^ 2 =
      2 * (1 - Real.sqrt (1 - s ^ 2)) := by
  have hsq : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hc : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hsq
  have hd : 0 < 1 + Real.sqrt (1 - s ^ 2) := by
    have := Real.sqrt_nonneg (1 - s ^ 2)
    linarith
  have hw : sharpTransferWeight s ^ 2 =
      2 / (1 + Real.sqrt (1 - s ^ 2)) := by
    exact Real.sq_sqrt (div_nonneg (by norm_num) hd.le)
  calc
    (sharpTransferWeight s * s) ^ 2 =
        (2 * s ^ 2) / (1 + Real.sqrt (1 - s ^ 2)) := by
          rw [mul_pow, hw]
          ring
    _ = 2 * (1 - Real.sqrt (1 - s ^ 2)) := by
          apply (div_eq_iff (ne_of_gt hd)).2
          nlinarith [hc]

/-- Scalar sharpness: the transfer multiplier is at most `sec(alpha/2)`
when its spectral parameter is at most `sin(alpha)`. -/
private theorem cos_half_mul_sharpTransferWeight_le_one
    {s alpha : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha < Real.pi / 2)
    (hs0 : 0 ≤ s) (hs1 : s ≤ Real.sin alpha) :
    Real.cos (alpha / 2) * sharpTransferWeight s ≤ 1 := by
  have hsin : 0 ≤ Real.sin alpha :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos alpha :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha1⟩
  have hcoshalf : 0 < Real.cos (alpha / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsle : s ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq alpha]
  have hsquare : 0 ≤ 1 - s ^ 2 := by nlinarith
  have hc0 : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  have hc2 : Real.sqrt (1 - s ^ 2) ^ 2 = 1 - s ^ 2 :=
    Real.sq_sqrt hsquare
  have hcfloor : Real.cos alpha ≤ Real.sqrt (1 - s ^ 2) := by
    nlinarith [Real.sin_sq_add_cos_sq alpha, hc2]
  have hcosdouble : 2 * Real.cos (alpha / 2) ^ 2 = 1 + Real.cos alpha := by
    have hd : alpha = alpha / 2 + alpha / 2 := by ring
    have hcosadd := Real.cos_add (alpha / 2) (alpha / 2)
    rw [← hd] at hcosadd
    nlinarith [Real.sin_sq_add_cos_sq (alpha / 2)]
  have hd : 0 < 1 + Real.sqrt (1 - s ^ 2) := by linarith
  have hw : sharpTransferWeight s ^ 2 =
      2 / (1 + Real.sqrt (1 - s ^ 2)) := by
    exact Real.sq_sqrt (div_nonneg (by norm_num) hd.le)
  have hsqle : (Real.cos (alpha / 2) * sharpTransferWeight s) ^ 2 ≤ 1 := by
    calc
      (Real.cos (alpha / 2) * sharpTransferWeight s) ^ 2 =
          (2 * Real.cos (alpha / 2) ^ 2) /
            (1 + Real.sqrt (1 - s ^ 2)) := by
            rw [mul_pow, hw]
            ring
      _ ≤ 1 := (div_le_iff₀ hd).2 (by nlinarith [hcosdouble, hcfloor])
  have hnonneg : 0 ≤ Real.cos (alpha / 2) * sharpTransferWeight s :=
    mul_nonneg hcoshalf.le (sharpTransferWeight_nonneg s)
  nlinarith

/-- The canonical displacement has the same singular values as an explicit
spectral multiplier of the positive sine. This avoids any sorted principal-plane
enumeration, and uses only the verified operator Pythagorean identity. -/
theorem singularValues_directDisplacement_eq_sharpTransfer
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    let S := sinAngleOperator U V
    let hS : S.IsPositive := TauCeti.isPositive_operatorAbs (projection U - projection V)
    let F := TauCeti.selfAdjointFunctionalCalculus hS.isSymmetric sharpTransferWeight
    (LinearMap.id - (directRotation U V hacute).toLinearMap).singularValues =
      (F ∘ₗ S).singularValues := by
  classical
  dsimp only
  let S : E →ₗ[𝕜] E := sinAngleOperator U V
  let hS : S.IsPositive := TauCeti.isPositive_operatorAbs (projection U - projection V)
  let b := hS.isSymmetric.eigenvectorBasis rfl
  let F := TauCeti.selfAdjointFunctionalCalculus hS.isSymmetric sharpTransferWeight
  let B := F ∘ₗ S
  let A : E →ₗ[𝕜] E := LinearMap.id - (directRotation U V hacute).toLinearMap
  have hFsym : F.IsSymmetric :=
    TauCeti.selfAdjointFunctionalCalculus_isSymmetric hS.isSymmetric sharpTransferWeight
  have hBadj : B.adjoint = S ∘ₗ F := by
    change (F ∘ₗ S).adjoint = S ∘ₗ F
    rw [LinearMap.adjoint_comp, hFsym.adjoint_eq, hS.isSymmetric.adjoint_eq]
  have hAgram : A.adjoint ∘ₗ A =
      (2 : 𝕜) • (LinearMap.id - directRotationCosine U V) :=
    adjoint_comp_displacement_directRotation U V hacute
  have hC := directRotationCosine_eq_calculus U V hS.isSymmetric
  have hgram : A.adjoint ∘ₗ A = B.adjoint ∘ₗ B := by
    apply b.toBasis.ext
    intro i
    rw [OrthonormalBasis.coe_toBasis]
    let s : ℝ := hS.isSymmetric.eigenvalues rfl i
    have hs0 : 0 ≤ s := hS.nonneg_eigenvalues rfl i
    have hs1 : s ≤ 1 := (sinAngleOperator_eigenvalues_mem_Icc U V hS.isSymmetric i).2
    have hSval : S (b i) = (s : 𝕜) • b i :=
      hS.isSymmetric.apply_eigenvectorBasis rfl i
    have hFval : F (b i) = (sharpTransferWeight s : 𝕜) • b i :=
      TauCeti.selfAdjointFunctionalCalculus_apply_eigenvectorBasis
        hS.isSymmetric sharpTransferWeight i
    have hCval : directRotationCosine U V (b i) =
        ((Real.sqrt (1 - s ^ 2) : ℝ) : 𝕜) • b i := by
      rw [hC, TauCeti.selfAdjointFunctionalCalculus_apply_eigenvectorBasis,
        Real.cos_arcsin]
    have hBval : B (b i) = ((sharpTransferWeight s * s : ℝ) : 𝕜) • b i := by
      change F (S (b i)) = _
      rw [hSval, map_smul, hFval, smul_smul]
      congr 1
      push_cast
      ring
    have hBgram : (B.adjoint ∘ₗ B) (b i) =
        (((sharpTransferWeight s * s) ^ 2 : ℝ) : 𝕜) • b i := by
      rw [hBadj]
      change S (F (B (b i))) = _
      rw [hBval, map_smul, hFval, map_smul, map_smul, hSval, smul_smul, smul_smul]
      congr 1
      push_cast
      ring
    calc
      (A.adjoint ∘ₗ A) (b i) =
          ((2 * (1 - Real.sqrt (1 - s ^ 2)) : ℝ) : 𝕜) • b i := by
            rw [hAgram, LinearMap.smul_apply, LinearMap.sub_apply,
              LinearMap.id_apply, hCval]
            match_scalars
            ring
      _ = (((sharpTransferWeight s * s) ^ 2 : ℝ) : 𝕜) • b i := by
            rw [sharpTransferWeight_sq s hs0 hs1]
      _ = (B.adjoint ∘ₗ B) (b i) := hBgram.symm
  exact TauCeti.singularValues_eq_of_gram_eq hgram


/-- Every eigenvalue of the full positive sine is bounded by the operator
norm of the projection difference.  This formulation works in dimension zero
and does not require matching up two separately ordered sine spectra. -/
theorem sinAngleOperator_eigenvalue_le_projectionGap
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (i : Fin (finrank 𝕜 E)) :
    (TauCeti.isPositive_operatorAbs
      (projection U - projection V)).isSymmetric.eigenvalues rfl i ≤
        U.projectionGap V := by
  classical
  let D : E →ₗ[𝕜] E := projection U - projection V
  let S : E →ₗ[𝕜] E := sinAngleOperator U V
  let hS : S.IsPositive := TauCeti.isPositive_operatorAbs D
  let b := hS.isSymmetric.eigenvectorBasis rfl
  let s : ℝ := hS.isSymmetric.eigenvalues rfl i
  have hs0 : 0 ≤ s := hS.nonneg_eigenvalues rfl i
  have hb : ‖b i‖ = 1 := by simp [b]
  have hSval : S (b i) = (s : 𝕜) • b i :=
    hS.isSymmetric.apply_eigenvectorBasis rfl i
  have hnormS : ‖S (b i)‖ = s := by
    rw [hSval, norm_smul, RCLike.norm_ofReal, abs_of_nonneg hs0, hb, mul_one]
  have hnormD : ‖S (b i)‖ = ‖D (b i)‖ :=
    TauCeti.norm_operatorAbs_apply D (b i)
  have hbound : ‖D (b i)‖ ≤ ‖D.toContinuousLinearMap‖ := by
    calc
      ‖D (b i)‖ ≤ ‖D.toContinuousLinearMap‖ * ‖b i‖ :=
        D.toContinuousLinearMap.le_opNorm (b i)
      _ = ‖D.toContinuousLinearMap‖ := by rw [hb, mul_one]
  have hgap : ‖D.toContinuousLinearMap‖ = U.projectionGap V := by
    rw [Submodule.projectionGap_def]
    rfl
  calc
    s = ‖S (b i)‖ := hnormS.symm
    _ = ‖D (b i)‖ := hnormD
    _ ≤ ‖D.toContinuousLinearMap‖ := hbound
    _ = U.projectionGap V := hgap

/-- **Sharp full-displacement comparison with projection distance.**
If `alpha` bounds the positive-sine spectrum then the exact multiplicative
factor is `sec(alpha/2)` for every real or complex unitarily invariant
seminorm.  The denominator-free formulation also includes the zero seminorm. -/
theorem cos_half_mul_uiNorm_directRotation_le_projection
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha < Real.pi / 2)
    (hangle : ∀ i : Fin (finrank 𝕜 E),
      (TauCeti.isPositive_operatorAbs
        (projection U - projection V)).isSymmetric.eigenvalues rfl i ≤
        Real.sin alpha) :
    Real.cos (alpha / 2) *
        N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (projection U - projection V) := by
  classical
  let S : E →ₗ[𝕜] E := sinAngleOperator U V
  let hS : S.IsPositive := TauCeti.isPositive_operatorAbs (projection U - projection V)
  let F := TauCeti.selfAdjointFunctionalCalculus hS.isSymmetric sharpTransferWeight
  let A : E →ₗ[𝕜] E := LinearMap.id - (directRotation U V hacute).toLinearMap
  have hc : 0 < Real.cos (alpha / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hFbound : ∀ y, ‖F y‖ ≤ (Real.cos (alpha / 2))⁻¹ * ‖y‖ := by
    intro y
    apply TauCeti.norm_selfAdjointFunctionalCalculus_apply_le
      hS.isSymmetric sharpTransferWeight (inv_nonneg.mpr hc.le) _ y
    intro i
    have hs0 : 0 ≤ hS.isSymmetric.eigenvalues rfl i :=
      hS.nonneg_eigenvalues rfl i
    have hs1 := hangle i
    rw [abs_of_nonneg (sharpTransferWeight_nonneg _)]
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hc).2
    simpa only [mul_comm] using
      cos_half_mul_sharpTransferWeight_le_one ha0 ha1 hs0 hs1
  have hN : N A = N (F ∘ₗ S) :=
    N.map_eq_of_singularValues_eq
      (singularValues_directDisplacement_eq_sharpTransfer U V hacute)
  have hbound : N A ≤ (Real.cos (alpha / 2))⁻¹ * N S := by
    rw [hN]
    exact N.apply_comp_le (inv_nonneg.mpr hc.le) hFbound
  have hbound' := mul_le_mul_of_nonneg_left hbound hc.le
  have hcancel : Real.cos (alpha / 2) *
      ((Real.cos (alpha / 2))⁻¹ * N S) = N S := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
  calc
    Real.cos (alpha / 2) * N A ≤ N S := by
      rw [hcancel] at hbound'
      exact hbound'
    _ = N (projection U - projection V) :=
      (uiNorm_projection_sub_eq_sinAngleOperator N U V).symm

/-- Every admissible competitor is at least the sharp cosine-weighted
canonical displacement, in every unitarily invariant seminorm. -/
theorem cos_half_mul_uiNorm_directRotation_le_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha < Real.pi / 2)
    (hangle : ∀ i : Fin (finrank 𝕜 E),
      (TauCeti.isPositive_operatorAbs
        (projection U - projection V)).isSymmetric.eigenvalues rfl i ≤
        Real.sin alpha)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    Real.cos (alpha / 2) *
        N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) := by
  exact (cos_half_mul_uiNorm_directRotation_le_projection
    N U V hacute alpha ha0 ha1 hangle).trans
      (projectionDifference_uiNorm_le_displacement N U V W hmap)


/-- The projection gap is the sine of the largest principal angle.  Thus the
sharp factor has no independent spectral-bound hypothesis: its angle is exactly
`arcsin` of the gap, which lies below `pi/2` for every acute finite pair. -/
theorem cos_half_arcsin_projectionGap_mul_uiNorm_directRotation_le_projection
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) :
    Real.cos (Real.arcsin (U.projectionGap V) / 2) *
        N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (projection U - projection V) := by
  have hg0 : 0 ≤ U.projectionGap V := by
    rw [Submodule.projectionGap_def]
    exact norm_nonneg _
  have hg1 : U.projectionGap V < 1 :=
    projectionGap_lt_one_of_isAcute hacute
  have ha0 : 0 ≤ Real.arcsin (U.projectionGap V) :=
    Real.arcsin_nonneg.mpr hg0
  have ha1 : Real.arcsin (U.projectionGap V) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.mpr hg1
  have hsin : Real.sin (Real.arcsin (U.projectionGap V)) = U.projectionGap V :=
    Real.sin_arcsin (by linarith) hg1.le
  refine cos_half_mul_uiNorm_directRotation_le_projection N U V hacute
    (Real.arcsin (U.projectionGap V)) ha0 ha1 ?_
  intro i
  rw [hsin]
  exact sinAngleOperator_eigenvalue_le_projectionGap U V i

/-- **Universal sharp factor for the canonical direct rotation**, for every
real or complex unitarily invariant seminorm and every admissible transport.
The angle `arcsin ‖P_U-P_V‖` is the maximal principal angle. -/
theorem cos_half_arcsin_projectionGap_mul_uiNorm_directRotation_le_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    Real.cos (Real.arcsin (U.projectionGap V) / 2) *
        N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) := by
  exact (cos_half_arcsin_projectionGap_mul_uiNorm_directRotation_le_projection
    N U V hacute).trans
      (projectionDifference_uiNorm_le_displacement N U V W hmap)

/-- The same bound expressed with any valid upper bound on the maximal angle. -/
theorem cos_half_mul_uiNorm_directRotation_le_displacement_of_gap
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (alpha : ℝ) (ha0 : 0 ≤ alpha) (ha1 : alpha < Real.pi / 2)
    (hgap : U.projectionGap V ≤ Real.sin alpha)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    Real.cos (alpha / 2) *
        N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) := by
  apply cos_half_mul_uiNorm_directRotation_le_displacement
    N U V hacute alpha ha0 ha1 _ W hmap
  intro i
  exact (sinAngleOperator_eigenvalue_le_projectionGap U V i).trans hgap

/-- In positive ambient dimension, the largest principal angle computed from
the directed sine spectrum agrees with the gap angle, for equal-rank pairs.
The gap formulation above is preferable in zero dimension. -/
theorem principalAngles_zero_eq_arcsin_projectionGap
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hrank : finrank 𝕜 U = finrank 𝕜 V)
    (hE : 0 < finrank 𝕜 E) :
    principalAngles U V 0 = Real.arcsin (U.projectionGap V) := by
  have hgap : U.projectionGap V = principalSines U V 0 := by
    calc
      U.projectionGap V =
          ‖(projection U - projection V).toContinuousLinearMap‖ := by
            rw [Submodule.projectionGap_def]
            rfl
      _ = ‖(sinThetaMap U V).toContinuousLinearMap‖ :=
            opNorm_projection_sub_eq_opNorm_sinThetaMap U V hrank
      _ = (sinThetaMap U V).singularValues 0 :=
            TauCeti.opNorm_eq_singularValues_zero (sinThetaMap U V) rfl hE
      _ = principalSines U V 0 := rfl
  rw [principalAngles, Finsupp.mapRange_apply, ← hgap]

/-- The sharp inequality expressed directly with the largest principal
angle, without an auxiliary spectrum hypothesis. -/
theorem cos_half_maxPrincipalAngle_mul_uiNorm_directRotation_le_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (hrank : finrank 𝕜 U = finrank 𝕜 V)
    (hE : 0 < finrank 𝕜 E)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    Real.cos (principalAngles U V 0 / 2) *
        N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) := by
  rw [principalAngles_zero_eq_arcsin_projectionGap U V hrank hE]
  exact cos_half_arcsin_projectionGap_mul_uiNorm_directRotation_le_displacement
    N U V hacute W hmap

/-- The sharp common factor on the original `alpha ≤ pi/3` range, in
its denominator-free form. This formulation also handles the zero seminorm. -/
theorem sqrt_three_div_two_mul_uiNorm_directRotation_le_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (hgap : U.projectionGap V ≤ Real.sin (Real.pi / 3))
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    Real.sqrt 3 / 2 *
        N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      N (LinearMap.id - W.toLinearMap) := by
  have hpi : 0 ≤ Real.pi / 3 := by positivity
  have hpi' : Real.pi / 3 < Real.pi / 2 := by
    have := Real.pi_pos
    linarith
  have h := cos_half_mul_uiNorm_directRotation_le_displacement_of_gap
    N U V hacute (Real.pi / 3) hpi hpi' hgap W hmap
  have hc : Real.cos ((Real.pi / 3) / 2) = Real.sqrt 3 / 2 := by
    have hangle : (Real.pi / 3) / 2 = Real.pi / 6 := by ring
    rw [hangle, Real.cos_pi_div_six]
  rwa [hc] at h

/-- Equivalent usual form: the sharp common factor is `2 / sqrt 3`. -/
theorem uiNorm_directRotation_le_two_div_sqrt_three_mul_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (hgap : U.projectionGap V ≤ Real.sin (Real.pi / 3))
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      (2 / Real.sqrt 3) * N (LinearMap.id - W.toLinearMap) := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hfactor : (2 / Real.sqrt 3) * (Real.sqrt 3 / 2) = 1 := by
    field_simp [ne_of_gt hs]
  have h := sqrt_three_div_two_mul_uiNorm_directRotation_le_displacement
    N U V hacute hgap W hmap
  calc
    N (LinearMap.id - (directRotation U V hacute).toLinearMap) =
        (2 / Real.sqrt 3) * (Real.sqrt 3 / 2 *
          N (LinearMap.id - (directRotation U V hacute).toLinearMap)) := by
            rw [← mul_assoc, hfactor, one_mul]
    _ ≤ (2 / Real.sqrt 3) * N (LinearMap.id - W.toLinearMap) :=
      mul_le_mul_of_nonneg_left h (div_nonneg (by norm_num) hs.le)

/-- The transfer multiplier is at most `sqrt 2` on the entire sine spectrum,
including the endpoint `s = 1`. -/
private theorem sharpTransferWeight_le_sqrt_two
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    sharpTransferWeight s ≤ Real.sqrt 2 := by
  have hsq : 0 ≤ 1 - s ^ 2 := by nlinarith
  have ht : 0 ≤ Real.sqrt (1 - s ^ 2) := Real.sqrt_nonneg _
  have hd : 0 < 1 + Real.sqrt (1 - s ^ 2) := by linarith
  have hw : sharpTransferWeight s ^ 2 =
      2 / (1 + Real.sqrt (1 - s ^ 2)) := by
    exact Real.sq_sqrt (div_nonneg (by norm_num) hd.le)
  have hwle : sharpTransferWeight s ^ 2 ≤ 2 := by
    rw [hw]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hroot : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [sharpTransferWeight_nonneg s, Real.sqrt_nonneg 2]

/-- **Uniform acute-pair bound `sqrt 2`.** All of the angle dependence has
been discharged, including any possible zero-dimensional ambient space. -/
theorem uiNorm_directRotation_le_sqrt_two_mul_displacement
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N (LinearMap.id - (directRotation U V hacute).toLinearMap) ≤
      Real.sqrt 2 * N (LinearMap.id - W.toLinearMap) := by
  let S : E →ₗ[𝕜] E := sinAngleOperator U V
  let hS : S.IsPositive := TauCeti.isPositive_operatorAbs (projection U - projection V)
  let F := TauCeti.selfAdjointFunctionalCalculus hS.isSymmetric sharpTransferWeight
  let A : E →ₗ[𝕜] E := LinearMap.id - (directRotation U V hacute).toLinearMap
  have hFbound : ∀ y, ‖F y‖ ≤ Real.sqrt 2 * ‖y‖ := by
    intro y
    apply TauCeti.norm_selfAdjointFunctionalCalculus_apply_le
      hS.isSymmetric sharpTransferWeight (Real.sqrt_nonneg 2) _ y
    intro i
    have hs0 := hS.nonneg_eigenvalues rfl i
    have hs1 := (sinAngleOperator_eigenvalues_mem_Icc U V hS.isSymmetric i).2
    rw [abs_of_nonneg (sharpTransferWeight_nonneg _)]
    exact sharpTransferWeight_le_sqrt_two hs0 hs1
  have hN : N A = N (F ∘ₗ S) :=
    N.map_eq_of_singularValues_eq
      (singularValues_directDisplacement_eq_sharpTransfer U V hacute)
  calc
    N A = N (F ∘ₗ S) := hN
    _ ≤ Real.sqrt 2 * N S :=
      N.apply_comp_le (Real.sqrt_nonneg 2) hFbound
    _ = Real.sqrt 2 * N (projection U - projection V) := by
      rw [uiNorm_projection_sub_eq_sinAngleOperator N U V]
    _ ≤ Real.sqrt 2 * N (LinearMap.id - W.toLinearMap) :=
      mul_le_mul_of_nonneg_left
        (projectionDifference_uiNorm_le_displacement N U V W hmap)
        (Real.sqrt_nonneg 2)

namespace SmallAngleCounterexample

open ShortRotationCounterexample (E4 U4)

/-- The projection gap of the real four-dimensional witness is its principal
sine. It follows directly from the four equal singular values of `P_U-P_V`. -/
theorem projectionGap_eq_sin (theta : ℝ)
    (h0 : 0 < theta) (h1 : theta < Real.pi / 2) :
    U4.projectionGap (V4 theta) = Real.sin theta := by
  let D : E4 →ₗ[ℝ] E4 := projection U4 - projection (V4 theta)
  have hfr : finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  have hs : 0 ≤ Real.sin theta :=
    (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])).le
  calc
    U4.projectionGap (V4 theta) = ‖D.toContinuousLinearMap‖ := by
      rw [Submodule.projectionGap_def]
      rfl
    _ = D.singularValues 0 :=
      TauCeti.opNorm_eq_singularValues_zero D hfr (by norm_num)
    _ = Real.sin theta := singularValues_projectionDifference theta hs 0

/-- At **every** prescribed nonzero acute angle, the trace-norm witness
attains the universal sharp factor, expressed via the actual maximal angle. -/
theorem fixedAngle_sharpFactor_attained (theta : ℝ)
    (h0 : 0 < theta) (h1 : theta < Real.pi / 2) :
    Real.cos (Real.arcsin (U4.projectionGap (V4 theta)) / 2) *
      kyFanSum 4 (LinearMap.id -
        (directRotation U4 (V4 theta)
          (acute theta (cos_pos theta h0 h1))).toLinearMap) =
      kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) := by
  rw [projectionGap_eq_sin theta h0 h1,
    Real.arcsin_sin (by linarith [Real.pi_pos]) h1.le]
  exact cos_half_mul_directTrace_eq_competitorTrace theta h0 h1

/-- Every universal multiplicative coefficient at the fixed angle `theta`
must be at least `sec(theta/2)`; equivalently its cosine-weighted value is
at least one. The witness is a global minimum, not merely a cheaper competitor. -/
theorem factor_necessary_at_fixedAngle (theta c : ℝ)
    (h0 : 0 < theta) (h1 : theta < Real.pi / 2)
    (hbound : kyFanSum 4 (LinearMap.id -
        (directRotation U4 (V4 theta)
          (acute theta (cos_pos theta h0 h1))).toLinearMap) ≤
      c * kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap)) :
    1 ≤ c * Real.cos (theta / 2) := by
  have hc : 0 < Real.cos (theta / 2) :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hs : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
  have hw : 0 < kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) := by
    rw [kyFanSum_displacement_W theta hs.le]
    positivity
  have heq := cos_half_mul_directTrace_eq_competitorTrace theta h0 h1
  have hscaled := mul_le_mul_of_nonneg_left hbound hc.le
  have hfactor : kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) ≤
      (c * Real.cos (theta / 2)) *
        kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) := by
    calc
      kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) =
          Real.cos (theta / 2) * kyFanSum 4 (LinearMap.id -
            (directRotation U4 (V4 theta)
              (acute theta (cos_pos theta h0 h1))).toLinearMap) := heq.symm
      _ ≤ Real.cos (theta / 2) *
          (c * kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap)) := hscaled
      _ = (c * Real.cos (theta / 2)) *
          kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) := by ring
  have hfactor' : (1 : ℝ) *
      kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) ≤
      (c * Real.cos (theta / 2)) *
        kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) := by
    simpa using hfactor
  exact le_of_mul_le_mul_right hfactor' hw


/-- Optimality of `2 / sqrt 3` on the original Davis--Kahan angle range:
even just the trace-norm real witness at `theta = pi/3` forces this factor. -/
theorem pi_div_three_common_factor_necessary (c : ℝ)
    (hbound : kyFanSum 4 (LinearMap.id -
        (directRotation U4 (V4 (Real.pi / 3))
          (acute (Real.pi / 3) (cos_pos (Real.pi / 3)
            (by positivity) (by have := Real.pi_pos; linarith)))).toLinearMap) ≤
      c * kyFanSum 4 (LinearMap.id - (Wequiv (Real.pi / 3)).toLinearMap)) :
    2 / Real.sqrt 3 ≤ c := by
  have hpi0 : 0 < Real.pi / 3 := by positivity
  have hpi1 : Real.pi / 3 < Real.pi / 2 := by
    have := Real.pi_pos
    linarith
  have h := factor_necessary_at_fixedAngle (Real.pi / 3) c hpi0 hpi1 hbound
  have hc : Real.cos ((Real.pi / 3) / 2) = Real.sqrt 3 / 2 := by
    have hangle : (Real.pi / 3) / 2 = Real.pi / 6 := by ring
    rw [hangle, Real.cos_pi_div_six]
  rw [hc] at h
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  exact (div_le_iff₀ hs).2 (by nlinarith)

end SmallAngleCounterexample

end DavisKahan.FiniteDimensional
end TauCeti
