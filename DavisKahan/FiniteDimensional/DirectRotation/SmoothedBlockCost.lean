/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedSpectralCost
public import ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.BlockSchatten
public import ForTauCeti.Analysis.InnerProductSpace.SchattenTransportRestriction

/-!
# Coordinate invariance, block additivity and scalar Charbonnier costs

The coordinate and block identities apply to arbitrary operators and every real smoothing
parameter. They retain every zero singular value and allow empty blocks.
The scalar formulas also give the exact cost of paired reflections with
a fixed remainder when the smoothing scale is nonnegative.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
/-- Every scalar operator has its exact literal smoothed displacement
cost, including a zero-dimensional carrier and every real parameter. -/
theorem smoothedDisplacementCost_scalar_complex (tau : ℝ) (z : ℂ) :
    smoothedDisplacementCost tau (z • (LinearMap.id : E →ₗ[ℂ] E)) =
      Module.finrank ℂ E * (Real.sqrt (tau ^ 2 + ‖1 - z‖ ^ 2) - tau) := by
  let e := stdOrthonormalBasis ℂ E
  have heigen (i : Fin (Module.finrank ℂ E)) :
      ((LinearMap.id : E →ₗ[ℂ] E) - z • (LinearMap.id : E →ₗ[ℂ] E)) (e i) =
        (1 - z) • e i := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      sub_smul, one_smul]
  rw [smoothedDisplacementCost, sum_singularValues_eq_sum_norm_eigenvalues e _ _ heigen
    (fun s : ℝ => Real.sqrt (tau ^ 2 + s ^ 2) - tau)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [CompleteSpace E] in
/-- Identity has zero cost for a nonnegative smoothing scale. -/
theorem smoothedDisplacementCost_id_complex (tau : ℝ) (htau : 0 ≤ tau) :
    smoothedDisplacementCost tau (LinearMap.id : E →ₗ[ℂ] E) = 0 := by
  simpa [Real.sqrt_sq htau] using smoothedDisplacementCost_scalar_complex (E := E) tau 1

omit [CompleteSpace E] in
/-- Negative identity contributes one maximal displacement per dimension. -/
theorem smoothedDisplacementCost_neg_id_complex (tau : ℝ) :
    smoothedDisplacementCost tau (-(LinearMap.id : E →ₗ[ℂ] E)) =
      Module.finrank ℂ E * (Real.sqrt (tau ^ 2 + 4) - tau) := by
  have hnorm : ‖(1 : ℂ) - (-1)‖ ^ 2 = 4 := by norm_num
  simpa only [neg_one_smul, hnorm] using
    smoothedDisplacementCost_scalar_complex (E := E) tau (-1)

/-- The literal Charbonnier displacement cost is unchanged by unitary
coordinates, including an isometric change of ambient carrier. -/
theorem smoothedDisplacementCost_conj_linearIsometryEquiv_complex
    (tau : ℝ) (e : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E) :
    smoothedDisplacementCost tau (e.conjStarAlgEquiv A).toLinearMap =
      smoothedDisplacementCost tau A.toLinearMap := by
  have hconj : LinearMap.id - (e.conjStarAlgEquiv A).toLinearMap =
      (e : E →ₗ[ℂ] F) ∘ₗ (LinearMap.id - A.toLinearMap) ∘ₗ
        (e.symm : F →ₗ[ℂ] E) := by
    ext x
    change x - e (A (e.symm x)) = e (e.symm x - A (e.symm x))
    rw [map_sub, e.apply_symm_apply]
  rw [smoothedDisplacementCost, smoothedDisplacementCost, hconj,
    LinearMap.singularValues_linearIsometryEquiv_comp,
    LinearMap.singularValues_comp_linearIsometryEquiv, ← e.toLinearEquiv.finrank_eq]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Orthogonal blocks contribute additively to the literal displacement
cost. No unitarity or positivity assumption is needed. -/
theorem smoothedDisplacementCost_withLpProdMap_complex
    (tau : ℝ) (A : E →L[ℂ] E) (B : F →L[ℂ] F) :
    smoothedDisplacementCost tau (A.withLpProdMap 2 B).toLinearMap =
      smoothedDisplacementCost tau A.toLinearMap + smoothedDisplacementCost tau B.toLinearMap := by
  have hblock : LinearMap.id - (A.withLpProdMap 2 B).toLinearMap =
      ((LinearMap.id - A.toLinearMap).prodMap (LinearMap.id - B.toLinearMap)).withLpMap 2 := by
    rw [ContinuousLinearMap.coe_withLpProdMap]
    ext x
    apply WithLp.ofLp_injective 2
    rfl
  rw [smoothedDisplacementCost, smoothedDisplacementCost, smoothedDisplacementCost, hblock]
  exact sum_singularValues_prodMap_withLpMap _ _ (fun s : ℝ =>
    Real.sqrt (tau ^ 2 + s ^ 2) - tau)

/-- In supplied paired coordinates, a reflection acting as `(-I,I)`
with a fixed remainder contributes exactly one maximal scalar cost per
negative dimension. The kernel theorem constructs such coordinates. -/
theorem smoothedDisplacementCost_paired_reflection_complex
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [FiniteDimensional ℂ G] [CompleteSpace G]
    (tau : ℝ) (htau : 0 ≤ tau) (V : E ≃ₗᵢ[ℂ] E)
    (e : WithLp 2 (WithLp 2 (F × F) × G) ≃ₗᵢ[ℂ] E)
    (hcoords : ∀ x, V (e x) = e (WithLp.toLp 2
      (WithLp.toLp 2 (-x.fst.fst, x.fst.snd), x.snd))) :
    smoothedDisplacementCost tau V.toLinearMap =
      Module.finrank ℂ F * (Real.sqrt (tau ^ 2 + 4) - tau) := by
  let D : WithLp 2 (WithLp 2 (F × F) × G) →L[ℂ] WithLp 2 (WithLp 2 (F × F) × G) :=
    ((-1 : F →L[ℂ] F).withLpProdMap 2 1).withLpProdMap 2 1
  have hVblock : (V : E →L[ℂ] E) =
      (LinearIsometryEquiv.conjStarAlgEquiv
        (H := WithLp 2 (WithLp 2 (F × F) × G)) (K := E) e) D := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.symm_apply_apply]
    simp only [LinearIsometryEquiv.coe_coe'']
    rw [hcoords]
    apply congrArg e
    apply WithLp.ofLp_injective 2
    simp only [D, ContinuousLinearMap.withLpProdMap_apply]
    apply Prod.ext <;> rfl
  change smoothedDisplacementCost tau (V : E →L[ℂ] E).toLinearMap = _
  rw [hVblock, smoothedDisplacementCost_conj_linearIsometryEquiv_complex]
  dsimp only [D]
  rw [smoothedDisplacementCost_withLpProdMap_complex,
    smoothedDisplacementCost_withLpProdMap_complex]
  change smoothedDisplacementCost tau (-(LinearMap.id : F →ₗ[ℂ] F)) +
    smoothedDisplacementCost tau (LinearMap.id : F →ₗ[ℂ] F) +
    smoothedDisplacementCost tau (LinearMap.id : G →ₗ[ℂ] G) = _
  rw [smoothedDisplacementCost_neg_id_complex, smoothedDisplacementCost_id_complex tau htau,
    smoothedDisplacementCost_id_complex tau htau, add_zero, add_zero]

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
