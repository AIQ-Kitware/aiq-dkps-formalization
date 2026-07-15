/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.OperatorBlocks.OffDiagonal
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Symmetric

/-!
# Sharp constants and planar extremal models

All constant claims reduce to explicit real two- or four-dimensional reducing
blocks.  The planar model has

`A = d (1-P₀)`, `B = d (1-Pθ)`, `B-A = d(P₀-Pθ)`.

Thus the `sin Θ` estimate is an operator identity.  The double-angle ratio is
`sin(2θ)/(2 sin θ)=cos θ`, proving asymptotic optimality of the factor two.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace
open Filter

variable {𝕜 : Type*} [RCLike 𝕜]

abbrev Plane (𝕜 : Type*) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 2)
abbrev ThresholdSpace (𝕜 : Type*) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 4)

noncomputable def modelProjection0 : Plane 𝕜 →L[𝕜] Plane 𝕜 :=
  (Matrix.toEuclideanLin !![(1 : 𝕜), 0; 0, 0]).toContinuousLinearMap

noncomputable def modelProjectionTheta (theta : ℝ) :
    Plane 𝕜 →L[𝕜] Plane 𝕜 :=
  (Matrix.toEuclideanLin !![
    [((Real.cos theta)^2 : ℝ),
      (Real.cos theta * Real.sin theta : ℝ)];
    [(Real.cos theta * Real.sin theta : ℝ),
      ((Real.sin theta)^2 : ℝ)]].map (algebraMap ℝ 𝕜)).toContinuousLinearMap

/-- The explicit rotated matrix is a star projection. -/
theorem modelProjectionTheta_isStarProjection (theta : ℝ) :
    IsStarProjection (modelProjectionTheta (𝕜 := 𝕜) theta) := by
  constructor
  · ext i
    fin_cases i <;>
      simp [modelProjectionTheta, Matrix.mul_apply, Fin.sum_univ_two,
        Real.sin_sq_add_cos_sq] <;> ring
  · rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    simp [modelProjectionTheta, Matrix.inner_mulVec, Matrix.conjTranspose]

/-- Range of the coordinate projection in the planar model. -/
noncomputable def modelSubspace0 : Submodule 𝕜 (Plane 𝕜) :=
  LinearMap.range (modelProjection0 (𝕜 := 𝕜)).toLinearMap

/-- Range of the rotated projection in the planar model. -/
noncomputable def modelSubspaceTheta (theta : ℝ) : Submodule 𝕜 (Plane 𝕜) :=
  LinearMap.range (modelProjectionTheta (𝕜 := 𝕜) theta).toLinearMap

noncomputable instance modelSubspace0_hasOrthogonalProjection :
    (modelSubspace0 (𝕜 := 𝕜)).HasOrthogonalProjection :=
  (modelProjectionTheta_isStarProjection (𝕜 := 𝕜) 0).range_hasOrthogonalProjection

noncomputable instance modelSubspaceTheta_hasOrthogonalProjection (theta : ℝ) :
    (modelSubspaceTheta (𝕜 := 𝕜) theta).HasOrthogonalProjection :=
  (modelProjectionTheta_isStarProjection (𝕜 := 𝕜) theta).range_hasOrthogonalProjection

@[simp] theorem projection_modelSubspace0 :
    projection (modelSubspace0 (𝕜 := 𝕜)) = modelProjection0 := by
  exact IsStarProjection.eq_starProjection_range
    (modelProjectionTheta_isStarProjection (𝕜 := 𝕜) 0)

@[simp] theorem projection_modelSubspaceTheta (theta : ℝ) :
    projection (modelSubspaceTheta (𝕜 := 𝕜) theta) =
      modelProjectionTheta theta := by
  exact IsStarProjection.eq_starProjection_range
    (modelProjectionTheta_isStarProjection (𝕜 := 𝕜) theta)

/-- Diagonal planar operator with eigenvalues separated by `d`. -/
noncomputable def modelGappedOperator (d : ℝ) :
    Plane 𝕜 →L[𝕜] Plane 𝕜 :=
  ((d : 𝕜) • (ContinuousLinearMap.id 𝕜 (Plane 𝕜) - modelProjection0))

/-- Difference between the rotated and unrotated two-level operators. -/
noncomputable def modelRotatedPerturbation (d theta : ℝ) :
    Plane 𝕜 →L[𝕜] Plane 𝕜 :=
  (d : 𝕜) • (modelProjection0 - modelProjectionTheta theta)

/-- Rotating the two-level operator adds exactly the model perturbation. -/
theorem modelGappedOperator_add_perturbation (d theta : ℝ) :
    modelGappedOperator (𝕜 := 𝕜) d +
      modelRotatedPerturbation (𝕜 := 𝕜) d theta =
    (d : 𝕜) • (ContinuousLinearMap.id 𝕜 (Plane 𝕜) -
      modelProjectionTheta theta) := by
  unfold modelGappedOperator modelRotatedPerturbation
  module

/-- Norm of the planar projection difference. -/
theorem norm_modelProjection_sub (theta : ℝ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ Real.pi/2) :
    ‖modelProjection0 (𝕜 := 𝕜) - modelProjectionTheta theta‖ =
      Real.sin theta := by
  rw [← Real.norm_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0
    (h1.trans (by linarith [Real.pi_pos])))]
  exact norm_projection_difference_rank_one
    (standardUnitVector 𝕜 (Fin 2) 0)
    (Real.cos theta • standardUnitVector 𝕜 (Fin 2) 0 +
      Real.sin theta • standardUnitVector 𝕜 (Fin 2) 1)
    (by simp [Real.sin_sq_add_cos_sq])

/-- Equality model for the constant-one `sin Θ` theorem. -/
theorem sinTheta_planar_equality
    {d theta : ℝ} (hd : 0 < d) (htheta : 0 ≤ theta)
    (htheta' : theta < Real.pi / 2) :
    let A := modelGappedOperator (𝕜 := 𝕜) d
    let H := modelRotatedPerturbation (𝕜 := 𝕜) d theta
    let U := modelSubspace0 (𝕜 := 𝕜)
    let V := modelSubspaceTheta (𝕜 := 𝕜) theta
    IsSelfAdjointOperator A ∧ IsSelfAdjointOperator H ∧
      Reduces A U ∧ Reduces (A + H) V ∧
      InternalGap A U d ∧ d * subspaceGap U V = ‖H‖ := by
  dsimp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isSelfAdjoint_starProjection _).one_sub.smul_ofReal d
  · exact ((isSelfAdjoint_starProjection _).sub
      (isSelfAdjoint_starProjection _)).smul_ofReal d
  · exact reduces_scalar_one_sub_projection _ _
  · rw [modelGappedOperator_add_perturbation]
    exact reduces_scalar_one_sub_projection _ _
  · exact internalGap_twoPointProjection hd
  · rw [subspaceGap, projection_modelSubspace0,
      projection_modelSubspaceTheta,
      norm_modelProjection_sub theta htheta htheta'.le]
    unfold modelRotatedPerturbation
    rw [norm_smul, RCLike.norm_ofReal, Real.norm_of_nonneg hd.le]

/-- Norm of the ambient double-sine operator in the planar model. -/
theorem norm_sinTwoAngle_planar (theta : ℝ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ Real.pi/2) :
    ‖sinTwoAngleOperator (modelSubspace0 (𝕜 := 𝕜))
      (modelSubspaceTheta (𝕜 := 𝕜) theta)‖ = |Real.sin (2*theta)| := by
  rw [sinTwoAngleOperator_norm_eq_sin_two_maximalAngle,
    maximalAngle_rank_one, abs_of_nonneg]
  · congr 2
  · exact Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)

/-- The factor two in the `sin 2Θ` theorem is asymptotically sharp. -/
theorem sinTwoTheta_planar_asymptotically_sharp
    {d : ℝ} (hd : 0 < d) :
    Tendsto
      (fun theta : ℝ =>
        (d * ‖sinTwoAngleOperator (modelSubspace0 (𝕜 := 𝕜))
          (modelSubspaceTheta (𝕜 := 𝕜) theta)‖) /
        (2 * ‖modelRotatedPerturbation (𝕜 := 𝕜) d theta‖))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  filter_upwards [eventually_lt_nhds 0 (Real.pi/2) Real.pi_pos,
    self_mem_nhdsWithin] with theta htheta htheta0
  rw [norm_sinTwoAngle_planar theta htheta0.le htheta.le,
    modelRotatedPerturbation, norm_smul, RCLike.norm_ofReal,
    Real.norm_of_nonneg hd.le,
    norm_modelProjection_sub theta htheta0.le htheta.le,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (by positivity) (by linarith)), Real.sin_two_mul]
  field_simp [hd.ne', Real.sin_pos_of_pos_of_lt_pi htheta0 (by linarith)]
  ring
  simpa using Real.continuousAt_cos.tendsto

/-- Explicit four-dimensional threshold model. -/
noncomputable def thresholdModelA (d : ℝ) :
    ThresholdSpace 𝕜 →L[𝕜] ThresholdSpace 𝕜 :=
  Matrix.toEuclideanCLM ![
    ![-d/2, 0, 0, 0], ![0, d/2, 0, 0],
    ![0, 0, -d/2, 0], ![0, 0, 0, d/2]]

noncomputable def thresholdModelH (d t : ℝ) :
    ThresholdSpace 𝕜 →L[𝕜] ThresholdSpace 𝕜 :=
  Matrix.toEuclideanCLM ![
    ![0, 0, t*d/2, t*d/2], ![0, 0, -t*d/2, t*d/2],
    ![t*d/2, -t*d/2, 0, 0], ![t*d/2, t*d/2, 0, 0]]

noncomputable def thresholdModelSubspace :
    Submodule 𝕜 (ThresholdSpace 𝕜) :=
  Submodule.span 𝕜 {standardUnitVector 𝕜 (Fin 4) 0,
    standardUnitVector 𝕜 (Fin 4) 1}

/-- Direct diagonalization of the four-dimensional threshold model. -/
theorem thresholdModel_calculation
    {d t : ℝ} (hd : 0 < d) (ht : Real.sqrt 2 < t) :
    let A := thresholdModelA (𝕜 := 𝕜) d
    let H := thresholdModelH (𝕜 := 𝕜) d t
    let U := thresholdModelSubspace (𝕜 := 𝕜)
    IsSelfAdjointOperator A ∧ IsSelfAdjointOperator H ∧
      Reduces A U ∧ IsOffDiagonal U H ∧
      InternalGap A U d ∧ FiniteGapConfiguration A U d ∧
      (restrictedSpectrum A U).Nonempty ∧
      (restrictedSpectrum A Uᗮ).Nonempty ∧
      ‖H‖ = Real.sqrt 2 / 2 * t * d ∧
      subspaceGap U
        (continuedSpectralSubspace A H (restrictedSpectrum A U)) = 1 := by
  dsimp
  constructor
  · exact Matrix.isHermitian_thresholdModelA hd
  constructor
  · exact Matrix.isHermitian_thresholdModelH
  constructor
  · exact thresholdModelA_reduces_coordinatePlane
  constructor
  · exact thresholdModelH_offDiagonal_coordinatePlane
  constructor
  · exact thresholdModelA_internalGap hd
  constructor
  · exact thresholdModelA_finiteGap hd
  constructor
  · exact thresholdModelA_selectedSpectrum_nonempty hd
  constructor
  · exact thresholdModelA_complementSpectrum_nonempty hd
  constructor
  · exact Matrix.opNorm_thresholdModelH hd.le
  · have hchar := Matrix.thresholdModel_characteristicPolynomial d t
    have hbranch := thresholdModel_continuedBranch hchar hd ht
    exact hbranch.projection_orthogonal

/-- The `√2 d` a priori threshold cannot be increased universally. -/
theorem sqrtTwo_threshold_sharp :
    ∀ c : ℝ, Real.sqrt 2 < c →
      ∃ d : ℝ, 0 < d ∧
      ∃ A H : ThresholdSpace 𝕜 →L[𝕜] ThresholdSpace 𝕜,
      ∃ U : Submodule 𝕜 (ThresholdSpace 𝕜),
        IsSelfAdjointOperator A ∧ IsSelfAdjointOperator H ∧
        Reduces A U ∧ IsOffDiagonal U H ∧
        InternalGap A U d ∧ FiniteGapConfiguration A U d ∧
        (restrictedSpectrum A U).Nonempty ∧
        (restrictedSpectrum A Uᗮ).Nonempty ∧
        ‖H‖ < c * d ∧
        subspaceGap U
          (continuedSpectralSubspace A H (restrictedSpectrum A U)) = 1 := by
  intro c hc
  choose t ht2 htc using exists_between hc
  refine ⟨1, zero_lt_one,
    thresholdModelA (𝕜 := 𝕜) 1,
    thresholdModelH (𝕜 := 𝕜) 1 t,
    thresholdModelSubspace (𝕜 := 𝕜), ?_⟩
  obtain ⟨hA, hH, hred, hoff, hgap, hfinite, hneU, hneC,
    hnorm, horth⟩ := thresholdModel_calculation (𝕜 := 𝕜) zero_lt_one ht2
  refine ⟨hA, hH, hred, hoff, hgap, hfinite, hneU, hneC, ?_, horth⟩
  rw [hnorm, mul_one]
  nlinarith [Real.sq_sqrt (show 0 ≤ (2:ℝ) by positivity)]

/-- The planar equality model is an extremizer for every symmetric ideal
containing its perturbation. -/
theorem ideal_planar_extremizer
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := Plane 𝕜))
    {d theta : ℝ} (hd : 0 < d) (htheta : 0 ≤ theta)
    (htheta' : theta < Real.pi / 2)
    (hmem : I.mem (modelRotatedPerturbation (𝕜 := 𝕜) d theta)) :
    I.mem (projection (modelSubspace0 (𝕜 := 𝕜)) -
      projection (modelSubspaceTheta (𝕜 := 𝕜) theta)) ∧
    d * I.gauge (projection (modelSubspace0 (𝕜 := 𝕜)) -
      projection (modelSubspaceTheta (𝕜 := 𝕜) theta)) =
      I.gauge (modelRotatedPerturbation (𝕜 := 𝕜) d theta) := by
  let T := projection (modelSubspace0 (𝕜 := 𝕜)) -
      projection (modelSubspaceTheta (𝕜 := 𝕜) theta)
  have hH : modelRotatedPerturbation (𝕜 := 𝕜) d theta = (d : 𝕜) • T := by
    simp [T, modelRotatedPerturbation]
  have hTmem : I.mem T := by
    rw [hH] at hmem
    exact I.mem_of_nonzero_smul (RCLike.ofReal_ne_zero.mpr hd.ne') hmem
  refine ⟨hTmem, ?_⟩
  rw [hH, I.gauge_smul (d : 𝕜) hTmem,
    RCLike.norm_ofReal, Real.norm_of_nonneg hd.le]

end DavisKahanExt
end ForMathlib
