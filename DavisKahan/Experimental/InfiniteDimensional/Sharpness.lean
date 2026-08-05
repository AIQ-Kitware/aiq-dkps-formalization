/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.OperatorBlocks.OffDiagonal
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Symmetric
import DavisKahan.SpectralTheory.AbstractSpectrum

/-!
# Sharp constants and planar extremal models

Literature writeup: local TeX, Section 35.  Infinite-dimensional sharpness is
inherited from two-dimensional reducing blocks and their orthogonal sums.
-/


/-! ## Construction plan

Realize every model in a fixed two-dimensional real or complex Euclidean
space.  Take `P0 = diag(1,0)` and obtain `Ptheta` by conjugating with the planar
rotation.  Define the model subspaces as their ranges and the gapped operator
as a two-point diagonal spectrum.  The rotated perturbation is conjugation by
that same rotation.  Reduce all norm and angle calculations to explicit
`2 x 2` matrices, then use these models to test constants and the necessity of
acute, ordered-gap, and rank hypotheses.
-/

namespace TauCeti
namespace DavisKahanExt

open DavisKahan.Experimental.Foundation

open DavisKahan

open scoped InnerProductSpace
open Filter

variable {𝕜 : Type*} [RCLike 𝕜]

abbrev Plane (𝕜 : Type*) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 2)
abbrev ThresholdSpace (𝕜 : Type*) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 4)

noncomputable def modelProjection0 : Plane 𝕜 →L[𝕜] Plane 𝕜 :=
  (Matrix.toEuclideanLin !![(1 : 𝕜), 0; 0, 0]).toContinuousLinearMap

/-- Planar rotation matrix by angle `theta` with real entries cast into `𝕜`. -/
noncomputable def planarRotation (theta : ℝ) : Matrix (Fin 2) (Fin 2) 𝕜 :=
  !![(Real.cos theta : 𝕜), -(Real.sin theta : 𝕜);
     (Real.sin theta : 𝕜), (Real.cos theta : 𝕜)]

/-- Rank-one projection onto the line at angle `theta`, obtained by
conjugating the coordinate projection with the planar rotation. -/
noncomputable def modelProjectionTheta (theta : ℝ) :
    Plane 𝕜 →L[𝕜] Plane 𝕜 :=
  (Matrix.toEuclideanLin
    (planarRotation theta * !![(1 : 𝕜), 0; 0, 0] *
      (planarRotation theta).transpose)).toContinuousLinearMap

/-- Range of the coordinate projection in the planar model. -/
noncomputable def modelSubspace0 : Submodule 𝕜 (Plane 𝕜) :=
  LinearMap.range (modelProjection0 (𝕜 := 𝕜)).toLinearMap

/-- Range of the rotated projection in the planar model. -/
noncomputable def modelSubspaceTheta (theta : ℝ) : Submodule 𝕜 (Plane 𝕜) :=
  LinearMap.range (modelProjectionTheta (𝕜 := 𝕜) theta).toLinearMap

/-! The following model objects should all be discharged by one explicit
`Fin 2` matrix calculation.  Prove both model projections are self-adjoint
idempotents, identify their ranges, and obtain the orthogonal-projection
instances from those facts.  Define the gapped operator diagonally and the
rotated perturbation by conjugation with the planar rotation; matrix ext plus
trigonometric normalization then supplies every later sharpness identity. -/


noncomputable instance modelSubspace0_hasOrthogonalProjection :
    (modelSubspace0 (𝕜 := 𝕜)).HasOrthogonalProjection := inferInstance


noncomputable instance modelSubspaceTheta_hasOrthogonalProjection (theta : ℝ) :
    (modelSubspaceTheta (𝕜 := 𝕜) theta).HasOrthogonalProjection := inferInstance

/-- Diagonal planar operator with eigenvalues separated by `d`. -/
noncomputable def modelGappedOperator (d : ℝ) :
    Plane 𝕜 →L[𝕜] Plane 𝕜 :=
  (Matrix.toEuclideanLin !![(0 : 𝕜), 0; 0, (d : 𝕜)]).toContinuousLinearMap

/-- Difference between the rotated and unrotated two-level operators.
This is the exact equality model for `sin Θ`; it is generally not off-diagonal
relative to the unrotated spectral subspace.

Construction route: conjugate `modelGappedOperator d` by the planar rotation
and subtract the original operator; retain this exact difference form so later
norm identities reduce to a `2×2` calculation. -/
noncomputable def modelRotatedPerturbation (d theta : ℝ) :
    Plane 𝕜 →L[𝕜] Plane 𝕜 :=
  (Matrix.toEuclideanLin
    (planarRotation theta * !![(0 : 𝕜), 0; 0, (d : 𝕜)] *
        (planarRotation theta).transpose -
      !![(0 : 𝕜), 0; 0, (d : 𝕜)])).toContinuousLinearMap

/-- Equality model for the constant-one `sin Θ` theorem.

Lean proof route for a weaker agent:

1. Write all four model operators as explicit `2×2` matrices in the standard basis.
2. Compute the projector difference norm from its eigenvalues, obtaining `sin theta`.
3. Compute the perturbation norm and simplify with the chosen scaling.
4. Use the angle-range hypotheses to remove absolute-value ambiguities.


Ext-agent signature audit (GPT 5.6 High): Correct after replacing the misleading
off-diagonal perturbation by the rotated two-level difference. In the model, `B-A` is
exactly `d` times the projector difference up to sign.

Preferred dependency route: Use explicit finite matrices inside the infinite theory,
verify every advertised hypothesis, and prove equality or a limiting ratio rather than
relying on informal optimality claims.
-/
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

/-- The factor two in the `sin 2Θ` theorem is attained asymptotically by
planar models as the angle tends to zero.

Lean proof route for a weaker agent:

1. Compute `modelRotatedPerturbation d theta = d * (P_theta - P_0)` up to sign.
2. Compute `‖sinTwoAngleOperator U_0 U_theta‖ = |sin (2 theta)|` and `‖P_theta-P_0‖ = |sin theta|`.
3. On `theta>0` near zero, simplify the quotient to `cos theta`.
4. Apply continuity of cosine at zero to prove the `Tendsto` statement.

Ext-agent signature audit (GPT 5.6 High): Correct as an asymptotic statement: the exact
planar ratio is `cos θ`, so the factor two is approached as `θ→0` rather than attained
for every positive angle.

Preferred dependency route: Use explicit finite matrices inside the infinite theory,
verify every advertised hypothesis, and prove equality or a limiting ratio rather than
relying on informal optimality claims.
-/
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

/-- The `√2 d` a priori threshold cannot be increased universally.

The witness is allowed to live in a four-dimensional reducing model because a
single two-dimensional off-diagonal block does not produce the required branch
loss.

Lean proof route for a weaker agent:

1. Build an explicit `4×4` self-adjoint block model with two isolated initial components and off-diagonal coupling.
2. Compute the continued eigenvalue/eigenspace branch and locate the coupling where its projection becomes orthogonal to the initial block.
3. Scale the model so the initial gap is `d` and the critical perturbation norm is `sqrt 2 * d`.
4. For arbitrary `c>sqrt 2`, choose a parameter just beyond the critical value but below `c`, then verify every conjunct explicitly.

Ext-agent signature audit (GPT 5.6 High): The four-dimensional existential is the right
level of generality; a single two-dimensional off-diagonal block does not realize loss
of the continued branch at the universal threshold.

Preferred dependency route: Use explicit finite matrices inside the infinite theory,
verify every advertised hypothesis, and prove equality or a limiting ratio rather than
relying on informal optimality claims.
-/
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

/-- The planar equality model is already sufficient to prove optimality for
any symmetric ideal that contains the model perturbation.

Lean proof route for a weaker agent:

1. Prove the planar operator identity underlying `sinTheta_planar_equality` before taking gauges.
2. Use the ideal property and `hmem` to obtain membership of the projector difference from the scaled identity.
3. Apply absolute homogeneity of the gauge and the scalar equality to derive the displayed equality.


Ext-agent signature audit (GPT 5.6 High): Correct for the rotated equality model. The
ideal equality follows from an actual scalar operator identity, not from operator-norm
sharpness alone.

Preferred dependency route: Use explicit finite matrices inside the infinite theory,
verify every advertised hypothesis, and prove equality or a limiting ratio rather than
relying on informal optimality claims.
-/
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
end TauCeti