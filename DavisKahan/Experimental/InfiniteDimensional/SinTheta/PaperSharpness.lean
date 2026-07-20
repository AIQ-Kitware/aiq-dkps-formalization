/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperRankOneNormalization
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperHilbertSchmidtFiniteRank
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperTheorem61Universal
import ForMathlib.Analysis.InnerProductSpace.UnitarilyInvariantNorm

/-!
# Source-faithful sharpness and the one-gap counterexample

The single-angle constant is already attained on a two-dimensional reducing
model.  The residual and the directed sine block are scalar multiples of the
same rank-one isometry, so equality holds simultaneously for every normalized
source norm.  Orthogonal finite sums retain the same scalar operator identity.

The final section records the explicit matrix counterexample printed directly
before Proposition 6.1: one directional gap does not imply the symmetric
square-norm estimate.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace BigOperators

noncomputable section

universe u

variable {𝕜 : Type u} [RCLike 𝕜]

abbrev PaperPlane (𝕜 : Type u) [RCLike 𝕜] := EuclideanSpace 𝕜 (Fin 2)

/-- First standard vector of the planar equality model. -/
def paperPlaneE0 : PaperPlane 𝕜 :=
  EuclideanSpace.single (0 : Fin 2) 1

/-- Second standard vector of the planar equality model. -/
def paperPlaneE1 : PaperPlane 𝕜 :=
  EuclideanSpace.single (1 : Fin 2) 1

/-- Scalar-to-vector map used for all one-dimensional model blocks. -/
noncomputable def paperScalarColumn (v : PaperPlane 𝕜) :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  (ContinuousLinearMap.id 𝕜 𝕜).smulRight v

/-- Exact spectral inclusion. -/
noncomputable def paperPlanarExactMap :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  paperScalarColumn paperPlaneE0

/-- Complementary spectral inclusion. -/
noncomputable def paperPlanarComplementMap :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  paperScalarColumn paperPlaneE1

/-- Trial inclusion at angle `theta`. -/
noncomputable def paperPlanarTrialMap (theta : ℝ) :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  paperScalarColumn
    ((Real.cos theta : 𝕜) • paperPlaneE0 +
      (Real.sin theta : 𝕜) • paperPlaneE1)

/-- Two-level self-adjoint operator with gap `delta`. -/
noncomputable def paperPlanarAmbient (delta : ℝ) :
    PaperPlane 𝕜 →L[𝕜] PaperPlane 𝕜 :=
  (Matrix.toEuclideanLin
    !![(0 : 𝕜), 0; 0, (delta : 𝕜)]).toContinuousLinearMap

/-- Zero trial operator. -/
noncomputable def paperPlanarTrialOperator : 𝕜 →L[𝕜] 𝕜 := 0

/-- Literal directed sine block of the planar model. -/
noncomputable def paperPlanarSineBlock (theta : ℝ) :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  ((Real.sin theta : 𝕜) • paperPlanarComplementMap)

/-- Residual of the planar equality model. -/
noncomputable def paperPlanarResidual (delta theta : ℝ) :
    𝕜 →L[𝕜] PaperPlane 𝕜 :=
  ((delta * Real.sin theta : ℝ) : 𝕜) • paperPlanarComplementMap

@[simp]
theorem norm_paperPlaneE0 : ‖paperPlaneE0 (𝕜 := 𝕜)‖ = 1 := by
  simp [paperPlaneE0]

@[simp]
theorem norm_paperPlaneE1 : ‖paperPlaneE1 (𝕜 := 𝕜)‖ = 1 := by
  simp [paperPlaneE1]

/-- The adjoint of a scalar column reads off the corresponding coordinate.

Every block identity below needs this; without it the adjoint stays an opaque
term and no component computation closes. -/
theorem adjoint_paperScalarColumn_apply (i : Fin 2) (x : PaperPlane 𝕜) :
    (paperScalarColumn (EuclideanSpace.single i (1 : 𝕜))).adjoint x =
      x.ofLp i := by
  -- Identify the adjoint by the defining inner-product identity, evaluated on
  -- the coordinate functional `x ↦ x i`.
  have hadj :
      (ContinuousLinearMap.id 𝕜 𝕜).smulRight
            (EuclideanSpace.single i (1 : 𝕜)) =
          ((EuclideanSpace.proj i : PaperPlane 𝕜 →L[𝕜] 𝕜)).adjoint := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro z y
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      inner_smul_left, EuclideanSpace.inner_single_left]
    simp [RCLike.inner_apply, mul_comm]
  have := congrArg (fun T : 𝕜 →L[𝕜] PaperPlane 𝕜 => T.adjoint) hadj
  simp only [ContinuousLinearMap.adjoint_adjoint] at this
  rw [paperScalarColumn, this]
  rfl

@[simp]
theorem paperScalarColumn_apply (v : PaperPlane 𝕜) (z : 𝕜) :
    paperScalarColumn v z = z • v := rfl

@[simp]
theorem paperPlanarExactMap_apply (z : 𝕜) :
    paperPlanarExactMap (𝕜 := 𝕜) z = z • paperPlaneE0 := rfl

@[simp]
theorem paperPlanarComplementMap_apply (z : 𝕜) :
    paperPlanarComplementMap (𝕜 := 𝕜) z = z • paperPlaneE1 := rfl

@[simp]
theorem paperPlanarTrialMap_apply (theta : ℝ) (z : 𝕜) :
    paperPlanarTrialMap (𝕜 := 𝕜) theta z =
      z • ((Real.cos theta : 𝕜) • paperPlaneE0 +
        (Real.sin theta : 𝕜) • paperPlaneE1) := rfl

@[simp]
theorem adjoint_paperPlanarExactMap_apply (x : PaperPlane 𝕜) :
    (paperPlanarExactMap (𝕜 := 𝕜)).adjoint x = x.ofLp 0 :=
  adjoint_paperScalarColumn_apply 0 x

@[simp]
theorem adjoint_paperPlanarComplementMap_apply (x : PaperPlane 𝕜) :
    (paperPlanarComplementMap (𝕜 := 𝕜)).adjoint x = x.ofLp 1 :=
  adjoint_paperScalarColumn_apply 1 x

/-- The trial column is isometric for every real angle. -/
theorem paperPlanarTrialMap_isometry (theta : ℝ) :
    IsometricEmbedding (paperPlanarTrialMap (𝕜 := 𝕜) theta) := by
  intro z
  simp only [paperPlanarTrialMap, paperScalarColumn,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
  rw [norm_smul]
  have horth :
      ⟪paperPlaneE0 (𝕜 := 𝕜), paperPlaneE1 (𝕜 := 𝕜)⟫_𝕜 = 0 := by
    simp [paperPlaneE0, paperPlaneE1, EuclideanSpace.inner_single_left]
  have hunit :
      ‖(Real.cos theta : 𝕜) • paperPlaneE0 +
          (Real.sin theta : 𝕜) • paperPlaneE1‖ = 1 := by
    rw [norm_eq_one_iff]
    simp [inner_add_left, inner_add_right, horth,
      RCLike.norm_ofReal, Real.sin_sq_add_cos_sq]
  rw [hunit, mul_one]

/-- Exact and complementary columns form the coordinate orthogonal
decomposition. -/
theorem paperPlanar_exact_decomposition :
    OrthogonalExactDecomposition
      (paperPlanarExactMap (𝕜 := 𝕜))
      (paperPlanarComplementMap (𝕜 := 𝕜)) := by
  refine {
    isometry₀ := ?_
    isometry₁ := ?_
    orthogonal := ?_
    projection_sum := ?_ }
  · intro z
    simp [paperPlanarExactMap, paperScalarColumn, norm_smul]
  · intro z
    simp [paperPlanarComplementMap, paperScalarColumn, norm_smul]
  · ext
    simp [paperPlaneE0, paperPlaneE1, PiLp.single_apply]
  · ext x i
    fin_cases i <;>
      simp [paperPlaneE0, paperPlaneE1, PiLp.single_apply]

/-- Direct matrix calculation of the planar residual identity. -/
theorem paperPlanar_residual_identity (delta theta : ℝ) :
    paperPlanarAmbient (𝕜 := 𝕜) delta ∘L
        paperPlanarTrialMap (𝕜 := 𝕜) theta -
      paperPlanarTrialMap (𝕜 := 𝕜) theta ∘L
        paperPlanarTrialOperator (𝕜 := 𝕜) =
      paperPlanarResidual (𝕜 := 𝕜) delta theta := by
  ext i
  fin_cases i <;>
    simp [paperPlanarAmbient, paperPlanarTrialOperator, paperPlanarResidual,
      paperPlaneE0, paperPlaneE1, Matrix.toEuclideanLin_apply,
      PiLp.single_apply, mul_comm] <;>
    push_cast <;> ring

/-- The projection residual is literally the rank-one sine block. -/
theorem paperPlanar_directedSine_identity (theta : ℝ) :
    (ContinuousLinearMap.id 𝕜 (PaperPlane 𝕜) -
        paperPlanarExactMap (𝕜 := 𝕜) ∘L
          (paperPlanarExactMap (𝕜 := 𝕜)).adjoint) ∘L
      paperPlanarTrialMap (𝕜 := 𝕜) theta =
        paperPlanarSineBlock (𝕜 := 𝕜) theta := by
  ext i
  fin_cases i <;>
    simp [paperPlanarSineBlock, paperPlaneE0, paperPlaneE1,
      PiLp.single_apply]

/-- The complement inclusion is a norm-one rank-one map. -/
theorem paperPlanarComplementMap_norm_rank :
    ‖paperPlanarComplementMap (𝕜 := 𝕜)‖ = 1 ∧
      (paperPlanarComplementMap (𝕜 := 𝕜)).rank ≤ (1 : Cardinal) := by
  constructor
  · rw [paperPlanarComplementMap, paperScalarColumn,
      ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_id, one_mul, norm_paperPlaneE1]
  · exact (LinearMap.rank_le_domain
      (paperPlanarComplementMap (𝕜 := 𝕜)).toLinearMap).trans_eq (by simp)

/-- Equality in Theorem 6.1 is attained simultaneously for every normalized
source norm. -/
theorem paperTheorem61_planar_equality_every_norm
    (N : PaperUnitaryInvariantNorm)
    {delta theta : ℝ} (hdelta : 0 ≤ delta) :
    N.gauge (paperPlanarResidual (𝕜 := 𝕜) delta theta) =
      delta * N.gauge (paperPlanarSineBlock (𝕜 := 𝕜) theta) := by
  have hV := paperPlanarComplementMap_norm_rank (𝕜 := 𝕜)
  have hVmem := N.mem_rankOne hV.1 hV.2
  rw [paperPlanarResidual, paperPlanarSineBlock,
    N.gauge_smul _ hVmem, N.gauge_smul _ hVmem]
  simp [RCLike.norm_ofReal, abs_of_nonneg hdelta, abs_mul]
  ring

/-- At every nonzero acute angle the sine block has strictly positive source
norm. -/
theorem paperPlanarSineBlock_gauge_pos
    (N : PaperUnitaryInvariantNorm)
    {theta : ℝ} (h0 : 0 < theta) (h1 : theta < Real.pi) :
    0 < N.gauge (paperPlanarSineBlock (𝕜 := 𝕜) theta) := by
  have hV := paperPlanarComplementMap_norm_rank (𝕜 := 𝕜)
  have hVmem := N.mem_rankOne hV.1 hV.2
  rw [paperPlanarSineBlock, N.gauge_smul _ hVmem,
    N.gauge_rankOne hV.1 hV.2, mul_one, RCLike.norm_ofReal]
  exact abs_pos.mpr (Real.sin_pos_of_pos_of_lt_pi h0 h1).ne'

/-- No constant strictly below one can replace the source constant in the
single-angle theorem. -/
theorem paperSinTheta_constant_one_optimal
    (N : PaperUnitaryInvariantNorm) :
    ∀ c : ℝ, c < 1 →
      ∃ delta theta : ℝ,
        0 < delta ∧ 0 < theta ∧ theta < Real.pi / 2 ∧
        c * N.gauge (paperPlanarResidual (𝕜 := 𝕜) delta theta) <
          delta * N.gauge (paperPlanarSineBlock (𝕜 := 𝕜) theta) := by
  intro c hc
  have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hpi42 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  refine ⟨1, Real.pi / 4, zero_lt_one, hpi4, hpi42, ?_⟩
  rw [paperTheorem61_planar_equality_every_norm N zero_le_one]
  have hpos := paperPlanarSineBlock_gauge_pos (𝕜 := 𝕜) N
    hpi4 (by linarith [Real.pi_pos])
  nlinarith

/-- Scalar operator identity behind equality for every finite orthogonal direct
sum of the planar model. -/
theorem paperFiniteMultiplicity_equality
    {m : ℕ} (N : PaperUnitaryInvariantNorm)
    (S : EuclideanSpace 𝕜 (Fin m) →L[𝕜] EuclideanSpace 𝕜 (Fin m))
    {delta : ℝ} (hdelta : 0 ≤ delta) (hS : N.Mem S) :
    N.gauge (((delta : ℝ) : 𝕜) • S) = delta * N.gauge S := by
  rw [N.gauge_smul _ hS]
  simp [RCLike.norm_ofReal, abs_of_nonneg hdelta]

section Counterexample

abbrev PaperRealPlane := EuclideanSpace ℝ (Fin 2)

noncomputable def paperCounterexampleA :
    PaperRealPlane →L[ℝ] PaperRealPlane :=
  (Matrix.toEuclideanLin !![(0 : ℝ), 0; 0, 1]).toContinuousLinearMap

noncomputable def paperCounterexampleH :
    PaperRealPlane →L[ℝ] PaperRealPlane :=
  (Matrix.toEuclideanLin !![(1 : ℝ), 1; 1, 0]).toContinuousLinearMap

noncomputable def paperCounterexampleExact : Submodule ℝ PaperRealPlane :=
  Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) 1}

noncomputable def paperCounterexampleTrial : Submodule ℝ PaperRealPlane :=
  Submodule.span ℝ
    {(1 / Real.sqrt 2) •
      (EuclideanSpace.single (0 : Fin 2) 1 -
        EuclideanSpace.single (1 : Fin 2) 1)}

noncomputable instance paperCounterexampleExact_projection :
    paperCounterexampleExact.HasOrthogonalProjection := inferInstance

noncomputable instance paperCounterexampleTrial_projection :
    paperCounterexampleTrial.HasOrthogonalProjection := inferInstance

/-- The source counterexample has angle `pi/4`, hence square sine norm one. -/
theorem paperCounterexample_sine_square_norm :
    paperHilbertSchmidtNorm
      (ForMathlib.DavisKahanExt.Real.sinAngleOperatorRC
        paperCounterexampleExact paperCounterexampleTrial) = 1 := by
  rw [← ForMathlib.UnitarilyInvariantNorm.frobenius_apply
    ℝ PaperRealPlane
    (ForMathlib.DavisKahanExt.Real.sinAngleOperatorRC
      paperCounterexampleExact paperCounterexampleTrial).toLinearMap rfl
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  norm_num [paperCounterexampleExact, paperCounterexampleTrial,
    ForMathlib.DavisKahanExt.Real.sinAngleOperatorRC,
    ForMathlib.DavisKahanExt.sinAngleOperatorC,
    paperHilbertSchmidtNorm, paperHilbertSchmidtEnergy]

/-- The perturbation in the printed counterexample has square norm `sqrt 3`. -/
theorem paperCounterexample_perturbation_square_norm :
    paperHilbertSchmidtNorm paperCounterexampleH = Real.sqrt 3 := by
  rw [← ForMathlib.UnitarilyInvariantNorm.frobenius_apply
    ℝ PaperRealPlane paperCounterexampleH.toLinearMap rfl
    (EuclideanSpace.basisFun (Fin 2) ℝ)]
  norm_num [paperCounterexampleH, paperHilbertSchmidtNorm,
    paperHilbertSchmidtEnergy]

/-- The single directional gap `delta=2` does not imply the symmetric
square-norm estimate. -/
theorem paperOneGap_does_not_imply_symmetric_square_estimate :
    paperHilbertSchmidtNorm paperCounterexampleH <
      2 * paperHilbertSchmidtNorm
        (ForMathlib.DavisKahanExt.Real.sinAngleOperatorRC
          paperCounterexampleExact paperCounterexampleTrial) := by
  rw [paperCounterexample_sine_square_norm,
    paperCounterexample_perturbation_square_norm]
  have hsqrt3 : Real.sqrt 3 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  nlinarith

end Counterexample

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
