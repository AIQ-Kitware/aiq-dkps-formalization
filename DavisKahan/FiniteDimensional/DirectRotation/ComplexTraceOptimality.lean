/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.Sources.DavisKahan1970.Section4Examples
public import DavisKahan.FiniteDimensional.DirectRotation.ProjectionDisplacement
public import ForTauCeti.Analysis.InnerProductSpace.TwoDimensionalSingularValues

/-!
# The complex principal-plane trace minimizer

The fixed-phase endpoint of Davis--Kahan Example 4.2 is a genuine complex
unitary, not merely an arbitrary linear transformation. Its displacement has
singular values `(2 sin theta, 0)`, including at the right-angle endpoint.
The source and target lines are related by this unitary, so the general
projection lower bound applies without an acuteness hypothesis.

The many-principal-plane global optimum needs an additional orthogonal
assembly argument; the planar endpoint alone does not assert that global
statement.
-/

public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace ComplexTraceOptimality

open scoped InnerProductSpace
open DavisKahan1970.Section4Examples

noncomputable section

abbrev E2 := ComplexPlane

private def phase (theta : ℝ) : ℂ := example42Phase (theta + theta)

private theorem phase_normSq (theta : ℝ) : Complex.normSq (phase theta) = 1 := by
  have hre : (phase theta).re = Real.cos (theta + theta) := by
    simp only [phase, example42Phase, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : (phase theta).im = Real.sin (theta + theta) := by
    simp only [phase, example42Phase, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [Complex.normSq_apply, hre, him]
  nlinarith [Real.sin_sq_add_cos_sq (theta + theta)]

private theorem star_phase_mul_phase (theta : ℝ) :
    star (phase theta) * phase theta = 1 := by
  calc
    star (phase theta) * phase theta =
        ((Complex.normSq (phase theta) : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.normSq_eq_conj_mul_self]
    _ = 1 := by rw [phase_normSq]; norm_num

private theorem phase_mul_star_phase (theta : ℝ) :
    phase theta * star (phase theta) = 1 := by
  rw [mul_comm, star_phase_mul_phase]

/-- The phase-corrected rotation in a diagonal eigenbasis. -/
private def phaseMap (theta : ℝ) : E2 →ₗ[ℂ] E2 :=
  Matrix.toEuclideanLin !![phase theta, 0; 0, 1]

/-- Its inverse is its adjoint. -/
private def inversePhaseMap (theta : ℝ) : E2 →ₗ[ℂ] E2 :=
  Matrix.toEuclideanLin !![star (phase theta), 0; 0, 1]

private theorem phaseMap_zero (theta : ℝ) (x : E2) :
    phaseMap theta x 0 = phase theta * x 0 := by
  simp [phaseMap, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

private theorem phaseMap_one (theta : ℝ) (x : E2) :
    phaseMap theta x 1 = x 1 := by
  simp [phaseMap, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

private theorem inversePhaseMap_zero (theta : ℝ) (x : E2) :
    inversePhaseMap theta x 0 = star (phase theta) * x 0 := by
  simp [inversePhaseMap, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

private theorem inversePhaseMap_one (theta : ℝ) (x : E2) :
    inversePhaseMap theta x 1 = x 1 := by
  simp [inversePhaseMap, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

private theorem phaseMap_left_inv (theta : ℝ) :
    inversePhaseMap theta ∘ₗ phaseMap theta = LinearMap.id := by
  have h0 (x : E2) : (inversePhaseMap theta (phaseMap theta x)) 0 = x 0 := by
    rw [inversePhaseMap_zero, phaseMap_zero]
    calc
      star (phase theta) * (phase theta * x 0) =
          (star (phase theta) * phase theta) * x 0 := by ring
      _ = x 0 := by rw [star_phase_mul_phase, one_mul]
  have h1 (x : E2) : (inversePhaseMap theta (phaseMap theta x)) 1 = x 1 := by
    rw [inversePhaseMap_one, phaseMap_one]
  ext x i
  fin_cases i
  · simpa using h0 x
  · simpa using h1 x

private theorem phaseMap_right_inv (theta : ℝ) :
    phaseMap theta ∘ₗ inversePhaseMap theta = LinearMap.id := by
  have h0 (x : E2) : (phaseMap theta (inversePhaseMap theta x)) 0 = x 0 := by
    rw [phaseMap_zero, inversePhaseMap_zero]
    calc
      phase theta * (star (phase theta) * x 0) =
          (phase theta * star (phase theta)) * x 0 := by ring
      _ = x 0 := by rw [phase_mul_star_phase, one_mul]
  have h1 (x : E2) : (phaseMap theta (inversePhaseMap theta x)) 1 = x 1 := by
    rw [phaseMap_one, inversePhaseMap_one]
  ext x i
  fin_cases i
  · simpa using h0 x
  · simpa using h1 x

private theorem phaseMap_preserves_inner (theta : ℝ) (x y : E2) :
    ⟪phaseMap theta x, phaseMap theta y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two,
    RCLike.inner_apply, phaseMap_zero, phaseMap_one, map_mul]
  have hscalar : (starRingEnd ℂ) (phase theta) * phase theta = 1 :=
    star_phase_mul_phase theta
  calc
    phase theta * y 0 * ((starRingEnd ℂ) (phase theta) * (starRingEnd ℂ) (x 0)) +
        y 1 * (starRingEnd ℂ) (x 1) =
      ((starRingEnd ℂ) (phase theta) * phase theta) *
          (y 0 * (starRingEnd ℂ) (x 0)) + y 1 * (starRingEnd ℂ) (x 1) := by ring
    _ = y 0 * (starRingEnd ℂ) (x 0) + y 1 * (starRingEnd ℂ) (x 1) := by
      rw [hscalar, one_mul]

/-- The complex phase-rotated planar operator as an attained unitary. -/
def phaseUnitary (theta : ℝ) : E2 ≃ₗᵢ[ℂ] E2 :=
  (LinearEquiv.ofLinearMap (phaseMap theta) (inversePhaseMap theta)
    (phaseMap_right_inv theta) (phaseMap_left_inv theta)).isometryOfInner
      (phaseMap_preserves_inner theta)

/-- Its linear map is exactly the endpoint of the historic phase family. -/
theorem phaseUnitary_toLinearMap (theta : ℝ) :
    (phaseUnitary theta).toLinearMap = example42Competitor theta theta := by
  change phaseMap theta = example42Competitor theta theta
  have h0 (x : E2) : phaseMap theta x 0 = example42Competitor theta theta x 0 := by
    rw [phaseMap_zero]
    simp [example42Competitor, phase, Matrix.toLpLin_apply,
      Matrix.vecHead, Matrix.vecTail]
  have h1 (x : E2) : phaseMap theta x 1 = example42Competitor theta theta x 1 := by
    rw [phaseMap_one]
    simp [example42Competitor, example42Phase_zero,
      Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]
  ext x i
  fin_cases i
  · simpa using h0 x
  · simpa using h1 x

/-- At every angle from zero through a right angle, the endpoint phase unitary
has exactly the singular values of a rank-one displacement. -/
theorem singularValues_phaseUnitary (theta : ℝ)
    (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    (LinearMap.id - (phaseUnitary theta).toLinearMap).singularValues =
      TauCeti.pairSingularValues (2 * Real.sin theta) 0 := by
  rw [phaseUnitary_toLinearMap]
  exact example4_2_endpoint_singularValues h0 hpi

/-- The trace displacement of the attained complex planar unitary is exactly
`2 sin theta`; no acute-angle restriction occurs. -/
theorem kyFanSum_phaseUnitary (theta : ℝ)
    (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    kyFanSum 2 (LinearMap.id - (phaseUnitary theta).toLinearMap) =
      2 * Real.sin theta := by
  rw [phaseUnitary_toLinearMap]
  exact example4_2_endpoint_traceDisplacement h0 hpi

/-- Source and target lines for the phase-unitary example. -/
private def diagonalVector : E2 :=
  (EuclideanSpace.basisFun (Fin 2) ℂ 0 : E2) +
    EuclideanSpace.basisFun (Fin 2) ℂ 1

private theorem diagonalVector_zero : diagonalVector 0 = 1 := by
  simp [diagonalVector, EuclideanSpace.basisFun_apply]

private theorem diagonalVector_one : diagonalVector 1 = 1 := by
  simp [diagonalVector, EuclideanSpace.basisFun_apply]

def sourceLine : Submodule ℂ E2 :=
  Submodule.span ℂ {diagonalVector}

/-- The source line is the diagonal complex line in the standard plane. -/
theorem sourceLine_def : sourceLine = Submodule.span ℂ
    {((EuclideanSpace.basisFun (Fin 2) ℂ 0 : E2) +
      EuclideanSpace.basisFun (Fin 2) ℂ 1)} := by
  rfl

@[expose]
def targetLine (theta : ℝ) : Submodule ℂ E2 :=
  sourceLine.map (phaseUnitary theta).toLinearMap

/-- This actual unitary transports the source complex line onto its target. -/
theorem phaseUnitary_transports (theta : ℝ) :
    sourceLine.map (phaseUnitary theta).toLinearMap = targetLine theta := rfl


/-- The source line is the diagonal line; its projection averages coordinates. -/
private theorem projection_sourceLine_apply (x : E2) :
    projection sourceLine x = ((x 0 + x 1) / 2) • diagonalVector := by
  change sourceLine.starProjection x = _
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        have hy' : y = diagonalVector := by simpa using hy
        subst y
        simp only [inner_sub_left, inner_smul_left, PiLp.inner_apply,
          Fin.sum_univ_two, RCLike.inner_apply]
        simp [diagonalVector_zero, diagonalVector_one]
        have htwo : ((starRingEnd ℂ) (2 : ℂ))⁻¹ * 2 = 1 := by
          change (star (2 : ℂ))⁻¹ * 2 = 1
          rw [star_ofNat]
          norm_num
        linear_combination -((starRingEnd ℂ) (x 0) + (starRingEnd ℂ) (x 1)) * htwo
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_right, ha, mul_zero]

private theorem projection_sourceLine_zero (x : E2) :
    projection sourceLine x 0 = (x 0 + x 1) / 2 := by
  rw [projection_sourceLine_apply]
  simp [diagonalVector_zero]

private theorem projection_sourceLine_one (x : E2) :
    projection sourceLine x 1 = (x 0 + x 1) / 2 := by
  rw [projection_sourceLine_apply]
  simp [diagonalVector_one]

private theorem projection_targetLine_apply (theta : ℝ) (x : E2) :
    projection (targetLine theta) x =
      phaseUnitary theta (projection sourceLine ((phaseUnitary theta).symm x)) := by
  have h := projection_intertwines_of_map_eq sourceLine (targetLine theta)
    (phaseUnitary theta) (phaseUnitary_transports theta)
  have hx := LinearMap.congr_fun h ((phaseUnitary theta).symm x)
  simp only [LinearMap.comp_apply] at hx
  have hWW : (phaseUnitary theta).toLinearMap ((phaseUnitary theta).symm x) = x :=
    (phaseUnitary theta).apply_symm_apply x
  rw [hWW] at hx
  exact hx.symm

private theorem projection_targetLine_zero (theta : ℝ) (x : E2) :
    projection (targetLine theta) x 0 =
      (x 0 + phase theta * x 1) / 2 := by
  rw [projection_targetLine_apply]
  change (phaseMap theta (projection sourceLine (inversePhaseMap theta x))) 0 = _
  rw [phaseMap_zero, projection_sourceLine_zero,
    inversePhaseMap_zero, inversePhaseMap_one]
  calc
    phase theta * ((star (phase theta) * x 0 + x 1) / 2) =
        ((phase theta * star (phase theta)) * x 0 + phase theta * x 1) / 2 := by
          ring
    _ = (x 0 + phase theta * x 1) / 2 := by
      rw [phase_mul_star_phase]
      ring

private theorem projection_targetLine_one (theta : ℝ) (x : E2) :
    projection (targetLine theta) x 1 =
      (star (phase theta) * x 0 + x 1) / 2 := by
  rw [projection_targetLine_apply]
  change (phaseMap theta (projection sourceLine (inversePhaseMap theta x))) 1 = _
  rw [phaseMap_one, projection_sourceLine_one,
    inversePhaseMap_zero, inversePhaseMap_one]

private theorem projectionDifference_zero (theta : ℝ) (x : E2) :
    ((projection sourceLine - projection (targetLine theta)) x) 0 =
      (1 - phase theta) * x 1 / 2 := by
  rw [LinearMap.sub_apply, PiLp.sub_apply, projection_sourceLine_zero,
    projection_targetLine_zero]
  ring

private theorem projectionDifference_one (theta : ℝ) (x : E2) :
    ((projection sourceLine - projection (targetLine theta)) x) 1 =
      (1 - star (phase theta)) * x 0 / 2 := by
  rw [LinearMap.sub_apply, PiLp.sub_apply, projection_sourceLine_one,
    projection_targetLine_one]
  ring

private theorem phase_chord_sq (theta : ℝ) :
    ‖(1 : ℂ) - phase theta‖ ^ 2 = (2 * Real.sin theta) ^ 2 := by
  rw [show phase theta = example42Phase (theta + theta) from rfl,
    norm_one_sub_example42Phase]
  have hhalf : (theta + theta) / 2 = theta := by ring
  rw [hhalf]
  nlinarith [sq_abs (Real.sin theta)]

private theorem phase_chord_mul_conj (theta : ℝ) :
    ((1 : ℂ) - phase theta) * (1 - star (phase theta)) =
      (((2 * Real.sin theta) ^ 2 : ℝ) : ℂ) := by
  calc
    ((1 : ℂ) - phase theta) * (1 - star (phase theta)) =
        star (1 - phase theta) * (1 - phase theta) := by
          rw [star_sub, star_one]
          ring
    _ = ((Complex.normSq (1 - phase theta) : ℝ) : ℂ) :=
      (Complex.normSq_eq_conj_mul_self).symm
    _ = (((2 * Real.sin theta) ^ 2 : ℝ) : ℂ) := by
      rw [Complex.normSq_eq_norm_sq, phase_chord_sq]

/-- The difference of the two complex-line projections has the same scalar
square as a real principal-plane projection difference, even at right angles. -/
theorem projectionDifference_sq (theta : ℝ) :
    (projection sourceLine - projection (targetLine theta)) ∘ₗ
        (projection sourceLine - projection (targetLine theta)) =
      ((Real.sin theta ^ 2 : ℝ) : ℂ) • (LinearMap.id : E2 →ₗ[ℂ] E2) := by
  apply LinearMap.ext
  intro x
  ext i
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  have hmul : ((1 : ℂ) - phase theta) * (1 - star (phase theta)) =
      4 * (Real.sin theta : ℂ) ^ 2 := by
    rw [phase_chord_mul_conj]
    push_cast
    ring
  have hmulSwap : (1 - star (phase theta)) * ((1 : ℂ) - phase theta) =
      4 * (Real.sin theta : ℂ) ^ 2 := by
    rw [mul_comm, hmul]
  have h0 :
      ((projection sourceLine - projection (targetLine theta))
        ((projection sourceLine - projection (targetLine theta)) x)) 0 =
          ((Real.sin theta ^ 2 : ℝ) : ℂ) * x 0 := by
    rw [projectionDifference_zero, projectionDifference_one]
    have hcast : (((Real.sin theta ^ 2 : ℝ) : ℂ)) = (Real.sin theta : ℂ) ^ 2 := by
      norm_cast
    rw [hcast]
    linear_combination (x 0 / 4) * hmul
  have h1 :
      ((projection sourceLine - projection (targetLine theta))
        ((projection sourceLine - projection (targetLine theta)) x)) 1 =
          ((Real.sin theta ^ 2 : ℝ) : ℂ) * x 1 := by
    rw [projectionDifference_one, projectionDifference_zero]
    have hcast : (((Real.sin theta ^ 2 : ℝ) : ℂ)) = (Real.sin theta : ℂ) ^ 2 := by
      norm_cast
    rw [hcast]
    linear_combination (x 1 / 4) * hmulSwap
  fin_cases i
  · simpa [PiLp.smul_apply, smul_eq_mul] using h0
  · simpa [PiLp.smul_apply, smul_eq_mul] using h1

/-- The two complex principal-plane projection singular values coincide. -/
theorem singularValues_projectionDifference (theta : ℝ)
    (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    (projection sourceLine - projection (targetLine theta)).singularValues =
      TauCeti.pairSingularValues (Real.sin theta) (Real.sin theta) := by
  have hs : 0 ≤ Real.sin theta :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hSym : (projection sourceLine - projection (targetLine theta)).IsSymmetric :=
    (projection_isSymmetric _).sub (projection_isSymmetric _)
  have hsq := projectionDifference_sq theta
  have h := TauCeti.singularValues_eq_abs_pair_of_isSymmetric_sq
    finrank_euclideanSpace_fin (EuclideanSpace.basisFun (Fin 2) ℂ)
    (projection sourceLine - projection (targetLine theta))
    (Real.sin theta) hSym hsq
  simpa [abs_of_nonneg hs] using h

/-- The complex planar projection distance is exactly `2 sin theta`. -/
theorem kyFanSum_projectionDifference (theta : ℝ)
    (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    kyFanSum 2 (projection sourceLine - projection (targetLine theta)) =
      2 * Real.sin theta := by
  rw [kyFanSum_eq_sum_fin, Fin.sum_univ_two,
    singularValues_projectionDifference theta h0 hpi]
  simp [TauCeti.pairSingularValues]
  ring

/-- The explicitly constructed complex planar unitary globally minimizes
the trace displacement, including the right-angle case. -/
theorem phaseUnitary_global_trace_minimizer (theta : ℝ)
    (h0 : 0 ≤ theta) (hpi : theta ≤ Real.pi / 2) :
    (∀ W : E2 ≃ₗᵢ[ℂ] E2,
      sourceLine.map W.toLinearMap = targetLine theta →
        kyFanSum 2 (LinearMap.id - (phaseUnitary theta).toLinearMap) ≤
          kyFanSum 2 (LinearMap.id - W.toLinearMap)) ∧
      kyFanSum 2 (LinearMap.id - (phaseUnitary theta).toLinearMap) =
        kyFanSum 2 (projection sourceLine - projection (targetLine theta)) := by
  constructor
  · intro W hmap
    calc
      kyFanSum 2 (LinearMap.id - (phaseUnitary theta).toLinearMap) =
          2 * Real.sin theta := kyFanSum_phaseUnitary theta h0 hpi
      _ = kyFanSum 2 (projection sourceLine - projection (targetLine theta)) :=
        (kyFanSum_projectionDifference theta h0 hpi).symm
      _ ≤ kyFanSum 2 (LinearMap.id - W.toLinearMap) :=
        projectionDifference_kyFanSum_le_displacement sourceLine
          (targetLine theta) W hmap 2
  · exact (kyFanSum_phaseUnitary theta h0 hpi).trans
      (kyFanSum_projectionDifference theta h0 hpi).symm

/-- The global projection bound already supplies the universal lower inequality
for this complex plane, valid even at `theta = pi/2`. -/
theorem projectionDifference_le_phaseUnitary (theta : ℝ) :
    kyFanSum 2 (projection sourceLine - projection (targetLine theta)) ≤
      kyFanSum 2 (LinearMap.id - (phaseUnitary theta).toLinearMap) :=
  projectionDifference_kyFanSum_le_displacement sourceLine
    (targetLine theta) (phaseUnitary theta) (phaseUnitary_transports theta) 2

end
end ComplexTraceOptimality
end DavisKahan.FiniteDimensional
end TauCeti
