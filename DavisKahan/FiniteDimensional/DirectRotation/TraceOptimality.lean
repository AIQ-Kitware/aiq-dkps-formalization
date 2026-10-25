/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.TraceRatio

/-!
# Trace-norm optimality of the real four-dimensional competitor

The projection difference in the parameterized real example has scalar
square, `(P_U - P_V)^2 = sin(theta)^2 I`.  This identifies each of its
four singular values without appealing to a general CS decomposition.
The projection-displacement lower bound then proves that the explicit
orthogonal competitor globally minimizes the trace norm, not merely that
it beats the canonical direct rotation.
-/

public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional
namespace SmallAngleCounterexample

open scoped InnerProductSpace
open Module (finrank)
open ShortRotationCounterexample (E4 U4 projection_U4_coord)

noncomputable section

private theorem circle (theta : ℝ) :
    Real.cos theta ^ 2 + Real.sin theta ^ 2 = 1 := by
  nlinarith [Real.sin_sq_add_cos_sq theta]

/-- Coordinate form of the projection difference in the two-plane family. -/
theorem projectionDifference_coord (theta : ℝ) (x : E4) (i : Fin 4) :
    ((projection U4 - projection (V4 theta)) x) i =
      if i = 0 then Real.sin theta ^ 2 * x 0 -
          Real.sin theta * Real.cos theta * x 3
      else if i = 1 then Real.sin theta ^ 2 * x 1 +
          Real.sin theta * Real.cos theta * x 2
      else if i = 2 then -(Real.sin theta ^ 2 * x 2) +
          Real.sin theta * Real.cos theta * x 1
      else -(Real.sin theta ^ 2 * x 3) -
          Real.sin theta * Real.cos theta * x 0 := by
  simp only [LinearMap.sub_apply]
  have hcircle := circle theta
  fin_cases i
  · simp [projection_U4_coord, projection_V4_coord];
      linear_combination -(x 0) * hcircle
  · simp [projection_U4_coord, projection_V4_coord];
      linear_combination -(x 1) * hcircle
  · simp [projection_U4_coord, projection_V4_coord]; ring
  · simp [projection_U4_coord, projection_V4_coord]; ring

/-- Squaring the projection difference gives `sin(theta)^2` times the identity.
The identity holds for arbitrary real `theta`, independently of acuteness. -/
theorem projectionDifference_sq (theta : ℝ) :
    (projection U4 - projection (V4 theta)) ∘ₗ
        (projection U4 - projection (V4 theta)) =
      Real.sin theta ^ 2 • (LinearMap.id : E4 →ₗ[ℝ] E4) := by
  apply LinearMap.ext
  intro x
  ext i
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
  have hcircle := circle theta
  -- Rewrite the *outer* projector difference before expanding its argument.
  -- A broad `simp` unfolds the map subtraction first and hides the coordinate lemma.
  have h0 (z : E4) :
      ((projection U4 - projection (V4 theta)) z) 0 =
        Real.sin theta ^ 2 * z 0 - Real.sin theta * Real.cos theta * z 3 := by
    simpa using projectionDifference_coord theta z 0
  have h1 (z : E4) :
      ((projection U4 - projection (V4 theta)) z) 1 =
        Real.sin theta ^ 2 * z 1 + Real.sin theta * Real.cos theta * z 2 := by
    simpa using projectionDifference_coord theta z 1
  have h2 (z : E4) :
      ((projection U4 - projection (V4 theta)) z) 2 =
        -(Real.sin theta ^ 2 * z 2) + Real.sin theta * Real.cos theta * z 1 := by
    simpa using projectionDifference_coord theta z 2
  have h3 (z : E4) :
      ((projection U4 - projection (V4 theta)) z) 3 =
        -(Real.sin theta ^ 2 * z 3) - Real.sin theta * Real.cos theta * z 0 := by
    simpa using projectionDifference_coord theta z 3
  -- Prove the four scalar identities at literal indices before applying
  -- coordinate extensionality.  Rewriting under `fin_cases` otherwise leaves
  -- elaborator-generated `Fin` indices that do not match `h0` through `h3`.
  have hsq0 :
      ((projection U4 - projection (V4 theta))
        ((projection U4 - projection (V4 theta)) x)) 0 =
        Real.sin theta ^ 2 * x 0 := by
    rw [h0, h0 x, h3 x]
    linear_combination (Real.sin theta ^ 2 * x 0) * hcircle
  have hsq1 :
      ((projection U4 - projection (V4 theta))
        ((projection U4 - projection (V4 theta)) x)) 1 =
        Real.sin theta ^ 2 * x 1 := by
    rw [h1, h1 x, h2 x]
    linear_combination (Real.sin theta ^ 2 * x 1) * hcircle
  have hsq2 :
      ((projection U4 - projection (V4 theta))
        ((projection U4 - projection (V4 theta)) x)) 2 =
        Real.sin theta ^ 2 * x 2 := by
    rw [h2, h2 x, h1 x]
    linear_combination (Real.sin theta ^ 2 * x 2) * hcircle
  have hsq3 :
      ((projection U4 - projection (V4 theta))
        ((projection U4 - projection (V4 theta)) x)) 3 =
        Real.sin theta ^ 2 * x 3 := by
    rw [h3, h3 x, h0 x]
    linear_combination (Real.sin theta ^ 2 * x 3) * hcircle
  fin_cases i
  · simpa using hsq0
  · simpa using hsq1
  · simpa using hsq2
  · simpa using hsq3

/-- The projector difference is self-adjoint, so the same scalar identity
holds for its Gram operator. -/
theorem gram_projectionDifference (theta : ℝ) :
    (projection U4 - projection (V4 theta)).adjoint ∘ₗ
        (projection U4 - projection (V4 theta)) =
      Real.sin theta ^ 2 • (LinearMap.id : E4 →ₗ[ℝ] E4) := by
  rw [map_sub, projection_adjoint, projection_adjoint]
  exact projectionDifference_sq theta

/-- Every singular value of the projector difference is `sin(theta)` when
that sine is nonnegative. -/
theorem singularValues_projectionDifference (theta : ℝ)
    (hs : 0 ≤ Real.sin theta) (j : Fin 4) :
    (projection U4 - projection (V4 theta)).singularValues (j : ℕ) =
      Real.sin theta := by
  let D : E4 →ₗ[ℝ] E4 := projection U4 - projection (V4 theta)
  have hfr : finrank ℝ E4 = 4 := finrank_euclideanSpace_fin
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis
    D.isSymmetric_adjoint_comp_self hfr (EuclideanSpace.basisFun (Fin 4) ℝ)
    (μ := fun _ => Real.sin theta ^ 2) (fun _ _ _ => le_rfl)
    (fun i => by
      rw [show D.adjoint ∘ₗ D = Real.sin theta ^ 2 • LinearMap.id from
        gram_projectionDifference theta]
      simp)
  rw [D.singularValues_of_lt hfr j.isLt, congrFun heig ⟨(j : ℕ), j.isLt⟩]
  exact Real.sqrt_sq hs

/-- The exact trace norm of the difference of the two rank-two projections. -/
theorem kyFanSum_projectionDifference (theta : ℝ) (hs : 0 ≤ Real.sin theta) :
    kyFanSum 4 (projection U4 - projection (V4 theta)) =
      4 * Real.sin theta := by
  rw [kyFanSum_eq_sum_fin, Fin.sum_univ_four]
  rw [singularValues_projectionDifference theta hs 0,
    singularValues_projectionDifference theta hs 1,
    singularValues_projectionDifference theta hs 2,
    singularValues_projectionDifference theta hs 3]
  ring

/-- Every admissible orthogonal transport incurs trace displacement of at
least `4 sin(theta)`. -/
theorem traceDisplacement_lower_bound (theta : ℝ) (hs : 0 ≤ Real.sin theta)
    (W : E4 ≃ₗᵢ[ℝ] E4) (hmap : U4.map W.toLinearMap = V4 theta) :
    4 * Real.sin theta ≤ kyFanSum 4 (LinearMap.id - W.toLinearMap) := by
  rw [← kyFanSum_projectionDifference theta hs]
  exact projectionDifference_kyFanSum_le_displacement U4 (V4 theta) W hmap 4

/-- The explicit competitor attains the global trace lower bound. -/
theorem Wequiv_traceMinimizer (theta : ℝ) (hs : 0 ≤ Real.sin theta)
    (W : E4 ≃ₗᵢ[ℝ] E4) (hmap : U4.map W.toLinearMap = V4 theta) :
    kyFanSum 4 (LinearMap.id - (Wequiv theta).toLinearMap) ≤
      kyFanSum 4 (LinearMap.id - W.toLinearMap) := by
  rw [kyFanSum_displacement_W theta hs]
  exact traceDisplacement_lower_bound theta hs W hmap

/-- An attained minimum, specified without a compactness argument or an
abstract minimization operator. -/
theorem exists_traceMinimizer (theta : ℝ) (hs : 0 ≤ Real.sin theta) :
    ∃ W : E4 ≃ₗᵢ[ℝ] E4,
      U4.map W.toLinearMap = V4 theta ∧
      kyFanSum 4 (LinearMap.id - W.toLinearMap) = 4 * Real.sin theta ∧
      ∀ Z : E4 ≃ₗᵢ[ℝ] E4, U4.map Z.toLinearMap = V4 theta →
        kyFanSum 4 (LinearMap.id - W.toLinearMap) ≤
          kyFanSum 4 (LinearMap.id - Z.toLinearMap) := by
  refine ⟨Wequiv theta, rfl, kyFanSum_displacement_W theta hs, ?_⟩
  intro Z hZ
  exact Wequiv_traceMinimizer theta hs Z hZ

/-- At each prescribed small positive angle, the exact trace minimum and
canonical displacement achieve the `sec(theta/2)` ratio. -/
theorem directTrace_sharpRatio (theta : ℝ)
    (h0 : 0 < theta) (h1 : theta < Real.pi / 2) :
    Real.cos (theta / 2) *
      kyFanSum 4 (LinearMap.id -
        (directRotation U4 (V4 theta)
          (acute theta (cos_pos theta h0 h1))).toLinearMap) =
      4 * Real.sin theta := by
  rw [cos_half_mul_directTrace_eq_competitorTrace theta h0 h1]
  exact kyFanSum_displacement_W theta
    (Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])).le

end
end SmallAngleCounterexample
end DavisKahan.FiniteDimensional
end TauCeti
