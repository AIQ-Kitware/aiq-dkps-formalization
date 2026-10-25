/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealTwoOptimization

/-!
# The real one-angle minimum for actual subspaces

The endpoint-complete cosine--sine chart identifies arbitrary real lines
in an actual two-dimensional space with the full coordinate transport
fiber. Every ambient competitor and every displacement singular value
pass through that chart. The result is therefore a minimum over all
orthogonal competitors, including reflections.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open _root_.Matrix
open TauCeti.Matrix (planeOrthogonal)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Actual lines admit the one-angle chart at both endpoints as well as
in the acute case. The angle is the accepted principal angle. -/
theorem exists_two_principalAngle_coordinates
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 2)
    (hK : Module.finrank ℝ K = 1) (hL : Module.finrank ℝ L = 1) :
    ∃ b : OrthonormalBasis (Fin 2) ℝ E,
      LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap = twoSourceProjection ∧
      LinearMap.toMatrixOrthonormal b L.starProjection.toLinearMap =
        planeOrthogonal (K.principalAngles L 0) 1 * twoSourceProjection *
          (planeOrthogonal (K.principalAngles L 0) 1).transpose := by
  classical
  have hc := K.exists_cosineSine_projection_matrices L
    (by omega : Module.finrank ℝ K = Module.finrank ℝ L)
    (by omega : Module.finrank ℝ E = 2 * Module.finrank ℝ L)
  rw [hL] at hc
  obtain ⟨b, hbK, hbL⟩ := hc
  let c := b.reindex (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2)
  have hmatrix (A : E →ₗ[ℝ] E) (i j : Fin 1 ⊕ Fin 1) :
      LinearMap.toMatrixOrthonormal c A (finSumFinEquiv i) (finSumFinEquiv j) =
        LinearMap.toMatrixOrthonormal b A i j := by
    simp only [LinearMap.toMatrixOrthonormal_apply_apply, c,
      OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply]
  refine ⟨c, ?_, ?_⟩
  · ext i j
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).surjective i
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).surjective j
    rw [hmatrix, hbK]
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      norm_num [twoSourceProjection, finSumFinEquiv]
  · ext i j
    obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).surjective i
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 1 ⊕ Fin 1 ≃ Fin 2).surjective j
    rw [hmatrix, hbL]
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;>
      simp [twoSourceProjection, planeOrthogonal, finSumFinEquiv,
        Matrix.mul_apply, Fin.sum_univ_two, pow_two]; ring

private theorem two_cost_coordinates
    (b : OrthonormalBasis (Fin 2) ℝ E) (hE : Module.finrank ℝ E = 2)
    (rho : ℝ → ℝ) (A : E →ₗ[ℝ] E) :
    realSpectralDisplacementCost rho A =
      twoDisplacementCost rho (LinearMap.toMatrixOrthonormal b A) := by
  have hsv := b.singularValues_toMatrixOrthonormal (LinearMap.id - A)
  have hid : LinearMap.toMatrixOrthonormal b (LinearMap.id : E →ₗ[ℝ] E) = 1 :=
    map_one (LinearMap.toMatrixOrthonormal b)
  rw [map_sub, hid, map_sub, Matrix.toLpLin_one] at hsv
  unfold realSpectralDisplacementCost twoDisplacementCost
  rw [hE, hsv]

private theorem two_transport_coordinates_iff
    (K L : Submodule ℝ E) (b : OrthonormalBasis (Fin 2) ℝ E) (t : ℝ)
    (hK : LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap = twoSourceProjection)
    (hL : LinearMap.toMatrixOrthonormal b L.starProjection.toLinearMap =
      planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose)
    (A : E →ₗ[ℝ] E) :
    (A.adjoint ∘ₗ A = LinearMap.id ∧
      A ∘ₗ K.starProjection.toLinearMap ∘ₗ A.adjoint = L.starProjection.toLinearMap) ↔
    ((LinearMap.toMatrixOrthonormal b A).transpose * LinearMap.toMatrixOrthonormal b A = 1 ∧
      LinearMap.toMatrixOrthonormal b A * twoSourceProjection *
        (LinearMap.toMatrixOrthonormal b A).transpose =
          planeOrthogonal t 1 * twoSourceProjection * (planeOrthogonal t 1).transpose) := by
  have hadj : LinearMap.toMatrixOrthonormal b A.adjoint =
      (LinearMap.toMatrixOrthonormal b A).transpose := by
    rw [← LinearMap.star_eq_adjoint, map_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
  change (A.adjoint * A = 1 ∧
    A * (K.starProjection.toLinearMap * A.adjoint) = L.starProjection.toLinearMap) ↔ _
  rw [← (LinearMap.toMatrixOrthonormal b).injective.eq_iff
      (a := A.adjoint * A) (b := 1),
    ← (LinearMap.toMatrixOrthonormal b).injective.eq_iff
      (a := A * (K.starProjection.toLinearMap * A.adjoint))
      (b := L.starProjection.toLinearMap)]
  change (LinearMap.toMatrixOrthonormal b (A.adjoint * A) =
      LinearMap.toMatrixOrthonormal b 1 ∧
    LinearMap.toMatrixOrthonormal b (A * (K.starProjection.toLinearMap * A.adjoint)) =
      LinearMap.toMatrixOrthonormal b L.starProjection.toLinearMap) ↔ _
  simp only [map_mul, map_one, hadj, hK, hL, mul_assoc]

/-- Exact one-angle real minimum for actual lines in dimension two.
The infimum is attained and compares with every ambient orthogonal map.
The penalty may be any nondecreasing function on `[0,2]` vanishing at zero. -/
theorem exists_minimizing_real_two_transport_principalAngles
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 2)
    (hK : Module.finrank ℝ K = 1) (hL : Module.finrank ℝ L = 1)
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0) :
    ∃ A : E →ₗ[ℝ] E,
      A.adjoint ∘ₗ A = LinearMap.id ∧
      A ∘ₗ K.starProjection.toLinearMap ∘ₗ A.adjoint = L.starProjection.toLinearMap ∧
      realSpectralDisplacementCost rho A =
        min (2 * rho (Real.sqrt (2 - 2 * Real.cos (K.principalAngles L 0)))) (rho 2) ∧
      IsMinOn (realSpectralDisplacementCost rho)
        {B | B.adjoint ∘ₗ B = LinearMap.id ∧
          B ∘ₗ K.starProjection.toLinearMap ∘ₗ B.adjoint = L.starProjection.toLinearMap} A := by
  obtain ⟨b, hbK, hbL⟩ := exists_two_principalAngle_coordinates K L hE hK hL
  obtain ⟨W, hW, htrans, hcost, hmin⟩ := exists_minimizing_two_transport
    (K.principalAngles L 0) ⟨K.principalAngles_nonneg L 0, K.principalAngles_le_pi_div_two L 0⟩
    rho hrho hzero
  let A := (LinearMap.toMatrixOrthonormal b).symm W
  have hA : LinearMap.toMatrixOrthonormal b A = W :=
    (LinearMap.toMatrixOrthonormal b).apply_symm_apply W
  have hfeas := (two_transport_coordinates_iff K L b _ hbK hbL A).mpr
    (by simpa only [hA] using And.intro hW htrans)
  refine ⟨A, hfeas.1, hfeas.2, ?_, ?_⟩
  · rw [two_cost_coordinates b hE, hA, hcost]
  · intro B hB
    change realSpectralDisplacementCost rho A ≤ realSpectralDisplacementCost rho B
    rw [two_cost_coordinates b hE, two_cost_coordinates b hE, hA]
    exact hmin ((two_transport_coordinates_iff K L b _ hbK hbL B).mp hB)

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
