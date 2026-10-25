/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.RealFourOptimization
public import ForTauCeti.Analysis.InnerProductSpace.Projection.CosineSineBasis
public import ForTauCeti.Analysis.InnerProductSpace.OrthonormalMatrix

/-!
# Real four-dimensional transport in terms of actual principal angles

The cosine--sine chart is constructed from the pair of subspaces, including
zero, equal and right principal angles. Orthogonality, projection transport
and every singular value of the displacement pass through the same chart.
Thus the ambient minimum below compares with every orthogonal competitor,
without a supplied coordinate chart or a principal-plane invariance assumption.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.RealTransport

open _root_.Matrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The full spectral displacement cost of a real endomorphism. -/
@[expose] def realSpectralDisplacementCost (rho : ℝ → ℝ) (A : E →ₗ[ℝ] E) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E), rho ((LinearMap.id - A).singularValues i)

/-- The real four-dimensional cosine--sine chart uses the accepted ordered
principal angles, including their endpoint multiplicities. -/
theorem exists_four_principalAngle_coordinates
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 4)
    (hK : Module.finrank ℝ K = 2) (hL : Module.finrank ℝ L = 2) :
    ∃ b : OrthonormalBasis (Fin 2 ⊕ Fin 2) ℝ E,
      LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap = fourSourceProjection ∧
      LinearMap.toMatrixOrthonormal b L.starProjection.toLinearMap =
        fourCSRotation (fun i => K.principalAngles L i) * fourSourceProjection *
          (fourCSRotation (fun i => K.principalAngles L i)).transpose := by
  classical
  have hc := K.exists_cosineSine_projection_matrices L
    (by omega : Module.finrank ℝ K = Module.finrank ℝ L)
    (by omega : Module.finrank ℝ E = 2 * Module.finrank ℝ L)
  rw [hL] at hc
  obtain ⟨b, hbK, hbL⟩ := hc
  refine ⟨b, hbK, ?_⟩
  rw [hbL]
  simp only [fourCSRotation, fourSourceProjection, fromBlocks_transpose,
    diagonal_transpose, transpose_neg, fromBlocks_multiply, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, diagonal_mul_diagonal]
  congr 1 <;> congr 1 <;> funext i <;>
    simp only [RCLike.ofReal_real_eq_id, id_eq] <;> ring

private theorem toMatrix_adjoint
    (b : OrthonormalBasis (Fin 2 ⊕ Fin 2) ℝ E) (A : E →ₗ[ℝ] E) :
    LinearMap.toMatrixOrthonormal b A.adjoint =
      (LinearMap.toMatrixOrthonormal b A).transpose := by
  rw [← LinearMap.star_eq_adjoint, map_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

private theorem realSpectralDisplacementCost_coordinates
    (b : OrthonormalBasis (Fin 2 ⊕ Fin 2) ℝ E) (hE : Module.finrank ℝ E = 4)
    (rho : ℝ → ℝ) (A : E →ₗ[ℝ] E) :
    realSpectralDisplacementCost rho A =
      fourDisplacementCost rho (LinearMap.toMatrixOrthonormal b A) := by
  have hsv := b.singularValues_toMatrixOrthonormal (LinearMap.id - A)
  have hid : LinearMap.toMatrixOrthonormal b (LinearMap.id : E →ₗ[ℝ] E) = 1 :=
    map_one (LinearMap.toMatrixOrthonormal b)
  rw [map_sub, hid, map_sub, Matrix.toLpLin_one] at hsv
  unfold realSpectralDisplacementCost fourDisplacementCost
  rw [hE, hsv]

private theorem four_transport_coordinates_iff
    (K L : Submodule ℝ E) (b : OrthonormalBasis (Fin 2 ⊕ Fin 2) ℝ E)
    (theta : Fin 2 → ℝ)
    (hK : LinearMap.toMatrixOrthonormal b K.starProjection.toLinearMap = fourSourceProjection)
    (hL : LinearMap.toMatrixOrthonormal b L.starProjection.toLinearMap =
      fourCSRotation theta * fourSourceProjection * (fourCSRotation theta).transpose)
    (A : E →ₗ[ℝ] E) :
    (A.adjoint ∘ₗ A = LinearMap.id ∧
      A ∘ₗ K.starProjection.toLinearMap ∘ₗ A.adjoint = L.starProjection.toLinearMap) ↔
    ((LinearMap.toMatrixOrthonormal b A).transpose * LinearMap.toMatrixOrthonormal b A = 1 ∧
      LinearMap.toMatrixOrthonormal b A * fourSourceProjection *
        (LinearMap.toMatrixOrthonormal b A).transpose =
          fourCSRotation theta * fourSourceProjection * (fourCSRotation theta).transpose) := by
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
  simp only [map_mul, map_one, toMatrix_adjoint, hK, hL, mul_assoc]

/-- Exact real four-dimensional transport minimum for arbitrary rank-two
subspaces. The angle parameters are their actual accepted principal angles.
Every ambient orthogonal transporter is compared, in both determinant classes.
The cost may be any continuous nondecreasing penalty on `[0,2]` vanishing at zero. -/
theorem exists_minimizing_real_four_transport_principalAngles
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 4)
    (hK : Module.finrank ℝ K = 2) (hL : Module.finrank ℝ L = 2)
    (rho : ℝ → ℝ) (hrho : MonotoneOn rho (Set.Icc 0 2))
    (hcont : ContinuousOn rho (Set.Icc 0 2)) (hzero : rho 0 = 0) :
    let h := (K.principalAngles L 0 + K.principalAngles L 1) / 2
    let d := (K.principalAngles L 0 - K.principalAngles L 1) / 2
    ∃ delta ∈ Set.Icc d h, IsMinOn (fourEdgeCost rho h) (Set.Icc d h) delta ∧
      ∃ A : E →ₗ[ℝ] E,
        A.adjoint ∘ₗ A = LinearMap.id ∧
        A ∘ₗ K.starProjection.toLinearMap ∘ₗ A.adjoint = L.starProjection.toLinearMap ∧
        realSpectralDisplacementCost rho A = min (fourEdgeCost rho h delta)
          (rho 2 + 2*fourPhasePenalty rho (K.principalAngles L 1)) ∧
        IsMinOn (realSpectralDisplacementCost rho)
          {B | B.adjoint ∘ₗ B = LinearMap.id ∧
            B ∘ₗ K.starProjection.toLinearMap ∘ₗ B.adjoint = L.starProjection.toLinearMap} A := by
  classical
  dsimp only
  let h := (K.principalAngles L 0 + K.principalAngles L 1) / 2
  let d := (K.principalAngles L 0 - K.principalAngles L 1) / 2
  have ht : h+d = K.principalAngles L 0 := by dsimp [h, d]; ring
  have hu : h-d = K.principalAngles L 1 := by dsimp [h, d]; ring
  have hd : 0 ≤ d := by
    have ho := K.principalAngles_antitone L (show 0 ≤ (1 : ℕ) by omega)
    dsimp [d]
    linarith
  have hdh : d ≤ h := by linarith [K.principalAngles_nonneg L 1]
  have hhd : h+d ≤ Real.pi / 2 := ht ▸ K.principalAngles_le_pi_div_two L 0
  have htheta : (fun i : Fin 2 => K.principalAngles L i) = ![h+d, h-d] := by
    funext i
    fin_cases i <;> simp [ht, hu]
  obtain ⟨b, hbK, hbL⟩ := exists_four_principalAngle_coordinates K L hE hK hL
  rw [htheta] at hbL
  obtain ⟨delta, hdelta, hscalar, W, hW, htrans, hcost, hmin⟩ :=
    exists_minimizing_four_transport h d hd hdh hhd rho hrho hcont hzero
  let A := (LinearMap.toMatrixOrthonormal b).symm W
  have hA : LinearMap.toMatrixOrthonormal b A = W :=
    (LinearMap.toMatrixOrthonormal b).apply_symm_apply W
  have hfeas := (four_transport_coordinates_iff K L b _ hbK hbL A).mpr
    (by simpa only [hA] using And.intro hW htrans)
  refine ⟨delta, hdelta, hscalar, A, hfeas.1, hfeas.2, ?_, ?_⟩
  · rw [realSpectralDisplacementCost_coordinates b hE, hA, hcost, hu]
  · intro B hB
    change realSpectralDisplacementCost rho A ≤ realSpectralDisplacementCost rho B
    rw [realSpectralDisplacementCost_coordinates b hE,
      realSpectralDisplacementCost_coordinates b hE, hA]
    exact hmin ((four_transport_coordinates_iff K L b _ hbK hbL B).mp hB)

/-- Closed nuclear minimum for arbitrary real rank-two subspaces in ambient
dimension four. It includes unequal and degenerate principal angles and
compares with all ambient orthogonal transporters. -/
theorem exists_minimizing_real_four_nuclear_transport_principalAngles
    (K L : Submodule ℝ E) (hE : Module.finrank ℝ E = 4)
    (hK : Module.finrank ℝ K = 2) (hL : Module.finrank ℝ L = 2) :
    ∃ A : E →ₗ[ℝ] E,
      A.adjoint ∘ₗ A = LinearMap.id ∧
      A ∘ₗ K.starProjection.toLinearMap ∘ₗ A.adjoint = L.starProjection.toLinearMap ∧
      realSpectralDisplacementCost id A =
        min (4*Real.sin ((K.principalAngles L 0 + K.principalAngles L 1)/2))
          (2+4*Real.sin (K.principalAngles L 1/2)) ∧
      IsMinOn (realSpectralDisplacementCost id)
        {B | B.adjoint ∘ₗ B = LinearMap.id ∧
          B ∘ₗ K.starProjection.toLinearMap ∘ₗ B.adjoint = L.starProjection.toLinearMap} A := by
  classical
  let h := (K.principalAngles L 0 + K.principalAngles L 1) / 2
  let d := (K.principalAngles L 0 - K.principalAngles L 1) / 2
  have ht : h+d = K.principalAngles L 0 := by dsimp [h, d]; ring
  have hu : h-d = K.principalAngles L 1 := by dsimp [h, d]; ring
  have hd : 0 ≤ d := by
    have ho := K.principalAngles_antitone L (show 0 ≤ (1 : ℕ) by omega)
    dsimp [d]
    linarith
  have hdh : d ≤ h := by linarith [K.principalAngles_nonneg L 1]
  have hhd : h+d ≤ Real.pi / 2 := ht ▸ K.principalAngles_le_pi_div_two L 0
  obtain ⟨delta, hdelta, hscalar, A, hA, htrans, hcost, hmin⟩ :=
    exists_minimizing_real_four_transport_principalAngles K L hE hK hL id
      (fun _ _ _ _ hxy => hxy) continuous_id.continuousOn rfl
  obtain ⟨hvalue, hedge⟩ := four_nuclear_edge_minimum h d hd hdh hhd
  have hscalarval : fourEdgeCost id h delta = 4*Real.sin h := by
    apply le_antisymm
    · rw [← hvalue]
      exact hscalar ⟨hdh, le_rfl⟩
    · rw [← hvalue]
      exact hedge hdelta
  refine ⟨A, hA, htrans, ?_, hmin⟩
  rw [hcost, hscalarval, fourPhasePenalty, id_eq,
    sqrt_displacement_chord_eq_two_sin_half _
      ⟨K.principalAngles_nonneg L 1, (K.principalAngles_le_pi_div_two L 1).trans
        (by linarith [Real.pi_pos])⟩]
  simp only [id_eq]
  congr 1
  ring

end TauCeti.DavisKahan.FiniteDimensional.RealTransport
