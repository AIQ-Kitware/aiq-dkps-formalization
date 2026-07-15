/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
import DavisKahan.Experimental.InfiniteDimensional.Core.Compatibility
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.General

/-!
# Infinite-dimensional `sin 2Θ` bounds

Reflection through the comparison subspace converts a double-angle problem
into an ordinary `sin Θ` problem.  If `J_V` is the reflection through `V`, the
angle between `U` and `J_V U` is twice the angle between `U` and `V`, while
`J_V A J_V-A` is twice the off-diagonal part of `A` relative to `V`.
-/

namespace ForMathlib
namespace DavisKahanExt

open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Mirror defect used in the reflection proof of `sin 2Θ`. -/
noncomputable def reflectionDefect (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (A : E →L[𝕜] E) : E →L[𝕜] E :=
  reflectionOperator U ∘L A ∘L reflectionOperator U - A

/-- The mirror defect vanishes when the subspace reduces the operator. -/
theorem reflectionDefect_eq_zero_of_reduces
    (A : E →L[𝕜] E) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] (hU : Reduces A U) :
    reflectionDefect U A = 0 := by
  rw [reflectionDefect]
  have hcomm := reflectionOperator_comm_of_reduces A U hU
  calc
    reflectionOperator U ∘L A ∘L reflectionOperator U
        = A ∘L reflectionOperator U ∘L reflectionOperator U := by
          rw [hcomm]
    _ = A := by rw [← ContinuousLinearMap.comp_assoc,
      reflectionOperator_involutive U]; simp
    _ - A = 0 := sub_self A

/-- Conjugating and subtracting a reducing comparison operator leaves only its perturbation. -/
theorem reflectionDefect_eq_perturbationDefect
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : Reduces B V) :
    reflectionDefect V A =
      reflectionOperator V ∘L (A - B) ∘L reflectionOperator V - (A - B) := by
  have hzero := reflectionDefect_eq_zero_of_reduces B V hV
  unfold reflectionDefect at hzero ⊢
  module at hzero ⊢
  exact sub_eq_zero.mp hzero

/-- The reflection defect is bounded by twice the perturbation norm. -/
theorem norm_reflectionDefect_le_two_mul
    (A B : E →L[𝕜] E) (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (hV : Reduces B V) :
    ‖reflectionDefect V A‖ ≤ 2 * ‖A - B‖ := by
  rw [reflectionDefect_eq_perturbationDefect A B V hV]
  let J := reflectionOperator V
  have hJ : ‖J‖ ≤ 1 := norm_reflectionOperator_le_one V
  calc
    ‖J ∘L (A-B) ∘L J - (A-B)‖
        ≤ ‖J ∘L (A-B) ∘L J‖ + ‖A-B‖ := norm_sub_le _ _
    _ ≤ (‖J‖ * ‖A-B‖ * ‖J‖) + ‖A-B‖ := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_comp_le _ _ _
    _ ≤ 2 * ‖A-B‖ := by nlinarith [norm_nonneg (A-B)]

/-- Reflection of a subspace through `V`. -/
noncomputable def reflectedSubspace (V U : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] : Submodule 𝕜 E :=
  U.map (reflectionOperator V).toLinearMap

/-- Reflection transports a reducing subspace to a reducing subspace of the
conjugated operator. -/
theorem reduces_reflectedSubspace
    {A : E →L[𝕜] E} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) :
    Reduces (reflectionOperator V ∘L A ∘L reflectionOperator V)
      (reflectedSubspace V U) := by
  exact hU.map_unitary
    (reflectionOperator_unitary V)
    (reflectionOperator_involutive V)

/-- Finite-gap data is invariant under unitary reflection. -/
theorem finiteGap_reflected
    {A : E →L[𝕜] E} {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    {d : ℝ} (hfinite : FiniteGapConfiguration A U d) :
    FiniteGapConfiguration
      (reflectionOperator V ∘L A ∘L reflectionOperator V)
      (reflectedSubspace V U) d := by
  exact hfinite.unitary_conjugate
    (reflectionOperator_unitary V)
    (reflectionOperator_involutive V)

/-- The ordinary sine between `U` and its reflection through `V` is the double
sine between `U` and `V`, including ambient multiplicities. -/
theorem sinAngle_reflected_eq_sinTwoAngle
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinAngleOperator U (reflectedSubspace V U) =
      sinTwoAngleOperator U V := by
  let P := projection U
  let Q := projection V
  have hproj : projection (reflectedSubspace V U) =
      reflectionOperator V ∘L P ∘L reflectionOperator V :=
    projection_map_unitary U (reflectionOperator_unitary V)
  rw [sinAngleOperator, hproj, sinTwoAngleOperator]
  apply positive_square_root_unique
  · exact operatorAbsoluteValue_nonneg _
  · exact sinTwoAngleOperator_nonneg U V
  · rw [operatorAbsoluteValue_mul_self, sinTwoAngleOperator_sq]
    noncomm_ring [U.isIdempotentElem_starProjection,
      V.isIdempotentElem_starProjection]

/-- Reflection-defect `sin 2Θ` theorem. -/
theorem sinTwoTheta_reflectionDefect
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ ‖reflectionDefect V A‖ := by
  let A' := reflectionOperator V ∘L A ∘L reflectionOperator V
  let U' := reflectedSubspace V U
  have hA' : IsSelfAdjointOperator A' :=
    hA.unitary_conjugate (reflectionOperator_unitary V)
  have hU' : Reduces A' U' := reduces_reflectedSubspace hU
  have hfinite' := finiteGap_reflected (V := V) hfinite
  have hgaps :
      ∃ l r l' r',
        IntervalExteriorSeparated A U A' U'ᗮ l r d ∧
        IntervalExteriorSeparated A' U' A Uᗮ l' r' d :=
    finiteGap_mixedIntervalExterior hfinite hfinite'
  obtain ⟨l, r, l', r', hUU', hU'U⟩ := hgaps
  have hsin := sinTheta_symmetric hA hA' hU hU' hd hUU' hU'U
  simpa [A', U', reflectionDefect, subspaceGap,
    sinAngle_reflected_eq_sinTwoAngle] using hsin

/-- The reflection defect through the range of an isometry is controlled by
twice the residual of an approximate invariant pair. -/
theorem reflectionDefect_range_le_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    (X : F →L[𝕜] E) (hX : IsometricEmbedding X)
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M) :
    ‖reflectionDefect (LinearMap.range X.toLinearMap) A‖ ≤
      2 * ‖residual A X M‖ := by
  let P : E →L[𝕜] E := X ∘L X.adjoint
  have hP : P = projection (LinearMap.range X.toLinearMap) :=
    isometry_comp_adjoint_eq_rangeProjection X hX
  have hcross : (1-P) ∘L A ∘L P =
      (1-P) ∘L residual A X M ∘L X.adjoint := by
    ext x
    simp [P, residual, ContinuousLinearMap.comp_assoc,
      hX.adjoint_comp_self]
  have hdefect : reflectionDefect (LinearMap.range X.toLinearMap) A =
      -2 • ((1-P) ∘L A ∘L P +
        P ∘L A ∘L (1-P)) := by
    rw [← hP]
    exact reflectionDefect_eq_neg_two_smul_offDiagonal hA P
  have hadj : P ∘L A ∘L (1-P) =
      ((1-P) ∘L A ∘L P).adjoint := by
    simp [hA, ContinuousLinearMap.adjoint_comp]
  rw [hdefect, hadj, hcross]
  exact norm_two_smul_selfAdjointOffDiagonal_le_two_residual
    hA hM hX

/-- Approximate-invariant-pair residual form of `sin 2Θ`. -/
theorem sinTwoTheta_residual
    {A : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hU : Reduces A U) (X : F →L[𝕜] E) (hX : IsometricEmbedding X)
    {M : F →L[𝕜] F} (hM : IsSelfAdjointOperator M)
    {d : ℝ} (hd : 0 < d) (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoThetaEmbedding U X‖ ≤ 2 * ‖residual A X M‖ := by
  let V := LinearMap.range X.toLinearMap
  have hangle : sinTwoThetaEmbedding U X = sinTwoAngleOperator U V :=
    sinTwoThetaEmbedding_eq_rangeAngle U X hX
  calc
    d * ‖sinTwoThetaEmbedding U X‖
        = d * ‖sinTwoAngleOperator U V‖ := by rw [hangle]
    _ ≤ ‖reflectionDefect V A‖ :=
      sinTwoTheta_reflectionDefect hA hU hd hfinite
    _ ≤ 2 * ‖residual A X M‖ :=
      reflectionDefect_range_le_residual hA X hX hM

/-- Perturbation form of the `sin 2Θ` theorem. -/
theorem sinTwoTheta_perturbation
    {A B : E →L[𝕜] E} (hA : IsSelfAdjointOperator A)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ 2 * ‖B - A‖ := by
  calc
    d * ‖sinTwoAngleOperator U V‖ ≤ ‖reflectionDefect V A‖ :=
      sinTwoTheta_reflectionDefect hA hU hd hfinite
    _ ≤ 2 * ‖A-B‖ := norm_reflectionDefect_le_two_mul A B V hV
    _ = 2 * ‖B-A‖ := by rw [norm_sub_rev]

/-- General spectral-separation `sin 2Θ` theorem. -/
theorem sinTwoTheta_generalSeparation
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d) (hgap : InternalGap A U d) :
    d * ‖sinTwoAngleOperator U V‖ ≤ Real.pi * ‖B - A‖ := by
  let A' := reflectionOperator V ∘L A ∘L reflectionOperator V
  let U' := reflectedSubspace V U
  have hA' : IsSelfAdjointOperator A' :=
    hA.unitary_conjugate (reflectionOperator_unitary V)
  have hU' : Reduces A' U' := reduces_reflectedSubspace hU
  have hhybrid : HybridGap A A' U U' d :=
    internalGap_reflection_transport hgap
  have hsin := sinTheta_generalSeparation hA hA' hU hU' hd hhybrid
  have hdefect := norm_reflectionDefect_le_two_mul A B V hV
  calc
    d * ‖sinTwoAngleOperator U V‖
        = d * directedGap U U' :=
          doubleAngle_directedGap_identity U V
    _ ≤ (Real.pi/2) * ‖A'-A‖ := hsin
    _ = (Real.pi/2) * ‖reflectionDefect V A‖ := rfl
    _ ≤ (Real.pi/2) * (2 * ‖B-A‖) := by gcongr
    _ = Real.pi * ‖B-A‖ := by ring

/-- Ideal-norm `sin 2Θ` theorem. -/
theorem ideal_sinTwoTheta
    (I : SymmetricNormIdeal (𝕜 := 𝕜) (E := E))
    {A B : E →L[𝕜] E}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : Reduces A U) (hV : Reduces B V)
    {d : ℝ} (hd : 0 < d)
    (hfinite : FiniteGapConfiguration A U d)
    (hmem : I.mem (B - A)) :
    I.mem (sinTwoAngleOperator U V) ∧
      d * I.gauge (sinTwoAngleOperator U V) ≤ 2 * I.gauge (B - A) := by
  let A' := reflectionOperator V ∘L A ∘L reflectionOperator V
  let U' := reflectedSubspace V U
  have hA' : IsSelfAdjointOperator A' :=
    hA.unitary_conjugate (reflectionOperator_unitary V)
  have hU' : Reduces A' U' := reduces_reflectedSubspace hU
  obtain ⟨l, r, l', r', hUU', hU'U⟩ :=
    finiteGap_mixedIntervalExterior hfinite
      (finiteGap_reflected (V := V) hfinite)
  have hdefMem : I.mem (A'-A) := by
    rw [show A'-A = reflectionDefect V A by rfl,
      reflectionDefect_eq_perturbationDefect A B V hV]
    exact I.add_mem
      (I.ideal_mem (reflectionOperator V) (reflectionOperator V) hmem)
      (by simpa using I.smul_mem (-1 : 𝕜) hmem)
  have hsin := ideal_sinTheta I hA hA' hU hU' hd hUU' hU'U hdefMem
  have hdefGauge : I.gauge (A'-A) ≤ 2 * I.gauge (B-A) := by
    rw [show A'-A = reflectionDefect V A by rfl,
      reflectionDefect_eq_perturbationDefect A B V hV]
    have hconj := I.unitary_invariant
      (reflectionOperator V) (reflectionOperator V) (A-B)
      (reflectionOperator_unitary V) (reflectionOperator_unitary V)
      (reflectionOperator_involutive V) (reflectionOperator_involutive V)
      (by simpa using hmem)
    have htri := I.triangle
      (I.ideal_mem (reflectionOperator V) (reflectionOperator V)
        (by simpa using hmem))
      (by simpa using I.smul_mem (-1 : 𝕜) (by simpa using hmem))
    simpa [hconj, I.gauge_smul] using htri
  have hangle : I.gauge (sinAngleOperator U U') =
      I.gauge (sinTwoAngleOperator U V) := by
    rw [sinAngle_reflected_eq_sinTwoAngle]
  exact ⟨by simpa [sinAngle_reflected_eq_sinTwoAngle] using hsin.1,
    by rw [← hangle]; exact hsin.2.trans hdefGauge⟩

end DavisKahanExt
end ForMathlib
