/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperLemma61
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperOperatorAngleBridge
import DavisKahan.Experimental.InfiniteDimensional.Ideals.PaperSubspaceSingularTransport
import DavisKahan.Experimental.InfiniteDimensional.Core.ReducingRestrictionExtras
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.LegacyGapCompletion

/-!
# Davis--Kahan Proposition 6.1: the symmetric sine theorem

This module follows the paper proof exactly.

1. Apply the one-sided sine theorem to the selected block of `A` and the
   complementary block of `B`.
2. Apply it again with `A` and `B` interchanged.
3. Use Lemma 6.1 to combine the two orthogonal cross blocks sharply.
4. Use Lemma 6.2 to contract the two corresponding perturbation blocks by the
   norm of `H = B - A`.
5. Identify the cross-block sum with the literal functional-calculus
   `sin Theta`.

No triangle estimate is used in the coupling step.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

open ForMathlib.DavisKahanExt

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Exact bounded inputs of Proposition 6.1.  The two gap hypotheses are the
paper's two applications of the original sine theorem. -/
structure PaperSymmetricSinThetaProblem where
  A : E →L[ℂ] E
  B : E →L[ℂ] E
  selfAdjoint_A : A.IsSymmetric
  selfAdjoint_B : B.IsSymmetric
  U : Submodule ℂ E
  V : Submodule ℂ E
  proj_U : U.HasOrthogonalProjection
  proj_V : V.HasOrthogonalProjection
  reduces_A_U : A.Reduces U
  reduces_B_V : B.Reduces V
  gap : ℝ
  gap_pos : 0 < gap
  gap_U_to_Vperp : UnboundedSylvesterGap
    (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded A) U
      (ClosedOperator.ofBounded_reducesSubspace A U reduces_A_U))
    (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded B) Vᗮ
      (ClosedOperator.ofBounded_reducesSubspace B V reduces_B_V).orthogonal)
    gap
  gap_V_to_Uperp : UnboundedSylvesterGap
    (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded B) V
      (ClosedOperator.ofBounded_reducesSubspace B V reduces_B_V))
    (ClosedOperator.reducingRestriction (ClosedOperator.ofBounded A) Uᗮ
      (ClosedOperator.ofBounded_reducesSubspace A U reduces_A_U).orthogonal)
    gap

attribute [instance] PaperSymmetricSinThetaProblem.proj_U
attribute [instance] PaperSymmetricSinThetaProblem.proj_V

namespace PaperSymmetricSinThetaProblem

/-- The perturbation `H` of the paper. -/
def perturbation (P : PaperSymmetricSinThetaProblem (E := E)) : E →L[ℂ] E :=
  P.B - P.A

/-- Internal data for the first directed application. -/
noncomputable def forwardData
    (P : PaperSymmetricSinThetaProblem (E := E)) :
    UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := P.U) (G := P.Vᗮ) where
  A := ClosedOperator.ofBounded P.B
  A₀ := ClosedOperator.reducingRestriction (ClosedOperator.ofBounded P.A) P.U
    (ClosedOperator.ofBounded_reducesSubspace P.A P.U P.reduces_A_U)
  Λ₁ := ClosedOperator.reducingRestriction (ClosedOperator.ofBounded P.B) P.Vᗮ
    (ClosedOperator.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal
  X := P.U.subtypeL
  F₁ := P.Vᗮ.subtypeL
  residual := P.perturbation ∘L P.U.subtypeL
  X_maps_domain := by intro x; simp
  F₁_maps_domain := by intro x; simp
  residual_eq := by
    intro x
    apply Subtype.ext
    simp [perturbation, ContinuousLinearMap.comp_apply,
      ClosedOperator.reducingRestriction_ofBounded_apply]
  intertwines :=
    ClosedOperator.reducingRestriction_inclusion_intertwines
      (ClosedOperator.ofBounded P.B) P.Vᗮ
      (ClosedOperator.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal

/-- Internal data for the reversed application. -/
noncomputable def reverseData
    (P : PaperSymmetricSinThetaProblem (E := E)) :
    UnboundedSinThetaData (𝕜 := ℂ) (E := E) (F := P.V) (G := P.Uᗮ) where
  A := ClosedOperator.ofBounded P.A
  A₀ := ClosedOperator.reducingRestriction (ClosedOperator.ofBounded P.B) P.V
    (ClosedOperator.ofBounded_reducesSubspace P.B P.V P.reduces_B_V)
  Λ₁ := ClosedOperator.reducingRestriction (ClosedOperator.ofBounded P.A) P.Uᗮ
    (ClosedOperator.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal
  X := P.V.subtypeL
  F₁ := P.Uᗮ.subtypeL
  residual := (-P.perturbation) ∘L P.V.subtypeL
  X_maps_domain := by intro x; simp
  F₁_maps_domain := by intro x; simp
  residual_eq := by
    intro x
    apply Subtype.ext
    simp [perturbation, ContinuousLinearMap.comp_apply,
      ClosedOperator.reducingRestriction_ofBounded_apply]
  intertwines :=
    ClosedOperator.reducingRestriction_inclusion_intertwines
      (ClosedOperator.ofBounded P.A) P.Uᗮ
      (ClosedOperator.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal

/-- The first exact cross-projection block. -/
def forwardSineBlock (P : PaperSymmetricSinThetaProblem (E := E)) :
    E →L[ℂ] E :=
  P.Vᗮ.starProjection ∘L P.U.starProjection

/-- The reversed exact cross-projection block. -/
def reverseSineBlock (P : PaperSymmetricSinThetaProblem (E := E)) :
    E →L[ℂ] E :=
  P.Uᗮ.starProjection ∘L P.V.starProjection

/-- The first projected perturbation block from the proof of Proposition 6.1. -/
def forwardResidualBlock (P : PaperSymmetricSinThetaProblem (E := E)) :
    E →L[ℂ] E :=
  P.Vᗮ.starProjection ∘L P.perturbation ∘L P.U.starProjection

/-- The second projected perturbation block. -/
def reverseResidualBlock (P : PaperSymmetricSinThetaProblem (E := E)) :
    E →L[ℂ] E :=
  P.V.starProjection ∘L P.perturbation ∘L P.Uᗮ.starProjection

/-- First one-sided estimate simultaneously for every finite Ky Fan gauge. -/
theorem forward_all_kyFan
    (P : PaperSymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.forwardSineBlock ≤
        kyFanApproximationGauge k P.forwardResidualBlock := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    let N := KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk
    let D := P.forwardData
    have hA0 : D.A₀.IsSelfAdjoint :=
      ClosedOperator.reducingRestriction_isSelfAdjoint
        (ClosedOperator.ofBounded P.A) P.U
        (ClosedOperator.ofBounded_reducesSubspace P.A P.U P.reduces_A_U)
        (ClosedOperator.ofBounded_isSelfAdjoint P.A P.selfAdjoint_A)
    have hL : D.Λ₁.IsSelfAdjoint :=
      ClosedOperator.reducingRestriction_isSelfAdjoint
        (ClosedOperator.ofBounded P.B) P.Vᗮ
        (ClosedOperator.ofBounded_reducesSubspace P.B P.V P.reduces_B_V).orthogonal
        (ClosedOperator.ofBounded_isSelfAdjoint P.B P.selfAdjoint_B)
    have hEq := unbounded_adjoint_residual_block_identity D
      (ClosedOperator.ofBounded_isSelfAdjoint P.B P.selfAdjoint_B) hA0 hL
    have hraw := davisKahan1970_sylvester_complex N hA0 hL P.gap_pos
      P.gap_U_to_Vperp hEq
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hk
        (-(D.residual.adjoint ∘L D.F₁)))
    have hsine : SameApproximationSingularValues
        P.forwardSineBlock (D.X.adjoint ∘L D.F₁) := by
      simpa [D, forwardData, forwardSineBlock,
        Submodule.adjoint_subtypeL] using
        (sameApproximationSingularValues_ambientSubspaceBlock
          P.U P.Vᗮ (D.X.adjoint ∘L D.F₁)).symm
    have hres : SameApproximationSingularValues
        P.forwardResidualBlock (-(D.residual.adjoint ∘L D.F₁)) := by
      have hadj : SameApproximationSingularValues
          P.forwardResidualBlock.adjoint P.forwardResidualBlock :=
        fun n => approximationSingularValue_adjoint _ n
      simpa [D, forwardData, forwardResidualBlock, perturbation,
        Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_sub, map_neg] using hadj.symm
    simpa [N, KyFanDominantIdealFamily.kyFan_gauge,
      hsine.kyFanApproximationGauge_eq k,
      hres.kyFanApproximationGauge_eq k] using hraw.2

/-- Reversed one-sided estimate simultaneously for every finite Ky Fan gauge. -/
theorem reverse_all_kyFan
    (P : PaperSymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k P.reverseSineBlock ≤
        kyFanApproximationGauge k P.reverseResidualBlock := by
  intro k
  by_cases hk0 : k = 0
  · subst k
    simp [kyFanApproximationGauge]
  · have hk : 0 < k := Nat.pos_of_ne_zero hk0
    let N := KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k hk
    let D := P.reverseData
    have hA0 : D.A₀.IsSelfAdjoint :=
      ClosedOperator.reducingRestriction_isSelfAdjoint
        (ClosedOperator.ofBounded P.B) P.V
        (ClosedOperator.ofBounded_reducesSubspace P.B P.V P.reduces_B_V)
        (ClosedOperator.ofBounded_isSelfAdjoint P.B P.selfAdjoint_B)
    have hL : D.Λ₁.IsSelfAdjoint :=
      ClosedOperator.reducingRestriction_isSelfAdjoint
        (ClosedOperator.ofBounded P.A) P.Uᗮ
        (ClosedOperator.ofBounded_reducesSubspace P.A P.U P.reduces_A_U).orthogonal
        (ClosedOperator.ofBounded_isSelfAdjoint P.A P.selfAdjoint_A)
    have hEq := unbounded_adjoint_residual_block_identity D
      (ClosedOperator.ofBounded_isSelfAdjoint P.A P.selfAdjoint_A) hA0 hL
    have hraw := davisKahan1970_sylvester_complex N hA0 hL P.gap_pos
      P.gap_V_to_Uperp hEq
      (KyFanDominantIdealFamily.kyFan_mem (𝕜 := ℂ) k hk
        (-(D.residual.adjoint ∘L D.F₁)))
    have hsine : SameApproximationSingularValues
        P.reverseSineBlock (D.X.adjoint ∘L D.F₁) := by
      simpa [D, reverseData, reverseSineBlock,
        Submodule.adjoint_subtypeL] using
        (sameApproximationSingularValues_ambientSubspaceBlock
          P.V P.Uᗮ (D.X.adjoint ∘L D.F₁)).symm
    have hres : SameApproximationSingularValues
        P.reverseResidualBlock (-(D.residual.adjoint ∘L D.F₁)) := by
      have hadj : SameApproximationSingularValues
          P.reverseResidualBlock.adjoint P.reverseResidualBlock :=
        fun n => approximationSingularValue_adjoint _ n
      simpa [D, reverseData, reverseResidualBlock, perturbation,
        Submodule.adjoint_subtypeL, ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_sub, map_neg] using hadj.symm
    simpa [N, KyFanDominantIdealFamily.kyFan_gauge,
      hsine.kyFanApproximationGauge_eq k,
      hres.kyFanApproximationGauge_eq k] using hraw.2

/-- Ky Fan form of the symmetric sine theorem, before universal Fan
 dominance. -/
theorem symmetric_all_kyFan
    (P : PaperSymmetricSinThetaProblem (E := E)) :
    ∀ k,
      P.gap * kyFanApproximationGauge k
          (ForMathlib.DavisKahanExt.paperSinAngleOperatorC P.U P.V) ≤
        kyFanApproximationGauge k P.perturbation := by
  intro k
  have hcombine := paperLemma61_all_kyFan P.Vᗮ P.U
    (P.gap • P.perturbation) (P.gap • P.perturbation)
    P.perturbation P.perturbation
    (fun j => by
      simpa [paperProjectionBlock, forwardSineBlock, forwardResidualBlock,
        kyFanApproximationGauge_smul, abs_of_pos P.gap_pos] using
        P.forward_all_kyFan j)
    (fun j => by
      simpa [paperProjectionBlock, reverseSineBlock, reverseResidualBlock,
        kyFanApproximationGauge_smul, abs_of_pos P.gap_pos] using
        P.reverse_all_kyFan j) k
  have hsine := paperCrossSineSum_same_literalSin P.U P.V
  have hres := paperDiagonalPair_all_kyFan_le P.Vᗮ P.U P.perturbation k
  calc
    P.gap * kyFanApproximationGauge k
        (ForMathlib.DavisKahanExt.paperSinAngleOperatorC P.U P.V) =
      kyFanApproximationGauge k
        (P.gap • paperCrossSineSum P.U P.V) := by
      rw [kyFanApproximationGauge_smul, abs_of_pos P.gap_pos,
        hsine.kyFanApproximationGauge_eq]
    _ ≤ kyFanApproximationGauge k
        (paperDiagonalPair P.Vᗮ P.U P.perturbation) := hcombine
    _ ≤ kyFanApproximationGauge k P.perturbation := hres

/-- **Davis--Kahan 1970, Proposition 6.1**, for every normalized unitarily
invariant norm in the source sense. -/
theorem result_every_unitarilyInvariantNorm
    (P : PaperSymmetricSinThetaProblem (E := E))
    (N : PaperUnitaryInvariantNorm) (hH : N.Mem P.perturbation) :
    N.Mem (ForMathlib.DavisKahanExt.paperSinAngleOperatorC P.U P.V) ∧
      P.gap * N.gauge
          (ForMathlib.DavisKahanExt.paperSinAngleOperatorC P.U P.V) ≤
        N.gauge P.perturbation :=
  N.mul_gauge_le_of_all_mul_kyFan_le P.gap_pos hH P.symmetric_all_kyFan

end PaperSymmetricSinThetaProblem

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
