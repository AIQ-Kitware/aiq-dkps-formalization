/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.ApproximationBlockSum
import DavisKahan.Experimental.InfiniteDimensional.SinTheta.PaperProjectionBlocks

/-!
# Davis--Kahan Lemma 6.1

This is the source-faithful infinite-dimensional form of Lemma 6.1.  The two
summands occupy mutually orthogonal initial and final blocks.  Separate weak
majorization of the blocks therefore combines into weak majorization of their
sum.  The converse follows when the two blocks on each side have matching
singular values, exactly as stated in the paper.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A bounded operator occupying one prescribed projection block. -/
def paperProjectionBlock
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K : E →L[ℂ] E) : E →L[ℂ] E :=
  Ω.starProjection ∘L K ∘L Γ.starProjection

/-- The two complementary blocks are unitarily equivalent to their Hilbert
orthogonal block sum. -/
theorem paperProjectionBlockPair_same_blockSum
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K L : E →L[ℂ] E) :
    SameApproximationSingularValues
      (paperProjectionBlock Ω Γ K + paperProjectionBlock Ωᗮ Γᗮ L)
      (continuousOrthogonalBlockSum
        (Ω.starProjection ∘L K ∘L Γ.starProjection)
        (Ωᗮ.starProjection ∘L L ∘L Γᗮ.starProjection)) := by
  let Udom := Γ.orthogonalDecompositionContinuousLinearEquiv
  let Ucod := Ω.orthogonalDecompositionContinuousLinearEquiv
  have hfactor :
      (Ucod : E →L[ℂ] WithLp 2 (Ω × Ωᗮ)) ∘L
          (paperProjectionBlock Ω Γ K + paperProjectionBlock Ωᗮ Γᗮ L) ∘L
          (Udom.symm : WithLp 2 (Γ × Γᗮ) →L[ℂ] E) =
        continuousOrthogonalBlockSum
          (Ω.subtypeL.adjoint ∘L K ∘L Γ.subtypeL)
          (Ωᗮ.subtypeL.adjoint ∘L L ∘L Γᗮ.subtypeL) := by
    ext x
    apply WithLp.ofLp_injective 2
    simp [paperProjectionBlock, Udom, Ucod,
      Submodule.orthogonalDecompositionContinuousLinearEquiv]
  exact SameApproximationSingularValues.of_isometricEquiv_comp
    Ucod Udom hfactor

/-- **Davis--Kahan 1970, Lemma 6.1, forward direction.** -/
theorem paperLemma61_all_kyFan
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℂ] E)
    (h₀ : ∀ k,
      kyFanApproximationGauge k (paperProjectionBlock Ω Γ K) ≤
        kyFanApproximationGauge k (paperProjectionBlock Ω Γ L))
    (h₁ : ∀ k,
      kyFanApproximationGauge k (paperProjectionBlock Ωᗮ Γᗮ Ktilde) ≤
        kyFanApproximationGauge k (paperProjectionBlock Ωᗮ Γᗮ Ltilde)) :
    ∀ k,
      kyFanApproximationGauge k
          (paperProjectionBlock Ω Γ K +
            paperProjectionBlock Ωᗮ Γᗮ Ktilde) ≤
        kyFanApproximationGauge k
          (paperProjectionBlock Ω Γ L +
            paperProjectionBlock Ωᗮ Γᗮ Ltilde) := by
  intro k
  let hleft := paperProjectionBlockPair_same_blockSum Ω Γ K Ktilde
  let hright := paperProjectionBlockPair_same_blockSum Ω Γ L Ltilde
  rw [hleft.kyFanApproximationGauge_eq k,
    hright.kyFanApproximationGauge_eq k]
  exact kyFanApproximationGauge_blockSum_le h₀ h₁ k

/-- Lemma 6.1 for every source-defined unitarily invariant norm. -/
theorem paperLemma61_every_unitarilyInvariantNorm
    (N : PaperUnitaryInvariantNorm)
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℂ] E)
    (h₀ : ∀ k,
      kyFanApproximationGauge k (paperProjectionBlock Ω Γ K) ≤
        kyFanApproximationGauge k (paperProjectionBlock Ω Γ L))
    (h₁ : ∀ k,
      kyFanApproximationGauge k (paperProjectionBlock Ωᗮ Γᗮ Ktilde) ≤
        kyFanApproximationGauge k (paperProjectionBlock Ωᗮ Γᗮ Ltilde)) :
    N.extendedGauge
        (paperProjectionBlock Ω Γ K +
          paperProjectionBlock Ωᗮ Γᗮ Ktilde) ≤
      N.extendedGauge
        (paperProjectionBlock Ω Γ L +
          paperProjectionBlock Ωᗮ Γᗮ Ltilde) :=
  N.extendedGauge_le_of_all_kyFan_le
    (paperLemma61_all_kyFan Ω Γ K Ktilde L Ltilde h₀ h₁)

/-- The converse in Lemma 6.1 under the source paper's matching-singular-value
hypotheses. -/
theorem paperLemma61_converse
    (Ω Γ : Submodule ℂ E)
    [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]
    (K Ktilde L Ltilde : E →L[ℂ] E)
    (hK : SameApproximationSingularValues
      (paperProjectionBlock Ω Γ K)
      (paperProjectionBlock Ωᗮ Γᗮ Ktilde))
    (hL : SameApproximationSingularValues
      (paperProjectionBlock Ω Γ L)
      (paperProjectionBlock Ωᗮ Γᗮ Ltilde))
    (hsum : ∀ k,
      kyFanApproximationGauge k
          (paperProjectionBlock Ω Γ K +
            paperProjectionBlock Ωᗮ Γᗮ Ktilde) ≤
        kyFanApproximationGauge k
          (paperProjectionBlock Ω Γ L +
            paperProjectionBlock Ωᗮ Γᗮ Ltilde)) :
    ∀ k,
      kyFanApproximationGauge k (paperProjectionBlock Ω Γ K) ≤
        kyFanApproximationGauge k (paperProjectionBlock Ω Γ L) := by
  intro k
  have hdoubleK := paperLemma61_all_kyFan Ω Γ K Ktilde K Ktilde
    (fun j => le_rfl) (fun j => le_rfl) (2 * k)
  have hmergeK := paperProjectionBlockPair_same_blockSum Ω Γ K Ktilde
  have hmergeL := paperProjectionBlockPair_same_blockSum Ω Γ L Ltilde
  have htwiceK :
      kyFanApproximationGauge (2 * k)
          (paperProjectionBlock Ω Γ K +
            paperProjectionBlock Ωᗮ Γᗮ Ktilde) =
        2 * kyFanApproximationGauge k (paperProjectionBlock Ω Γ K) := by
    rw [hmergeK.kyFanApproximationGauge_eq]
    exact kyFan_blockSum_equal_components hK k
  have htwiceL :
      kyFanApproximationGauge (2 * k)
          (paperProjectionBlock Ω Γ L +
            paperProjectionBlock Ωᗮ Γᗮ Ltilde) =
        2 * kyFanApproximationGauge k (paperProjectionBlock Ω Γ L) := by
    rw [hmergeL.kyFanApproximationGauge_eq]
    exact kyFan_blockSum_equal_components hL k
  have h := hsum (2 * k)
  rw [htwiceK, htwiceL] at h
  linarith

end

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
