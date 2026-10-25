/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import DavisKahan.FiniteDimensional.DirectRotation.SmoothedGradientKernel
public import ForTauCeti.Analysis.InnerProductSpace.BalancedReflection

/-!
# Actual fixed and right-angle blocks on the zero-gradient kernel

Balance pairs the actual negative reflection space with its orthogonal
image under source reflection. The actual restricted transporter is
`(-I,I)` on these pairs and fixes the remaining space. Its literal cost
is the negative-space dimension times the maximal scalar displacement cost.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A balanced reflection has paired right-angle coordinates and a
fixed remainder, with exact literal Charbonnier cost. This theorem starts
from the prescribed reflection; the ambient kernel theorem constructs it. -/
theorem balanced_reflection_smoothed_paired_planes_complex
    (tau : ℝ) (htau : 0 ≤ tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (A : E →L[ℂ] E) (hA : IsStarProjection A)
    (hbalance : (2 : ℂ) • (A * K.starProjection * A) = A)
    (V : E ≃ₗᵢ[ℂ] E) (hV : (V : E →L[ℂ] E) = 1 - (2 : ℂ) • A) :
    ∃ (Z : Submodule ℂ E)
      (d : WithLp 2 (WithLp 2 (A.range × A.range) × Z) ≃ₗᵢ[ℂ] E)
      (J₀ : Z ≃ₗᵢ[ℂ] Z),
      Z = (A.range ⊔ A.range.map K.reflection.toLinearMap)ᗮ ∧
      (∀ x y : A.range, ⟪(x : E), K.reflection y⟫_ℂ = 0) ∧
      Function.Involutive J₀ ∧ (∀ z, (J₀ z : E) = K.reflection z) ∧
      (∀ x, d x = (x.fst.fst : E) + K.reflection x.fst.snd + (x.snd : E)) ∧
      (∀ x, V (d x) = d (WithLp.toLp 2
        (WithLp.toLp 2 (-x.fst.fst, x.fst.snd), x.snd))) ∧
      (∀ x, K.reflection (d x) = d (WithLp.toLp 2
        (WithLp.toLp 2 (x.fst.snd, x.fst.fst), J₀ x.snd))) ∧
      smoothedDisplacementCost tau V.toLinearMap =
        Module.finrank ℂ A.range * (Real.sqrt (tau ^ 2 + 4) - tau) := by
  obtain ⟨horth, J₀, hJ₀inv, hJ₀act, hVcoords, hJcoords⟩ :=
    balanced_reflection_paired_decomposition K A hA hbalance V hV
  let S := (pairedInvolutionEmbedding A.range K.reflection horth).toLinearMap.range
  let d : WithLp 2 (WithLp 2 (A.range × A.range) × Sᗮ) ≃ₗᵢ[ℂ] E :=
    pairedInvolutionDecomposition A.range K.reflection horth
  have hcost := smoothedDisplacementCost_paired_reflection_complex tau htau V d hVcoords
  refine ⟨Sᗮ, d, J₀, ?_, horth, hJ₀inv, hJ₀act, ?_, hVcoords, hJcoords, hcost⟩
  · dsimp only [S]
    rw [pairedInvolutionEmbedding_range]
  · exact pairedInvolutionDecomposition_apply A.range K.reflection horth

/-- Every actual local minimum has fixed and source-reflection-paired
right-angle coordinates on its actual zero-gradient kernel. Both ambient
actions are retained, and its cost counts the negative reflection space.
There is no prescribed kernel frame or excluded reflection phase. -/
theorem gradient_kernel_paired_planes_of_isLocalMinOn_transports_complex
    (tau : ℝ) (htau : 0 < tau)
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (Q : E →L[ℂ] E) (U : unitary (E →L[ℂ] E))
    (htrans : (U : E →L[ℂ] E) * K.starProjection * star (U : E →L[ℂ] E) = Q)
    (hmin : IsLocalMinOn
      (fun W : E →L[ℂ] E => smoothedDisplacementCost tau W.toLinearMap)
      {W | W ∈ unitary (E →L[ℂ] E) ∧ W * K.starProjection * star W = Q}
      (U : E →L[ℂ] E)) :
    let L := (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap.ker
    ∃ (V : L ≃ₗᵢ[ℂ] L) (A : L →L[ℂ] L) (K₀ Z : Submodule ℂ L)
      (d : WithLp 2 (WithLp 2 (A.range × A.range) × Z) ≃ₗᵢ[ℂ] L)
      (J₀ : Z ≃ₗᵢ[ℂ] Z),
      IsStarProjection A ∧
      (∀ x : L, (V x : E) = (U : E →L[ℂ] E) x) ∧
      (∀ x : L, (K₀.starProjection x : E) = K.starProjection x) ∧
      (V : L →L[ℂ] L) = 1 - (2 : ℂ) • A ∧
      Z = (A.range ⊔ A.range.map K₀.reflection.toLinearMap)ᗮ ∧
      (∀ x y : A.range, ⟪(x : L), K₀.reflection y⟫_ℂ = 0) ∧
      Function.Involutive J₀ ∧ (∀ z, (J₀ z : L) = K₀.reflection z) ∧
      (∀ x, d x = (x.fst.fst : L) + K₀.reflection x.fst.snd + (x.snd : L)) ∧
      (∀ x, V (d x) = d (WithLp.toLp 2
        (WithLp.toLp 2 (-x.fst.fst, x.fst.snd), x.snd))) ∧
      (∀ x, K₀.reflection (d x) = d (WithLp.toLp 2
        (WithLp.toLp 2 (x.fst.snd, x.fst.fst), J₀ x.snd))) ∧
      smoothedDisplacementCost tau V.toLinearMap =
        Module.finrank ℂ A.range * (Real.sqrt (tau ^ 2 + 4) - tau) := by
  let L := (smoothedUnitaryGradient tau (U : E →L[ℂ] E)).toLinearMap.ker
  obtain ⟨V, A, P₀, hA, hP₀, hVact, hP₀act, hV, hbalance, _⟩ :=
    gradient_kernel_local_reflection_restriction_complex tau htau K Q U htrans hmin
  let K₀ := P₀.range
  have hP₀eq : P₀ = K₀.starProjection :=
    (isStarProjection_iff_eq_starProjection_range.mp hP₀).choose_spec
  have hbalance' : (2 : ℂ) • (A * K₀.starProjection * A) = A := by
    rw [← hP₀eq]
    exact hbalance
  obtain ⟨Z, d, J₀, hZ, horth, hJ₀inv, hJ₀act, hd, hVcoords, hJcoords, hcost⟩ :=
    balanced_reflection_smoothed_paired_planes_complex tau htau.le K₀ A hA hbalance' V hV
  refine ⟨V, A, K₀, Z, d, J₀, hA, hVact, ?_, hV, hZ, horth,
    hJ₀inv, hJ₀act, hd, hVcoords, hJcoords, hcost⟩
  intro x
  rw [← hP₀eq]
  exact hP₀act x

end TauCeti.DavisKahan.FiniteDimensional.SmoothedPhaseTransition
