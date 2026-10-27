/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.CharbonnierCanonicalTrace
public import DavisKahan.Geometry.Polar.CanonicalCutoffTail

/-! # The exact Charbonnier minimum on infinite subcritical tails -/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition

open FiniteDimensional.SmoothedPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance comapSubtypeProjection
    (K N : Submodule ℂ E) [K.HasOrthogonalProjection] [CompleteSpace N] :
    (K.comap N.subtype).HasOrthogonalProjection :=
  K.hasOrthogonalProjection_comap_subtype_of_complete N

/-- Removing any positive subcritical sine cutoff leaves the exact
intrinsic smoothed minimum on the whole infinite complementary pair.
The equality includes divergent costs and the closed critical cutoff. -/
theorem charbonnier_canonical_cutoff_tail_eq_minimum_sum
    (tau : ℝ) (hτ : 0 < tau)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E))
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (smoothedCriticalAngle tau)) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    (Mᗮ.orthogonalProjectionOnto ∘L (1 - nonacuteDirectRotation K L J) ∘L
      Mᗮ.subtypeL).charbonnierCost tau =
      ∑' j, ENNReal.ofReal (smoothedPhaseMinimum tau
        (Real.arcsin (((K.comap Mᗮ.subtype).sinThetaMap
          (L.comap Mᗮ.subtype)).singularValue j : ℝ))) := by
  dsimp only
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  obtain ⟨hM, hK, hL, _⟩ := finite_sine_spectral_cutoff K L hD c hc
  let : FiniteDimensional ℂ M := hM
  let K₀ := K.comap Mᗮ.subtype
  let L₀ := L.comap Mᗮ.subtype
  obtain ⟨V, hV, _, hcanonical, hgap⟩ :=
    exists_canonical_tail_of_finite_sine_cutoff K L J hD c hc hc1
  have hacute : IsUniformlyAcute K₀ L₀ := hgap.trans_lt hc1
  have hz := halmosSourceDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute
  have hz' := halmosTargetDefect_eq_bot_of_isUniformlyAcute K₀ L₀ hacute
  let J₀ := LinearIsometryEquiv.ofEq _ _ (hz.trans hz'.symm)
  have hVe : (V : Mᗮ →L[ℂ] Mᗮ) = nonacuteDirectRotation K₀ L₀ J₀ :=
    hcanonical.trans (nonacuteDirectRotation_eq_canonicalPolarFactor_of_acute K₀ L₀ J₀ hz hz').symm
  have hD₀ : IsCompactOperator ((K₀.starProjection - L₀.starProjection) : Mᗮ →L[ℂ] Mᗮ) := by
    rw [K.projection_sub_comap_subtype_eq_compression_of_invariant L Mᗮ
      hK.orthogonal_mem_invtSubmodule hL.orthogonal_mem_invtSubmodule]
    exact (hD.comp_clm Mᗮ.subtypeL).clm_comp Mᗮ.orthogonalProjectionOnto
  have hdisp : Mᗮ.orthogonalProjectionOnto ∘L
      (1 - nonacuteDirectRotation K L J) ∘L Mᗮ.subtypeL = 1 - (V : Mᗮ →L[ℂ] Mᗮ) := by
    apply ContinuousLinearMap.ext
    intro x
    change Mᗮ.orthogonalProjectionOnto ((x : E) - nonacuteDirectRotation K L J x) = x - V x
    rw [map_sub, ← hV, Mᗮ.orthogonalProjectionOnto_mem_subspace_eq_self,
      Mᗮ.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [hdisp, hVe]
  exact charbonnier_nonacuteDirectRotation_eq_minimum_sum_of_subcritical tau hτ
    K₀ L₀ J₀ hD₀ (hgap.trans hcrit)

end TauCeti.DavisKahan.InfiniteDimensional.SmoothedPhaseTransition
