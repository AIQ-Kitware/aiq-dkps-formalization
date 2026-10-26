/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCanonicalTrace
public import DavisKahan.Geometry.Polar.CanonicalCutoffTail

/-!
# The exact Schatten minimum on subcritical infinite tails

Below and at the scalar critical angle, every canonical spectral cost
equals the exact scalar minimum. The canonical trace formula therefore
identifies the actual displacement cost on an infinite cutoff tail.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition

open FiniteDimensional.SchattenPhaseTransition
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance comapSubtypeProjection
    (K N : Submodule ℂ E) [K.HasOrthogonalProjection] [CompleteSpace N] :
    (K.comap N.subtype).HasOrthogonalProjection :=
  K.hasOrthogonalProjection_comap_subtype_of_complete N

/-- The canonical cost is the exact intrinsic phase minimum for a
compact uniformly acute pair whose directed gap is subcritical.
Equality at the critical threshold is included. -/
theorem schatten_nonacuteDirectRotation_rpow_eq_phaseMinimum_of_subcritical
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E))
    (hacute : IsUniformlyAcute K L)
    (hcut : K.directedProjectionGap L ≤ Real.sin (criticalAngle p.toReal)) :
    (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (1 - nonacuteDirectRotation K L J) ^ p.toReal =
      ∑' j, ENNReal.ofReal (phaseMinimum p.toReal
        (Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ))) := by
  rw [schatten_nonacuteDirectRotation_rpow_eq_canonical_sine_sum p hp hp1.le K L J hD hacute]
  apply tsum_congr
  intro j
  have hc := criticalAngle_mem p.toReal hp1 hp2
  have hs : ((K.sinThetaMap L).singularValue j : ℝ) ≤ Real.sin (criticalAngle p.toReal) := by
    calc
      _ ≤ ‖K.sinThetaMap L‖ := by
        exact_mod_cast (K.sinThetaMap L).singularValue_le_nnnorm j
      _ = K.directedProjectionGap L := K.norm_sinThetaMap L
      _ ≤ _ := hcut
  have hangle : Real.arcsin ((K.sinThetaMap L).singularValue j : ℝ) ≤ criticalAngle p.toReal := by
    calc
      _ ≤ Real.arcsin (Real.sin (criticalAngle p.toReal)) := Real.arcsin_le_arcsin hs
      _ = _ := Real.arcsin_sin (by linarith [hc.1, Real.pi_pos]) hc.2.le
  congr 1
  exact ((phaseMinimum_eq_canonical_iff_le_criticalAngle p.toReal _ hp1 hp2
    ⟨Real.arcsin_nonneg.mpr (NNReal.coe_nonneg _), Real.arcsin_le_pi_div_two _⟩).mpr hangle).symm

/-- **The actual infinite subcritical tail identity.** Removing the
finite sine sector above any positive subcritical cutoff leaves exactly
the intrinsic minimum phase cost on the complementary pair. No finite
rank or Schatten membership is required of the tail. -/
theorem schatten_canonical_cutoff_tail_rpow_eq_phaseMinimum_sum
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hp1 : 1 < p.toReal) (hp2 : p.toReal < 2)
    (K L : Submodule ℂ E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[ℂ] E))
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1)
    (hcrit : c ≤ Real.sin (criticalAngle p.toReal)) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    (OperatorIdealFamily.schatten ℂ p.toReal hp1.le).gauge
        (Mᗮ.orthogonalProjectionOnto ∘L (1 - nonacuteDirectRotation K L J) ∘L
          Mᗮ.subtypeL) ^ p.toReal =
      ∑' j, ENNReal.ofReal (phaseMinimum p.toReal
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
  exact schatten_nonacuteDirectRotation_rpow_eq_phaseMinimum_of_subcritical p hp hp1 hp2
    K₀ L₀ J₀ hD₀ hacute ((K₀.directedProjectionGap_le_projectionGap L₀).trans
      (hgap.trans hcrit))

end TauCeti.DavisKahan.InfiniteDimensional.SchattenPhaseTransition
