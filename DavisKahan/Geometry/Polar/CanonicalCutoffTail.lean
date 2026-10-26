/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.CanonicalRestriction
public import DavisKahan.Geometry.Polar.FiniteSpectralCutoff

/-!
# The actual canonical tail after a finite sine cutoff

Removing the sine spectral sector above `0 < c < 1` leaves an actual
uniformly acute restricted projection pair, of gap at most `c`. The
ambient completed rotation restricts to its canonical polar unitary.
The tail may have infinite rank and nonseparable fixed directions.

This discharges the geometric restriction obligation in infinite-rank
Schatten optimization. Exact objective identification on a subcritical
tail remains a separate spectral trace theorem.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

local instance comapSubtypeProjection
    (K N : Submodule 𝕜 E) [K.HasOrthogonalProjection] [CompleteSpace N] :
    (K.comap N.subtype).HasOrthogonalProjection :=
  K.hasOrthogonalProjection_comap_subtype_of_complete N

/-- **Canonical infinite tail after a finite spectral cutoff.** Its
actual projection gap is at most the cutoff, and its actual unitary
restriction is the canonical polar rotation. Both fields are included. -/
theorem exists_canonical_tail_of_finite_sine_cutoff
    (K L : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[𝕜] halmosTargetDefect K L)
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : E →L[𝕜] E))
    (c : ℝ) (hc : 0 < c) (hc1 : c < 1) :
    let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
    ∃ V : Mᗮ ≃ₗᵢ[𝕜] Mᗮ,
      (∀ x : Mᗮ, (V x : E) = nonacuteDirectRotation K L J x) ∧
      (∀ x : Mᗮ, (V.symm x : E) = star (nonacuteDirectRotation K L J) x) ∧
      (V : Mᗮ →L[𝕜] Mᗮ) =
        spectraCanonicalPolarFactor (K.comap Mᗮ.subtype) (L.comap Mᗮ.subtype) ∧
      (K.comap Mᗮ.subtype).projectionGap (L.comap Mᗮ.subtype) ≤ c := by
  let M := eigenSpan (K.sinAngleOperator L) (Set.Ioi c)
  obtain ⟨hM, hK, hL, htail⟩ := finite_sine_spectral_cutoff K L hD c hc
  let : FiniteDimensional 𝕜 M := hM
  have hgap : (K.comap Mᗮ.subtype).projectionGap (L.comap Mᗮ.subtype) ≤ c :=
    (K.projectionGap_comap_subtype_le_norm_projection_sub_comp L Mᗮ
      hK.orthogonal_mem_invtSubmodule hL.orthogonal_mem_invtSubmodule).trans htail
  have hacute : IsUniformlyAcute (K.comap Mᗮ.subtype) (L.comap Mᗮ.subtype) :=
    hgap.trans_lt hc1
  have hzero := halmosSourceDefect_eq_bot_of_isUniformlyAcute _ _ hacute
  have hzero' := halmosTargetDefect_eq_bot_of_isUniformlyAcute _ _ hacute
  have hred : Mᗮ.IsReducing (nonacuteDirectRotation K L J).toLinearMap :=
    (Submodule.isReducing_orthogonal_iff M _).mpr
      (sine_spectral_cutoff_isReducing_nonacuteDirectRotation K L J hD c hc)
  obtain ⟨V, hV, hVs, hcanonical⟩ := exists_canonical_restriction_of_acute_reducing_pair
    K L Mᗮ J hred hK.orthogonal_mem_invtSubmodule hzero hzero'
  exact ⟨V, hV, hVs, hcanonical, hgap⟩

end TauCeti.DavisKahan
