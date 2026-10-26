/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Halmos.CrossedDefectGap
public import TauCeti.Analysis.Normed.Operator.Compact.Eigenspace

/-!
# Finite crossed defects of a compact projection perturbation

The crossed defects embed in the `+1` and `-1` eigenspaces of the compact
projection difference. They are therefore finite-dimensional even when
the two subspaces have infinite rank and corank. Consequently their
finite-dimensional balance supplies the actual isometric identification
needed for a completed direct rotation.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Compactness of the projection difference forces both crossed
defects to be finite-dimensional, in arbitrary ambient dimension. -/
theorem finiteDimensional_crossedDefects_of_compact_projection_sub
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : H →L[𝕜] H)) :
    FiniteDimensional 𝕜 (halmosSourceDefect K L) ∧
      FiniteDimensional 𝕜 (halmosTargetDefect K L) := by
  let D := (K.starProjection - L.starProjection).toLinearMap
  have hsource : halmosSourceDefect K L ≤ Module.End.eigenspace D 1 := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff]
    change K.starProjection x - L.starProjection x = (1 : 𝕜) • x
    rw [K.starProjection_eq_self_iff.mpr hx.1,
      L.starProjection_apply_eq_zero_iff.mpr hx.2, sub_zero, one_smul]
  have htarget : halmosTargetDefect K L ≤ Module.End.eigenspace D (-1) := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff]
    change K.starProjection x - L.starProjection x = (-1 : 𝕜) • x
    rw [K.starProjection_apply_eq_zero_iff.mpr hx.1,
      L.starProjection_eq_self_iff.mpr hx.2, zero_sub, neg_one_smul]
  let : FiniteDimensional 𝕜 (Module.End.eigenspace D 1) :=
    hD.finiteDimensional_eigenspace one_ne_zero
  let : FiniteDimensional 𝕜 (Module.End.eigenspace D (-1)) :=
    hD.finiteDimensional_eigenspace (μ := (-1 : 𝕜)) (by simp)
  exact ⟨Submodule.finiteDimensional_of_le hsource, Submodule.finiteDimensional_of_le htarget⟩

/-- For compact projection difference, equality of the finite crossed
dimensions supplies their isometric identification. -/
theorem crossedDefectsEquivalent_of_compact_projection_sub_of_finrank_eq [CompleteSpace H]
    (K L : Submodule 𝕜 H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (hD : IsCompactOperator ((K.starProjection - L.starProjection) : H →L[𝕜] H))
    (hbalance : Module.finrank 𝕜 (halmosSourceDefect K L) =
      Module.finrank 𝕜 (halmosTargetDefect K L)) : CrossedDefectsEquivalent K L := by
  obtain ⟨hsource, htarget⟩ := finiteDimensional_crossedDefects_of_compact_projection_sub K L hD
  let : FiniteDimensional 𝕜 (halmosSourceDefect K L) := hsource
  let : FiniteDimensional 𝕜 (halmosTargetDefect K L) := htarget
  exact (crossedDefectsEquivalent_iff_finrank_eq K L).mpr hbalance

end TauCeti.DavisKahan
