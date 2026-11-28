/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ProjValMeasure.Bounded

/-!
# The spectral measure of an unbounded self-adjoint operator: bounded sets

The native spectral-cut graph and norm laws give domain inclusion and
the centered norm estimate for vectors in a bounded spectral range.

The original DKPS spectral measure followed the Cayley route of Rudin and
Reed–Simon. The contribution census preserves that provenance.
-/

public section

open scoped InnerProductSpace
open MeasureTheory

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section BoundedSet

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

variable (B : Set ℝ) (hB : MeasurableSet B)

/-- A bounded spectral range lies inside the operator domain. -/
theorem mem_domain_of_mem_specRange_of_bounded {M : ℝ} (hbnd : ∀ s ∈ B, |s| ≤ M)
    {x : H} (hx : x ∈ ((A.spectralPVM hA).proj B hB).range) : x ∈ A.domain := by
  have hM : 0 ≤ max 0 M := le_max_left _ _
  have hcut := hA.mem_graph_spectralCut B hB 0 (max 0 M) hM
    (fun s hs => by simpa only [sub_zero] using (hbnd s hs).trans (le_max_right _ _)) x
  have hfix := Submodule.starProjection_eq_self_iff.mpr hx
  rw [ProjValMeasure.starProjection_range_proj] at hfix
  rw [hfix] at hcut
  exact _root_.LinearPMap.mem_domain_of_mem_graph hcut

/-- On a bounded spectral range, the operator differs from its center by the spectral radius. -/
theorem norm_sub_smul_le_of_mem_specRange {M c r : ℝ} (_hbnd : ∀ s ∈ B, |s| ≤ M)
    (hr : 0 ≤ r) (hcr : ∀ s ∈ B, |s - c| ≤ r) {x : H}
    (hx : x ∈ ((A.spectralPVM hA).proj B hB).range)
    (hmem : x ∈ A.domain) :
    ‖A ⟨x, hmem⟩ - (c : ℂ) • x‖ ≤ r * ‖x‖ := by
  have hcut := hA.mem_graph_spectralCut B hB c r hr hcr x
  have hfix := Submodule.starProjection_eq_self_iff.mpr hx
  rw [ProjValMeasure.starProjection_range_proj] at hfix
  rw [hfix] at hcut
  have hact := A.mem_graph_snd_inj (A.mem_graph ⟨x, hmem⟩) hcut rfl
  rw [hact, add_sub_cancel_right]
  exact (A.spectralCut hA B hB c r hr hcr).le_of_opNorm_le
    (hA.norm_spectralCut_le B hB c r hr hcr) x

end BoundedSet

end LinearPMap
end TauCeti
