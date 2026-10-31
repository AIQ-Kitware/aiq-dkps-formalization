/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Spectral projections on the uniform real grid

The elementary real-grid geometry is now maintained in TauCeti (PR #18927):
`Real.gridCell`, `Real.measurableSet_gridCell`, `Real.pairwise_disjoint_gridCell`,
`Real.iUnion_gridCell`, and the two endpoint bounds. This module uses those
accepted definitions directly, without local aliases or duplicate proofs.

The remaining spectral-projection statements are genuinely unmerged donor
mathematics: the square-summability decomposition, its adjoint form, projection
idempotence, and existence of spectral points in nonzero measurable blocks.

## Provenance

The original Kitware/DKPS grid definitions and lemmas at this path were
adapted upstream in TauCeti PR #18927 (main commit `3bd7882f07072fe6918ca2a50175cbca678f07de`).
Pre-retirement DKPS source is preserved at `e4637c3919ae` and in
`dev/tauceti/extraction-manifest.json` / the contribution census.
-/

public section

namespace TauCeti
namespace LinearPMap

variable {ε : ℝ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- **The grid's spectral projections split norms.**  This is the hypothesis the
reassembly lemmas take, instantiated at the `ε`-grid. -/
theorem tsum_enorm_sq_specProjection_gridCell (hε : 0 < ε) (v : H) :
    ∑' k : ℤ, ‖specProjection hA (Real.gridCell ε k) (Real.measurableSet_gridCell ε k) v‖ₑ ^ 2
      = ‖v‖ₑ ^ 2 := by
  simp only [specProjection_def]
  exact (spectralPVM hA).tsum_enorm_sq_proj (Real.gridCell ε) (Real.measurableSet_gridCell ε)
    (Real.pairwise_disjoint_gridCell ε) (Real.iUnion_gridCell hε) v

/-- The same, for the adjoints — which is the form the *right*-hand reassembly
takes.  Spectral projections are self-adjoint, so it is the same statement. -/
theorem tsum_enorm_sq_adjoint_specProjection_gridCell (hε : 0 < ε) (v : H) :
    ∑' k : ℤ,
        ‖(specProjection hA (Real.gridCell ε k) (Real.measurableSet_gridCell ε k)).adjoint v‖ₑ ^ 2
      = ‖v‖ₑ ^ 2 := by
  have hsa : ∀ k : ℤ,
      (specProjection hA (Real.gridCell ε k) (Real.measurableSet_gridCell ε k)).adjoint
        = specProjection hA (Real.gridCell ε k) (Real.measurableSet_gridCell ε k) := fun k => by
    simp only [specProjection_def]
    exact ((spectralPVM hA).isSelfAdjoint_proj _ _).adjoint_eq
  simp_rw [hsa]
  exact tsum_enorm_sq_specProjection_gridCell hA hε v

/-- Spectral projections are idempotent, in the composition form the block
lemmas take. -/
theorem specProjection_comp_self (Bset : Set ℝ) (hBset : MeasurableSet Bset) :
    (specProjection hA Bset hBset).comp (specProjection hA Bset hBset)
      = specProjection hA Bset hBset := by
  simp only [specProjection_def]
  exact (spectralPVM hA).proj_idem Bset hBset


/-- **A cell carrying a nonzero projection meets the spectrum.**  Contrapositive
of `specProjection_eq_zero_of_subset_resolventSet`; it is what lets empty cells
be discarded and the separation hypothesis be used on the survivors. -/
theorem exists_mem_spectrum_of_specProjection_ne_zero (B : Set ℝ) (hB : MeasurableSet B)
    (h : specProjection hA B hB ≠ 0) :
    ∃ lam ∈ B, (lam : ℂ) ∈ _root_.LinearPMap.spectrum A := by
  by_contra hcon
  push Not at hcon
  refine h (specProjection_eq_zero_of_subset_resolventSet hA B hB fun lam hlam => ?_)
  have := hcon lam hlam
  have hroot : (lam : ℂ) ∈ _root_.LinearPMap.resolventSet A := by
    by_contra hnot
    exact this ((_root_.LinearPMap.mem_spectrum_iff A _).2 hnot)
  obtain ⟨R, hR⟩ := _root_.LinearPMap.mem_resolventSet_iff.mp hroot
  exact mem_resolventSet_iff.mpr ⟨R,
    ⟨hR.mem_domain, hR.smul_sub_apply, hR.apply_smul_sub⟩⟩

end LinearPMap
end TauCeti
