/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity
public import TauCeti.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Spectral projections on the uniform real grid

The elementary real-grid geometry is now maintained in TauCeti (PR #18927):
`Real.gridCell`, `Real.measurableSet_gridCell`, `Real.pairwise_disjoint_gridCell`,
`Real.iUnion_gridCell`, and the two endpoint bounds. This module uses those
accepted definitions directly, without local aliases or duplicate proofs.

A nonzero measurable spectral block meets the spectrum. The proof takes the
contrapositive of the native spectral support theorem.

## Provenance

The original Kitware/DKPS grid definitions and lemmas at this path were
adapted upstream in TauCeti PR #18927 (main commit `3bd7882f07072fe6918ca2a50175cbca678f07de`).
Pre-retirement DKPS source is preserved at `e4637c3919ae` and in
`dev/tauceti/extraction-manifest.json` / the contribution census.
-/

public section

open _root_.LinearPMap (
  mem_resolventSet_iff)

namespace TauCeti
namespace LinearPMap

variable {ε : ℝ}

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- **A cell carrying a nonzero projection meets the spectrum.**  Contrapositive
of the native spectral support theorem; it is what lets empty cells
be discarded and the separation hypothesis be used on the survivors. -/
theorem exists_mem_spectrum_of_specProjection_ne_zero (B : Set ℝ) (hB : MeasurableSet B)
    (h : (A.spectralPVM hA).proj B hB ≠ 0) :
    ∃ lam ∈ B, (lam : ℂ) ∈ _root_.LinearPMap.spectrum A := by
  by_contra hcon
  push Not at hcon
  refine h (hA.spectralPVM_proj_eq_zero_of_forall_mem_resolventSet hB fun lam hlam => ?_)
  have := hcon lam hlam
  have hroot : (lam : ℂ) ∈ _root_.LinearPMap.resolventSet A := by
    by_contra hnot
    exact this ((_root_.LinearPMap.mem_spectrum_iff A _).2 hnot)
  exact hroot

end LinearPMap
end TauCeti
