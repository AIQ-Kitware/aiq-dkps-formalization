/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ClosedOperator.Basic
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent

/-!
# Closed-operator real spectrum and the Spectra spectrum

The low-level closed-operator API defines the real resolvent without importing
Spectra, so it remains available over every `RCLike` scalar field.  This file
identifies its complex specialization with the real spectrum used by Spectra.
The bridge is intentionally kept above both foundations to avoid an import
cycle.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental

open scoped InnerProductSpace

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Membership in the closed-operator real resolvent is exactly membership of
the real scalar in the Spectra resolvent. -/
theorem mem_realResolventSet_iff_mem_spectraResolvent
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E))
    (lam : ℝ) :
    lam ∈ A.realResolventSet ↔
      (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet A.toLinearPMap := by
  rfl

omit [CompleteSpace E] in
/-- The generic closed-operator real spectrum agrees with the genuine Spectra
spectrum after specializing the scalar field to `ℂ`. -/
theorem realSpectrum_eq_spectraSpectrum
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)) :
    A.realSpectrum
      = Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap := by
  ext lam
  rfl

/-! ## The spectrum of a self-adjoint operator is real

**Now proved natively, 2026-07-28.**  This lemma briefly had a canonical
statement and a proof borrowed from `Spectra.Resolvent.mem_resolventSet_of_im_ne_zero`,
because the native argument needs the `±i` deficiency-surjectivity of a
self-adjoint partial map.  That is now
`TauCeti.LinearPMap.mem_resolventSet_of_im_ne_zero` in
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/SelfAdjointResolvent.lean`,
proved from Mathlib's `LinearPMap` adjoint API — the estimate
`|Im z| ‖x‖ ≤ ‖(A - z)x‖`, closed range from closedness of `A`, dense range from
"no non-real eigenvalues" — so the borrowed proof and this file's last Spectra
import are both gone. -/

/-- **A self-adjoint partial map has real spectrum.** -/
theorem spectrum_subset_real_of_isSelfAdjoint {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) :
    TauCeti.LinearPMap.spectrum A ⊆ Complex.ofReal '' Set.univ :=
  TauCeti.LinearPMap.spectrum_subset_real hA

end Experimental
end DavisKahan
end TauCeti