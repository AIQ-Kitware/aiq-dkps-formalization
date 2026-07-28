/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.SpectralTheory.ClosedOperator.Basic
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import Spectra.Resolvent.Spectrum

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
namespace SpectraBridge

open scoped InnerProductSpace

universe v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Membership in the closed-operator real resolvent is exactly membership of
the real scalar in the Spectra resolvent. -/
theorem mem_realResolventSet_iff_mem_spectraResolvent
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E))
    (lam : ℝ) :
    lam ∈ A.realResolventSet ↔
      (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet A.toLinearPMap := by
  rfl

/-- The generic closed-operator real spectrum agrees with the genuine Spectra
spectrum after specializing the scalar field to `ℂ`. -/
theorem realSpectrum_eq_spectraSpectrum
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := E)) :
    A.realSpectrum
      = Complex.ofReal ⁻¹' TauCeti.LinearPMap.spectrum A.toLinearPMap := by
  ext lam
  rfl

/-! ## The spectrum of a self-adjoint operator is real

This is the one genuinely *mathematical* consequence of taking the canonical
spectrum in `ℂ` rather than in `ℝ`: statements that used to be about a set of
reals by construction now have to *prove* that the spectrum is real.

**It is still proved through Spectra, and that is deliberate and temporary.**
The standard argument — for symmetric `A` and `z = a + bi` with `b ≠ 0`,
`‖(A - z)x‖² = ‖(A - a)x‖² + b²‖x‖² ≥ b²‖x‖²`, so `A - z` is injective with
closed range, and self-adjointness makes the range dense hence everything —
needs the `±i` deficiency-surjectivity of a self-adjoint partial map, which lives
in Spectra's resolvent/Yosida–Hille layer and is scheduled for phases S2/S5 of
`dev/tauceti/spectra-removal-plan.md`.  Rather than block the `spectrum`
migration on that, the *statement* is canonical (`TauCeti.LinearPMap.spectrum`)
and only the *proof* is borrowed, so the remaining dependency is a single lemma
in a single file instead of being spread across 26 modules.

Provenance: the proof is `Spectra.Resolvent.mem_resolventSet_of_im_ne_zero`,
`Spectra/Resolvent/Spectrum.lean` at `8dbaaf67…`, Copyright (c) 2026 Spectra
Formalization Project, Apache 2.0.  Re-prove natively and this file's last
Spectra import disappears. -/

/-- **A self-adjoint partial map has real spectrum.** -/
theorem spectrum_subset_real_of_isSelfAdjoint {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) :
    TauCeti.LinearPMap.spectrum A ⊆ Complex.ofReal '' Set.univ := by
  intro z hz
  by_cases him : z.im = 0
  · exact ⟨z.re, Set.mem_univ _, by
      simp [Complex.ext_iff, him]⟩
  · exact absurd (Spectra.Resolvent.mem_resolventSet_of_im_ne_zero hA him) hz

end SpectraBridge
end Experimental
end DavisKahan
end TauCeti