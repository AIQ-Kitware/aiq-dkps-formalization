/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.QuantumMechanics.Channels.PolarDecomp
import ForTauCeti.Analysis.InnerProductSpace.PolarPartialIsometry

/-!
# Spectra-backed bounded operator absolute value and polar factor

This module exposes Spectra's proof-complete bounded complex polar
decomposition under bridge-specific names. It is independent of Spectra's
Stone and spectral-PVM construction and therefore provides an immediately
usable alternate route for the Davis--Kahan operator-angle and direct-rotation
programs.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Spectra's bounded operator modulus, kept under a bridge-specific name until
it is compared with the independent DKPS construction. -/
noncomputable def spectraOperatorAbsoluteValue (T : H →L[ℂ] H) : H →L[ℂ] H :=
  Spectra.QuantumMechanics.Channels.absOp T

/-- The Spectra-backed modulus is positive. -/
theorem spectraOperatorAbsoluteValue_nonneg (T : H →L[ℂ] H) :
    0 ≤ spectraOperatorAbsoluteValue T :=
  Spectra.QuantumMechanics.Channels.absOp_nonneg T

/-- The Spectra-backed modulus is self-adjoint. -/
theorem spectraOperatorAbsoluteValue_isSelfAdjoint (T : H →L[ℂ] H) :
    IsSelfAdjoint (spectraOperatorAbsoluteValue T) :=
  Spectra.QuantumMechanics.Channels.absOp_isSelfAdjoint T

/-- Squaring the modulus gives `T⋆T`. -/
theorem spectraOperatorAbsoluteValue_mul_self (T : H →L[ℂ] H) :
    spectraOperatorAbsoluteValue T * spectraOperatorAbsoluteValue T =
      star T * T :=
  Spectra.QuantumMechanics.Channels.absOp_mul_absOp T

/-- The modulus and the original operator have equal pointwise norms. -/
theorem norm_spectraOperatorAbsoluteValue_apply (T : H →L[ℂ] H) (x : H) :
    ‖spectraOperatorAbsoluteValue T x‖ = ‖T x‖ :=
  Spectra.QuantumMechanics.Channels.norm_absOp_apply T x

/-- The Spectra-backed modulus has the same operator norm as the original
operator.  This is derived from the pointwise norm identity in both
directions, so it does not require the heavier spectral-calculus stack. -/
theorem norm_spectraOperatorAbsoluteValue (T : H →L[ℂ] H) :
    ‖spectraOperatorAbsoluteValue T‖ = ‖T‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) ?_
    intro x
    rw [norm_spectraOperatorAbsoluteValue_apply]
    exact T.le_opNorm x
  · refine ContinuousLinearMap.opNorm_le_bound _
      (norm_nonneg (spectraOperatorAbsoluteValue T)) ?_
    intro x
    rw [← norm_spectraOperatorAbsoluteValue_apply T x]
    exact (spectraOperatorAbsoluteValue T).le_opNorm x

/-- Anything commuting with the Gram operator `T⋆T` commutes with the modulus
`|T|`.  Since `|T| = CFC.sqrt (T⋆T)` is a continuous function of `T⋆T`, this is
the non-unital `nnreal` continuous-functional-calculus commutation lemma. -/
theorem commute_spectraOperatorAbsoluteValue_of_commute_star_mul_self
    (T b : H →L[ℂ] H) (h : Commute (star T * T) b) :
    Commute (spectraOperatorAbsoluteValue T) b := by
  have : spectraOperatorAbsoluteValue T = CFC.sqrt (star T * T) := rfl
  rw [this, CFC.sqrt]
  exact Commute.cfcₙ_nnreal h NNReal.sqrt

/-- Spectra's partial isometry in the bounded polar decomposition. -/
noncomputable def spectraPolarIsometry (T : H →L[ℂ] H) : H →L[ℂ] H :=
  Spectra.QuantumMechanics.Channels.polarIsometry T

/-- The bounded polar decomposition `T = U |T|`. -/
theorem spectraPolar_decomposition (T : H →L[ℂ] H) :
    spectraPolarIsometry T ∘L spectraOperatorAbsoluteValue T = T :=
  Spectra.QuantumMechanics.Channels.polar_decomposition T

/-! ## Bridge to the Spectra-free polar decomposition

`ForTauCeti/Analysis/InnerProductSpace/PolarPartialIsometry.lean` develops the general
bounded polar decomposition without Spectra, and more generally (rectangular rather than
square).  These two lemmas identify it with the Spectra-backed one, so every result proved
there transfers to this bridge by rewriting — and so the Spectra dependency here becomes a
naming convenience rather than a mathematical one. -/

/-- Spectra's `absOp` is our `modulus`: both are `CFC.sqrt` of the Gram operator. -/
theorem spectra_absOp_eq_modulus (T : H →L[ℂ] H) :
    Spectra.QuantumMechanics.Channels.absOp T = T.modulus := by
  unfold Spectra.QuantumMechanics.Channels.absOp CFC.abs ContinuousLinearMap.modulus
  congr 1

@[simp]
theorem spectraOperatorAbsoluteValue_eq_modulus (T : H →L[ℂ] H) :
    spectraOperatorAbsoluteValue T = T.modulus :=
  spectra_absOp_eq_modulus T

/-- Spectra's initial space is ours. -/
theorem spectra_polarRange_eq_polarInitial (T : H →L[ℂ] H) :
    Spectra.QuantumMechanics.Channels.polarRange T = T.polarInitial := by
  unfold Spectra.QuantumMechanics.Channels.polarRange ContinuousLinearMap.polarInitial
  rw [spectra_absOp_eq_modulus]

/-- **The Spectra-backed polar isometry is ours.**  Proved from the uniqueness
characterisation: it factors `T` through the modulus and vanishes off the initial space. -/
@[simp]
theorem spectraPolarIsometry_eq_polarPartial (T : H →L[ℂ] H) :
    spectraPolarIsometry T = T.polarPartial := by
  refine T.eq_polarPartial_of_comp_modulus _ ?_ ?_
  · rw [← spectraOperatorAbsoluteValue_eq_modulus, spectraPolar_decomposition]
  · intro y hy
    have hy' : y ∈ (Spectra.QuantumMechanics.Channels.polarRange T)ᗮ := by
      rw [spectra_polarRange_eq_polarInitial]; exact hy
    show Spectra.QuantumMechanics.Channels.polarIsometry T y = 0
    unfold Spectra.QuantumMechanics.Channels.polarIsometry
    rw [ContinuousLinearMap.comp_apply,
      Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr hy', map_zero]



/-- **The adjoint of the polar isometry is the polar isometry of the adjoint**, for the
Spectra-backed factor.  Immediate from the bridge and the ForTauCeti uniqueness theorem;
the direct Spectra-side argument runs some 140 lines. -/
theorem adjoint_spectraPolarIsometry (T : H →L[ℂ] H) :
    (spectraPolarIsometry T).adjoint = spectraPolarIsometry T.adjoint := by
  rw [spectraPolarIsometry_eq_polarPartial, spectraPolarIsometry_eq_polarPartial,
    T.polarPartial_adjoint]

/-- The final projection identity, transferred through the bridge. -/
theorem spectraPolarIsometry_comp_adjoint (T : H →L[ℂ] H) :
    spectraPolarIsometry T ∘L (spectraPolarIsometry T).adjoint = T.polarFinal.starProjection := by
  rw [spectraPolarIsometry_eq_polarPartial, T.polarPartial_comp_adjoint]

/-- The initial projection identity, transferred through the bridge. -/
theorem adjoint_spectraPolarIsometry_comp (T : H →L[ℂ] H) :
    (spectraPolarIsometry T).adjoint ∘L spectraPolarIsometry T
      = T.polarInitial.starProjection := by
  rw [spectraPolarIsometry_eq_polarPartial, T.adjoint_comp_polarPartial]

end SpectraBridge
end Experimental
end DavisKahan
end TauCeti
