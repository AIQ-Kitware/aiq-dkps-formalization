/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralSupport

/-!
# Inverting a self-adjoint operator across a vector spectral gap

If the diagonal measure of `ξ` gives no mass to `(-δ, δ)` — a *vector* spectral
gap — then `ξ` is in the range of `A`, and the preimage has norm at most
`δ⁻¹ ‖ξ‖`.

The construction is the Borel calculus of the **cut-off reciprocal**

```
gapSymbol δ s = if δ ≤ |s| then s⁻¹ else 0
```

which is bounded by `δ⁻¹` everywhere, so the norm bound is immediate from
`norm_borelCalculus_apply_le` and needs no spectral theory at all.  The
substance is the other half: `s · gapSymbol δ s = 1` wherever `δ ≤ |s|`, and the
vector gap says the diagonal measure lives exactly there — so multiplying by the
coordinate recovers `ξ`.

## Why this is not stated for Hilbert–Schmidt operators

It is the engine of the Davis–Kahan square-norm Sylvester estimate, where `A` is
the Sylvester operator `Z ↦ A Z - Z B` on the Hilbert–Schmidt class and the gap
is the pairwise spectral separation.  But nothing in it is about
Hilbert–Schmidt: it is a statement about *any* self-adjoint operator and *any*
vector whose diagonal measure avoids a neighbourhood of zero.  Stating it
generically is what makes the sharp constant `δ⁻¹` reusable — and the sharp
constant is the whole point, since the Fourier/semigroup route to the same
estimate yields `π/(2δ)`.

## Provenance

The donor is `Spectra.QuantumMechanics.SpectralTheory.spectralGapSolution`
(`SpectralTheory/Calculus/SpectralGapInverse.lean`), and the *symbol* is its
idea: Spectra also inverts by cutting off the reciprocal.  What differs is the
setting — Spectra runs it through the group calculus of a one-parameter unitary
group, this runs it through the native Cayley-transform Borel calculus, so no
Stone theorem is involved.
-/

@[expose] public section

open scoped InnerProductSpace
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section GapSymbol

/-- The cut-off reciprocal: `s⁻¹` where `|s| ≥ δ`, and `0` elsewhere. -/
noncomputable def gapSymbol (δ : ℝ) (s : ℝ) : ℂ :=
  if δ ≤ |s| then ((s : ℂ))⁻¹ else 0

theorem measurable_gapSymbol (δ : ℝ) : Measurable (gapSymbol δ) := by
  unfold gapSymbol
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_le measurable_const measurable_norm
  · exact (Complex.measurable_ofReal).inv

/-- The cut-off reciprocal is bounded by `δ⁻¹`. -/
theorem norm_gapSymbol_le {δ : ℝ} (hδ : 0 < δ) (s : ℝ) :
    ‖gapSymbol δ s‖ ≤ δ⁻¹ := by
  unfold gapSymbol
  split_ifs with hs
  · have hs0 : (0 : ℝ) < |s| := lt_of_lt_of_le hδ hs
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    exact inv_anti₀ hδ hs
  · simpa using inv_nonneg.mpr hδ.le

/-- **The defining identity of the cut-off reciprocal**: it inverts the
coordinate exactly where the cut-off is inactive. -/
theorem coord_mul_gapSymbol {δ : ℝ} {s : ℝ} (hs : δ ≤ |s|) (hδ : 0 < δ) :
    (s : ℂ) * gapSymbol δ s = 1 := by
  have hs0 : (s : ℂ) ≠ 0 := by
    have : (0 : ℝ) < |s| := lt_of_lt_of_le hδ hs
    exact_mod_cast abs_pos.mp this
  rw [gapSymbol, if_pos hs, mul_inv_cancel₀ hs0]

end GapSymbol

section GapInverse

variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A)

/-- The cut-off reciprocal pulled back to the spectrum of the Cayley transform,
which is where the Borel calculus of an unbounded self-adjoint operator lives. -/
noncomputable def gapSymbolCayley (δ : ℝ) :
    _root_.spectrum ℂ (cayley hA) → ℂ :=
  fun w => gapSymbol δ (cayleyInv hA w)

theorem isBddMeasurable_gapSymbolCayley {δ : ℝ} (hδ : 0 < δ) :
    BorelCalculus.IsBddMeasurable (gapSymbolCayley hA δ) :=
  ⟨(measurable_gapSymbol δ).comp (measurable_cayleyInv hA), δ⁻¹,
    by positivity, fun w => norm_gapSymbol_le hδ _⟩

/-- **The bounded inverse across a spectral gap.**  On the part of the spectrum
at distance `δ` from the origin this is `A⁻¹`; elsewhere it is zero. -/
noncomputable def gapInverse {δ : ℝ} (hδ : 0 < δ) : H →L[ℂ] H :=
  BorelCalculus.borelCalculus (isStarNormal_cayley hA)
    (isBddMeasurable_gapSymbolCayley hA hδ)

/-- **The sharp constant.**  It is `δ⁻¹` and it is immediate: the symbol is
bounded by `δ⁻¹` pointwise, so no spectral theory enters the estimate at all.

This is the constant the Fourier/semigroup route cannot reach — that one yields
`π/(2δ)`, the exact `L¹` mass of the Haagerup--Zsidó kernel. -/
theorem norm_gapInverse_apply_le {δ : ℝ} (hδ : 0 < δ) (ξ : H) :
    ‖gapInverse hA hδ ξ‖ ≤ δ⁻¹ * ‖ξ‖ :=
  BorelCalculus.norm_borelCalculus_apply_le _ _ (by positivity)
    (fun w => norm_gapSymbol_le hδ _) ξ

theorem norm_gapInverse_le {δ : ℝ} (hδ : 0 < δ) :
    ‖gapInverse hA hδ‖ ≤ δ⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    (norm_gapInverse_apply_le hA hδ)

end GapInverse

end LinearPMap
end TauCeti
