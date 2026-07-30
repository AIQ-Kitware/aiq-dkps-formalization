/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.ClosedSylvesterEquation

/-!
# Form-bounded gap configurations for the unbounded Sylvester equation

The interval/exterior configuration says one block has spectrum inside a compact
interval while the other stays a fixed distance away from it.  The predicate is
symmetric in the two blocks: either orientation is allowed.

`FormBoundedSylvesterGap` collects every gap configuration the `sin Θ` endpoint
needs.  Its two ordered constructors let both diagonal blocks be genuinely
unbounded; only the interval/exterior constructor requires a bounded spectral
block.

## Two spellings of the same configurations

This module states the ordered configurations as **operator-form bounds** —
`SemiboundedBelow`/`SemiboundedAbove` — and the interval/exterior configuration
over `LinearPMap.realSpectrum`.  `SpectralIntervalExteriorGap` and
`SpectralSylvesterGap` (`SinTheta/Unbounded/IntervalExterior.lean`,
`Sylvester/Unbounded/AllGap.lean`) instead state all three configurations as
**spectral containments** in `Set.Ici`/`Set.Iic`, which is the form Davis--Kahan
1970 uses.

For self-adjoint blocks the two describe the same configurations — a form bound
`⟪Ax, x⟫ ≥ c‖x‖²` and a spectral containment `spectrum A ⊆ Set.Ici c` are the
spectral theorem apart — but they are different propositions, and **only one
direction is proved here**:

* `formBoundedSylvesterGap_of_spectral` gives `SpectralSylvesterGap → `
  `FormBoundedSylvesterGap` in **every** configuration, the ordered branches by
  `semiboundedBelow_of_spectrum_subset_Ici` and its mirror
  (`SpectralTheory/OrderedHalfLine.lean`), the interval branch by
  `realSpectrum_eq_spectraSpectrum`;
* the converse holds for the **interval/exterior branch only**
  (`SpectralSylvesterGap.intervalExterior_of_formBounded`).  Recovering a
  spectral containment from a form bound is the half of the spectral theorem
  this tree does not have.

**So the form-bounded predicate is the weaker hypothesis, and a theorem stated
over it is the stronger theorem** — which is exactly how the endpoints are
arranged: `davisKahan1970_sylvester_complex` takes this predicate, and
`davisKahan1970_sylvester_of_spectrumGap` is available at the spectral one.

Neither predicate carries an unqualified name.  They are equivalent mathematics
stated two ways, so a bare `SylvesterGap` would leave a reader asking which one
it is; each name says how its ordered configurations are given.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Interval/exterior configuration for two partial maps, over
`LinearPMap.realSpectrum`: one block has real spectrum inside a compact interval
and the other stays a distance `δ` away from it.  The predicate is symmetric in
the two blocks.

It needs neither a dense domain nor a closed graph — only the two real spectra —
so it is stated over `LinearPMap` and the closedness hypotheses live with the
theorems that consume the gap.

`UnboundedIntervalExteriorGapPMap` is the same configuration spelled through
`ofReal ⁻¹' LinearPMap.spectrum`; `realSpectrum_eq_spectraSpectrum` identifies
the two spectra, and `sylvesterIntervalExteriorGap_of_realSpectrum` transports
this predicate to that one. -/
def linearPMap_RealSpectrumIntervalExteriorGap
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (β α δ : ℝ) : Prop :=
  (TauCeti.LinearPMap.realSpectrum A ⊆ Set.Icc β α ∧
    TauCeti.LinearPMap.realSpectrum B ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
  (TauCeti.LinearPMap.realSpectrum B ⊆ Set.Icc β α ∧
    TauCeti.LinearPMap.realSpectrum A ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x})

/-- Every gap configuration the `sin Θ` endpoint needs, over the canonical
partial-map representation, with the two ordered configurations given as
operator-form bounds.  The ordered constructors allow both diagonal blocks to be
genuinely unbounded; only the interval/exterior constructor has a bounded
spectral block.

For self-adjoint blocks `SemiboundedBelow A c` and
`ofReal ⁻¹' spectrum A ⊆ Set.Ici c` describe the same configuration but are
different propositions.  `SpectralSylvesterGap` is the spectral spelling and
implies this one (`formBoundedSylvesterGap_of_spectral`); the converse is proved
for the `intervalExterior` constructor only. -/
inductive linearPMap_FormBoundedSylvesterGap
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) (δ : ℝ) : Prop where
  | intervalExterior
      {β α : ℝ}
      (hβα : β ≤ α)
      (hgap : linearPMap_RealSpectrumIntervalExteriorGap A B β α δ)
  | leftAboveRightBelow
      (c : ℝ)
      (hA : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
      (hB : TauCeti.LinearPMap.SemiboundedAbove B c)
  | leftBelowRightAbove
      (c : ℝ)
      (hA : TauCeti.LinearPMap.SemiboundedAbove A c)
      (hB : TauCeti.LinearPMap.SemiboundedBelow B (c + δ))

/-- Interval/exterior configuration for two closed self-adjoint blocks, over
`realSpectrum`.

Representation shim: `ClosedOperator.realSpectrum` is itself a shim for
`TauCeti.LinearPMap.realSpectrum` at `A.toLinearPMap`, so this is *definitionally*
`linearPMap_RealSpectrumIntervalExteriorGap` and the two are interchangeable by
`Iff.rfl`.  The mathematics lives in that definition; this spelling exists for
callers holding a bundled `ClosedOperator`. -/
abbrev RealSpectrumIntervalExteriorGap
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F))
    (β α δ : ℝ) : Prop :=
  linearPMap_RealSpectrumIntervalExteriorGap A.toLinearPMap B.toLinearPMap β α δ

/-- Every gap configuration the `sin Θ` endpoint needs, for bundled closed
operators, with the two ordered configurations given as operator-form bounds.

Representation shim for the partial-map predicate; every component
(`realSpectrum`, `SemiboundedBelow`, `SemiboundedAbove`) is already a shim over
the `TauCeti.LinearPMap` layer, so the two spellings are definitionally equal at
`A.toLinearPMap` and `cases`/`rcases` see the underlying constructors directly.

`SpectralSylvesterGap` is the spectral spelling and implies this one in every
configuration (`formBoundedSylvesterGap_of_spectral`), so this is the weaker
hypothesis.  In the other direction only the interval/exterior constructor
transports, by `SpectralSylvesterGap.intervalExterior_of_formBounded`. -/
abbrev FormBoundedSylvesterGap
    (A : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E))
    (B : TauCeti.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F))
    (δ : ℝ) : Prop :=
  linearPMap_FormBoundedSylvesterGap A.toLinearPMap B.toLinearPMap δ

namespace FormBoundedSylvesterGap

/-- Shim constructor: interval/exterior configuration. -/
alias intervalExterior := linearPMap_FormBoundedSylvesterGap.intervalExterior

/-- Shim constructor: left block above, right block below. -/
alias leftAboveRightBelow := linearPMap_FormBoundedSylvesterGap.leftAboveRightBelow

/-- Shim constructor: left block below, right block above. -/
alias leftBelowRightAbove := linearPMap_FormBoundedSylvesterGap.leftBelowRightAbove

end FormBoundedSylvesterGap

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti