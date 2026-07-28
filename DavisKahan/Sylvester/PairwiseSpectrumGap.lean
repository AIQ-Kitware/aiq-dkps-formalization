/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Interop.TauCeti.ClosedOperator
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Pairwise spectral separation for two closed self-adjoint blocks

This is the exact weak spectral hypothesis used by the square-norm Sylvester
estimate and Davis--Kahan Theorem 6.2.  It is intentionally independent of the
three stronger interval/exterior and ordered gap configurations.

## Migration note (phase S2, 2026-07-28)

The spectrum here was `Spectra.Resolvent.spectrum : Set ℝ` and is now
`TauCeti.LinearPMap.spectrum : Set ℂ` (`dev/tauceti/spectra-removal-plan.md`).
The separation is therefore measured by `‖lam - α‖` in `ℂ` rather than `|lam - α|`
in `ℝ`.  This is the *same* condition whenever the operators are self-adjoint —
their spectra are real — and it is the honest statement otherwise, which the
real-valued version was not: Spectra's `spectrum` silently kept only the real
slice, so two operators with separated real slices but colliding complex spectra
satisfied the old predicate.  For the self-adjoint blocks Davis--Kahan actually
uses, nothing changes.
-/

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

noncomputable section

universe v

open TauCeti.DavisKahanExt

/-- Every point of the spectra of two partial maps is separated by at least
`delta`.  This is the canonical pairwise-gap predicate; the bundled
`ClosedOperator` form below remains only for existing source-facing data. -/
def LinearPMap.GenuinePairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →ₗ.[ℂ] E) (B : F →ₗ.[ℂ] F) (δ : ℝ) : Prop :=
  ∀ lam ∈ TauCeti.LinearPMap.spectrum A,
    ∀ α ∈ TauCeti.LinearPMap.spectrum B,
      δ ≤ ‖lam - α‖

namespace LinearPMap.GenuinePairwiseSpectrumGap

/-- Pairwise spectral distance is symmetric. -/
theorem symm
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F} {δ : ℝ}
    (h : LinearPMap.GenuinePairwiseSpectrumGap A B δ) :
    LinearPMap.GenuinePairwiseSpectrumGap B A δ := by
  intro α hα lam hlam
  simpa [norm_sub_rev] using h lam hlam α hα

/-- Decreasing the requested distance preserves pairwise separation. -/
theorem mono
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F} {δ ε : ℝ}
    (h : LinearPMap.GenuinePairwiseSpectrumGap A B δ) (hεδ : ε ≤ δ) :
    LinearPMap.GenuinePairwiseSpectrumGap A B ε := by
  intro lam hlam α hα
  exact hεδ.trans (h lam hlam α hα)

/-- Positive pairwise separation implies disjoint spectra. -/
theorem disjoint
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F} {δ : ℝ}
    (h : LinearPMap.GenuinePairwiseSpectrumGap A B δ) (hδ : 0 < δ) :
    Disjoint (TauCeti.LinearPMap.spectrum A)
      (TauCeti.LinearPMap.spectrum B) := by
  refine Set.disjoint_left.mpr ?_
  intro lam hlamA hlamB
  have hsep : δ ≤ ‖lam - lam‖ := h lam hlamA lam hlamB
  exact (not_le_of_gt hδ) (by simpa using hsep)

end LinearPMap.GenuinePairwiseSpectrumGap

/-- Every point of the two real spectra is separated by at least `delta`. -/
def GenuinePairwiseSpectrumGap
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : ClosedOperator (𝕜 := ℂ) (E := E))
    (B : ClosedOperator (𝕜 := ℂ) (E := F))
    (δ : ℝ) : Prop :=
  LinearPMap.GenuinePairwiseSpectrumGap A.toLinearPMap B.toLinearPMap δ

namespace GenuinePairwiseSpectrumGap

/-- Pairwise spectral distance is symmetric. -/
theorem symm
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)} {δ : ℝ}
    (h : GenuinePairwiseSpectrumGap A B δ) :
    GenuinePairwiseSpectrumGap B A δ := by
  exact LinearPMap.GenuinePairwiseSpectrumGap.symm h

/-- Decreasing the requested distance preserves pairwise separation. -/
theorem mono
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)} {δ ε : ℝ}
    (h : GenuinePairwiseSpectrumGap A B δ) (hεδ : ε ≤ δ) :
    GenuinePairwiseSpectrumGap A B ε := by
  exact LinearPMap.GenuinePairwiseSpectrumGap.mono h hεδ

/-- Positive pairwise separation implies disjoint spectra. -/
theorem disjoint
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {A : ClosedOperator (𝕜 := ℂ) (E := E)}
    {B : ClosedOperator (𝕜 := ℂ) (E := F)} {δ : ℝ}
    (h : GenuinePairwiseSpectrumGap A B δ) (hδ : 0 < δ) :
    Disjoint (TauCeti.LinearPMap.spectrum A.toLinearPMap)
      (TauCeti.LinearPMap.spectrum B.toLinearPMap) := by
  exact LinearPMap.GenuinePairwiseSpectrumGap.disjoint h hδ

end GenuinePairwiseSpectrumGap

end

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti
