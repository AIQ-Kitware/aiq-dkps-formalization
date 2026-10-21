/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Authors: Jon Crall, OpenAI GPT-6
-/
module

public import ForTauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import TauCeti.Analysis.Normed.Operator.Resolvent.Spectrum
public import TauCeti.Analysis.Normed.Operator.Resolvent.RealSpectrum

/-!
# Real-set elimination for partial-map spectra

Tau Ceti owns the canonical partial-map spectrum and its resolvent complement
API. These two helpers convert inclusions into the real scalar copy of a set
to pointwise real statements used by downstream spectral-gap arguments.
-/

public section

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Read a spectral inclusion in the real scalar copy pointwise. -/
theorem mem_of_subset_ofReal_image {A : E →ₗ.[𝕜] E} {s : Set ℝ}
    (h : _root_.LinearPMap.spectrum A ⊆ RCLike.ofReal (K := 𝕜) '' s) {x : ℝ}
    (hx : RCLike.ofReal (K := 𝕜) x ∈ _root_.LinearPMap.spectrum A) : x ∈ s := by
  obtain ⟨y, hy, hxy⟩ := h hx
  rwa [RCLike.ofReal_inj.mp hxy] at hy

/-- Put a pointwise real spectral bound back in the scalar copy of a spectrum. -/
theorem subset_ofReal_image_of_forall {A : E →ₗ.[𝕜] E} {s : Set ℝ}
    (hreal : _root_.LinearPMap.spectrum A ⊆ RCLike.ofReal (K := 𝕜) '' Set.univ)
    (h : ∀ x : ℝ, RCLike.ofReal (K := 𝕜) x ∈ _root_.LinearPMap.spectrum A → x ∈ s) :
    _root_.LinearPMap.spectrum A ⊆ RCLike.ofReal (K := 𝕜) '' s := by
  intro z hz
  obtain ⟨x, -, rfl⟩ := hreal hz
  exact ⟨x, h x hz, rfl⟩

end LinearPMap
end TauCeti

end
