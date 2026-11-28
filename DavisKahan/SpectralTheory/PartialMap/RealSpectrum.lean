/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed
public import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import DavisKahan.BoundedOperator.Problem
public import DavisKahan.SpectralTheory.AbstractSpectrum

/-! # Real spectrum of a complex self-adjoint partial map -/

public section

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- **A self-adjoint partial map has real spectrum.** -/
theorem spectrum_subset_real_of_isSelfAdjoint {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) :
    _root_.LinearPMap.spectrum A ⊆ Complex.ofReal '' Set.univ := by
  intro z hz
  have him : z.im = 0 := hA.spectrum_subset_im_eq_zero hz
  exact ⟨z.re, Set.mem_univ _, by simp [Complex.ext_iff, him]⟩

end DavisKahan
end TauCeti
