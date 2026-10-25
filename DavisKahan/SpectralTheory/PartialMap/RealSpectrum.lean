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

/-!
# The real resolvent of a partial map, and the ambient spectrum

`TauCeti.LinearPMap.realResolventSet` is defined without importing the ambient
spectral theory, so it remains available over every `RCLike` scalar field.  This
file identifies its complex specialization with the ambient spectrum.  The
bridge is intentionally kept above both foundations to avoid an import cycle.
-/

public section

namespace TauCeti
namespace DavisKahan

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-! ### The donor and upstream resolvent representations

The mathematical endpoints use TauCeti's canonical partial-map spectrum.
A few constructive source arguments still use the old donor resolvent with the
same inverse-record fields. Those witnesses are translated here only at
remaining legacy consumers; canonical spectral predicates stay in statements. -/

/-- Membership in the donor and upstream resolvent sets is equivalent. -/
theorem mem_local_resolventSet_iff_root
    (A : E →ₗ.[𝕜] E) (z : 𝕜) :
    z ∈ TauCeti.LinearPMap.resolventSet A ↔
      z ∈ _root_.LinearPMap.resolventSet A := by
  rw [TauCeti.LinearPMap.mem_resolventSet_iff,
    _root_.LinearPMap.mem_resolventSet_iff]
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R, {
      mem_domain := hR.mem_domain
      smul_sub_apply := hR.smul_sub_apply
      apply_smul_sub := hR.apply_smul_sub
    }⟩
  · rintro ⟨R, hR⟩
    exact ⟨R, {
      mem_domain := hR.mem_domain
      smul_sub_apply := hR.smul_sub_apply
      apply_smul_sub := hR.apply_smul_sub
    }⟩

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

variable {F : Type v}
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
/-- The old sign-convention inverse condition and the donor complex-resolvent
interface agree.  The hard sign change is proved once, scalar-generically, in
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Closed.lean` and the donor
complex resolvent has a separately proved equivalence with canonical TauCeti. -/
theorem mem_realResolventSet_iff_mem_spectraResolvent
    (A : E →ₗ.[ℂ] E) (lam : ℝ) :
    lam ∈ TauCeti.LinearPMap.realResolventSet A ↔
      (lam : ℂ) ∈ TauCeti.LinearPMap.resolventSet A :=
  (TauCeti.LinearPMap.mem_realResolventSet_iff_mem_canonical_resolventSet A lam).trans
    (mem_local_resolventSet_iff_root A (lam : ℂ)).symm

/-! ## The spectrum of a self-adjoint operator is real

Tau Ceti proves the more general `RCLike` statement that the canonical
`LinearPMap` spectrum lies on the zero-imaginary axis. This paper-facing result
now states that canonical spectrum directly. -/

/-- **A self-adjoint partial map has real spectrum.** -/
theorem spectrum_subset_real_of_isSelfAdjoint {A : E →ₗ.[ℂ] E}
    (hA : IsSelfAdjoint A) :
    _root_.LinearPMap.spectrum A ⊆ Complex.ofReal '' Set.univ := by
  intro z hz
  have him : z.im = 0 := hA.spectrum_subset_im_eq_zero hz
  exact ⟨z.re, Set.mem_univ _, by simp [Complex.ext_iff, him]⟩

end DavisKahan
end TauCeti
