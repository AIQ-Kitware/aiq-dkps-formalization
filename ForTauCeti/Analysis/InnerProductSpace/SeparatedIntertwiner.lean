/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
import ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjointResolvent

/-!
# Intertwiners of spectrally separated operators

An `X` intertwining two partial maps intertwines everything built from them:
first their resolvents, and from there their spectral projections, so that
disjoint spectra force `X = 0`.

This is Spectra-removal lane **SR-E**
(`dev/tauceti/spectra-removal-parallel-lanes.md`), replacing the donor constant
`generatorIntertwiner_eq_zero_of_disjoint_spectrum`.

## Status

This module currently carries the **first** step, resolvent intertwining, which
needs nothing beyond the definition of `resolventSet`.  The remaining chain —
Cayley, `borelCalculus`, `specProjection` — is written up in the lane document.
The two spectral-projection facts the final argument needs are already available
from lane SR-B's `specProjection_eq_zero_of_subset_resolventSet`.

## Provenance

* Replaces `vendor/Spectra/Spectra/SpectralTheory/SeparatedIntertwiner.lean`.
  Proved natively rather than relocated: the donor's route runs through
  `borelMeasure` and the Born-rule support estimate, spanning 44 Spectra files,
  none of which `ForTauCeti` may import.
* Spectra influence: none.
-/

@[expose] public section

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **An intertwiner intertwines the resolvents.**

If `X` carries `B` to `A` — `A (X y) = X (B y)` on `dom B` — and `z` is a
resolvent point of both, then `X R_B = R_A X`.

Only the two defining properties of a resolvent are used: that `R_A` inverts
`A - z` on the domain, and that `R_B` lands in `dom B` and inverts `B - z`
there.  Neither self-adjointness nor closedness is needed. -/
theorem resolvent_intertwines
    {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {X : F →L[𝕜] E} {z : 𝕜}
    {RA : E →L[𝕜] E} {RB : F →L[𝕜] F}
    (hRA : ∀ ψ : A.domain, RA (A ψ - z • (ψ : E)) = (ψ : E))
    (hRB : ∀ φ : F, ∃ h : RB φ ∈ B.domain, B ⟨RB φ, h⟩ - z • RB φ = φ)
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L RB = RA ∘L X := by
  refine ContinuousLinearMap.ext fun φ => ?_
  obtain ⟨hmem, hBinv⟩ := hRB φ
  -- Push `X` through `B ⟨RB φ⟩ - z • RB φ = φ` and rewrite with the
  -- intertwining relation, turning it into a statement about `A`.
  have hXpush : A ⟨X (RB φ), hmaps ⟨RB φ, hmem⟩⟩ - z • X (RB φ) = X φ := by
    have := congrArg X hBinv
    rw [map_sub, map_smul] at this
    rw [hint ⟨RB φ, hmem⟩]
    exact this
  -- `RA` inverts `A - z` at that domain vector, which is exactly the claim.
  have := hRA ⟨X (RB φ), hmaps ⟨RB φ, hmem⟩⟩
  rw [hXpush] at this
  simpa using this.symm

/-- `resolvent`-specialised form of `resolvent_intertwines`. -/
theorem resolvent_intertwines' {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} {z : 𝕜}
    (hzA : z ∈ resolventSet A) (hzB : z ∈ resolventSet B)
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L resolvent B hzB = resolvent A hzA ∘L X :=
  resolvent_intertwines (fun ψ => resolvent_apply_sub_smul hzA ψ)
    (fun φ => ⟨resolvent_mem_domain hzB φ, sub_smul_resolvent hzB φ⟩) hmaps hint

section Complex

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **An intertwiner intertwines the Cayley transforms.**

Immediate from `resolvent_intertwines'` at `z = -i`, since
`cayley hA = 1 - 2i • R_A(-i)`.  This is the step that carries the intertwining
into the bounded world, where the Borel calculus lives. -/
theorem cayley_intertwines {A : E →ₗ.[ℂ] E} {B : F →ₗ.[ℂ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {X : F →L[ℂ] E}
    (hmaps : ∀ y : B.domain, X (y : F) ∈ A.domain)
    (hint : ∀ y : B.domain, A ⟨X (y : F), hmaps y⟩ = X (B y)) :
    X ∘L cayley hB = cayley hA ∘L X := by
  have hres := resolvent_intertwines' (A := A) (B := B) (X := X)
    (negI_mem_resolventSet hA) (negI_mem_resolventSet hB) hmaps hint
  refine ContinuousLinearMap.ext fun φ => ?_
  have hr := congrArg (fun T : F →L[ℂ] E => T φ) hres
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at hr
  simp only [cayley, ContinuousLinearMap.coe_comp, Function.comp_apply,
    sub_apply, one_apply_eq_self, smul_apply, map_sub, map_smul, hr]

end Complex

end LinearPMap
end TauCeti
