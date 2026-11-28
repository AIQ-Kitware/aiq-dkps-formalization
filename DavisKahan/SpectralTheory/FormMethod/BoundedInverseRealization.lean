/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Inverse
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Nonnegativity of the partial inverse of a bounded operator -/

public section

open scoped InnerProductSpace

namespace TauCeti.DavisKahan.FreeBeam.Abstract

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- A bounded injective operator with a nonnegative real quadratic form
has a nonnegative quadratic form on the domain of its partial inverse. -/
theorem inverse_toPMap_top_nonnegative
    (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (hR : ∀ y : H, 0 ≤ RCLike.re ⟪R y, y⟫_𝕜)
    (x : (R.toLinearMap.toPMap ⊤).inverse.domain) :
    0 ≤ RCLike.re ⟪(R.toLinearMap.toPMap ⊤).inverse x, (x : H)⟫_𝕜 := by
  rw [← R.apply_inverse_toPMap_top hinj x, inner_re_symm]
  exact hR ((R.toLinearMap.toPMap ⊤).inverse x)

end TauCeti.DavisKahan.FreeBeam.Abstract
