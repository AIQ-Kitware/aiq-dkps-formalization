/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-6 (runtime variant undetermined)
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Extensionality for continuous operators on complex Hilbert spaces

Mathlib's `Complex.ext_inner_map` proves extensionality for linear maps from
their diagonal matrix elements. This is the continuous-linear-map form used by
the spectral calculus.
-/

public section

open scoped InnerProductSpace

namespace TauCeti

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Continuous complex-linear operators are determined by their diagonal
matrix elements. -/
theorem op_ext_of_inner_self {S T : H →L[ℂ] H}
    (h : ∀ ξ : H, ⟪ξ, S ξ⟫_ℂ = ⟪ξ, T ξ⟫_ℂ) : S = T := by
  refine ContinuousLinearMap.coe_injective ((ext_inner_map _ _).mp fun ξ => ?_)
  change ⟪S ξ, ξ⟫_ℂ = ⟪T ξ, ξ⟫_ℂ
  rw [← inner_conj_symm (S ξ) ξ, ← inner_conj_symm (T ξ) ξ, h ξ]

end TauCeti
