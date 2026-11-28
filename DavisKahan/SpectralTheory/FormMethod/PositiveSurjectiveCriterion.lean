/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking

The density proof comes from the free-beam adaptation of Adam Bornemann's
`Spectra.TomitaTakesaki.modularOp_isSelfAdjoint` in
`Spectra/Modular/TomitaTakesaki/VonNeumannTstarT.lean`, Spectra commit
`8dbaaf6728d1342ae16acf79fd7eef7c59b37e63` (Apache-2.0).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Tactic

/-! # Dense domain from positivity and surjectivity of the one-plus operator

The density argument applies to arbitrary nonnegative partial operators.
For formally self-adjoint operators, TauCeti proves self-adjointness directly
from surjectivity at a real shift.
-/

public section

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- Positivity and surjectivity of `A + 1` force density of the operator
 domain.  This is useful when a variational construction initially presents a
 domain but has not yet established density independently. -/
theorem dense_domain_of_nonnegative_one_add_surjective
    (A : H →ₗ.[𝕜] H)
    (hnonneg : ∀ x : A.domain,
      0 ≤ RCLike.re ⟪A x, (x : H)⟫_𝕜)
    (hsurj : ∀ h : H, ∃ x : A.domain, A x + (x : H) = h) :
    Dense (A.domain : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro h hh
  obtain ⟨g, hg⟩ := hsurj h
  have hortho : ⟪(g : H), h⟫_𝕜 = 0 :=
    (Submodule.mem_orthogonal _ h).1 hh (g : H) g.property
  rw [← hg, inner_add_right] at hortho
  have hpos : 0 ≤ RCLike.re ⟪(g : H), A g⟫_𝕜 := by
    rw [inner_re_symm]
    exact hnonneg g
  have hre : RCLike.re ⟪(g : H), A g⟫_𝕜 + ‖(g : H)‖ ^ 2 = 0 := by
    have hr := congrArg RCLike.re hortho
    rwa [map_add, map_zero, inner_self_eq_norm_sq] at hr
  have hg0 : (g : H) = 0 := by
    have hsq : ‖(g : H)‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖(g : H)‖]
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  have g_eq_zero : g = 0 := Subtype.ext hg0
  rw [← hg, g_eq_zero]
  simp

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
