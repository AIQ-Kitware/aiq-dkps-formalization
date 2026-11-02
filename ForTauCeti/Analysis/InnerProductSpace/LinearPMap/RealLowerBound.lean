/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent

/-!
# Coercivity against a bounded isometry

Coercivity of `J (A - c)` gives a norm lower bound when `J` preserves norms.
The accepted self-adjoint shift criterion then supplies the canonical resolvent.
The norm estimate below remains a local reusable extension; inverse construction,
closed range, and dense range are owned by TauCeti.
-/

public section

open _root_.LinearPMap (resolventSet)

open scoped InnerProductSpace

namespace TauCeti
namespace LinearPMap

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {A : E →ₗ.[𝕜] E} {z : 𝕜} {c : ℝ}

omit [CompleteSpace E] in
/-- **A norm lower bound follows from coercivity against a bounded isometry.**

`J` need not be a reflection here -- norm preservation is all that is used. -/
theorem norm_sub_smul_ge_of_coercive_comp
    {J : E →L[𝕜] E} (hJ : ∀ y : E, ‖J y‖ = ‖y‖)
    {c δ : ℝ}
    (hcoer : ∀ x : A.domain,
      δ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪J (A x - (c : 𝕜) • (x : E)), (x : E)⟫_𝕜)
    (x : A.domain) :
    δ * ‖(x : E)‖ ≤ ‖A x - (c : 𝕜) • (x : E)‖ := by
  have hcs : RCLike.re (⟪J (A x - (c : 𝕜) • (x : E)), (x : E)⟫_𝕜)
      ≤ ‖A x - (c : 𝕜) • (x : E)‖ * ‖(x : E)‖ := by
    refine le_trans (RCLike.re_le_norm (K := 𝕜) _) ?_
    refine le_trans (norm_inner_le_norm _ _) ?_
    rw [hJ]
  have hb := hcoer x
  rcases eq_or_lt_of_le (norm_nonneg ((x : E))) with h0 | h0
  · rw [← h0, mul_zero]
    exact norm_nonneg _
  · nlinarith

/-- **A real point is a resolvent point when the shifted operator is coercive
against a bounded isometry.**

The unbounded companion of `TauCeti.isUnit_of_coercive`: where that concludes
invertibility of a bounded `J (A - c)` from its quadratic form, this concludes
that `c` lies in the resolvent set of a self-adjoint partial map `A`, which is
the same statement for an operator that is not everywhere defined. -/
theorem mem_resolventSet_of_coercive_comp (hA : IsSelfAdjoint A)
    {J : E →L[𝕜] E} (hJ : ∀ y : E, ‖J y‖ = ‖y‖)
    {c δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ x : A.domain,
      δ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪J (A x - (c : 𝕜) • (x : E)), (x : E)⟫_𝕜) :
    ((c : ℝ) : 𝕜) ∈ resolventSet A :=
  hA.mem_resolventSet_of_norm_le hδ (fun x => by
    rw [norm_sub_rev]
    exact norm_sub_smul_ge_of_coercive_comp hJ hcoer x)

end LinearPMap
end TauCeti
