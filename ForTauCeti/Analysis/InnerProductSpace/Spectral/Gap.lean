/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace

/-!
# Finite-dimensional spectral-gap predicates

The native point-spectrum predicates live in `Module.End`. This module
records the two-sided form bound and the two orientations of an ordered
internal gap used by the Davis–Kahan theorems.

The original source was `DavisKahan/FiniteDimensional/Core/SpectralGap.lean`.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
/-- Ordered quadratic-form separation between the two blocks of `A`.

The selected block `U` lies above `b`, while its orthogonal complement lies
below `a`.  Together with `a < b`, this is the sharp constant-one hypothesis
used by the finite-dimensional `sin (2 Θ)` theorem. -/
@[expose]
def TwoBlockFormGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E)
    (a b : ℝ) : Prop :=
  (∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜) ∧
    (∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)

/-- Ordered separation of the two diagonal blocks of `A`, in either
orientation.  This stronger predicate is useful when reducing a double-angle
argument to the elementary ordered Sylvester theorem. -/
def OrderedInternalGap (A : E →ₗ[𝕜] E) (U : Submodule 𝕜 E) (δ : ℝ) : Prop :=
  Module.End.PointOrderedGap A U A Uᗮ δ ∨ Module.End.PointOrderedGap A Uᗮ A U δ

omit [FiniteDimensional 𝕜 E] in
/-- Spectral inclusion on opposite sides of a cut gives the corresponding
ordered internal gap. -/
theorem orderedInternalGap_of_pointSpectrumIn_Iic_Ici
    {A : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} {a b : ℝ}
    (hUa : Module.End.PointSpectrumIn A U (Set.Iic a))
    (hUb : Module.End.PointSpectrumIn A Uᗮ (Set.Ici b)) :
    OrderedInternalGap A U (b - a) := by
  left
  exact Module.End.PointOrderedGap.of_pointSpectrumIn hUa (by
    rw [show a + (b - a) = b by ring]
    exact hUb)

omit [FiniteDimensional 𝕜 E] in
/-- Ordered separation in either direction gives an internal point-spectrum gap. -/
theorem OrderedInternalGap.pointInternalGap {A : E →ₗ[𝕜] E}
    {U : Submodule 𝕜 E} {δ : ℝ} (_hδ : 0 ≤ δ)
    (h : OrderedInternalGap A U δ) (hU : (U ∈ Module.End.invtSubmodule A)) :
    Module.End.PointInternalGap A U δ := by
  refine ⟨(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem A).mp hU, ?_⟩
  rcases h with hlow | hhigh
  · exact hlow.pointSpectraSeparated
  · exact hhigh.pointSpectraSeparated.symm

end TauCeti
