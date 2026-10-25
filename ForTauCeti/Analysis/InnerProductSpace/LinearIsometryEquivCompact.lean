/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Compactness of finite-dimensional linear isometry equivalences

Use the accepted operator norm topology on linear isometry equivalences.
The finite-dimensional unitary group is compact. The space of isometric
identifications between two finite-dimensional Hilbert spaces is compact
as well, including when no identification exists.
-/

public section

noncomputable section

open scoped TauCeti.LinearIsometryEquivOperatorNorm

namespace LinearIsometryEquiv

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Inversion of an isometric identification is continuous even when its
domain and codomain are different Hilbert spaces. -/
theorem continuous_symm_operatorNorm :
    Continuous (fun e : E ≃ₗᵢ[𝕜] F => e.symm) := by
  apply continuous_operatorNorm_iff.mpr
  exact (ContinuousLinearMap.adjoint.continuous.comp
    isEmbedding_toContinuousLinearMap.continuous).congr fun e => e.adjoint_eq_symm

variable [FiniteDimensional 𝕜 E]

/-- The unitary group on a finite-dimensional Hilbert space is compact
in operator norm; the trivial Hilbert space is allowed. -/
theorem compactSpace_end_operatorNorm : CompactSpace (E ≃ₗᵢ[𝕜] E) := by
  let := FiniteDimensional.proper 𝕜 (E →L[𝕜] E)
  have hcompact : IsCompact (unitary (E →L[𝕜] E) : Set (E →L[𝕜] E)) := by
    apply (isCompact_closedBall (0 : E →L[𝕜] E) 1).of_isClosed_subset isClosed_unitary
    intro U hU
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply U.opNorm_le_bound zero_le_one
    intro x
    rw [one_mul, Unitary.norm_map ⟨U, hU⟩]
  let : CompactSpace (unitary (E →L[𝕜] E)) := isCompact_iff_compactSpace.mp hcompact
  have hc : Continuous (Unitary.linearIsometryEquiv (𝕜 := 𝕜) (H := E)) := by
    apply continuous_operatorNorm_iff.mpr
    exact continuous_subtype_val
  exact Function.Surjective.compactSpace hc Unitary.linearIsometryEquiv.surjective

omit [CompleteSpace F] in
/-- Isometric identifications between finite-dimensional Hilbert spaces
form a compact space. Unequal dimensions give the empty compact space. -/
theorem compactSpace_operatorNorm : CompactSpace (E ≃ₗᵢ[𝕜] F) := by
  classical
  rcases isEmpty_or_nonempty (E ≃ₗᵢ[𝕜] F) with h | h
  · infer_instance
  · let D := Classical.choice h
    let : CompactSpace (E ≃ₗᵢ[𝕜] E) := compactSpace_end_operatorNorm
    have hc : Continuous (fun A : E ≃ₗᵢ[𝕜] E => A.trans D) := by
      apply continuous_operatorNorm_iff_apply.mpr
      intro x
      exact D.continuous.comp (continuous_id.eval_const x)
    apply Function.Surjective.compactSpace hc
    intro B
    exact ⟨B.trans D.symm, by ext x; simp⟩

scoped[TauCeti.LinearIsometryEquivOperatorNorm] attribute [instance]
  LinearIsometryEquiv.compactSpace_operatorNorm

end LinearIsometryEquiv
