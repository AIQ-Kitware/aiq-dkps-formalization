/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import TauCeti.Analysis.Normed.Operator.Compact.Eigenspace
public import ForTauCeti.Analysis.InnerProductSpace.FiniteTransportSupport

/-!
# Compact perturbations of the identity that are reflections

A self-adjoint unitary with compact displacement has finite-rank
displacement: its displacement range lies in the nonzero eigenspace
at `2`. This retains the negative reflection sector, rather than
incorrectly concluding that a zero phase gradient forces identity.
-/

public section

noncomputable section

namespace LinearIsometryEquiv

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- A compact-displacement reflection has finite-rank displacement.
The finite rank is not asserted to vanish. -/
theorem exists_rank_displacement_le_of_isSelfAdjoint
    (U : E ≃ₗᵢ[𝕜] E) (hself : IsSelfAdjoint (U : E →L[𝕜] E))
    (hc : IsCompactOperator ((1 : E →L[𝕜] E) - (U : E →L[𝕜] E))) :
    ∃ n : ℕ, (1 - U.toLinearMap).rank ≤ n := by
  have hs : (U.symm : E →L[𝕜] E) = (U : E →L[𝕜] E) :=
    U.adjoint_eq_symm.symm.trans hself.star_eq
  have hsq (x : E) : U (U x) = x := by
    have h := congrArg (fun A : E →L[𝕜] E => A (U x)) hs
    exact h.symm.trans (U.symm_apply_apply x)
  let T : E →L[𝕜] E := 1 - (U : E →L[𝕜] E)
  let N := Module.End.eigenspace T.toLinearMap (2 : 𝕜)
  let : FiniteDimensional 𝕜 N := hc.finiteDimensional_eigenspace (by norm_num : (2 : 𝕜) ≠ 0)
  have hle : (1 - U.toLinearMap).range ≤ N := by
    rintro _ ⟨x, rfl⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change (x - U x) - U (x - U x) = (2 : 𝕜) • (x - U x)
    rw [map_sub, hsq, two_smul]
    abel
  let : FiniteDimensional 𝕜 (1 - U.toLinearMap).range :=
    Submodule.finiteDimensional_of_le hle
  exact ⟨Module.finrank 𝕜 (1 - U.toLinearMap).range, by
    rw [Module.finrank_eq_rank]⟩

end LinearIsometryEquiv
