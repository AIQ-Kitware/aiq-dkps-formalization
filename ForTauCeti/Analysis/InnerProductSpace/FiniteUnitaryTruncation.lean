/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.FiniteUnitaryRestriction
public import ForTauCeti.Analysis.OperatorIdeal.Family.UnitaryTransport
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# Finite-rank unitary truncations without increasing ideal costs

Keep a unitary on a finite invariant subspace and replace it by the
identity on the orthogonal complement. The result is unitary and its
displacement is the original displacement composed with an orthogonal
projection. Hence every accepted operator-ideal gauge decreases.

## Provenance

Classical finite invariant-subspace restriction and orthogonal sums,
implemented here for the DKPS infinite-dimensional transport argument.
The ambient Hilbert space need not be separable or finite-dimensional.
-/

public section

noncomputable section

namespace TauCeti

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Truncating a unitary to any finite invariant subspace preserves
unitarity, has finite-rank displacement, and decreases every ideal gauge.
The operator-norm error is bounded by the discarded restriction. -/
theorem exists_finite_unitary_truncation
    (U : E ≃ₗᵢ[𝕜] E) (M : Submodule 𝕜 E) [FiniteDimensional 𝕜 M]
    (hUM : ∀ x ∈ M, U x ∈ M) :
    ∃ V : E ≃ₗᵢ[𝕜] E,
      (∀ x ∈ M, V x = U x) ∧ (∀ x ∈ Mᗮ, V x = x) ∧
      (1 - (V : E →L[𝕜] E) = (1 - (U : E →L[𝕜] E)) ∘L M.starProjection) ∧
      (1 - (V : E →L[𝕜] E)).rank ≤ Module.finrank 𝕜 M ∧
      ‖(V : E →L[𝕜] E) - (U : E →L[𝕜] E)‖ ≤
        ‖((U : E →L[𝕜] E) - 1) ∘L Mᗮ.subtypeL‖ ∧
      ∀ Φ : OperatorIdealFamily.{u, v, v} 𝕜,
        Φ.gauge (1 - (V : E →L[𝕜] E)) ≤ Φ.gauge (1 - (U : E →L[𝕜] E)) := by
  obtain ⟨UM, hUM', _, _⟩ := U.exists_restriction_of_finite_invariant M hUM
  obtain ⟨V, hVM, hVperp⟩ := M.exists_unitary_orthogonal_sum UM (LinearIsometryEquiv.refl 𝕜 Mᗮ)
  have hV (x : E) : V x = U (M.starProjection x) + Mᗮ.starProjection x := by
    calc
      _ = V (M.starProjection x + Mᗮ.starProjection x) :=
        congrArg V (M.starProjection_add_starProjection_orthogonal x).symm
      _ = V (M.starProjection x) + V (Mᗮ.starProjection x) := map_add V _ _
      _ = _ := congrArg₂ (· + ·)
        ((hVM ⟨_, M.starProjection_apply_mem x⟩).trans (hUM' _))
        (hVperp ⟨_, Mᗮ.starProjection_apply_mem x⟩)
  have hfactor : 1 - (V : E →L[𝕜] E) =
      (1 - (U : E →L[𝕜] E)) ∘L M.starProjection := by
    ext x
    change x - V x = M.starProjection x - U (M.starProjection x)
    rw [hV]
    calc
      _ = (M.starProjection x + Mᗮ.starProjection x) -
          (U (M.starProjection x) + Mᗮ.starProjection x) :=
        congrArg (fun y => y - (U (M.starProjection x) + Mᗮ.starProjection x))
          (M.starProjection_add_starProjection_orthogonal x).symm
      _ = _ := by abel
  have herror (x : E) : V x - U x =
      -(U (Mᗮ.starProjection x) - Mᗮ.starProjection x) := by
    rw [hV]
    conv_lhs => arg 2; rw [← M.starProjection_add_starProjection_orthogonal x, map_add]
    abel
  refine ⟨V, fun x hx => (hVM ⟨x, hx⟩).trans (hUM' _),
    fun x hx => hVperp ⟨x, hx⟩, hfactor, ?_, ?_, ?_⟩
  · rw [hfactor]
    exact (1 - (U : E →L[𝕜] E)).rank_comp_starProjection_le
      (by rw [← Module.finrank_eq_rank])
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖V x - U x‖ ≤ _
    rw [herror, norm_neg]
    have h := (((U : E →L[𝕜] E) - 1) ∘L Mᗮ.subtypeL).le_opNorm
      ⟨Mᗮ.starProjection x, Mᗮ.starProjection_apply_mem x⟩
    calc
      _ ≤ _ := h
      _ ≤ _ := mul_le_mul_of_nonneg_left (Mᗮ.norm_starProjection_apply_le x) (norm_nonneg _)
  · intro Φ
    rw [hfactor]
    exact Φ.gauge_comp_right_le_self _ M.starProjection_norm_le

end TauCeti
