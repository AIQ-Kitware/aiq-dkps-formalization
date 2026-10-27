/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReplaceFiniteTransport
public import ForTauCeti.Analysis.OperatorIdeal.ReducingTrace

/-!
# Actual finite restrictions of Hilbert-space Charbonnier minimizers

Every finite source-reducing sector invariant under a finite-cost global
minimizer carries a global minimizer of the actual restricted pair.
Exact cost additivity allows cancellation of the unchanged finite-cost
tail. The finiteness hypothesis is essential to this cancellation.
-/

public section

noncomputable section

namespace TauCeti

open scoped ENNReal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- Finite-cost global optimality descends to every actual reducing
sector, including an infinite-dimensional one. Competitors on that
sector extend with exactly the original complementary action. -/
theorem exists_charbonnier_minimizing_reducing_restriction
    (tau : ℝ) (hτ : 0 < tau)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] [CompleteSpace M]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hUM : M.IsReducing U.toLinearMap) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = U x) ∧
      (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
      ∀ W : M ≃ₗᵢ[𝕜] M,
        (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
        (1 - (V : M →L[𝕜] M)).charbonnierCost tau ≤
          (1 - (W : M →L[𝕜] M)).charbonnierCost tau := by
  let := K.hasOrthogonalProjection_comap_subtype_of_complete M
  let := L.hasOrthogonalProjection_comap_subtype_of_complete M
  obtain ⟨V, hV, _⟩ := U.exists_restriction_of_reducing M hUM
  have hlocal := K.map_comap_subtype_of_isometry_restriction L M U V hmap hV
  have hsplit := ContinuousLinearMap.charbonnierCost_unitary_displacement_eq_block_add_tail
    tau hτ M U U V (fun x => (hV x).symm) (fun _ _ => rfl)
  have htail : (Mᗮ.orthogonalProjectionOnto ∘L
      (1 - (U : E →L[𝕜] E)) ∘L Mᗮ.subtypeL).charbonnierCost tau ≠ ∞ := by
    rw [hsplit] at hfinite
    exact (ENNReal.add_ne_top.mp hfinite).2
  refine ⟨V, hV, hlocal, ?_⟩
  intro W hW
  obtain ⟨T, hTmap, hTM, hTtail⟩ :=
    K.exists_transport_replacing_reducing_block L M hK U hmap hUM W hW
  have hsplitT := ContinuousLinearMap.charbonnierCost_unitary_displacement_eq_block_add_tail
    tau hτ M T U W hTM hTtail
  have hle := hmin T hTmap
  rw [hsplit, hsplitT] at hle
  exact (ENNReal.add_le_add_iff_right htail).mp hle

/-- Global finite-cost Charbonnier optimality descends to every actual
finite reducing sector. Neither ambient finite dimension nor a
prescribed block form of the competing ambient transports is assumed. -/
theorem exists_charbonnier_minimizing_finite_restriction
    (tau : ℝ) (hτ : 0 < tau)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 M]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (1 - (U : E →L[𝕜] E)).charbonnierCost tau ≤
        (1 - (T : E →L[𝕜] E)).charbonnierCost tau)
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hUM : ∀ x ∈ M, U x ∈ M) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = U x) ∧
      (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
      ∀ W : M ≃ₗᵢ[𝕜] M,
        (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
        (1 - (V : M →L[𝕜] M)).charbonnierCost tau ≤
          (1 - (W : M →L[𝕜] M)).charbonnierCost tau := by
  obtain ⟨_, _, _, hred⟩ := U.exists_restriction_of_finite_invariant M hUM
  exact exists_charbonnier_minimizing_reducing_restriction tau hτ K L M U hmap hfinite hmin hK hred


end TauCeti
