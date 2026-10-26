/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Projection.ReplaceFiniteTransport
public import ForTauCeti.Analysis.OperatorIdeal.ReducingTrace

/-!
# Actual finite restrictions of Hilbert-space Schatten minimizers

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
theorem exists_schatten_minimizing_reducing_restriction
    (p : ℝ) (hp : 1 ≤ p)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] [CompleteSpace M]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten 𝕜 p hp).gauge
      (1 - (U : E →L[𝕜] E)) ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) ≤
        (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (T : E →L[𝕜] E)))
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hUM : M.IsReducing U.toLinearMap) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = U x) ∧
      (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
      ∀ W : M ≃ₗᵢ[𝕜] M,
        (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
        (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (V : M →L[𝕜] M)) ≤
          (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (W : M →L[𝕜] M)) := by
  let := K.hasOrthogonalProjection_comap_subtype_of_complete M
  let := L.hasOrthogonalProjection_comap_subtype_of_complete M
  let Φ := OperatorIdealFamily.schatten 𝕜 p hp
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  obtain ⟨V, hV, _⟩ := U.exists_restriction_of_reducing M hUM
  have hlocal := K.map_comap_subtype_of_isometry_restriction L M U V hmap hV
  have hsplit := ContinuousLinearMap.gauge_schatten_unitary_displacement_rpow_eq_block_add_tail
    p hp M U U V (fun x => (hV x).symm) (fun _ _ => rfl)
  have htail : Φ.gauge (Mᗮ.orthogonalProjectionOnto ∘L
      (1 - (U : E →L[𝕜] E)) ∘L Mᗮ.subtypeL) ^ p ≠ ∞ := by
    have hpow := ENNReal.rpow_ne_top_of_nonneg hp0.le hfinite
    rw [hsplit] at hpow
    exact (ENNReal.add_ne_top.mp hpow).2
  refine ⟨V, hV, hlocal, ?_⟩
  intro W hW
  obtain ⟨T, hTmap, hTM, hTtail⟩ :=
    K.exists_transport_replacing_reducing_block L M hK U hmap hUM W hW
  have hsplitT := ContinuousLinearMap.gauge_schatten_unitary_displacement_rpow_eq_block_add_tail
    p hp M T U W hTM hTtail
  have hle := ENNReal.rpow_le_rpow (hmin T hTmap) hp0.le
  rw [hsplit, hsplitT] at hle
  exact (ENNReal.rpow_le_rpow_iff hp0).mp
    ((ENNReal.add_le_add_iff_right htail).mp hle)

/-- Global finite-cost Schatten optimality descends to every actual
finite reducing sector. Neither ambient finite dimension nor a
prescribed block form of the competing ambient transports is assumed. -/
theorem exists_schatten_minimizing_finite_restriction
    (p : ℝ) (hp : 1 ≤ p)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 M]
    (U : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten 𝕜 p hp).gauge
      (1 - (U : E →L[𝕜] E)) ≠ ∞)
    (hmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) ≤
        (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (T : E →L[𝕜] E)))
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hUM : ∀ x ∈ M, U x ∈ M) :
    ∃ V : M ≃ₗᵢ[𝕜] M,
      (∀ x : M, (V x : E) = U x) ∧
      (K.comap M.subtype).map V.toLinearMap = L.comap M.subtype ∧
      ∀ W : M ≃ₗᵢ[𝕜] M,
        (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
        (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (V : M →L[𝕜] M)) ≤
          (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (W : M →L[𝕜] M)) := by
  obtain ⟨_, _, _, hred⟩ := U.exists_restriction_of_finite_invariant M hUM
  exact exists_schatten_minimizing_reducing_restriction p hp K L M U hmap hfinite hmin hK hred

/-- With the same complementary action as a global minimizing
reference, global optimality is equivalent to optimality of the actual
finite restriction. The tail may have infinite rank. -/
theorem schatten_minimal_iff_restriction_of_minimizing_reference_tail
    (p : ℝ) (hp : 1 ≤ p)
    (K L M : Submodule 𝕜 E) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    [FiniteDimensional 𝕜 M]
    (U R : E ≃ₗᵢ[𝕜] E) (hmap : K.map U.toLinearMap = L)
    (hRmap : K.map R.toLinearMap = L)
    (hfinite : (OperatorIdealFamily.schatten 𝕜 p hp).gauge
      (1 - (U : E →L[𝕜] E)) ≠ ∞)
    (hRmin : ∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (R : E →L[𝕜] E)) ≤
        (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (T : E →L[𝕜] E)))
    (hK : M.IsReducing K.starProjection.toLinearMap)
    (hRM : ∀ x ∈ M, R x ∈ M)
    (htail : ∀ x ∈ Mᗮ, U x = R x)
    (V : M ≃ₗᵢ[𝕜] M) (hV : ∀ x : M, (V x : E) = U x) :
    (∀ T : E ≃ₗᵢ[𝕜] E, K.map T.toLinearMap = L →
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (U : E →L[𝕜] E)) ≤
        (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (T : E →L[𝕜] E))) ↔
    (∀ W : M ≃ₗᵢ[𝕜] M,
      (K.comap M.subtype).map W.toLinearMap = L.comap M.subtype →
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (V : M →L[𝕜] M)) ≤
        (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (W : M →L[𝕜] M))) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  constructor
  · intro hmin
    obtain ⟨V', hV', _, hmin'⟩ := exists_schatten_minimizing_finite_restriction p hp K L M
      U hmap hfinite hmin hK (fun x hx => by rw [← hV ⟨x, hx⟩]; exact (V ⟨x, hx⟩).property)
    have heq : V' = V := by
      ext x
      exact (hV' x).trans (hV x).symm
    simpa only [heq] using hmin'
  · intro hmin T hT
    obtain ⟨W, hW, _, _⟩ := R.exists_restriction_of_finite_invariant M hRM
    have hWmap := K.map_comap_subtype_of_isometry_restriction L M R W hRmap hW
    have hUcost := ContinuousLinearMap.gauge_schatten_unitary_displacement_rpow_eq_block_add_tail
      p hp M U R V (fun x => (hV x).symm) htail
    have hRcost := ContinuousLinearMap.gauge_schatten_unitary_displacement_rpow_eq_block_add_tail
      p hp M R R W (fun x => (hW x).symm) (fun _ _ => rfl)
    have hle : (OperatorIdealFamily.schatten 𝕜 p hp).gauge
        (1 - (U : E →L[𝕜] E)) ^ p ≤
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge (1 - (R : E →L[𝕜] E)) ^ p := by
      rw [hUcost, hRcost]
      exact add_le_add (ENNReal.rpow_le_rpow (hmin W hWmap) hp0.le) le_rfl
    exact ((ENNReal.rpow_le_rpow_iff hp0).mp hle).trans (hRmin T hT)

end TauCeti
