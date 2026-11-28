/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Inverse
public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Tactic

/-!
# Compact resolvents and compact graph embeddings

The Section 9 analytic interface currently states compactness sequentially:
graph-bounded sequences in the free-beam domain have ambiently Cauchy
subsequences.  A variational construction instead produces a compact bounded
solution operator `R`, whose inverse is the shifted beam operator.

This file relates the sequential graph condition to `IsCompactOperator R`
in both directions.
-/

public section

open scoped InnerProductSpace
open Set Filter Topology

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Abstract

noncomputable section

universe u

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- Sequential compactness of the ambient embedding of a closed-operator graph
 domain.  This matches the shape used by `SobolevTraceFoundation.graph_compact`.
-/
@[expose] def SequentiallyCompactGraphEmbedding
    (A : H →ₗ.[𝕜] H) : Prop :=
  ∀ x : ℕ → A.domain,
    (∃ C : ℝ, ∀ n,
      ‖(x n : H)‖ ^ 2 + ‖A (x n)‖ ^ 2 ≤ C) →
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      CauchySeq (fun n => ((x (phi n) : A.domain) : H))

omit [CompleteSpace H] in
/-- A sum-of-squares graph bound gives a uniform bound on operator values. -/
theorem operator_values_bounded_of_graph_bound
    (A : H →ₗ.[𝕜] H)
    (x : ℕ → A.domain) {C : ℝ}
    (hC : ∀ n,
      ‖(x n : H)‖ ^ 2 + ‖A (x n)‖ ^ 2 ≤ C) :
    ∀ n, ‖A (x n)‖ ≤ Real.sqrt (max C 0) := by
  intro n
  have hsquare : ‖A (x n)‖ ^ 2 ≤ max C 0 := by
    have hnonneg : 0 ≤ ‖(x n : H)‖ ^ 2 := sq_nonneg _
    have hle : ‖A (x n)‖ ^ 2 ≤ C := by
      linarith [hC n]
    exact hle.trans (le_max_left _ _)
  exact Real.le_sqrt_of_sq_le hsquare

omit [CompleteSpace H] in
/-- A sum-of-squares graph bound gives a uniform bound on ambient values. -/
theorem ambient_values_bounded_of_graph_bound
    (A : H →ₗ.[𝕜] H)
    (x : ℕ → A.domain) {C : ℝ}
    (hC : ∀ n,
      ‖(x n : H)‖ ^ 2 + ‖A (x n)‖ ^ 2 ≤ C) :
    ∀ n, ‖(x n : H)‖ ≤ Real.sqrt (max C 0) := by
  intro n
  have hsquare : ‖(x n : H)‖ ^ 2 ≤ max C 0 := by
    have hnonneg : 0 ≤ ‖A (x n)‖ ^ 2 := sq_nonneg _
    have hle : ‖(x n : H)‖ ^ 2 ≤ C := by
      linarith [hC n]
    exact hle.trans (le_max_left _ _)
  exact Real.le_sqrt_of_sq_le hsquare

omit [CompleteSpace H] in
/-- Compactness of a bounded resolvent implies compactness of the ambient
 embedding of its inverse graph domain. -/
theorem inverse_graph_embedding_compact
    (R : H →L[𝕜] H)
    (hinj : Function.Injective R)
    (hcompact : IsCompactOperator R) :
    SequentiallyCompactGraphEmbedding (R.toLinearMap.toPMap ⊤).inverse := by
  intro x hx
  obtain ⟨C, hC⟩ := hx
  let y : ℕ → H := fun n =>
    (R.toLinearMap.toPMap ⊤).inverse (x n)
  have hybounded : ∃ D : ℝ, ∀ n, ‖y n‖ ≤ D := by
    refine ⟨Real.sqrt (max C 0), ?_⟩
    exact operator_values_bounded_of_graph_bound
      (R.toLinearMap.toPMap ⊤).inverse x hC
  obtain ⟨C', hC'⟩ := hybounded
  obtain ⟨v, phi, hphi, hv⟩ := hcompact.exists_subseq_tendsto hC'
  have hcauchy := hv.cauchySeq
  change CauchySeq (fun n => R (y (phi n))) at hcauchy
  refine ⟨phi, hphi, ?_⟩
  have heq : (fun n => R (y (phi n))) =
      fun n => ((x (phi n) : (R.toLinearMap.toPMap ⊤).inverse.domain) : H) := by
    funext n
    exact R.apply_inverse_toPMap_top hinj (x (phi n))
  rwa [heq] at hcauchy

omit [CompleteSpace H] in
/-- A uniform bound on `y` gives a graph bound for the inverse-domain sequence
 `R y`. -/
theorem graph_bound_of_bounded_preimage
    (R : H →L[𝕜] H)
    (hinj : Function.Injective R)
    (y : ℕ → H) {C : ℝ} (hC : ∀ n, ‖y n‖ ≤ C) :
    ∀ n,
      ‖((⟨R (y n), R.apply_mem_domain_inverse_toPMap_top (y n)⟩ :
          (R.toLinearMap.toPMap ⊤).inverse.domain) : H)‖ ^ 2 +
        ‖(R.toLinearMap.toPMap ⊤).inverse
          ⟨R (y n), R.apply_mem_domain_inverse_toPMap_top (y n)⟩‖ ^ 2
      ≤ (‖R‖ ^ 2 + 1) * max C 0 ^ 2 := by
  intro n
  have hCn : ‖y n‖ ≤ max C 0 :=
    (hC n).trans (le_max_left _ _)
  have hRyn : ‖R (y n)‖ ≤ ‖R‖ * max C 0 :=
    (R.le_opNorm (y n)).trans
      (mul_le_mul_of_nonneg_left hCn (norm_nonneg R))
  rw [R.inverse_toPMap_top_apply hinj]
  change ‖R (y n)‖ ^ 2 + ‖y n‖ ^ 2 ≤
    (‖R‖ ^ 2 + 1) * max C 0 ^ 2
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have hR0 : 0 ≤ ‖R‖ := norm_nonneg _
  have hRyn_sq : ‖R (y n)‖ ^ 2 ≤ (‖R‖ * max C 0) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR0 hC0)).2 hRyn
  have hyn_sq : ‖y n‖ ^ 2 ≤ max C 0 ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hC0).2 hCn
  calc
    ‖R (y n)‖ ^ 2 + ‖y n‖ ^ 2
        ≤ (‖R‖ * max C 0) ^ 2 + max C 0 ^ 2 :=
      add_le_add hRyn_sq hyn_sq
    _ = (‖R‖ ^ 2 + 1) * max C 0 ^ 2 := by ring

/-- Compactness of the inverse graph embedding makes the bounded operator compact. -/
theorem compact_of_inverse_graph_embedding_compact
    (R : H →L[𝕜] H) (hinj : Function.Injective R)
    (hgraph : SequentiallyCompactGraphEmbedding (R.toLinearMap.toPMap ⊤).inverse) :
    IsCompactOperator R := by
  apply (isCompactOperator_iff_totallyBounded_image_closedBall R.toLinearMap zero_lt_one).2
  intro U hU
  -- Use the separated-sequence argument from Mathlib's `IsSeqCompact.totallyBounded`.
  by_contra! h
  obtain ⟨v, hv, hsep⟩ :
      ∃ v : ℕ → H, (∀ n, v n ∈ R.toLinearMap '' Metric.closedBall 0 1) ∧
        ∀ n m, m < n → v n ∉ SetRel.ball U (v m) := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and] using! seq_of_forall_finite_exists h
  choose y hy hRy using hv
  let x : ℕ → (R.toLinearMap.toPMap ⊤).inverse.domain := fun n =>
    ⟨R (y n), R.apply_mem_domain_inverse_toPMap_top (y n)⟩
  have hy' (n : ℕ) : ‖y n‖ ≤ 1 := mem_closedBall_zero_iff.mp (hy n)
  obtain ⟨phi, hphi, hcauchy⟩ :=
    hgraph x ⟨(‖R‖ ^ 2 + 1) * max 1 0 ^ 2, graph_bound_of_bounded_preimage R hinj y hy'⟩
  have heq : (fun n => (x (phi n) : H)) = fun n => v (phi n) :=
    funext fun n => hRy (phi n)
  rw [heq] at hcauchy
  obtain ⟨N, hN⟩ := hcauchy.mem_entourage hU
  exact hsep (phi (N + 1)) (phi N) (hphi N.lt_succ_self) (hN (N + 1) N N.le_succ le_rfl)

/-- Compactness of the bounded operator is equivalent to sequential compactness
of the projection from its inverse graph. -/
theorem inverse_graph_compact_iff (R : H →L[𝕜] H) (hinj : Function.Injective R) :
    SequentiallyCompactGraphEmbedding (R.toLinearMap.toPMap ⊤).inverse ↔
      IsCompactOperator R :=
  ⟨compact_of_inverse_graph_embedding_compact R hinj, inverse_graph_embedding_compact R hinj⟩

end

end Abstract
end FreeBeam
end DavisKahan
end TauCeti
