/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CompactUnitaryApproximation
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenConvergence

/-!
# Schatten-norm approximation of restricted unitaries

Every Schatten perturbation of identity in the unitary group is a
Schatten-norm limit of finite-rank unitary perturbations. One sequence
preserves every bounded operator commuting with the original unitary and
never increases any operator-ideal displacement gauge. The proof combines
compact spectral truncation with singular-value dominated convergence.

## Provenance

Classical trace-ideal approximation, implemented here as the analytic
step in the DKPS infinite-dimensional transport proof. All Schatten
gauges are the accepted Tau Ceti families. No dimension, separability or
previous unitary-density assumption is imposed.
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped Topology ENNReal

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- Finite-rank unitary corrections are dense in the Schatten restricted
unitary group, even inside every commutant of the original unitary.
Every operator-ideal displacement gauge decreases along the sequence. -/
theorem exists_schatten_finite_unitary_approximation_sequence
    (p : ℝ) (hp : 1 ≤ p) (U : E ≃ₗᵢ[𝕜] E)
    (hU : (OperatorIdealFamily.schatten 𝕜 p hp).gauge
      ((U : E →L[𝕜] E) - 1) ≠ ∞) :
    ∃ V : ℕ → E ≃ₗᵢ[𝕜] E, ∃ N : ℕ → ℕ,
      (∀ n, (1 - (V n : E →L[𝕜] E)).rank ≤ N n) ∧
      Tendsto (fun n => (V n : E →L[𝕜] E)) atTop (𝓝 (U : E →L[𝕜] E)) ∧
      Tendsto (fun n => (OperatorIdealFamily.schatten 𝕜 p hp).gauge
        ((V n : E →L[𝕜] E) - (U : E →L[𝕜] E))) atTop (𝓝 0) ∧
      (∀ n (Φ : OperatorIdealFamily.{u, v, v} 𝕜),
        Φ.gauge (1 - (V n : E →L[𝕜] E)) ≤ Φ.gauge (1 - (U : E →L[𝕜] E))) ∧
      ∀ n (B : E →L[𝕜] E), Commute (U : E →L[𝕜] E) B → Commute (V n : E →L[𝕜] E) B := by
  have hcompact := OperatorIdealFamily.isCompactOperator_of_gauge_schatten_ne_top p hp
    (((U : E →L[𝕜] E) - 1) : E →L[𝕜] E) hU
  obtain ⟨V, N, hN, hlim, hdom, hcost, _, hcomm⟩ :=
    exists_finite_unitary_approximation_sequence U hcompact
  refine ⟨V, N, hN, hlim, ?_, hcost, hcomm⟩
  apply OperatorIdealFamily.tendsto_gauge_schatten_zero_of_singularValue_le
    p hp (((U : E →L[𝕜] E) - 1) : E →L[𝕜] E) hU _ _ hdom
  simpa only [sub_self] using hlim.sub_const (U : E →L[𝕜] E)

end TauCeti
