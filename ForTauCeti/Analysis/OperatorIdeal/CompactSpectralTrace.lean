/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.CompactApproximationEigenvalues
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Compact
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Spectral penalty sums by positive-eigenvalue multiplicity

For a compact positive operator, every zero-preserving nonnegative
singular-value penalty is its sum over positive eigenvalues weighted
by eigenspace dimension. Zero padding and infinite-dimensional kernels
contribute exactly zero. No monotonicity, continuity, summability,
separability or ambient eigenbasis hypothesis is imposed on the penalty.

This classical counting identity supports additive infinite-dimensional
spectral costs; the compactness assumption prevents hidden lower entries
in generalized noncompact decreasing merges.
-/

public section

noncomputable section

namespace ContinuousLinearMap

open Filter TauCeti
open scoped ENNReal NNReal Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The indices at a positive singular value of a compact map form a
finite set, including when the ambient Hilbert dimension is arbitrary. -/
theorem finite_singularValue_level (A : E →L[𝕜] E) (hAc : IsCompactOperator A)
    (mu : ℝ≥0) (hmu : 0 < mu) : {n : ℕ | A.singularValue n = mu}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((tendsto_order.mp hAc.tendsto_singularValue).2 mu hmu)
  apply (Finset.range N).finite_toSet.subset
  intro n hn
  apply Finset.mem_range.mpr
  by_contra hnN
  have h := hN n (Nat.le_of_not_gt hnN)
  rw [hn] at h
  exact (lt_irrefl mu) h

/-- **Compact spectral trace formula.** Every nonnegative penalty
vanishing at zero can be summed using positive-eigenspace multiplicities.
The equality includes infinite spectral sums and infinite kernels. -/
theorem tsum_singularValue_penalty_eq_tsum_eigenspace
    (A : E →L[𝕜] E) (hAc : IsCompactOperator A) (hA : A.IsPositive)
    (f : ℝ≥0 → ℝ≥0∞) (hf : f 0 = 0) :
    (∑' n, f (A.singularValue n)) = ∑' mu : ℝ≥0,
      (Module.finrank 𝕜 (Module.End.eigenspace A.toLinearMap ((mu : ℝ) : 𝕜)) : ℝ≥0∞) *
        f mu := by
  classical
  rw [← ENNReal.tsum_fiberwise (fun n => f (A.singularValue n)) A.singularValue]
  apply tsum_congr
  intro mu
  have hconst : (∑' n : A.singularValue ⁻¹' {mu}, f (A.singularValue n)) =
      ∑' _n : A.singularValue ⁻¹' {mu}, f mu := by
    apply tsum_congr
    intro n
    exact congrArg f n.property
  rw [hconst]
  by_cases hzero : mu = 0
  · simp [hzero, hf]
  have hmu : 0 < mu := pos_iff_ne_zero.mpr hzero
  have hfinite := A.finite_singularValue_level hAc mu hmu
  let : Fintype (A.singularValue ⁻¹' {mu}) := hfinite.fintype
  have hcard := finrank_eigenspace_eq_card_approximationNumber_eq hAc hA.isSelfAdjoint
    hA.re_inner_nonneg_left (show 0 < (mu : ℝ) by exact_mod_cast hmu)
  have hequiv : {n : ℕ // A.approximationNumber n = (mu : ℝ)} ≃
      (A.singularValue ⁻¹' {mu}) :=
    Equiv.subtypeEquivRight fun n => by
      simp only [approximationNumber_eq_singularValue_toReal, Set.mem_preimage,
        Set.mem_singleton_iff, NNReal.coe_inj]
  rw [Nat.card_congr hequiv] at hcard
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, ← hcard]

end ContinuousLinearMap
