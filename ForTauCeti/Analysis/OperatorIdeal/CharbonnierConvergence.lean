/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import ForTauCeti.Analysis.OperatorIdeal.Charbonnier
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Charbonnier trace convergence with controlled singular-value tails

Operator-norm convergence alone does not preserve an infinite spectral
trace. A fixed Hilbert--Schmidt bound on every singular-value tail after
a fixed finite shift suffices. Finite-rank perturbation interlacing
supplies exactly this hypothesis for the unitary variation argument.
-/

public section

namespace ContinuousLinearMap

open Filter
open scoped ENNReal NNReal Topology

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜] {E : Type v} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A fixed finite shift in singular-value domination is enough for
norm limits to preserve the literal Charbonnier trace. The dominating
operator is native Hilbert--Schmidt; neither the operators nor the
ambient spaces need have finite rank or dimension. -/
theorem tendsto_charbonnierCost_of_singularValue_tail_le
    (tau : ℝ) (hτ : 0 < tau) (B : E →L[𝕜] F)
    (hB : (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge B ≠ ∞)
    {α : Type*} {l : Filter α} (T : α → E →L[𝕜] F) (A : E →L[𝕜] F)
    (hT : Tendsto T l (𝓝 A)) (r : ℕ)
    (hdom : ∀ n k, (T n).singularValue (k + r) ≤ B.singularValue k) :
    Tendsto (fun n => (T n).charbonnierCost tau) l (𝓝 (A.charbonnierCost tau)) := by
  rcases l.eq_or_neBot with rfl | _
  · exact tendsto_bot
  let f (S : E →L[𝕜] F) (k : ℕ) :=
    Real.sqrt (tau ^ 2 + (S.singularValue k : ℝ) ^ 2) - tau
  let b (k : ℕ) := (2 * tau)⁻¹ * (B.singularValue k : ℝ) ^ 2
  have hnonneg (S : E →L[𝕜] F) (k : ℕ) : 0 ≤ f S k :=
    sub_nonneg.mpr (Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (S.singularValue k : ℝ)]))
  have hcont (k : ℕ) : Continuous (fun S : E →L[𝕜] F => f S k) := by
    have hsv := NNReal.continuous_coe.comp (continuous_singularValue (𝕜 := 𝕜) (E := E) (F := F) k)
    exact (Real.continuous_sqrt.comp (continuous_const.add (hsv.pow 2))).sub continuous_const
  have hsumNN : Summable (fun k => B.singularValue k ^ (2 : ℝ)) := by
    apply (TauCeti.OperatorIdealFamily.mem_finiteSubmodule_schatten_iff 2 (by norm_num) B).mp
    simpa only [TauCeti.OperatorGauge.mem_finiteSubmodule,
      TauCeti.OperatorIdealFamily.operatorGauge_apply] using lt_top_iff_ne_top.mpr hB
  have hsum : Summable b := by
    have hs : Summable (fun k => (B.singularValue k : ℝ) ^ 2) := by
      simpa only [NNReal.coe_rpow, Real.rpow_two] using NNReal.summable_coe.mpr hsumNN
    exact hs.mul_left _
  have hbound (S : E →L[𝕜] F) (k : ℕ)
      (hs : S.singularValue (k + r) ≤ B.singularValue k) : ‖f S (k + r)‖ ≤ b k := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg S _)]
    have hsc : (S.singularValue (k + r) : ℝ) ≤ (B.singularValue k : ℝ) := hs
    have h := (TauCeti.charbonnier_quadratic_bounds tau (S.singularValue (k + r) : ℝ)
      (B.singularValue k : ℝ) hτ (NNReal.coe_nonneg _) hsc).2
    exact h.trans (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)).mpr hsc) (by positivity))
  have hdomA (k : ℕ) : A.singularValue (k + r) ≤ B.singularValue k :=
    le_of_tendsto ((continuous_singularValue (k + r)).tendsto A |>.comp hT)
      (Eventually.of_forall fun n => hdom n k)
  have hsumT (n : α) : Summable (fun k => f (T n) (k + r)) :=
    hsum.of_norm_bounded (fun k => hbound (T n) k (hdom n k))
  have hsumA : Summable (fun k => f A (k + r)) :=
    hsum.of_norm_bounded (fun k => hbound A k (hdomA k))
  have htail := tendsto_tsum_of_dominated_convergence hsum
    (fun k => (hcont (k + r)).tendsto A |>.comp hT)
    (Eventually.of_forall fun n k => hbound (T n) k (hdom n k))
  have htail' := (ENNReal.continuous_ofReal.tendsto _).comp htail
  have hvalueT (n : α) : ENNReal.ofReal (∑' k, f (T n) (k + r)) =
      ∑' k, ENNReal.ofReal (f (T n) (k + r)) :=
    ENNReal.ofReal_tsum_of_nonneg (fun k => hnonneg _ _) (hsumT n)
  have hvalueA : ENNReal.ofReal (∑' k, f A (k + r)) =
      ∑' k, ENNReal.ofReal (f A (k + r)) :=
    ENNReal.ofReal_tsum_of_nonneg (fun k => hnonneg _ _) hsumA
  change Tendsto (fun n => ENNReal.ofReal (∑' k, f (T n) (k + r))) l
    (𝓝 (ENNReal.ofReal (∑' k, f A (k + r)))) at htail'
  simp_rw [hvalueT, hvalueA] at htail'
  have hhead := tendsto_finsetSum (Finset.range r) (fun k _ =>
    ((ENNReal.continuous_ofReal.comp (hcont k)).tendsto A).comp hT)
  have h := hhead.add htail'
  have hsplit (S : E →L[𝕜] F) :
      (∑ k ∈ Finset.range r, ENNReal.ofReal (f S k)) +
        (∑' k, ENNReal.ofReal (f S (k + r))) = S.charbonnierCost tau :=
    (ENNReal.summable (f := fun k => ENNReal.ofReal (f S (k + r)))).sum_add_tsum_nat_add'
  change Tendsto (fun n => (∑ k ∈ Finset.range r, ENNReal.ofReal (f (T n) k)) +
    (∑' k, ENNReal.ofReal (f (T n) (k + r)))) l
    (𝓝 ((∑ k ∈ Finset.range r, ENNReal.ofReal (f A k)) +
      (∑' k, ENNReal.ofReal (f A (k + r))))) at h
  simpa only [hsplit] using h

/-- Rank-bounded perturbations of a singular-value-dominated family
preserve the Charbonnier trace in every operator-norm limit. The rank
bound is uniform; no bound on the perturbations' norms is needed. -/
theorem tendsto_charbonnierCost_of_bounded_rank_perturbation
    (tau : ℝ) (hτ : 0 < tau) (B : E →L[𝕜] F)
    (hB : (TauCeti.OperatorIdealFamily.schatten 𝕜 2 (by norm_num)).gauge B ≠ ∞)
    {α : Type*} {l : Filter α} (S C : α → E →L[𝕜] F) (A : E →L[𝕜] F)
    (hT : Tendsto (fun n => S n + C n) l (𝓝 A))
    (r : ℕ) (hC : ∀ n, (C n).rank ≤ r)
    (hdom : ∀ n k, (S n).singularValue k ≤ B.singularValue k) :
    Tendsto (fun n => (S n + C n).charbonnierCost tau) l (𝓝 (A.charbonnierCost tau)) := by
  apply tendsto_charbonnierCost_of_singularValue_tail_le tau hτ B hB _ A hT r
  intro n k
  calc
    _ ≤ (S n).singularValue k + (C n).singularValue r := singularValue_add_index_le _ _ _ _
    _ = (S n).singularValue k := by rw [singularValue_eq_zero_of_rank_le (hC n), add_zero]
    _ ≤ _ := hdom n k

end ContinuousLinearMap
