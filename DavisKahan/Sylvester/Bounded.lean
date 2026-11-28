/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Analysis.OperatorIdeal.OperatorNorm
public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import DavisKahan.OperatorIdeal.CanonicalRealView
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Bound/inverse Sylvester estimates

This module isolates the exact dimension-free form of Davis--Kahan Theorem 5.1.
The Neumann series is expressed using the ring inverse. Invertibility is a
hypothesis when the sum is shown to solve the equation.
-/

public section

namespace TauCeti
namespace DavisKahan
namespace Sylvester

open scoped InnerProductSpace

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] in
/-- Powers of a continuous endomorphism satisfy the expected operator-norm bound. -/
theorem opNorm_pow_le (T : E →L[𝕜] E) (n : ℕ) :
    ‖T ^ n‖ ≤ ‖T‖ ^ n := by
  induction n with
  | zero =>
      change ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1
      exact ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E)
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (ContinuousLinearMap.opNorm_comp_le (T ^ n) T).trans
        (mul_le_mul_of_nonneg_right ih (norm_nonneg T))

/-- The `n`th term in the Neumann construction for `A X - X B = C`. -/
noncomputable def sylvesterNeumannTerm
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) : F →L[𝕜] E :=
  (Ring.inverse A ^ (n + 1)) ∘L C ∘L (B ^ n)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The first Neumann term cancels the left block. -/
theorem comp_sylvesterNeumannTerm_zero
    {A : E →L[𝕜] E}
    (hA : IsUnit A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) :
    A ∘L sylvesterNeumannTerm A B C 0 = C := by
  unfold sylvesterNeumannTerm
  simp only [zero_add, pow_one, pow_zero]
  rw [← ContinuousLinearMap.comp_assoc A (Ring.inverse A)]
  rw [show A ∘L Ring.inverse A = ContinuousLinearMap.id 𝕜 E from
    Ring.mul_inverse_cancel A hA]
  change C ∘L ContinuousLinearMap.id 𝕜 F = C
  exact ContinuousLinearMap.comp_id C

omit [CompleteSpace E] [CompleteSpace F] in
/-- Consecutive Neumann terms telescope through the two diagonal blocks. -/
theorem comp_sylvesterNeumannTerm_succ
    {A : E →L[𝕜] E}
    (hA : IsUnit A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) :
    A ∘L sylvesterNeumannTerm A B C (n + 1) =
      sylvesterNeumannTerm A B C n ∘L B := by
  ext x
  change
    A ((Ring.inverse A ^ ((n + 1) + 1)) (C ((B ^ (n + 1)) x))) =
      (Ring.inverse A ^ (n + 1)) (C ((B ^ n) (B x)))
  rw [pow_succ' (Ring.inverse A) (n + 1), pow_succ B n]
  change
    A (Ring.inverse A ((Ring.inverse A ^ (n + 1)) (C ((B ^ n) (B x))))) =
      (Ring.inverse A ^ (n + 1)) (C ((B ^ n) (B x)))
  exact ContinuousLinearMap.apply_ringInverse_apply hA _

omit [CompleteSpace E] [CompleteSpace F] in
/-- Operator-norm geometric bound for one Neumann term. -/
theorem norm_sylvesterNeumannTerm_le
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) (n : ℕ) :
    ‖sylvesterNeumannTerm A B C n‖ ≤
      ‖Ring.inverse A‖ * ‖C‖ * (‖Ring.inverse A‖ * ‖B‖) ^ n := by
  change
    ‖((Ring.inverse A ^ (n + 1)) ∘L C) ∘L (B ^ n)‖ ≤
      ‖Ring.inverse A‖ * ‖C‖ * (‖Ring.inverse A‖ * ‖B‖) ^ n
  have hleft :
      ‖(Ring.inverse A ^ (n + 1)) ∘L C‖ ≤ ‖Ring.inverse A ^ (n + 1)‖ * ‖C‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  have houter :
      ‖((Ring.inverse A ^ (n + 1)) ∘L C) ∘L (B ^ n)‖ ≤
        ‖(Ring.inverse A ^ (n + 1)) ∘L C‖ * ‖B ^ n‖ :=
    ContinuousLinearMap.opNorm_comp_le _ _
  calc
    ‖((Ring.inverse A ^ (n + 1)) ∘L C) ∘L (B ^ n)‖
        ≤ ‖(Ring.inverse A ^ (n + 1)) ∘L C‖ * ‖B ^ n‖ := houter
    _ ≤ (‖Ring.inverse A ^ (n + 1)‖ * ‖C‖) * ‖B ^ n‖ :=
      mul_le_mul_of_nonneg_right hleft (norm_nonneg (B ^ n))
    _ ≤ (‖Ring.inverse A‖ ^ (n + 1) * ‖C‖) * ‖B‖ ^ n := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (opNorm_pow_le (Ring.inverse A) (n + 1))
          (norm_nonneg C))
        (opNorm_pow_le B n)
        (norm_nonneg (B ^ n))
        (mul_nonneg (pow_nonneg (norm_nonneg (Ring.inverse A)) _) (norm_nonneg C))
    _ = ‖Ring.inverse A‖ * ‖C‖ * (‖Ring.inverse A‖ * ‖B‖) ^ n := by
      rw [pow_succ', mul_pow]
      ring

/-- Each Neumann term belongs to the same rectangular ideal as `C`. -/
theorem sylvesterNeumannTerm_mem
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C) (n : ℕ) :
    N.Mem (sylvesterNeumannTerm A B C n) := by
  unfold sylvesterNeumannTerm
  exact N.comp_mem (Ring.inverse A ^ (n + 1)) (B ^ n) hC

/-- Geometric bound for one Neumann term. -/
theorem gauge_sylvesterNeumannTerm_le
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C) (n : ℕ) :
    N.gaugeReal (sylvesterNeumannTerm A B C n)
      ≤ ‖Ring.inverse A‖ ^ (n + 1) * N.gaugeReal C * ‖B‖ ^ n := by
  unfold sylvesterNeumannTerm
  have hcomp := N.gaugeReal_comp_le (Ring.inverse A ^ (n + 1)) (B ^ n) hC
  have hinv := opNorm_pow_le (Ring.inverse A) (n + 1)
  have hBpow := opNorm_pow_le B n
  have hgauge := N.gaugeReal_nonneg hC
  calc
    N.gaugeReal ((Ring.inverse A ^ (n + 1)) ∘L C ∘L (B ^ n))
        ≤ ‖Ring.inverse A ^ (n + 1)‖ * N.gaugeReal C * ‖B ^ n‖ := hcomp
    _ ≤ (‖Ring.inverse A‖ ^ (n + 1) * N.gaugeReal C) * ‖B ^ n‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hinv hgauge) (norm_nonneg (B ^ n))
    _ ≤ (‖Ring.inverse A‖ ^ (n + 1) * N.gaugeReal C) * ‖B‖ ^ n := by
      exact mul_le_mul_of_nonneg_left hBpow
        (mul_nonneg (pow_nonneg (norm_nonneg (Ring.inverse A)) _) hgauge)

omit [CompleteSpace F] in
/-- Operator-norm summability of the Neumann terms under the strict ratio. -/
theorem sylvesterNeumannTerm_summable
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E)
    (hratio : ‖Ring.inverse A‖ * ‖B‖ < 1) :
    Summable (fun n : ℕ => sylvesterNeumannTerm A B C n) := by
  let q : ℝ := ‖Ring.inverse A‖ * ‖B‖
  let g₀ : ℝ := ‖Ring.inverse A‖ * ‖C‖
  have hq0 : 0 ≤ q := mul_nonneg (norm_nonneg (Ring.inverse A)) (norm_nonneg B)
  have hmajor : Summable (fun n : ℕ => q ^ n * g₀) :=
    (summable_geometric_of_lt_one hq0 hratio).mul_right g₀
  refine Summable.of_norm_bounded hmajor (fun n => ?_)
  calc
    ‖sylvesterNeumannTerm A B C n‖
        ≤ ‖Ring.inverse A‖ * ‖C‖ * (‖Ring.inverse A‖ * ‖B‖) ^ n :=
      norm_sylvesterNeumannTerm_le A B C n
    _ = q ^ n * g₀ := by
      simp only [q, g₀]
      ring

/-- Ideal-norm Cauchy control for partial Neumann sums under the strict ratio. -/
theorem sylvesterNeumannPartialSum_cauchy
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C)
    (hratio : ‖Ring.inverse A‖ * ‖B‖ < 1) :
    ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n, M ≤ m → M ≤ n →
      N.gaugeReal
        ((∑ j ∈ Finset.range m, sylvesterNeumannTerm A B C j) -
         (∑ j ∈ Finset.range n, sylvesterNeumannTerm A B C j)) < ε := by
  let q : ℝ := ‖Ring.inverse A‖ * ‖B‖
  let g₀ : ℝ := ‖Ring.inverse A‖ * N.gaugeReal C
  let t : ℕ → F →L[𝕜] E := fun n => sylvesterNeumannTerm A B C n
  let P : ℕ → F →L[𝕜] E := fun n => ∑ j ∈ Finset.range n, t j
  let G : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, q ^ j * g₀
  have hq0 : 0 ≤ q := mul_nonneg (norm_nonneg (Ring.inverse A)) (norm_nonneg B)
  have htmem : ∀ n, N.Mem (t n) := fun n =>
    sylvesterNeumannTerm_mem N A B hC n
  have hPmem : ∀ n, N.Mem (P n) := by
    intro n
    exact N.finset_sum_mem (Finset.range n) t fun j _ => htmem j
  have htGauge : ∀ n, N.gaugeReal (t n) ≤ q ^ n * g₀ := by
    intro n
    calc
      N.gaugeReal (t n)
          ≤ ‖Ring.inverse A‖ ^ (n + 1) * N.gaugeReal C * ‖B‖ ^ n :=
        gauge_sylvesterNeumannTerm_le N A B hC n
      _ = q ^ n * g₀ := by
        simp only [q, g₀]
        rw [pow_succ', mul_pow]
        ring
  have hgap : ∀ {m n : ℕ}, n ≤ m →
      N.gaugeReal (P m - P n) ≤ G m - G n :=
    fun {_ _} hnm => N.gaugeReal_sum_range_sub_le htmem htGauge hnm
  have hGcauchy : CauchySeq G := by
    have hsummable : Summable (fun j : ℕ => q ^ j * g₀) :=
      (summable_geometric_of_lt_one hq0 hratio).mul_right g₀
    exact hsummable.hasSum.tendsto_sum_nat.cauchySeq
  have hPcauchy : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n, M ≤ m → M ≤ n →
      N.gaugeReal (P m - P n) < ε :=
    N.gaugeReal_sub_lt_of_cauchy_majorant hPmem hgap hGcauchy
  simpa only [P, t] using hPcauchy

/-- The ideal-norm limit of the Neumann series. -/
noncomputable def sylvesterNeumannSolution
    (_N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [_N.toOperatorIdealFamily.IsComplete]
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E) : F →L[𝕜] E :=
  ∑' n : ℕ, sylvesterNeumannTerm A B C n

/-- The selected Neumann solution belongs to the ideal. -/
theorem sylvesterNeumannSolution_mem
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    (A : E →L[𝕜] E) (B : F →L[𝕜] F)
    {C : F →L[𝕜] E} (hC : N.Mem C)
    (hratio : ‖Ring.inverse A‖ * ‖B‖ < 1) :
    N.Mem (sylvesterNeumannSolution N A B C) := by
  let t : ℕ → F →L[𝕜] E := fun n => sylvesterNeumannTerm A B C n
  let P : ℕ → F →L[𝕜] E := fun n => ∑ j ∈ Finset.range n, t j
  have htmem : ∀ n, N.Mem (t n) := fun n =>
    sylvesterNeumannTerm_mem N A B hC n
  have hPmem : ∀ n, N.Mem (P n) := by
    intro n
    exact N.finset_sum_mem (Finset.range n) t fun j _ => htmem j
  have hPcauchy : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n, M ≤ m → M ≤ n →
      N.gaugeReal (P m - P n) < ε := by
    simpa only [P, t] using
      sylvesterNeumannPartialSum_cauchy N A B hC hratio
  obtain ⟨L, hLmem, hLlim⟩ := N.gaugeReal_complete P hPmem hPcauchy
  have hPL : Filter.Tendsto P Filter.atTop (nhds L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => N.opNorm_le_gaugeReal (N.sub_mem (hPmem n) hLmem)) ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := hLlim ε hε
    refine ⟨M, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (N.gaugeReal_nonneg (N.sub_mem (hPmem n) hLmem))]
    exact hM n hn
  have hsum : Summable t := by
    simpa only [t] using sylvesterNeumannTerm_summable A B C hratio
  have hPS : Filter.Tendsto P Filter.atTop
      (nhds (sylvesterNeumannSolution N A B C)) := by
    simpa only [P, t, sylvesterNeumannSolution] using
      hsum.hasSum.tendsto_sum_nat
  have hEq : L = sylvesterNeumannSolution N A B C :=
    tendsto_nhds_unique hPL hPS
  rw [← hEq]
  exact hLmem

omit [CompleteSpace F] in
/-- The Neumann solution satisfies the Sylvester equation. -/
theorem sylvesterNeumannSolution_eq
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →L[𝕜] E}
    (hA : IsUnit A) (B : F →L[𝕜] F)
    (C : F →L[𝕜] E)
    (hratio : ‖Ring.inverse A‖ * ‖B‖ < 1) :
    A ∘L sylvesterNeumannSolution N A B C -
      sylvesterNeumannSolution N A B C ∘L B = C := by
  let t : ℕ → F →L[𝕜] E := fun n => sylvesterNeumannTerm A B C n
  let P : ℕ → F →L[𝕜] E := fun n => ∑ j ∈ Finset.range n, t j
  let S : F →L[𝕜] E := sylvesterNeumannSolution N A B C
  have hsum : Summable t := by
    simpa only [t] using sylvesterNeumannTerm_summable A B C hratio
  have hP : Filter.Tendsto P Filter.atTop (nhds S) := by
    simpa only [P, t, S, sylvesterNeumannSolution] using
      hsum.hasSum.tendsto_sum_nat
  have hPshift : Filter.Tendsto (fun n : ℕ => P (n + 1))
      Filter.atTop (nhds S) :=
    hP.comp (Filter.tendsto_add_atTop_nat 1)
  have hstep : ∀ n : ℕ, A ∘L t (n + 1) = t n ∘L B := fun n => by
    simpa only [t] using comp_sylvesterNeumannTerm_succ hA B C n
  have hfinite : ∀ n : ℕ,
      A ∘L P (n + 1) - P (n + 1) ∘L B = C - t n ∘L B := by
    intro n
    induction n with
    | zero =>
        have hP1 : P (0 + 1) = t 0 := by
          simp only [P, zero_add, Finset.sum_range_one]
        rw [hP1, comp_sylvesterNeumannTerm_zero hA B C]
    | succ n ih =>
        have hPsucc : P (n + 1 + 1) = P (n + 1) + t (n + 1) :=
          Finset.sum_range_succ t (n + 1)
        have hexpand :
            A ∘L P (n + 1 + 1) - P (n + 1 + 1) ∘L B =
              (A ∘L P (n + 1) - P (n + 1) ∘L B) +
                (A ∘L t (n + 1) - t (n + 1) ∘L B) := by
          rw [hPsucc, ContinuousLinearMap.comp_add,
            ContinuousLinearMap.add_comp]
          abel
        rw [hexpand, ih, hstep n]
        abel
  ext x
  change A (S x) - S (B x) = C x
  have hPx : Filter.Tendsto (fun n : ℕ => P (n + 1) x)
      Filter.atTop (nhds (S x)) :=
    ((ContinuousLinearMap.apply 𝕜 E x).continuous.tendsto S).comp hPshift
  have hPBx : Filter.Tendsto (fun n : ℕ => P (n + 1) (B x))
      Filter.atTop (nhds (S (B x))) :=
    ((ContinuousLinearMap.apply 𝕜 E (B x)).continuous.tendsto S).comp hPshift
  have hlhs : Filter.Tendsto
      (fun n : ℕ => A (P (n + 1) x) - P (n + 1) (B x))
      Filter.atTop (nhds (A (S x) - S (B x))) :=
    ((A.continuous.tendsto (S x)).comp hPx).sub hPBx
  have htail : Filter.Tendsto (fun n : ℕ => t n (B x))
      Filter.atTop (nhds 0) := by
    have ht0 : Filter.Tendsto t Filter.atTop (nhds 0) := hsum.tendsto_atTop_zero
    exact ((ContinuousLinearMap.apply 𝕜 E (B x)).continuous.tendsto 0).comp ht0
  have hrhs : Filter.Tendsto (fun n : ℕ => C x - t n (B x))
      Filter.atTop (nhds (C x)) := by
    simpa using tendsto_const_nhds.sub htail
  have hsame : (fun n : ℕ => A (P (n + 1) x) - P (n + 1) (B x)) =ᶠ[Filter.atTop]
      (fun n : ℕ => C x - t n (B x)) :=
    Filter.Eventually.of_forall fun n => by
      have h := congrArg (fun T : F →L[𝕜] E => T x) (hfinite n)
      simpa only [sub_apply,
        ContinuousLinearMap.comp_apply] using h
  exact tendsto_nhds_unique (hlhs.congr' hsame) hrhs

omit [CompleteSpace E] [CompleteSpace F] in
/-- Uniqueness under the bound/inverse separation. -/
theorem sylvester_unique_of_bound_inverse
    {A : E →L[𝕜] E}
    (hA : IsUnit A) (B : F →L[𝕜] F)
    (hratio : ‖Ring.inverse A‖ * ‖B‖ < 1)
    {X Y : F →L[𝕜] E}
    (hXY : A ∘L X - X ∘L B = A ∘L Y - Y ∘L B) :
    X = Y := by
  have hEq' : A ∘L X - A ∘L Y = X ∘L B - Y ∘L B := by
    calc
      A ∘L X - A ∘L Y =
          (A ∘L X - X ∘L B) - (A ∘L Y - Y ∘L B) +
            (X ∘L B - Y ∘L B) := by abel
      _ = X ∘L B - Y ∘L B := by rw [hXY, sub_self, zero_add]
  have hEq : A ∘L (X - Y) = (X - Y) ∘L B := by
    simpa only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp] using hEq'
  have hfixed : X - Y = Ring.inverse A ∘L ((X - Y) ∘L B) := by
    calc
      X - Y = ContinuousLinearMap.id 𝕜 E ∘L (X - Y) := by simp
      _ = (Ring.inverse A ∘L A) ∘L (X - Y) := by
        rw [show Ring.inverse A ∘L A = ContinuousLinearMap.id 𝕜 E from
          Ring.inverse_mul_cancel A hA]
      _ = Ring.inverse A ∘L (A ∘L (X - Y)) :=
        ContinuousLinearMap.comp_assoc _ _ _
      _ = Ring.inverse A ∘L ((X - Y) ∘L B) := by rw [hEq]
  have hnormle : ‖X - Y‖ ≤ (‖Ring.inverse A‖ * ‖B‖) * ‖X - Y‖ := by
    calc
      ‖X - Y‖ = ‖Ring.inverse A ∘L ((X - Y) ∘L B)‖ := congrArg norm hfixed
      _ ≤ ‖Ring.inverse A‖ * ‖(X - Y) ∘L B‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖Ring.inverse A‖ * (‖X - Y‖ * ‖B‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg (Ring.inverse A))
      _ = (‖Ring.inverse A‖ * ‖B‖) * ‖X - Y‖ := by ring
  have hnorm : ‖X - Y‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖X - Y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hlt : (‖Ring.inverse A‖ * ‖B‖) * ‖X - Y‖ < ‖X - Y‖ := by
      calc
        (‖Ring.inverse A‖ * ‖B‖) * ‖X - Y‖ < 1 * ‖X - Y‖ :=
          mul_lt_mul_of_pos_right hratio hpos
        _ = ‖X - Y‖ := one_mul _
    exact (not_lt_of_ge hnormle) hlt
  rw [← sub_eq_zero]
  exact norm_eq_zero.mp hnorm

/-- Davis--Kahan Theorem 5.1 in a rectangular ideal family. -/
theorem sylvester_mem_and_gauge_le_of_bound_inverse
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {A : E →L[𝕜] E}
    (hA : IsUnit A) (B : F →L[𝕜] F)
    {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hAinv : ‖Ring.inverse A‖ ≤ (ρ + δ)⁻¹)
    (hB : ‖B‖ ≤ ρ)
    (hEq : A ∘L X - X ∘L B = C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gaugeReal X ≤ N.gaugeReal C := by
  have hρδ : 0 < ρ + δ := by linarith
  have hratio : ‖Ring.inverse A‖ * ‖B‖ < 1 := by
    calc
      ‖Ring.inverse A‖ * ‖B‖ ≤ (ρ + δ)⁻¹ * ρ := by
        exact mul_le_mul hAinv hB (norm_nonneg B)
          (inv_nonneg.mpr hρδ.le)
      _ = ρ / (ρ + δ) := by rw [div_eq_mul_inv, mul_comm]
      _ < 1 := (div_lt_one hρδ).2 (by linarith)
  let S : F →L[𝕜] E := sylvesterNeumannSolution N A B C
  have hSmem : N.Mem S := by
    exact sylvesterNeumannSolution_mem N A B hC hratio
  have hSEq : A ∘L S - S ∘L B = C :=
    sylvesterNeumannSolution_eq N hA B C hratio
  have hXS : X = S := by
    apply sylvester_unique_of_bound_inverse hA B hratio
    exact hEq.trans hSEq.symm
  have hXmem : N.Mem X := by rw [hXS]; exact hSmem
  have hAX : A ∘L X = C + X ∘L B := by
    rw [← hEq]
    abel
  have hfix : X = Ring.inverse A ∘L (C + X ∘L B) := by
    calc
      X = ContinuousLinearMap.id 𝕜 E ∘L X := by simp
      _ = (Ring.inverse A ∘L A) ∘L X := by
        rw [show Ring.inverse A ∘L A = ContinuousLinearMap.id 𝕜 E from
          Ring.inverse_mul_cancel A hA]
      _ = Ring.inverse A ∘L (A ∘L X) := ContinuousLinearMap.comp_assoc _ _ _
      _ = Ring.inverse A ∘L (C + X ∘L B) := by rw [hAX]
  have hXBmem : N.Mem (X ∘L B) := N.comp_right_mem B hXmem
  have hgauge : N.gaugeReal X ≤
      (ρ + δ)⁻¹ * (N.gaugeReal C + N.gaugeReal X * ρ) :=
    N.gaugeReal_le_of_comp_add_comp_fixedPoint hρδ hAinv hB hC hXmem hXBmem hfix
  refine ⟨hXmem, ?_⟩
  have hkey := mul_le_mul_of_nonneg_left hgauge hρδ.le
  rw [← mul_assoc, mul_inv_cancel₀ hρδ.ne', one_mul] at hkey
  linarith

/-- Reversed orientation of the bound/inverse Sylvester estimate. -/
theorem sylvester_mem_and_gauge_le_of_bound_inverse_swapped
    (N : TauCeti.SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete]
    {B : F →L[𝕜] F}
    (hB : IsUnit B) (A : E →L[𝕜] E)
    {X C : F →L[𝕜] E} {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hBinv : ‖Ring.inverse B‖ ≤ (ρ + δ)⁻¹)
    (hA : ‖A‖ ≤ ρ)
    (hEq : A ∘L X - X ∘L B = C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gaugeReal X ≤ N.gaugeReal C := by
  have hBadj : IsUnit B.adjoint := ContinuousLinearMap.isUnit_adjoint_iff.mpr hB
  have hBadjInv : ‖Ring.inverse B.adjoint‖ ≤ (ρ + δ)⁻¹ := by
    rw [ContinuousLinearMap.ringInverse_adjoint, ContinuousLinearMap.adjoint.norm_map]
    exact hBinv
  have hAadj : ‖A.adjoint‖ ≤ ρ := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hA
  have hEqAdj :
      B.adjoint ∘L X.adjoint - X.adjoint ∘L A.adjoint = -C.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hEq
    rw [map_sub, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_comp] at h
    calc
      B.adjoint ∘L X.adjoint - X.adjoint ∘L A.adjoint =
          -(X.adjoint ∘L A.adjoint - B.adjoint ∘L X.adjoint) := by abel
      _ = -C.adjoint := by rw [h]
  have hCadj : N.Mem C.adjoint := N.adjoint_mem hC
  have hnegCadj : N.Mem (-C.adjoint) := N.neg_mem hCadj
  have hmain := sylvester_mem_and_gauge_le_of_bound_inverse
    N hBadj A.adjoint hρ hδ hBadjInv hAadj hEqAdj hnegCadj
  have hXmem : N.Mem X := by
    have hdouble := N.adjoint_mem hmain.1
    simpa using hdouble
  refine ⟨hXmem, ?_⟩
  have hbound := hmain.2
  rw [N.gaugeReal_adjoint hXmem, N.gaugeReal_neg hCadj,
    N.gaugeReal_adjoint hC] at hbound
  exact hbound

end Sylvester
end DavisKahan
end TauCeti