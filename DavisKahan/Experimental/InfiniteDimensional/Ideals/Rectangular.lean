/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.BoundedOperator.Basic
import Mathlib.Topology.Basic

/-!
# Rectangular symmetric ideal families for the exact `sin Θ` program

The original Davis--Kahan theorem compares operators between different Hilbert
spaces.  A square endomorphism norm is therefore not a sufficient abstraction.
This module records one coherent norm-ideal family across all source and target
spaces in a fixed universe.

The fields are intentionally explicit.  A concrete instance must provide
membership, the gauge, adjoint invariance, two-sided ideal control, and
completeness.  The bounded and one-unbounded interval/exterior theory uses
only this interface.  The genuinely two-unbounded cutoff route uses the
stronger `KyFanDominantIdealFamily` defined in `ApproximationNumbers.lean`.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

/-- A coherent rectangular symmetric norm ideal over Hilbert spaces in one
universe.  `Mem` records finite ideal norm; `gauge` is only used on members. -/
structure RectangularSymmetricIdealFamily (𝕜 : Type u) [RCLike 𝕜] where
  Mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → Prop
  gauge :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → ℝ
  zero_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      Mem (0 : E →L[𝕜] F)
  add_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F}, Mem A → Mem B → Mem (A + B)
  smul_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) {A : E →L[𝕜] F}, Mem A → Mem (c • A)
  adjoint_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → Mem A.adjoint
  comp_mem :
    ∀ {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E),
      Mem A → Mem (L ∘L A ∘L R)
  gauge_nonneg :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → 0 ≤ gauge A
  gauge_zero :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      gauge (0 : E →L[𝕜] F) = 0
  gauge_eq_zero :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → gauge A = 0 → A = 0
  gauge_add_le :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F}, Mem A → Mem B →
        gauge (A + B) ≤ gauge A + gauge B
  gauge_smul :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) {A : E →L[𝕜] F}, Mem A →
        gauge (c • A) = ‖c‖ * gauge A
  gauge_adjoint :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → gauge A.adjoint = gauge A
  gauge_comp_le :
    ∀ {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E),
      Mem A → gauge (L ∘L A ∘L R) ≤ ‖L‖ * gauge A * ‖R‖
  opNorm_le_gauge :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → ‖A‖ ≤ gauge A
  gauge_complete :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : ℕ → E →L[𝕜] F),
      (∀ n, Mem (A n)) →
      (∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
        gauge (A m - A n) < ε) →
      ∃ L, Mem L ∧ ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
        gauge (A n - L) < ε

namespace RectangularSymmetricIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]

/-- Membership is preserved by left composition with a bounded map. -/
theorem comp_left_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F G : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.Mem (L ∘L A) := by
  simpa using N.comp_mem L (ContinuousLinearMap.id 𝕜 E) hA

/-- Ideal-gauge control under left composition by a bounded map. -/
theorem gauge_comp_left_le_mul
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F G : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G) {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge (L ∘L A) ≤ ‖L‖ * N.gauge A := by
  have hraw := N.gauge_comp_le L (ContinuousLinearMap.id 𝕜 E) hA
  calc
    N.gauge (L ∘L A) =
        N.gauge (L ∘L A ∘L ContinuousLinearMap.id 𝕜 E) := by simp
    _ ≤ ‖L‖ * N.gauge A * ‖ContinuousLinearMap.id 𝕜 E‖ := hraw
    _ ≤ ‖L‖ * N.gauge A * 1 := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := E))
        (mul_nonneg (norm_nonneg L) (N.gauge_nonneg hA))
    _ = ‖L‖ * N.gauge A := by ring

/-- Left composition by a contraction does not increase the ideal gauge. -/
theorem gauge_comp_left_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F G : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (L : F →L[𝕜] G) {A : E →L[𝕜] F}
    (hA : N.Mem A) (hL : ‖L‖ ≤ 1) :
    N.gauge (L ∘L A) ≤ N.gauge A := by
  calc
    N.gauge (L ∘L A) ≤ ‖L‖ * N.gauge A :=
      N.gauge_comp_left_le_mul L hA
    _ ≤ 1 * N.gauge A :=
      mul_le_mul_of_nonneg_right hL (N.gauge_nonneg hA)
    _ = N.gauge A := one_mul _

/-- Membership is preserved by right composition with a bounded map. -/
theorem comp_right_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {A : E →L[𝕜] F} (R : H →L[𝕜] E) (hA : N.Mem A) :
    N.Mem (A ∘L R) := by
  simpa using N.comp_mem (ContinuousLinearMap.id 𝕜 F) R hA

/-- Ideal-gauge control under right composition by a bounded map. -/
theorem gauge_comp_right_le_mul
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {A : E →L[𝕜] F} (R : H →L[𝕜] E) (hA : N.Mem A) :
    N.gauge (A ∘L R) ≤ N.gauge A * ‖R‖ := by
  have hraw := N.gauge_comp_le (ContinuousLinearMap.id 𝕜 F) R hA
  have hid : ‖ContinuousLinearMap.id 𝕜 F‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := F)
  calc
    N.gauge (A ∘L R)
        = N.gauge ((ContinuousLinearMap.id 𝕜 F) ∘L A ∘L R) := by simp
    _ ≤ ‖ContinuousLinearMap.id 𝕜 F‖ * N.gauge A * ‖R‖ := hraw
    _ ≤ (1 * N.gauge A) * ‖R‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hid (N.gauge_nonneg hA))
        (norm_nonneg R)
    _ = N.gauge A * ‖R‖ := by ring

/-- Right composition by a contraction does not increase the ideal gauge. -/
theorem gauge_comp_right_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    {A : E →L[𝕜] F} (R : H →L[𝕜] E)
    (hA : N.Mem A) (hR : ‖R‖ ≤ 1) :
    N.gauge (A ∘L R) ≤ N.gauge A := by
  have hraw := N.gauge_comp_le (ContinuousLinearMap.id 𝕜 F) R hA
  have hnonneg := N.gauge_nonneg hA
  calc
    N.gauge (A ∘L R)
        = N.gauge ((ContinuousLinearMap.id 𝕜 F) ∘L A ∘L R) := by simp
    _ ≤ ‖ContinuousLinearMap.id 𝕜 F‖ * N.gauge A * ‖R‖ := hraw
    _ ≤ 1 * N.gauge A * 1 := by
      gcongr
      · exact ContinuousLinearMap.norm_id_le
    _ = N.gauge A := by ring

/-- Ideal membership is preserved by subtraction. -/
theorem sub_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.Mem (A - B) := by
  rw [sub_eq_add_neg]
  exact N.add_mem hA (by simpa using N.smul_mem (-1 : 𝕜) hB)

/-- Triangle inequality for subtraction in the ideal gauge. -/
theorem gauge_sub_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A B : E →L[𝕜] F} (hA : N.Mem A) (hB : N.Mem B) :
    N.gauge (A - B) ≤ N.gauge A + N.gauge B := by
  rw [sub_eq_add_neg]
  have hneg : N.Mem (-B) := by
    simpa using N.smul_mem (-1 : 𝕜) hB
  calc
    N.gauge (A + -B) ≤ N.gauge A + N.gauge (-B) :=
      N.gauge_add_le hA hneg
    _ = N.gauge A + N.gauge B := by
      rw [show -B = (-1 : 𝕜) • B by simp, N.gauge_smul (-1 : 𝕜) hB]
      simp

/-- Finite sums of ideal members remain in the ideal. -/
theorem finset_sum_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F ι : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (s : Finset ι) (A : ι → E →L[𝕜] F)
    (hA : ∀ i ∈ s, N.Mem (A i)) :
    N.Mem (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (N.zero_mem (E := E) (F := F))
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact N.add_mem (hA a (Finset.mem_insert_self a s))
        (ih fun i hi => hA i (Finset.mem_insert_of_mem hi))

/-- The gauge of a finite sum is bounded by the sum of the gauges. -/
theorem gauge_finset_sum_le
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F ι : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (s : Finset ι) (A : ι → E →L[𝕜] F)
    (hA : ∀ i ∈ s, N.Mem (A i)) :
    N.gauge (∑ i ∈ s, A i) ≤ ∑ i ∈ s, N.gauge (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [N.gauge_zero]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (N.gauge_add_le
        (hA a (Finset.mem_insert_self a s))
        (N.finset_sum_mem s A fun i hi => hA i (Finset.mem_insert_of_mem hi))).trans
          (add_le_add le_rfl (ih fun i hi => hA i (Finset.mem_insert_of_mem hi)))

/-- A member has zero gauge exactly when it is the zero operator. -/
theorem gauge_eq_zero_iff
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} (hA : N.Mem A) :
    N.gauge A = 0 ↔ A = 0 := by
  constructor
  · exact N.gauge_eq_zero hA
  · rintro rfl
    exact N.gauge_zero

/-- Two-sided composition by contractions does not increase the gauge. -/
theorem gauge_comp_le_of_contractions
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E)
    (hA : N.Mem A) (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    N.gauge (L ∘L A ∘L R) ≤ N.gauge A := by
  calc
    N.gauge (L ∘L A ∘L R) ≤ ‖L‖ * N.gauge A * ‖R‖ :=
      N.gauge_comp_le L R hA
    _ ≤ 1 * N.gauge A * 1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hL (N.gauge_nonneg hA)) hR
        (norm_nonneg R)
        (mul_nonneg zero_le_one (N.gauge_nonneg hA))
    _ = N.gauge A := by ring

/-- Ideal membership is invariant under negation. -/
theorem neg_mem
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} (hA : N.Mem A) : N.Mem (-A) := by
  simpa using N.smul_mem (-1 : 𝕜) hA

/-- The ideal gauge is invariant under negation. -/
theorem gauge_neg
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    {A : E →L[𝕜] F} (hA : N.Mem A) : N.gauge (-A) = N.gauge A := by
  simpa using N.gauge_smul (-1 : 𝕜) hA

/-- Operator-norm bound for a two-sided composition. -/
theorem opNorm_comp_comp_le
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    ‖L ∘L A ∘L R‖ ≤ ‖L‖ * ‖A‖ * ‖R‖ :=
  calc ‖L ∘L A ∘L R‖ ≤ ‖L‖ * ‖A ∘L R‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L‖ * (‖A‖ * ‖R‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le A R) (norm_nonneg L)
    _ = ‖L‖ * ‖A‖ * ‖R‖ := (mul_assoc _ _ _).symm

/-- An operator-norm Cauchy modulus converges to a limit in operator norm. -/
theorem exists_opNorm_limit
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : ℕ → E →L[𝕜] F)
    (hcauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
      ‖A m - A n‖ < ε) :
    ∃ L : E →L[𝕜] F, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
      ‖A n - L‖ < ε := by
  have hcs : CauchySeq A := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchy ε hε
    exact ⟨N, fun m hm n hn => by
      rw [dist_eq_norm]; exact hN m n hm hn⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨L, fun ε hε => ?_⟩
  rw [Metric.tendsto_atTop] at hL
  obtain ⟨N, hN⟩ := hL ε hε
  exact ⟨N, fun n hn => by
    rw [← dist_eq_norm]; exact hN n hn⟩

/-- The ordinary operator norm as a coherent rectangular family. -/
noncomputable def operatorNorm : RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  classical
  refine
    { Mem := fun _ => True
      gauge := fun T => ‖T‖
      zero_mem := by intros; trivial
      add_mem := by intros; trivial
      smul_mem := by intros; trivial
      adjoint_mem := by intros; trivial
      comp_mem := by intros; trivial
      gauge_nonneg := by intros; exact norm_nonneg _
      gauge_zero := by intros; exact norm_zero
      gauge_eq_zero := by intros E F _ _ _ _ _ _ A _ h; exact norm_eq_zero.mp h
      gauge_add_le := by intros; exact norm_add_le _ _
      gauge_smul := by intros; exact norm_smul _ _
      gauge_adjoint := by
        intros E F _ _ _ _ _ _ A _
        exact ContinuousLinearMap.adjoint.norm_map A
      gauge_comp_le := by
        intros E F G H _ _ _ _ _ _ _ _ _ _ _ _ L A R _
        exact opNorm_comp_comp_le L A R
      opNorm_le_gauge := by intros; exact le_rfl
      gauge_complete := by
        intro E F _ _ _ _ _ _ A hA hcauchy
        obtain ⟨L, hL⟩ := exists_opNorm_limit A hcauchy
        exact ⟨L, trivial, hL⟩ }

/-- Compact operators equipped with the ordinary operator norm.

The adjoint-invariance field is Schauder's theorem for Hilbert-space
adjoints, which the pinned Mathlib does not yet provide; that single field
remains an open obligation. -/
noncomputable def compactOperatorNorm :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  classical
  refine
    { Mem := fun T => IsCompactOperator T
      gauge := fun T => ‖T‖
      zero_mem := by intros; exact isCompactOperator_zero
      add_mem := by
        intros E F _ _ _ _ _ _ A B hA hB
        rw [FunLike.coe_add]
        exact hA.add hB
      smul_mem := by
        intros E F _ _ _ _ _ _ c A hA
        rw [FunLike.coe_smul]
        exact hA.smul c
      adjoint_mem := by intros; sorry
      comp_mem := by
        intros E F G H _ _ _ _ _ _ _ _ _ _ _ _ L A R hA
        rw [ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp]
        exact (hA.comp_clm R).clm_comp L
      gauge_nonneg := by intros; exact norm_nonneg _
      gauge_zero := by intros; exact norm_zero
      gauge_eq_zero := by intros E F _ _ _ _ _ _ A _ h; exact norm_eq_zero.mp h
      gauge_add_le := by intros; exact norm_add_le _ _
      gauge_smul := by intros; exact norm_smul _ _
      gauge_adjoint := by
        intros E F _ _ _ _ _ _ A _
        exact ContinuousLinearMap.adjoint.norm_map A
      gauge_comp_le := by
        intros E F G H _ _ _ _ _ _ _ _ _ _ _ _ L A R _
        exact opNorm_comp_comp_le L A R
      opNorm_le_gauge := by intros; exact le_rfl
      gauge_complete := by
        intro E F _ _ _ _ _ _ A hA hcauchy
        obtain ⟨L, hL⟩ := exists_opNorm_limit A hcauchy
        have htendsto : Filter.Tendsto A Filter.atTop (nhds L) := by
          rw [Metric.tendsto_atTop]
          intro ε hε
          obtain ⟨N, hN⟩ := hL ε hε
          exact ⟨N, fun n hn => by
            rw [dist_eq_norm]; exact hN n hn⟩
        have hcompact : IsCompactOperator L :=
          isClosed_setOf_isCompactOperator.mem_of_tendsto htendsto
            (Filter.Eventually.of_forall hA)
        exact ⟨L, hcompact, hL⟩ }

/-- Hilbert--Schmidt operators as a coherent rectangular family.

Construction route: define membership by summability of `‖A e i‖ ^ 2` over a
Hilbert basis (basis independence via Parseval), the gauge as the square root
of that sum, adjoint invariance by the double-sum symmetry, ideal control by
termwise operator-norm bounds, and completeness by a diagonal argument.  The
required rectangular Hilbert--Schmidt theory over `RCLike` scalars is not yet
available in this development, the pinned Mathlib, or the pinned Spectra
checkout (Spectra's trace-class development is `ℂ`-only and square). -/
noncomputable def hilbertSchmidt :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Trace-class operators as a coherent rectangular family.

Construction route: define the trace gauge through the singular-value
sequence (equivalently `tr |A|`), with adjoint invariance from the shared
singular values of `A` and `A⋆`, ideal control from singular-value
domination, and completeness against the operator-norm limit.  The required
rectangular trace-class theory over `RCLike` scalars is not yet available in
this development, the pinned Mathlib, or the pinned Spectra checkout. -/
noncomputable def traceClass :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Schatten `p` operators as a coherent rectangular family.

Construction route: apply the `ℓᵖ` gauge to the approximation-number
sequence; the triangle inequality is the Tomić--Weyl weak-majorization
argument, and completeness follows from Fatou against the operator-norm
limit.  The required Schatten theory is not yet available in this
development, the pinned Mathlib, or the pinned Spectra checkout. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

/-- Ky Fan `k` gauges, with positive `k`.

Construction route: the gauge is the sum of the first `k` approximation
numbers; subadditivity is Ky Fan's inequality, adjoint invariance is the
equality of approximation numbers of `A` and `A⋆`, and completeness reduces
to the operator norm through `opNorm_le_kyFanGauge` since all members are
bounded.  The infinite-dimensional approximation-number development in
`ApproximationNumbers.lean` must land first. -/
noncomputable def kyFan (k : ℕ) (hk : 0 < k) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  sorry

end RectangularSymmetricIdealFamily

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
