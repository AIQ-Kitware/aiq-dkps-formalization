/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.BoundedOperator.Compat
import ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
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

namespace TauCeti
namespace DavisKahan
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
    {E F : Type v} {ι : Type*}
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
    {E F : Type v} {ι : Type*}
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

/-- Operator-norm bound for a two-sided composition.

**Deprecated location.**  The statement has nothing to do with ideal families —
it needs neither an inner product nor completeness — and non-Experimental code
was reaching into `Experimental.ExactSinTheta` to get it.  It now lives as
`ContinuousLinearMap.opNorm_comp_comp_le` in
`ForTauCeti/Analysis/OperatorIdeal/Family/OperatorNorm.lean`, where the same
calc proof already existed inline.  This alias remains only so the legacy
namespace keeps building; new uses should take the `ForTauCeti` name. -/
theorem opNorm_comp_comp_le
    {E F G H : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    ‖L ∘L A ∘L R‖ ≤ ‖L‖ * ‖A‖ * ‖R‖ :=
  TauCeti.ContinuousLinearMap.opNorm_comp_comp_le L A R

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

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Every operator lies in the operator-norm family: it is the whole of `E →L[𝕜] F`. -/
@[simp] theorem operatorNorm_mem (A : E →L[𝕜] F) :
    (operatorNorm (𝕜 := 𝕜)).Mem A := trivial

/-- The gauge of the operator-norm family is the operator norm.  Together with
`operatorNorm_mem` this is what lets an operator-norm statement be read off from its
ideal-gauge counterpart instead of proved a second time. -/
@[simp] theorem operatorNorm_gauge (A : E →L[𝕜] F) :
    (operatorNorm (𝕜 := 𝕜)).gauge A = ‖A‖ := rfl

end RectangularSymmetricIdealFamily
end ExactSinTheta
end DavisKahan
end TauCeti

namespace TauCeti.SymmetricOperatorIdealFamily

open scoped ENNReal

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]

open DavisKahan.ExactSinTheta

/-- The historical record built from a canonical symmetric ideal family:
membership is finiteness of the gauge, the real gauge is the canonical gauge read
in `ℝ`.

**This is the last thing keeping `RectangularSymmetricIdealFamily` alive.**  It used
to live in `DavisKahan/Interop/TauCeti/RectangularFamilyAdapter.lean`, framed as an
interop bridge; that framing was wrong -- there is no external party -- and the file
is gone.  The *function* is still needed, because five `Experimental/` modules
construct legacy records, so it sits with the structure it builds.  It goes when they
do; nothing in production calls it. -/
noncomputable def toRectangular (N : SymmetricOperatorIdealFamily.{u, v} 𝕜)
    [N.toOperatorIdealFamily.IsComplete] :
    RectangularSymmetricIdealFamily.{u, v} 𝕜 where
  Mem := @fun _ _ _ _ _ _ _ _ A => N.gauge A ≠ ∞
  gauge := @fun _ _ _ _ _ _ _ _ A => (N.gauge A).toReal
  zero_mem := by intros; exact N.toOperatorIdealFamily.carrier.zero_mem
  add_mem := by intros; exact N.toOperatorIdealFamily.carrier.add_mem ‹_› ‹_›
  smul_mem := by intros; exact N.toOperatorIdealFamily.carrier.smul_mem _ ‹_›
  adjoint_mem := by intros; exact N.adjoint_mem_carrier ‹_›
  comp_mem := by intros; exact N.toOperatorIdealFamily.comp_mem_carrier _ _ ‹_›
  gauge_nonneg := by intros; exact ENNReal.toReal_nonneg
  gauge_zero := by intros; simp
  gauge_eq_zero := by
    intros
    rename_i hA h
    exact N.toOperatorIdealFamily.gauge_eq_zero
      (((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right hA)
  gauge_add_le := by
    intros
    rename_i hA hB
    rw [← ENNReal.toReal_add hA hB]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA, hB⟩)
      (N.toOperatorIdealFamily.gauge_add_le _ _)
  gauge_smul := by
    intros
    rw [N.toOperatorIdealFamily.gauge_smul, ENNReal.toReal_mul, toReal_enorm]
  gauge_adjoint := by intros; rw [N.gauge_adjoint]
  gauge_comp_le := by
    intros
    rename_i L A R hA
    have hbound := N.toOperatorIdealFamily.gauge_comp_le L A R
    have hfin : ‖L‖ₑ * N.gauge A * ‖R‖ₑ ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) hA) (by simp)
    refine (ENNReal.toReal_mono hfin hbound).trans_eq ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm, toReal_enorm]
  opNorm_le_gauge := by
    intros
    rename_i hA
    have h := ENNReal.toReal_mono hA (N.toOperatorIdealFamily.enorm_le_gauge _)
    rwa [toReal_enorm] at h
  gauge_complete := by
    intro E F _ _ _ _ _ _ A hmem hcauchy
    -- Read the sequence inside the ideal, where the gauge *is* the norm.
    -- Canonical `∈ carrier` form, so that `Elem.val_mk` matches below; see the same step in
    -- `DavisKahan/OperatorIdeal/CanonicalRealView.lean`.
    set a : ℕ → N.toOperatorIdealFamily.Elem E F :=
      fun n => OperatorIdealFamily.Elem.mk
        ((N.toOperatorIdealFamily.mem_carrier_iff).mpr (hmem n)) with ha
    have hdist : ∀ m n, dist (a m) (a n) = (N.gauge (A m - A n)).toReal := by
      intro m n
      rw [dist_eq_norm, ha, OperatorIdealFamily.Elem.norm_def]
      simp [OperatorIdealFamily.Elem.val_mk]
    have hcs : CauchySeq a := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨M, hM⟩ := hcauchy ε hε
      exact ⟨M, fun m hm n hn => by rw [hdist]; exact hM m n hm hn⟩
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hcs
    refine ⟨l.val, l.val_mem, fun ε hε => ?_⟩
    rw [Metric.tendsto_atTop] at hl
    obtain ⟨M, hM⟩ := hl ε hε
    refine ⟨M, fun n hn => ?_⟩
    have := hM n hn
    rwa [dist_eq_norm, OperatorIdealFamily.Elem.norm_def, show (a n - l).val = A n - l.val from
      by simp [ha]] at this

/-! ### The canonical family a historical record determines

`toRectangular` above is one-directional, and its docstring says why: a historical
record does not determine a canonical family, because its gauge is unconstrained
off the ideal.

That is an argument against a *unique* inverse, not against any inverse.  Choosing
the canonical extension -- `∞` off the ideal, which is what `OperatorIdealFamily`
means by a total gauge -- gives a canonical family whose gauge agrees with the
record's on members, and that is all a consumer ever asked of it.

This is what lets the three concrete constructions (Schatten, and the complex and
real Hilbert--Schmidt families) produce canonical families without rebuilding each
one field-by-field in `ℝ≥0∞`. -/

/-- The `ℝ≥0∞` gauge determined by a historical record: its real gauge on members,
`∞` off the ideal. -/
noncomputable def ofRectangularGauge
    (N : RectangularSymmetricIdealFamily.{u, v} 𝕜)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : ℝ≥0∞ :=
  open Classical in
  if N.Mem A then ENNReal.ofReal (N.gauge A) else ∞

variable {N : RectangularSymmetricIdealFamily.{u, v} 𝕜}
variable {E F G H : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- On members the extended gauge is the record's gauge. -/
theorem ofRectangularGauge_of_mem {A : E →L[𝕜] F} (hA : N.Mem A) :
    ofRectangularGauge N A = ENNReal.ofReal (N.gauge A) := if_pos hA

/-- Off the ideal the extended gauge is `∞`. -/
theorem ofRectangularGauge_of_not_mem {A : E →L[𝕜] F} (hA : ¬ N.Mem A) :
    ofRectangularGauge N A = ∞ := if_neg hA

/-- Finiteness of the extended gauge is exactly membership. -/
theorem ofRectangularGauge_ne_top_iff {A : E →L[𝕜] F} :
    ofRectangularGauge N A ≠ ∞ ↔ N.Mem A := by
  classical
  by_cases h : N.Mem A
  · simp [ofRectangularGauge_of_mem h, h]
  · simp [ofRectangularGauge_of_not_mem h, h]

/-- Scaling by a nonzero scalar does not change membership. -/
theorem mem_smul_iff {c : 𝕜} (hc : c ≠ 0) {A : E →L[𝕜] F} :
    N.Mem (c • A) ↔ N.Mem A := by
  refine ⟨fun h => ?_, fun h => N.smul_mem c h⟩
  have := N.smul_mem c⁻¹ h
  rwa [← mul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- Membership is adjoint-invariant. -/
theorem mem_adjoint_iff {A : E →L[𝕜] F} : N.Mem A.adjoint ↔ N.Mem A := by
  refine ⟨fun h => ?_, fun h => N.adjoint_mem h⟩
  have := N.adjoint_mem h
  rwa [ContinuousLinearMap.adjoint_adjoint] at this

/-- Subadditivity, unconditionally: off the ideal the right-hand side is `∞`. -/
theorem ofRectangularGauge_add_le (A B : E →L[𝕜] F) :
    ofRectangularGauge N (A + B)
      ≤ ofRectangularGauge N A + ofRectangularGauge N B := by
  classical
  by_cases hA : N.Mem A
  · by_cases hB : N.Mem B
    · rw [ofRectangularGauge_of_mem hA, ofRectangularGauge_of_mem hB,
        ofRectangularGauge_of_mem (N.add_mem hA hB),
        ← ENNReal.ofReal_add (N.gauge_nonneg hA) (N.gauge_nonneg hB)]
      exact ENNReal.ofReal_le_ofReal (N.gauge_add_le hA hB)
    · simp [ofRectangularGauge_of_not_mem hB]
  · simp [ofRectangularGauge_of_not_mem hA]

/-- Absolute homogeneity, unconditionally.  The `c = 0` case is where the
extension is doing work: the left side is the gauge of `0`, and the right side is
`0 * ∞ = 0` in `ℝ≥0∞` when `A` is off the ideal. -/
theorem ofRectangularGauge_smul (c : 𝕜) (A : E →L[𝕜] F) :
    ofRectangularGauge N (c • A) = ‖c‖ₑ * ofRectangularGauge N A := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · simp [ofRectangularGauge_of_mem (N.zero_mem (E := E) (F := F)), N.gauge_zero]
  · by_cases hA : N.Mem A
    · rw [ofRectangularGauge_of_mem hA,
        ofRectangularGauge_of_mem (N.smul_mem c hA), N.gauge_smul c hA,
        ENNReal.ofReal_mul (norm_nonneg c), ← ofReal_norm]
    · rw [ofRectangularGauge_of_not_mem hA,
        ofRectangularGauge_of_not_mem (fun h => hA ((mem_smul_iff hc).mp h))]
      simp [ENNReal.mul_top, enorm_ne_zero.mpr hc]

/-- The operator norm is dominated by the extended gauge. -/
theorem enorm_le_ofRectangularGauge (A : E →L[𝕜] F) :
    ‖A‖ₑ ≤ ofRectangularGauge N A := by
  classical
  by_cases hA : N.Mem A
  · rw [ofRectangularGauge_of_mem hA, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (N.opNorm_le_gauge hA)
  · simp [ofRectangularGauge_of_not_mem hA]

/-- The two-sided ideal law, unconditionally. -/
theorem ofRectangularGauge_comp_le (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    ofRectangularGauge N (L ∘L A ∘L R)
      ≤ ‖L‖ₑ * ofRectangularGauge N A * ‖R‖ₑ := by
  classical
  by_cases hA : N.Mem A
  · rw [ofRectangularGauge_of_mem hA,
      ofRectangularGauge_of_mem (N.comp_mem L R hA),
      ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg L),
      ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (N.gauge_nonneg hA))]
    exact ENNReal.ofReal_le_ofReal (N.gauge_comp_le L R hA)
  · rcases eq_or_ne ‖L‖ₑ 0 with hL | hL
    · have hL0 : L = 0 := by
        rw [← ofReal_norm, ENNReal.ofReal_eq_zero] at hL
        exact norm_eq_zero.mp (le_antisymm hL (norm_nonneg L))
      subst hL0
      simp [ContinuousLinearMap.zero_comp,
        ofRectangularGauge_of_mem (N.zero_mem (E := H) (F := G)), N.gauge_zero]
    · rcases eq_or_ne ‖R‖ₑ 0 with hR | hR
      · have hR0 : R = 0 := by
          rw [← ofReal_norm, ENNReal.ofReal_eq_zero] at hR
          exact norm_eq_zero.mp (le_antisymm hR (norm_nonneg R))
        subst hR0
        simp [ContinuousLinearMap.comp_zero,
          ofRectangularGauge_of_mem (N.zero_mem (E := H) (F := G)), N.gauge_zero]
      · rw [ofRectangularGauge_of_not_mem hA]
        simp [ENNReal.mul_top, hL, hR]

/-- The extended gauge is adjoint-invariant. -/
theorem ofRectangularGauge_adjoint (A : E →L[𝕜] F) :
    ofRectangularGauge N A.adjoint = ofRectangularGauge N A := by
  classical
  by_cases hA : N.Mem A
  · rw [ofRectangularGauge_of_mem hA, ofRectangularGauge_of_mem (N.adjoint_mem hA),
      N.gauge_adjoint hA]
  · rw [ofRectangularGauge_of_not_mem hA,
      ofRectangularGauge_of_not_mem (fun h => hA (mem_adjoint_iff.mp h))]

/-- The canonical symmetric family determined by a legacy rectangular record.

This is the inverse direction to `toRectangular`, and it exists because the
legacy record's gauge is only defined *on* the ideal.  There is no canonical
`ℝ`-valued extension off it, but there is a canonical `ℝ≥0∞`-valued one — `∞` —
and that is what the canonical structure asks for.  So the round trip
`toRectangular ∘ ofRectangular` is the identity on members while
`ofRectangular ∘ toRectangular` need not be: `toRectangular` forgets which
non-members had which junk gauge value, and `ofRectangular` sends them all
to `∞`.

`toRectangular`'s docstring says the conversion has no inverse.  That remains
true of a *two-sided* inverse in `ℝ`; what this definition supplies is the
canonical extension, which is the thing the canonical structure was designed
to have. -/
noncomputable def ofRectangular (N : RectangularSymmetricIdealFamily.{u, v} 𝕜) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge := ofRectangularGauge N
  gauge_add_le := ofRectangularGauge_add_le
  gauge_smul := ofRectangularGauge_smul
  enorm_le_gauge := enorm_le_ofRectangularGauge
  gauge_comp_le := ofRectangularGauge_comp_le
  gauge_adjoint := ofRectangularGauge_adjoint

/-- The constructed family's gauge is the extended gauge, definitionally. -/
@[simp]
theorem gauge_ofRectangular (N : RectangularSymmetricIdealFamily.{u, v} 𝕜)
    (A : E →L[𝕜] F) : (ofRectangular N).gauge A = ofRectangularGauge N A := rfl

/-- Membership in the constructed family is the record's own membership. -/
theorem gauge_ofRectangular_ne_top_iff {N : RectangularSymmetricIdealFamily.{u, v} 𝕜}
    {A : E →L[𝕜] F} : (ofRectangular N).gauge A ≠ ∞ ↔ N.Mem A :=
  ofRectangularGauge_ne_top_iff

/-- `ofRectangular` is a section of `toRectangular` where that is meaningful:
on members the real view of the constructed family is the record's own gauge.

Stated on `toReal` of the gauge rather than through `toRectangular` itself,
because `toRectangular` carries an `IsComplete` hypothesis that this direction
does not need — and because `toReal ∘ gauge` is simultaneously `toRectangular`'s
gauge field and the canonical real view's `gaugeReal`, so this one statement
serves both vocabularies without either file importing the other. -/
theorem toReal_gauge_ofRectangular {N : RectangularSymmetricIdealFamily.{u, v} 𝕜}
    {A : E →L[𝕜] F} (hA : N.Mem A) :
    ((ofRectangular N).gauge A).toReal = N.gauge A := by
  rw [gauge_ofRectangular, ofRectangularGauge_of_mem hA,
    ENNReal.toReal_ofReal (N.gauge_nonneg hA)]

/-- The constructed family is complete.

This is the field `ofRectangular` would otherwise drop.  The canonical structure
has no completeness field — completeness is the separate class `IsComplete`,
`CompleteSpace (N.Elem E F)` — whereas the legacy record carries
`gauge_complete` as an `ℝ`-valued Cauchy statement.  Without this instance the
retype would silently lose a proved fact, so the bridge is only lossless with it.

Every legacy record has the field, so this holds for all of them
unconditionally; the proof is the translation between the two idioms, using the
fact that `Elem`'s norm is exactly the record's gauge on members. -/
instance isComplete_ofRectangular (N : RectangularSymmetricIdealFamily.{u, v} 𝕜) :
    (ofRectangular N).toOperatorIdealFamily.IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    have hnorm : ∀ x : (ofRectangular N).toOperatorIdealFamily.Elem E F,
        ‖x‖ = N.gauge x.val := fun x =>
      toReal_gauge_ofRectangular (gauge_ofRectangular_ne_top_iff.mp x.gauge_val_ne_top)
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    have hmem : ∀ n, N.Mem (a n).val := fun n =>
      gauge_ofRectangular_ne_top_iff.mp (a n).gauge_val_ne_top
    have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n, M ≤ m → M ≤ n →
        N.gauge ((a m).val - (a n).val) < ε := by
      intro ε hε
      rw [Metric.cauchySeq_iff] at ha
      obtain ⟨M, hM⟩ := ha ε hε
      refine ⟨M, fun m n hm hn => ?_⟩
      have h := hM m hm n hn
      rw [dist_eq_norm, hnorm] at h
      exact h
    obtain ⟨L, hLmem, hL⟩ := N.gauge_complete (fun n => (a n).val) hmem hcauchy
    refine ⟨OperatorIdealFamily.Elem.mk (gauge_ofRectangular_ne_top_iff.mpr hLmem), ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := hL ε hε
    refine ⟨M, fun n hn => ?_⟩
    rw [dist_eq_norm, hnorm]
    exact hM n hn

end TauCeti.SymmetricOperatorIdealFamily
