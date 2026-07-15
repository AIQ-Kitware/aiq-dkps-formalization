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
      gauge_eq_zero := by intros E F _ _ _ _ A _ h; exact norm_eq_zero.mp h
      gauge_add_le := by intros; exact norm_add_le _ _
      gauge_smul := by intros; exact norm_smul _ _
      gauge_adjoint := by intros; exact ContinuousLinearMap.norm_adjoint _
      gauge_comp_le := by
        intros E F G H _ _ _ _ _ _ _ _ L A R _
        exact ContinuousLinearMap.opNorm_comp_comp_le L A R
      opNorm_le_gauge := by intros; exact le_rfl
      gauge_complete := by
        intro E F _ _ _ _ A hA hcauchy
        obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
          (cauchySeq_iff_norm_sub_tendsto_zero.mpr hcauchy)
        refine ⟨L, trivial, ?_⟩
        simpa [Metric.tendsto_atTop] using hL }

/-- Compact operators equipped with the ordinary operator norm. -/
noncomputable def compactOperatorNorm :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  classical
  refine
    { Mem := fun T => IsCompactOperator T
      gauge := fun T => ‖T‖
      zero_mem := by intros; exact isCompactOperator_zero
      add_mem := by intros; exact IsCompactOperator.add ‹_› ‹_›
      smul_mem := by intros; exact IsCompactOperator.smul ‹_›
      adjoint_mem := by intros; exact IsCompactOperator.adjoint ‹_›
      comp_mem := by intros; exact IsCompactOperator.comp_left_right ‹_› _ _
      gauge_nonneg := by intros; exact norm_nonneg _
      gauge_zero := by intros; exact norm_zero
      gauge_eq_zero := by intros E F _ _ _ _ A _ h; exact norm_eq_zero.mp h
      gauge_add_le := by intros; exact norm_add_le _ _
      gauge_smul := by intros; exact norm_smul _ _
      gauge_adjoint := by intros; exact ContinuousLinearMap.norm_adjoint _
      gauge_comp_le := by
        intros E F G H _ _ _ _ _ _ _ _ L A R _
        exact ContinuousLinearMap.opNorm_comp_comp_le L A R
      opNorm_le_gauge := by intros; exact le_rfl
      gauge_complete := by
        intro E F _ _ _ _ A hA hcauchy
        obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
          (cauchySeq_iff_norm_sub_tendsto_zero.mpr hcauchy)
        have hcompact : IsCompactOperator L :=
          isClosed_setOf_isCompactOperator.mem_of_tendsto hL
            (Eventually.of_forall hA)
        refine ⟨L, hcompact, ?_⟩
        simpa [Metric.tendsto_atTop] using hL }

/-- Hilbert--Schmidt operators as a coherent rectangular family. -/
noncomputable def hilbertSchmidt :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  classical
  refine
    { Mem := fun T => HilbertSchmidt T
      gauge := fun T => hilbertSchmidtNorm T
      zero_mem := by intros; exact HilbertSchmidt.zero
      add_mem := by intros; exact HilbertSchmidt.add ‹_› ‹_›
      smul_mem := by intros; exact HilbertSchmidt.smul ‹_›
      adjoint_mem := by intros; exact HilbertSchmidt.adjoint ‹_›
      comp_mem := by intros; exact HilbertSchmidt.comp_left_right ‹_› _ _
      gauge_nonneg := by intros; exact hilbertSchmidtNorm_nonneg _
      gauge_zero := by intros; exact hilbertSchmidtNorm_zero
      gauge_eq_zero := by intros; exact hilbertSchmidtNorm_eq_zero.mp
      gauge_add_le := by intros; exact hilbertSchmidtNorm_add_le ‹_› ‹_›
      gauge_smul := by intros; exact hilbertSchmidtNorm_smul _ ‹_›
      gauge_adjoint := by intros; exact hilbertSchmidtNorm_adjoint ‹_›
      gauge_comp_le := by intros; exact hilbertSchmidtNorm_comp_left_right_le ‹_› _ _
      opNorm_le_gauge := by intros; exact opNorm_le_hilbertSchmidtNorm ‹_›
      gauge_complete := by
        intros E F _ _ _ _ A hA hcauchy
        exact HilbertSchmidt.complete_in_norm A hA hcauchy }

/-- Trace-class operators as a coherent rectangular family. -/
noncomputable def traceClass :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  classical
  refine
    { Mem := fun T => TraceClass T
      gauge := fun T => traceNorm T
      zero_mem := by intros; exact TraceClass.zero
      add_mem := by intros; exact TraceClass.add ‹_› ‹_›
      smul_mem := by intros; exact TraceClass.smul ‹_›
      adjoint_mem := by intros; exact TraceClass.adjoint ‹_›
      comp_mem := by intros; exact TraceClass.comp_left_right ‹_› _ _
      gauge_nonneg := by intros; exact traceNorm_nonneg _
      gauge_zero := by intros; exact traceNorm_zero
      gauge_eq_zero := by intros; exact traceNorm_eq_zero.mp
      gauge_add_le := by intros; exact traceNorm_add_le ‹_› ‹_›
      gauge_smul := by intros; exact traceNorm_smul _ ‹_›
      gauge_adjoint := by intros; exact traceNorm_adjoint ‹_›
      gauge_comp_le := by intros; exact traceNorm_comp_left_right_le ‹_› _ _
      opNorm_le_gauge := by intros; exact opNorm_le_traceNorm ‹_›
      gauge_complete := by
        intros E F _ _ _ _ A hA hcauchy
        exact TraceClass.complete_in_traceNorm A hA hcauchy }

/-- Schatten `p` operators as a coherent rectangular family. -/
noncomputable def schatten (p : ℝ) (hp : 1 ≤ p) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  classical
  refine
    { Mem := fun T => SchattenClass p T
      gauge := fun T => schattenNorm p T
      zero_mem := by intros; exact SchattenClass.zero p
      add_mem := by intros; exact SchattenClass.add hp ‹_› ‹_›
      smul_mem := by intros; exact SchattenClass.smul ‹_›
      adjoint_mem := by intros; exact SchattenClass.adjoint ‹_›
      comp_mem := by intros; exact SchattenClass.comp_left_right ‹_› _ _
      gauge_nonneg := by intros; exact schattenNorm_nonneg _ _
      gauge_zero := by intros; exact schattenNorm_zero p
      gauge_eq_zero := by intros; exact schattenNorm_eq_zero hp |>.mp
      gauge_add_le := by intros; exact schattenNorm_add_le hp ‹_› ‹_›
      gauge_smul := by intros; exact schattenNorm_smul p _ ‹_›
      gauge_adjoint := by intros; exact schattenNorm_adjoint p ‹_›
      gauge_comp_le := by intros; exact schattenNorm_comp_left_right_le hp ‹_› _ _
      opNorm_le_gauge := by intros; exact opNorm_le_schattenNorm hp ‹_›
      gauge_complete := by
        intros E F _ _ _ _ A hA hcauchy
        exact SchattenClass.complete_in_schattenNorm hp A hA hcauchy }

/-- Ky Fan `k` gauges, with positive `k`. -/
noncomputable def kyFan (k : ℕ) (hk : 0 < k) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) := by
  classical
  refine
    { Mem := fun _ => True
      gauge := fun T => kyFanGauge k T
      zero_mem := by intros; trivial
      add_mem := by intros; trivial
      smul_mem := by intros; trivial
      adjoint_mem := by intros; trivial
      comp_mem := by intros; trivial
      gauge_nonneg := by intros; exact kyFanGauge_nonneg _ _
      gauge_zero := by intros; exact kyFanGauge_zero k
      gauge_eq_zero := by
        intro E F _ _ _ _ A _ h
        exact kyFanGauge_eq_zero hk |>.mp h
      gauge_add_le := by intros; exact kyFanGauge_add_le k _ _
      gauge_smul := by intros; exact kyFanGauge_smul k _ _
      gauge_adjoint := by intros; exact kyFanGauge_adjoint k _
      gauge_comp_le := by intros; exact kyFanGauge_comp_left_right_le k _ _ _
      opNorm_le_gauge := by intros; exact opNorm_le_kyFanGauge hk _
      gauge_complete := by
        intro E F _ _ _ _ A hA hcauchy
        have hopCauchy : ∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n,
            N ≤ m → N ≤ n → ‖A m - A n‖ < ε := by
          intro ε hε
          obtain ⟨N, hN⟩ := hcauchy ε hε
          exact ⟨N, fun m n hm hn =>
            lt_of_le_of_lt (opNorm_le_kyFanGauge hk _) (hN m n hm hn)⟩
        obtain ⟨L, hL⟩ := continuousLinearMap_complete_limit A hopCauchy
        refine ⟨L, trivial, ?_⟩
        exact kyFanGauge_tendsto_of_opNorm_tendsto k hL }

end RectangularSymmetricIdealFamily

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
