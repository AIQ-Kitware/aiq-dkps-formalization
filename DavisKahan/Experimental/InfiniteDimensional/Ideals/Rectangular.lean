/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-!
# Open obligations of the rectangular ideal families

The family structure and its proved theory now live in
`DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily`.  The concrete
Hilbert-Schmidt, trace-class, and Schatten families remain unresolved
and stay here.  The Ky Fan family reuses the proved approximation-number package.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace

universe u v

namespace RectangularSymmetricIdealFamily

variable {𝕜 : Type u} [RCLike 𝕜]

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

/-- Trace-class operators as a coherent rectangular family.

Construction route: define the trace gauge through the singular-value
sequence (equivalently `tr |A|`), with adjoint invariance from the shared
singular values of `A` and `A⋆`, ideal control from singular-value
domination, and completeness against the operator-norm limit.  The required
rectangular trace-class theory over `RCLike` scalars is not yet available in
this development, the pinned Mathlib, or the pinned Spectra checkout. -/
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

/-- Schatten `p` operators as a coherent rectangular family.

Construction route: apply the `ℓᵖ` gauge to the approximation-number
sequence; the triangle inequality is the Tomić--Weyl weak-majorization
argument, and completeness follows from Fatou against the operator-norm
limit.  The required Schatten theory is not yet available in this
development, the pinned Mathlib, or the pinned Spectra checkout. -/
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

/-- Ky Fan `k` gauges, with positive `k`, obtained from the already-proved
approximation-number family. -/
noncomputable def kyFan [HasKyFanApproximationGaugeTriangle.{u, v} 𝕜]
    (k : ℕ) (hk : 0 < k) :
    RectangularSymmetricIdealFamily (𝕜 := 𝕜) :=
  (KyFanDominantIdealFamily.kyFan (𝕜 := 𝕜) k hk).
    toRectangularSymmetricIdealFamily

end RectangularSymmetricIdealFamily
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
