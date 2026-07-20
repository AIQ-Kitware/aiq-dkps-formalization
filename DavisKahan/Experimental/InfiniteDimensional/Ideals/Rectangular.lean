/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily

/-!
# Open obligations of the rectangular ideal families

The family structure and its proved theory now live in
`DavisKahan.OperatorIdeal.UnitarilyInvariant.RectangularFamily`.  The concrete
Hilbert-Schmidt, trace-class, Schatten and Ky Fan families remain unresolved
and stay here.
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
