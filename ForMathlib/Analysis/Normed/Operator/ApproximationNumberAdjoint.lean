/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Niels Voss, Arnav Mehta, Rawad Kansoh
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import ForMathlib.Analysis.Normed.Operator.ApproximationNumber

/-!
# Adjoint invariance of approximation numbers

This module proves that approximation numbers of bounded operators between
Hilbert spaces are invariant under adjoint. It is separated from the elementary
normed-operator API so the foundational definition does not require
inner-product-space imports.
-/

open NNReal

noncomputable section

universe u v w

namespace ContinuousLinearMap

open Cardinal

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- A finite-rank bounded operator has an adjoint obeying the same
natural-number rank bound.

The proof factors the operator through its finite-dimensional range.  After
 taking adjoints, the adjoint still factors through that same range.

The two ranks live in different universes once the domain and codomain are
allowed to move independently, so the conclusion is stated against the
natural-number bound, which `Cardinal.lift` fixes. -/
private theorem rank_adjoint_le_natCast_of_rank_le
    (R : E →L[𝕜] F) {n : ℕ} (hR : R.rank ≤ (n : Cardinal)) :
    R.adjoint.rank ≤ (n : Cardinal) := by
  have hlt : R.rank < Cardinal.aleph0 :=
    hR.trans_lt Cardinal.natCast_lt_aleph0
  have hrank_eq : R.rank = (R.rank.toNat : Cardinal) := by
    exact (Cardinal.cast_toNat_of_lt_aleph0 hlt).symm
  letI : FiniteDimensional 𝕜 R.range :=
    Module.finite_of_rank_eq_nat hrank_eq
  letI : CompleteSpace R.range := FiniteDimensional.complete 𝕜 R.range
  have hadj : R.adjoint =
      R.rangeRestrict.adjoint ∘L R.range.subtypeL.adjoint := by
    rw [← ContinuousLinearMap.adjoint_comp]
    congr 1
  have hrestrict :
      LinearMap.rank R.rangeRestrict.adjoint.toLinearMap ≤ (n : Cardinal) := by
    have hlift := lift_rank_range_le R.rangeRestrict.adjoint.toLinearMap
    have hbound :
        Cardinal.lift.{v} (Module.rank 𝕜 R.range) ≤ (n : Cardinal) := by
      calc
        Cardinal.lift.{v} (Module.rank 𝕜 R.range)
            ≤ Cardinal.lift.{v} ((n : Cardinal)) := Cardinal.lift_le.mpr hR
        _ = (n : Cardinal) := Cardinal.lift_natCast n
    exact Cardinal.le_natCast_of_lift_le (hlift.trans hbound)
  rw [hadj]
  refine le_trans ?_ hrestrict
  change LinearMap.rank
      (R.rangeRestrict.adjoint.toLinearMap.comp
        R.range.subtypeL.adjoint.toLinearMap) ≤
    LinearMap.rank R.rangeRestrict.adjoint.toLinearMap
  exact LinearMap.rank_comp_le_left _ _

/-- One half of adjoint invariance for approximation numbers. -/
private theorem approximationNumber_adjoint_le
    (T : E →L[𝕜] F) (n : ℕ) :
    T.adjoint.approximationNumber n ≤ T.approximationNumber n := by
  apply T.le_approximationNumber
  intro R hR
  calc
    T.adjoint.approximationNumber n ≤ ‖T.adjoint - R.adjoint‖₊ :=
      T.adjoint.approximationNumber_le
        (rank_adjoint_le_natCast_of_rank_le R hR)
    _ = ‖T - R‖₊ := by
      apply NNReal.eq
      simpa only [coe_nnnorm, ← map_sub] using
        (ContinuousLinearMap.adjoint.norm_map (T - R))

/-- Approximation numbers of bounded operators between Hilbert spaces are
 invariant under adjoint. -/
theorem approximationNumber_adjoint (T : E →L[𝕜] F) (n : ℕ) :
    T.adjoint.approximationNumber n = T.approximationNumber n := by
  apply le_antisymm
  · exact approximationNumber_adjoint_le T n
  · simpa only [ContinuousLinearMap.adjoint_adjoint] using
      (approximationNumber_adjoint_le T.adjoint n)

end ContinuousLinearMap

end
