/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForTauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# DKPS adapters for ranges of projection-valued measures

These declarations intentionally live in the DKPS bridge namespace. If this API
proves broadly useful it can be proposed upstream later.

The projection-valued measure structure itself is
`TauCeti.ProjValMeasure`, in
`ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Basic.lean` — ported from
Spectra with provenance recorded there.  This module was repointed from
`Spectra.ProjValMeasure` to it on 2026-07-28; the two structures are the same,
so nothing in the mathematics below changed.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The range of a measurable projection from a Spectra projection-valued
measure, packaged as a submodule. -/
noncomputable def pvmRangeSubspace (P : TauCeti.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) : Submodule ℂ H :=
  (P.proj B hB).range

/-- The subspace attached to a projection-valued measure is the range of its projection. -/
@[simp]
theorem pvmRangeSubspace_eq_range (P : TauCeti.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    pvmRangeSubspace P B hB = (P.proj B hB).range :=
  rfl

/-- Every projected vector belongs to the corresponding range subspace. -/
theorem pvmProjection_mem_rangeSubspace (P : TauCeti.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    P.proj B hB x ∈ pvmRangeSubspace P B hB := by
  exact ⟨x, rfl⟩

/-- A vector in the range of a PVM projection is fixed by that projection. -/
theorem pvmProjection_eq_self_of_mem_rangeSubspace
    (P : TauCeti.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) {x : H}
    (hx : x ∈ pvmRangeSubspace P B hB) :
    P.proj B hB x = x := by
  rcases hx with ⟨y, rfl⟩
  change P.proj B hB (P.proj B hB y) = P.proj B hB y
  simpa only [mul_apply_eq_comp] using
    congrArg (fun T : H →L[ℂ] H => T y) (P.proj_idem B hB)

/-- Membership in a PVM range is equivalent to being fixed by the
projection. -/
theorem mem_pvmRangeSubspace_iff (P : TauCeti.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    x ∈ pvmRangeSubspace P B hB ↔ P.proj B hB x = x := by
  constructor
  · exact pvmProjection_eq_self_of_mem_rangeSubspace P B hB
  · intro hx
    exact ⟨x, hx⟩

/-- The range of a measurable PVM projection is complete. -/
noncomputable instance pvmRangeSubspace_completeSpace
    (P : TauCeti.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    CompleteSpace (pvmRangeSubspace P B hB) := by
  change CompleteSpace (P.proj B hB).range
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (P.proj_idem B hB)).completeSpace_coe

/-- The range of a measurable PVM projection admits an orthogonal
projection. -/
noncomputable instance pvmRangeSubspace_hasOrthogonalProjection
    (P : TauCeti.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    (pvmRangeSubspace P B hB).HasOrthogonalProjection := by
  change (P.proj B hB).range.HasOrthogonalProjection
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (show IsIdempotentElem (P.proj B hB) from P.proj_idem B hB)

/-- The PVM projection is the Mathlib star projection onto its range. -/
theorem pvmProjection_eq_starProjection_rangeSubspace
    (P : TauCeti.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    P.proj B hB = (pvmRangeSubspace P B hB).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact pvmProjection_mem_rangeSubspace P B hB x
  · intro y hy
    have hyfix : P.proj B hB y = y :=
      pvmProjection_eq_self_of_mem_rangeSubspace P B hB hy
    rw [← hyfix]
    have hadj := ContinuousLinearMap.adjoint_inner_right
      (P.proj B hB) (x - P.proj B hB x) y
    rw [← ContinuousLinearMap.star_eq_adjoint,
      (P.isSelfAdjoint_proj B hB).star_eq] at hadj
    rw [hadj, map_sub,
      pvmProjection_eq_self_of_mem_rangeSubspace P B hB
        (pvmProjection_mem_rangeSubspace P B hB x), sub_self, inner_zero_left]

end Experimental
end DavisKahan
end TauCeti