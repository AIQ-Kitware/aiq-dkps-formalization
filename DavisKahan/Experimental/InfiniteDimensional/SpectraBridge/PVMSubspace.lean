/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import Spectra.ProjValMeasure.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# DKPS adapters for ranges of Spectra projection-valued measures

These declarations intentionally live in the DKPS bridge namespace. They do
not modify Spectra. If this API proves broadly useful, it can be proposed
upstream later without coupling the initial Davis--Kahan integration to that
process.

This module depends only on `Spectra.ProjValMeasure.Basic`, which is a shallow
Mathlib-facing part of Spectra and does not import the spectral-theorem or
Stone-calculus stack.
-/

open scoped InnerProductSpace

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace SpectraBridge

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The range of a measurable projection from a Spectra projection-valued
measure, packaged as a submodule. -/
noncomputable def pvmRangeSubspace (P : Spectra.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) : Submodule ℂ H :=
  (P.proj B hB).range

@[simp]
theorem pvmRangeSubspace_eq_range (P : Spectra.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) :
    pvmRangeSubspace P B hB = (P.proj B hB).range :=
  rfl

/-- Every projected vector belongs to the corresponding range subspace. -/
theorem pvmProjection_mem_rangeSubspace (P : Spectra.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    P.proj B hB x ∈ pvmRangeSubspace P B hB := by
  exact ⟨x, rfl⟩

/-- A vector in the range of a PVM projection is fixed by that projection. -/
theorem pvmProjection_eq_self_of_mem_rangeSubspace
    (P : Spectra.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) {x : H}
    (hx : x ∈ pvmRangeSubspace P B hB) :
    P.proj B hB x = x := by
  rcases hx with ⟨y, rfl⟩
  change P.proj B hB (P.proj B hB y) = P.proj B hB y
  simpa only [mul_apply_eq_comp] using
    congrArg (fun T : H →L[ℂ] H => T y) (P.proj_idem B hB)

/-- Membership in a PVM range is equivalent to being fixed by the
projection. -/
theorem mem_pvmRangeSubspace_iff (P : Spectra.ProjValMeasure H)
    (B : Set ℝ) (hB : MeasurableSet B) (x : H) :
    x ∈ pvmRangeSubspace P B hB ↔ P.proj B hB x = x := by
  constructor
  · exact pvmProjection_eq_self_of_mem_rangeSubspace P B hB
  · intro hx
    exact ⟨x, hx⟩

/-- The range of a measurable PVM projection admits an orthogonal
projection. -/
noncomputable instance pvmRangeSubspace_hasOrthogonalProjection
    (P : Spectra.ProjValMeasure H) (B : Set ℝ)
    (hB : MeasurableSet B) :
    (pvmRangeSubspace P B hB).HasOrthogonalProjection := by
  change (P.proj B hB).range.HasOrthogonalProjection
  exact ContinuousLinearMap.IsIdempotentElem.hasOrthogonalProjection_range
    (show IsIdempotentElem (P.proj B hB) from P.proj_idem B hB)

/-- The PVM projection is the Mathlib star projection onto its range. -/
theorem pvmProjection_eq_starProjection_rangeSubspace
    (P : Spectra.ProjValMeasure H) (B : Set ℝ)
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

end SpectraBridge
end Experimental
end DavisKahan
end ForMathlib
