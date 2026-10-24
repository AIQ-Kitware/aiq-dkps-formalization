/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.RealPoints
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import ForTauCeti.Analysis.InnerProductSpace.Projection.TwoBlocks

/-!
# Real blocks for projections preserving a conjugation

A bounded complex operator commuting with a specified conjugation restricts
to its accepted fixed real subspace. Orthogonal projections remain orthogonal
projections there. Two such projections consequently have common real
invariant blocks of dimension at most two, with no supplied real basis.
-/

public section

noncomputable section

namespace TauCeti

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local instance : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E

/-- Restrict a conjugation-preserving operator to the accepted fixed real space. -/
def realPointsOperator (J : E →ₛₗ[starRingEnd ℂ] E) (T : E →L[ℂ] E)
    (hTJ : ∀ x, J (T x) = T (J x)) : realPoints J →L[ℝ] realPoints J :=
  (T.restrictScalars ℝ).restrict fun x hx => by
    rw [mem_realPoints]
    change J (T x) = T x
    rw [hTJ, mem_realPoints.mp hx]

/-- The fixed-space restriction has the original operator's actual action. -/
@[simp]
theorem realPointsOperator_apply
    (J : E →ₛₗ[starRingEnd ℂ] E) (T : E →L[ℂ] E)
    (hTJ : ∀ x, J (T x) = T (J x)) (x : realPoints J) :
    (realPointsOperator J T hTJ x : E) = T x := by
  unfold realPointsOperator
  rfl

/-- A complex orthogonal projection preserving a conjugation is a real
orthogonal projection on its fixed space. -/
theorem realPointsOperator_isStarProjection [FiniteDimensional ℂ E]
    (J : E →ₛₗ[starRingEnd ℂ] E) (P : E →L[ℂ] E)
    (hPJ : ∀ x, J (P x) = P (J x)) (hP : IsStarProjection P) :
    IsStarProjection (realPointsOperator J P hPJ) := by
  refine ⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_⟩
  · change realPointsOperator J P hPJ * realPointsOperator J P hPJ = _
    ext x
    change P (P (x : E)) = P (x : E)
    exact congrArg (fun A : E →L[ℂ] E => A x) hP.isIdempotentElem.eq
  · intro x y
    change (⟪P (x : E), (y : E)⟫_ℂ).re = (⟪(x : E), P (y : E)⟫_ℂ).re
    exact congrArg Complex.re (hP.isSelfAdjoint.isSymmetric (x : E) (y : E))

/-- Two complex orthogonal projections preserving a specified conjugation
have a complete orthogonal family of common invariant real lines and planes
in its fixed real subspace. -/
theorem exists_orthogonal_realPoints_blocks_of_two_projections
    [FiniteDimensional ℂ E]
    (J : E →ₛₗ[starRingEnd ℂ] E)
    (P Q : E →L[ℂ] E) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPJ : ∀ x, J (P x) = P (J x)) (hQJ : ∀ x, J (Q x) = Q (J x)) :
    ∃ F : Finset (Submodule ℝ (realPoints J)),
      (∀ K ∈ F, K ≠ ⊥ ∧ Module.finrank ℝ K ≤ 2 ∧
        (∀ x ∈ K, realPointsOperator J P hPJ x ∈ K) ∧
        (∀ x ∈ K, realPointsOperator J Q hQJ x ∈ K)) ∧
      (F : Set (Submodule ℝ (realPoints J))).Pairwise Submodule.IsOrtho ∧ F.sup id = ⊤ :=
  exists_orthogonal_blocks_of_two_projections
    (realPointsOperator J P hPJ) (realPointsOperator J Q hQJ)
    (realPointsOperator_isStarProjection J P hPJ hP)
    (realPointsOperator_isStarProjection J Q hQJ hQ)

end TauCeti
