/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.Parts
public import ForTauCeti.Analysis.InnerProductSpace.Projection.RealBlocks

/-!
# Real invariant blocks of actual complex Hermitian projections

The real and imaginary operators of a Hermitian projection satisfy the
component identities used in the real block theorem. Consequently its
action on a real complexification admits real invariant blocks of dimension
at most two, without supplied component data or a coordinate basis.
-/

public section

noncomputable section

namespace TauCeti.RealComplexification

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The real component of a self-adjoint operator is real symmetric. -/
theorem realPartOperator_isSymmetric
    (A : RealComplexification E →L[ℂ] RealComplexification E) (hA : IsSelfAdjoint A) :
    (realPartOperator A).toLinearMap.IsSymmetric := by
  intro x y
  have h := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) (ofReal x) (ofReal y)
  simpa [inner_apply, realPartOperator_apply] using congrArg Complex.re h

/-- The imaginary component of a self-adjoint operator is real skew. -/
theorem imaginaryPartOperator_skew
    (A : RealComplexification E →L[ℂ] RealComplexification E) (hA : IsSelfAdjoint A)
    (x y : E) :
    ⟪imaginaryPartOperator A x, y⟫_ℝ = -⟪x, imaginaryPartOperator A y⟫_ℝ := by
  have h := congrArg Complex.im
    ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) (ofReal x) (ofReal y))
  simp [inner_apply] at h
  simp only [imaginaryPartOperator_apply]
  linarith

/-- The real and imaginary components of a genuine Hermitian projection
satisfy the two quadratic projection identities. -/
theorem parts_projection_relations
    (A : RealComplexification E →L[ℂ] RealComplexification E) (hA : IsStarProjection A) :
    let X := (realPartOperator A).toLinearMap
    let Y := (imaginaryPartOperator A).toLinearMap
    X * X - Y * Y = X ∧ X * Y + Y * X = Y := by
  have hsq : A ∘L A = A := hA.isIdempotentElem.eq
  constructor
  · have h := congrArg realPartOperator hsq
    rw [realPartOperator_comp] at h
    exact congrArg ContinuousLinearMap.toLinearMap h
  · have h := congrArg imaginaryPartOperator hsq
    rw [imaginaryPartOperator_comp] at h
    have h' := congrArg ContinuousLinearMap.toLinearMap h
    change (imaginaryPartOperator A).toLinearMap * (realPartOperator A).toLinearMap +
        (realPartOperator A).toLinearMap * (imaginaryPartOperator A).toLinearMap =
      (imaginaryPartOperator A).toLinearMap at h'
    rw [add_comm] at h'
    exact h'

/-- The real components of every finite complex Hermitian projection
have a complete common orthogonal invariant decomposition into real
subspaces of dimension at most two. -/
theorem exists_orthogonal_real_blocks_of_isStarProjection [FiniteDimensional ℝ E]
    (A : RealComplexification E →L[ℂ] RealComplexification E) (hA : IsStarProjection A) :
    let X := realPartOperator A
    let Y := imaginaryPartOperator A
    ∃ F : Finset (Submodule ℝ E),
      (∀ K ∈ F, K ≠ ⊥ ∧ Module.finrank ℝ K ≤ 2 ∧
        (∀ x ∈ K, X x ∈ K) ∧ (∀ x ∈ K, Y x ∈ K)) ∧
      (F : Set (Submodule ℝ E)).Pairwise Submodule.IsOrtho ∧ F.sup id = ⊤ := by
  obtain ⟨hquad, hanti⟩ := parts_projection_relations A hA
  exact exists_orthogonal_real_projection_blocks
    (realPartOperator A).toLinearMap (imaginaryPartOperator A).toLinearMap
      (realPartOperator_isSymmetric A hA.isSelfAdjoint)
      (imaginaryPartOperator_skew A hA.isSelfAdjoint) hquad hanti

end TauCeti.RealComplexification
