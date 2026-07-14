/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.ExactSinTheta.RectangularIdeals
import ForMathlib.Analysis.InnerProductSpace.DavisKahan.Experimental.Foundation.Unbounded

/-!
# Unbounded self-adjoint substrate for the exact `sin Θ` program

The declarations are split into adjoint/resolvent, spectral resolution,
spectral cutoff, and one-unbounded Sylvester layers.  They deliberately avoid
hiding the whole unbounded spectral theorem behind one construction.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace
open scoped Topology
open Filter

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

abbrev ClosedOperatorE :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)

/-- A closed operator whose inverse is everywhere defined and bounded. -/
structure HasBoundedEverywhereInverse (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) where
  inv : E →L[𝕜] E
  inv_mapsTo_domain : ∀ y, inv y ∈ A.domain
  apply_inv : ∀ y,
    A.toLinearMap ⟨inv y, inv_mapsTo_domain y⟩ = y
  inv_apply : ∀ x : A.domain, inv (A.toLinearMap x) = (x : E)

/-- The provisional adjoint has closed graph. -/
theorem closedOperator_adjoint_closed
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) :
    IsClosed (Set.range fun x : A.adjoint.domain =>
      ((x : E), A.adjoint.toLinearMap x)) := by
  sorry

/-- Double adjoint recovers a densely defined closed operator. -/
theorem closedOperator_adjoint_adjoint
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) :
    A.adjoint.adjoint = A := by
  sorry

/-- Nonreal resolvent of a self-adjoint closed operator. -/
noncomputable def closedOperatorResolvent
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (z : 𝕜) : E →L[𝕜] E := by
  sorry

/-- Bounded inverse data for the shifted closed operator `A - z`. -/
structure ClosedResolventData
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (z : 𝕜) where
  resolvent : E →L[𝕜] E
  mapsTo_domain : ∀ y, resolvent y ∈ A.domain
  right_inverse : ∀ y,
    A.toLinearMap ⟨resolvent y, mapsTo_domain y⟩ - z • resolvent y = y
  left_inverse : ∀ x : A.domain,
    resolvent (A.toLinearMap x - z • (x : E)) = (x : E)

/-- A nonreal point belongs to the resolvent set. -/
noncomputable def selfAdjoint_resolventData_of_im_ne_zero
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (z : 𝕜)
    (hz : RCLike.im z ≠ 0) :
    ClosedResolventData A z := by
  sorry

/-- Standard self-adjoint resolvent norm estimate. -/
theorem norm_closedOperatorResolvent_le_inv_abs_im
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (z : 𝕜)
    (hz : RCLike.im z ≠ 0) :
    ‖closedOperatorResolvent A z‖ ≤ |RCLike.im z|⁻¹ := by
  sorry

/-- Cayley transform of a self-adjoint closed operator. -/
noncomputable def closedOperatorCayleyTransform
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) :
    E →L[𝕜] E := by
  sorry

/-- The Cayley transform is unitary. -/
theorem closedOperatorCayleyTransform_unitary
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    IsometricEmbedding (closedOperatorCayleyTransform A) ∧
      Function.Surjective (closedOperatorCayleyTransform A) := by
  sorry

/-- Spectral resolution data for a self-adjoint closed operator. -/
structure SelfAdjointSpectralResolution
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) where
  projection : Set ℝ → E →L[𝕜] E
  projection_idempotent : ∀ s, projection s ∘L projection s = projection s
  projection_symmetric : ∀ s, (projection s).IsSymmetric
  empty : projection ∅ = 0
  univ : projection Set.univ = ContinuousLinearMap.id 𝕜 E
  disjoint_additive : ∀ s t, Disjoint s t →
    projection (s ∪ t) = projection s + projection t
  countably_additive_strong : Prop
  reconstructs_operator : Prop
  characterizes_domain : Prop

/-- Spectral resolution supplied by the unbounded spectral theorem. -/
noncomputable def selfAdjointSpectralResolution
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    SelfAdjointSpectralResolution A := by
  sorry

/-- Symmetric bounded spectral cutoff. -/
noncomputable def spectralCutoff
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) : E →L[𝕜] E :=
  (selfAdjointSpectralResolution A hA).projection (Set.Icc (-τ) τ)

/-- Spectral cutoff is an orthogonal projection. -/
theorem spectralCutoff_isOrthogonalProjection
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    spectralCutoff A hA τ ∘L spectralCutoff A hA τ = spectralCutoff A hA τ ∧
      (spectralCutoff A hA τ).IsSymmetric := by
  sorry

/-- Cutoff vectors belong to the operator domain. -/
theorem spectralCutoff_range_le_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    LinearMap.range (spectralCutoff A hA τ).toLinearMap ≤ A.domain := by
  sorry

/-- Spectral cutoffs converge strongly to the identity. -/
theorem spectralCutoff_tendsto_identity
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    ∀ x, Tendsto (fun τ : ℝ => spectralCutoff A hA τ x) atTop (𝓝 x) := by
  sorry

/-- Bounded truncation of a self-adjoint closed operator. -/
noncomputable def boundedSpectralTruncation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) : E →L[𝕜] E := by
  sorry

/-- Bounded truncation is self-adjoint. -/
theorem boundedSpectralTruncation_isSymmetric
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    (boundedSpectralTruncation A hA τ).IsSymmetric := by
  sorry

/-- Bounded truncation agrees with the original operator on the cutoff range. -/
theorem boundedSpectralTruncation_eq_on_cutoff
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) (x : E) :
    ∃ hx : spectralCutoff A hA τ x ∈ A.domain,
      boundedSpectralTruncation A hA τ x =
        A.toLinearMap ⟨spectralCutoff A hA τ x, hx⟩ := by
  sorry

/-- The bounded truncation preserves a lower semibound. -/
theorem boundedSpectralTruncation_lowerBound
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) {c : ℝ}
    (hLower : ∀ x : A.domain,
      c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ x, c * ‖spectralCutoff A hA τ x‖ ^ 2 ≤
      RCLike.re ⟪boundedSpectralTruncation A hA τ x,
        spectralCutoff A hA τ x⟫_𝕜 := by
  sorry

/-- Bounded realization of a closed operator on its domain. -/
structure BoundedRealization
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) where
  operator : E →L[𝕜] E
  agrees : ∀ x : A.domain, operator (x : E) = A.toLinearMap x

/-- Spectral inclusion in a bounded interval produces a bounded realization. -/
theorem boundedRealization_of_spectrumIn_Icc
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) {β α : ℝ} (hβα : β ≤ α)
    (hσ : A.realSpectrum ⊆ Set.Icc β α) :
    ∃ hB : BoundedRealization A,
      ‖hB.operator - (((β + α) / 2 : ℝ) : 𝕜) •
        ContinuousLinearMap.id 𝕜 E‖ ≤ (α - β) / 2 := by
  sorry

/-- Exterior spectral inclusion produces a bounded inverse after centering. -/
theorem boundedInverse_of_spectrumOutside
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) {β α δ : ℝ}
    (hβα : β ≤ α) (hδ : 0 < δ)
    (hσ : A.realSpectrum ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) :
    ∃ hInv : HasBoundedEverywhereInverse
        (A.addBounded
          (-((((β + α) / 2 : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 E))),
      ‖hInv.inv‖ ≤ ((α - β) / 2 + δ)⁻¹ := by
  sorry

/-- Interval/exterior spectral configuration for two closed self-adjoint blocks. -/
def UnboundedIntervalExteriorGap
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F))
    (β α δ : ℝ) : Prop :=
  (A.realSpectrum ⊆ Set.Icc β α ∧
    B.realSpectrum ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
  (B.realSpectrum ⊆ Set.Icc β α ∧
    A.realSpectrum ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x})

/-- Equation with one unbounded left block and one bounded right block. -/
def HasUnboundedBoundedSylvesterEquation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : F →L[𝕜] F) (X C : F →L[𝕜] E) : Prop :=
  ∀ x, ∃ hx : X x ∈ A.domain,
    A.toLinearMap ⟨X x, hx⟩ - X (B x) = C x

/-- One-unbounded version of the bound/inverse Sylvester estimate. -/
theorem sylvester_mem_and_gauge_le_of_unbounded_bound_inverse
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)}
    (hAinv : HasBoundedEverywhereInverse A)
    (B : F →L[𝕜] F) {X C : F →L[𝕜] E}
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hInvNorm : ‖hAinv.inv‖ ≤ (ρ + δ)⁻¹)
    (hB : ‖B‖ ≤ ρ)
    (hEq : HasUnboundedBoundedSylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  sorry

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
