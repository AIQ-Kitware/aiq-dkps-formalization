/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Rectangular
import DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Unbounded self-adjoint substrate for the exact `sin Θ` program

The declarations are split into adjoint/resolvent, measurable spectral
projection, cutoff, bounded-truncation, and one-unbounded Sylvester layers.
Each analytic law is a separate proof obligation.  In particular, this file
does not hide the unbounded spectral theorem behind fields of type `Prop`.

The Cayley-transform declarations are complex-only.  A real implementation
must pass through complexification and then descend the spectral data.
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
abbrev ClosedOperatorF :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)

/-- Lower semibound for a closed operator. -/
def SemiboundedBelow
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    c * ‖(x : E)‖ ^ 2 ≤
      RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜

/-- Upper semibound for a closed operator. -/
def SemiboundedAbove
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜 ≤
      c * ‖(x : E)‖ ^ 2

/-- Domain-aware equation `A X - X B = C` for two closed blocks. -/
def HasClosedSylvesterEquation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorF (𝕜 := 𝕜) (F := F))
    (X C : F →L[𝕜] E) : Prop :=
  ∀ x : B.domain,
    ∃ hx : X (x : F) ∈ A.domain,
      A.toLinearMap ⟨X (x : F), hx⟩ -
        X (B.toLinearMap x) = C (x : F)

/-- A closed operator whose inverse is everywhere defined and bounded. -/
structure HasBoundedEverywhereInverse
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) where
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

/-- The resolvent is the bounded inverse supplied by the self-adjoint
resolvent theorem.  It is not an unrelated arbitrary choice. -/
noncomputable def closedOperatorResolvent
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (z : 𝕜)
    (hz : RCLike.im z ≠ 0) : E →L[𝕜] E :=
  (selfAdjoint_resolventData_of_im_ne_zero A hA z hz).resolvent

/-- Standard self-adjoint resolvent norm estimate. -/
theorem norm_closedOperatorResolvent_le_inv_abs_im
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (z : 𝕜)
    (hz : RCLike.im z ≠ 0) :
    ‖closedOperatorResolvent A hA z hz‖ ≤ |RCLike.im z|⁻¹ := by
  sorry

section ComplexCayley

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ComplexClosedOperatorH :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)

/-- Cayley transform of a complex self-adjoint closed operator. -/
noncomputable def closedOperatorCayleyTransform
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) : H →L[ℂ] H := by
  sorry

/-- The complex Cayley transform is unitary. -/
theorem closedOperatorCayleyTransform_unitary
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) :
    IsometricEmbedding (closedOperatorCayleyTransform A hA) ∧
      Function.Surjective (closedOperatorCayleyTransform A hA) := by
  sorry

end ComplexCayley

/-- Measurable spectral projection of a self-adjoint closed operator.

The generic `RCLike` signature includes the real case; its implementation is
expected to use complexification and descent.  Laws are only asserted for
measurable sets. -/
noncomputable def selfAdjointSpectralProjection
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) : E →L[𝕜] E := by
  sorry

/-- A measurable spectral projection is idempotent. -/
theorem selfAdjointSpectralProjection_idempotent
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) (hs : MeasurableSet s) :
    selfAdjointSpectralProjection A hA s ∘L
      selfAdjointSpectralProjection A hA s =
        selfAdjointSpectralProjection A hA s := by
  sorry

/-- A measurable spectral projection is symmetric. -/
theorem selfAdjointSpectralProjection_symmetric
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) (hs : MeasurableSet s) :
    (selfAdjointSpectralProjection A hA s).IsSymmetric := by
  sorry

/-- Spectral projection of the empty set. -/
theorem selfAdjointSpectralProjection_empty
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    selfAdjointSpectralProjection A hA ∅ = 0 := by
  sorry

/-- Spectral projection of the whole real line. -/
theorem selfAdjointSpectralProjection_univ
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    selfAdjointSpectralProjection A hA Set.univ =
      ContinuousLinearMap.id 𝕜 E := by
  sorry

/-- Multiplication of measurable spectral projections corresponds to
intersection. -/
theorem selfAdjointSpectralProjection_inter
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    selfAdjointSpectralProjection A hA s ∘L
      selfAdjointSpectralProjection A hA t =
        selfAdjointSpectralProjection A hA (s ∩ t) := by
  sorry

/-- Finite additivity on disjoint measurable sets. -/
theorem selfAdjointSpectralProjection_disjoint_additive
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    selfAdjointSpectralProjection A hA (s ∪ t) =
      selfAdjointSpectralProjection A hA s +
        selfAdjointSpectralProjection A hA t := by
  sorry

/-- Countable additivity in the strong operator topology. -/
theorem selfAdjointSpectralProjection_iUnion_tendsto
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : ℕ → Set ℝ)
    (hs : ∀ n, MeasurableSet (s n))
    (hdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    (x : E) :
    Tendsto
      (fun n =>
        (∑ k ∈ Finset.range n,
          selfAdjointSpectralProjection A hA (s k)) x)
      atTop
      (𝓝 (selfAdjointSpectralProjection A hA (⋃ k, s k) x)) := by
  sorry

/-- A measurable set disjoint from the real spectrum has zero projection. -/
theorem selfAdjointSpectralProjection_eq_zero_of_disjoint_spectrum
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ)
    (hs : MeasurableSet s)
    (hdisj : Disjoint s A.realSpectrum) :
    selfAdjointSpectralProjection A hA s = 0 := by
  sorry

/-- Vectors in a bounded spectral interval belong to the operator domain. -/
theorem selfAdjointSpectralProjection_Icc_range_le_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (a b : ℝ) :
    LinearMap.range
      (selfAdjointSpectralProjection A hA (Set.Icc a b)).toLinearMap ≤
        A.domain := by
  sorry

/-- Symmetric bounded spectral cutoff. -/
noncomputable def spectralCutoff
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) : E →L[𝕜] E :=
  selfAdjointSpectralProjection A hA (Set.Icc (-τ) τ)

/-- Spectral cutoff is an orthogonal projection. -/
theorem spectralCutoff_isOrthogonalProjection
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    spectralCutoff A hA τ ∘L spectralCutoff A hA τ =
        spectralCutoff A hA τ ∧
      (spectralCutoff A hA τ).IsSymmetric := by
  sorry

/-- Cutoff vectors belong to the operator domain. -/
theorem spectralCutoff_range_le_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    LinearMap.range (spectralCutoff A hA τ).toLinearMap ≤ A.domain := by
  sorry

/-- Spectral cutoffs preserve the operator domain and commute with the
operator there. -/
theorem spectralCutoff_commutes_on_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) (x : A.domain) :
    ∃ hx : spectralCutoff A hA τ (x : E) ∈ A.domain,
      A.toLinearMap ⟨spectralCutoff A hA τ (x : E), hx⟩ =
        spectralCutoff A hA τ (A.toLinearMap x) := by
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


/-- Spectral truncations reconstruct the closed operator on its domain. -/
theorem boundedSpectralTruncation_tendsto_on_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (x : A.domain) :
    Tendsto
      (fun τ : ℝ => boundedSpectralTruncation A hA τ (x : E))
      atTop (𝓝 (A.toLinearMap x)) := by
  sorry

/-- Domain characterization by uniform boundedness of the spectral
truncations.  This is the concrete replacement for an opaque domain field in a
spectral-resolution record. -/
theorem mem_domain_iff_boundedSpectralTruncation_norm_bounded
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (x : E) :
    x ∈ A.domain ↔
      ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖boundedSpectralTruncation A hA τ x‖ ≤ C := by
  sorry

/-- The bounded truncation preserves a lower semibound on its cutoff range. -/
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

/-- The bounded truncation preserves an upper semibound on its cutoff range. -/
theorem boundedSpectralTruncation_upperBound
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) {c : ℝ}
    (hUpper : ∀ x : A.domain,
      RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜 ≤
        c * ‖(x : E)‖ ^ 2)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ x, RCLike.re ⟪boundedSpectralTruncation A hA τ x,
        spectralCutoff A hA τ x⟫_𝕜 ≤
      c * ‖spectralCutoff A hA τ x‖ ^ 2 := by
  sorry

/-- Bounded spectral truncation commutes with its cutoff projection. -/
theorem boundedSpectralTruncation_commutes_cutoff
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    boundedSpectralTruncation A hA τ ∘L spectralCutoff A hA τ =
      boundedSpectralTruncation A hA τ ∧
    spectralCutoff A hA τ ∘L boundedSpectralTruncation A hA τ =
      boundedSpectralTruncation A hA τ := by
  sorry

/-- Bounded spectrum forces the domain of a self-adjoint closed operator to be
all of the ambient Hilbert space. -/
theorem domain_eq_top_of_spectrumIn_Icc
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) {β α : ℝ} (hβα : β ≤ α)
    (hσ : A.realSpectrum ⊆ Set.Icc β α) :
    A.domain = ⊤ := by
  sorry

/-- Bounded realization of a closed operator on its full domain. -/
structure BoundedRealization
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) where
  operator : E →L[𝕜] E
  domain_eq_top : A.domain = ⊤
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
