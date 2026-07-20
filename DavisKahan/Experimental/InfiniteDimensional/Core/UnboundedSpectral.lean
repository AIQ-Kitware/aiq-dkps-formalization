/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.ClosedSylvesterEquation
import DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Open obligations of the unbounded spectral theory

The proved front now lives in `DavisKahan.Sylvester.ClosedSylvesterEquation`.
The provisional adjoint properties, the spectral projections and the bounded
spectral truncation remain unresolved and stay here.
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
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

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

/-- Apply the shifted operator `A - z` on its natural domain. -/
def shiftedApply
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (z : 𝕜)
    (x : A.domain) : E :=
  A.toLinearMap x - z • (x : E)

/-- Bounded inverse data for the shifted closed operator `A - z`. -/
structure ClosedResolventData
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (z : 𝕜) where
  resolvent : E →L[𝕜] E
  mapsTo_domain : ∀ y, resolvent y ∈ A.domain
  right_inverse : ∀ y,
    A.toLinearMap ⟨resolvent y, mapsTo_domain y⟩ - z • resolvent y = y
  left_inverse : ∀ x : A.domain,
    resolvent (A.toLinearMap x - z • (x : E)) = (x : E)

namespace ClosedResolventData

omit [CompleteSpace E] in
/-- Resolvent data makes the shifted operator injective. -/
theorem shiftedApply_injective
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)} {z : 𝕜}
    (h : ClosedResolventData A z) :
    Function.Injective (shiftedApply A z) := by
  intro x y hxy
  apply Subtype.ext
  calc
    (x : E) = h.resolvent (shiftedApply A z x) := (h.left_inverse x).symm
    _ = h.resolvent (shiftedApply A z y) := congrArg h.resolvent hxy
    _ = (y : E) := h.left_inverse y

omit [CompleteSpace E] in
/-- Resolvent data makes the shifted operator surjective. -/
theorem shiftedApply_surjective
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)} {z : 𝕜}
    (h : ClosedResolventData A z) :
    Function.Surjective (shiftedApply A z) := by
  intro y
  refine ⟨⟨h.resolvent y, h.mapsTo_domain y⟩, ?_⟩
  exact h.right_inverse y

omit [CompleteSpace E] in
/-- Bounded inverse data for a fixed shifted operator is unique. -/
theorem resolvent_eq
    {A : ClosedOperatorE (𝕜 := 𝕜) (E := E)} {z : 𝕜}
    (h k : ClosedResolventData A z) :
    h.resolvent = k.resolvent := by
  ext y
  have hk : shiftedApply A z
      ⟨k.resolvent y, k.mapsTo_domain y⟩ = y := by
    simpa [shiftedApply] using k.right_inverse y
  calc
    h.resolvent y =
        h.resolvent (shiftedApply A z
          ⟨k.resolvent y, k.mapsTo_domain y⟩) :=
      congrArg h.resolvent hk.symm
    _ = k.resolvent y := h.left_inverse _

end ClosedResolventData

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

/-- Equation with one unbounded left block and one bounded right block.

This is not a second equation model: it is the closed Sylvester equation with
the right block embedded as a full-domain closed operator. -/
abbrev HasUnboundedBoundedSylvesterEquation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : F →L[𝕜] F) (X C : F →L[𝕜] E) : Prop :=
  HasClosedSylvesterEquation A
    (ForMathlib.DavisKahanExt.ClosedOperator.ofBounded B) X C

/-- One-unbounded version of the bound/inverse Sylvester estimate.

The solution is exhibited as the ideal-gauge limit of the Neumann iteration
`X = J C + J X B + J (J X B) B + ⋯` (with `J` the bounded inverse of the
unbounded block): each iterate lies in the ideal by the two-sided composition
law, the gauges decay geometrically because `‖J‖ ‖B‖ ≤ ρ / (ρ + δ) < 1`, the
`gauge_complete` field produces an ideal member as the gauge limit, and the
operator-norm contraction identifies that limit with `X`.  The gauge estimate
then follows from the fixed-point identity by absorption, exactly as in the
operator-norm shift-and-invert argument. -/
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
  set J : E →L[𝕜] E := hAinv.inv with hJdef
  have hρδ : (0 : ℝ) < ρ + δ := by linarith
  set q : ℝ := ρ * (ρ + δ)⁻¹ with hqdef
  have hq0 : 0 ≤ q := mul_nonneg hρ (inv_nonneg.mpr hρδ.le)
  have hq1 : q < 1 := by
    rw [hqdef, ← div_eq_mul_inv]
    exact (div_lt_one hρδ).mpr (by linarith)
  -- every value of `X` lies in the domain of `A`
  have hdom : ∀ x : F, X x ∈ A.domain := fun x =>
    hEq.mapsTo_domain ⟨x, Submodule.mem_top⟩
  -- the bounded fixed-point identity `X = J (C + X B)`
  have hfix : X = J ∘L (C + X ∘L B) := by
    ext x
    have heq : A.toLinearMap ⟨X x, hdom x⟩ - X (B x) = C x :=
      hEq.equation ⟨x, Submodule.mem_top⟩
    have happ : A.toLinearMap ⟨X x, hdom x⟩ = C x + X (B x) := by
      rw [← heq]; abel
    have hinv : J (A.toLinearMap ⟨X x, hdom x⟩) = X x :=
      hAinv.inv_apply ⟨X x, hdom x⟩
    calc X x = J (A.toLinearMap ⟨X x, hdom x⟩) := hinv.symm
      _ = J (C x + X (B x)) := by rw [happ]
      _ = (J ∘L (C + X ∘L B)) x := by
          simp [ContinuousLinearMap.comp_apply]
  -- the Neumann contraction `Y ↦ J Y B`
  set T : (F →L[𝕜] E) → (F →L[𝕜] E) := fun Y => J ∘L Y ∘L B with hTdef
  have hTadd : ∀ Y Z : F →L[𝕜] E, T (Y + Z) = T Y + T Z := by
    intro Y Z
    simp only [hTdef]
    simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  have hTnorm : ∀ Y : F →L[𝕜] E, ‖T Y‖ ≤ q * ‖Y‖ := by
    intro Y
    calc ‖T Y‖ ≤ ‖J‖ * ‖Y‖ * ‖B‖ :=
          RectangularSymmetricIdealFamily.opNorm_comp_comp_le J Y B
      _ ≤ (ρ + δ)⁻¹ * ‖Y‖ * ρ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hInvNorm (norm_nonneg Y))
            hB (norm_nonneg B)
            (mul_nonneg (inv_nonneg.mpr hρδ.le) (norm_nonneg Y))
      _ = q * ‖Y‖ := by rw [hqdef]; ring
  have hTmem : ∀ Y : F →L[𝕜] E, N.Mem Y → N.Mem (T Y) := fun Y hY =>
    N.comp_mem J B hY
  have hTgauge : ∀ Y : F →L[𝕜] E, N.Mem Y →
      N.gauge (T Y) ≤ q * N.gauge Y := by
    intro Y hY
    calc N.gauge (T Y) ≤ ‖J‖ * N.gauge Y * ‖B‖ := N.gauge_comp_le J B hY
      _ ≤ (ρ + δ)⁻¹ * N.gauge Y * ρ :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right hInvNorm (N.gauge_nonneg hY))
            hB (norm_nonneg B)
            (mul_nonneg (inv_nonneg.mpr hρδ.le) (N.gauge_nonneg hY))
      _ = q * N.gauge Y := by rw [hqdef]; ring
  -- the Neumann iterates and their partial sums
  set t : ℕ → F →L[𝕜] E := fun n => T^[n] (J ∘L C) with htdef
  have ht0 : t 0 = J ∘L C := rfl
  have htsucc : ∀ n, t (n + 1) = T (t n) := by
    intro n
    simp only [htdef, Function.iterate_succ_apply']
  have htmem : ∀ n, N.Mem (t n) := by
    intro n
    induction n with
    | zero => exact N.comp_left_mem J hC
    | succ n ih => rw [htsucc]; exact hTmem _ ih
  set g₀ : ℝ := N.gauge (J ∘L C) with hg₀def
  have htgauge : ∀ n, N.gauge (t n) ≤ q ^ n * g₀ := by
    intro n
    induction n with
    | zero => simp [htdef, hg₀def]
    | succ n ih =>
        rw [htsucc, pow_succ]
        calc N.gauge (T (t n)) ≤ q * N.gauge (t n) := hTgauge _ (htmem n)
          _ ≤ q * (q ^ n * g₀) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ n * q * g₀ := by ring
  set P : ℕ → F →L[𝕜] E := fun n => ∑ k ∈ Finset.range n, t k with hPdef
  have hPmem : ∀ n, N.Mem (P n) := by
    intro n
    simp only [hPdef]
    exact N.finset_sum_mem (Finset.range n) t fun k _ => htmem k
  -- the real comparison sequence of geometric partial sums
  set G : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, q ^ k * g₀ with hGdef
  have hgap : ∀ {m n : ℕ}, n ≤ m → N.gauge (P m - P n) ≤ G m - G n := by
    intro m n hnm
    have hsum : P m - P n = ∑ k ∈ Finset.Ico n m, t k :=
      (Finset.sum_Ico_eq_sub _ hnm).symm
    have hG : ∑ k ∈ Finset.Ico n m, q ^ k * g₀ = G m - G n :=
      Finset.sum_Ico_eq_sub _ hnm
    rw [hsum, ← hG]
    calc N.gauge (∑ k ∈ Finset.Ico n m, t k)
        ≤ ∑ k ∈ Finset.Ico n m, N.gauge (t k) :=
          N.gauge_finset_sum_le (Finset.Ico n m) t fun k _ => htmem k
      _ ≤ ∑ k ∈ Finset.Ico n m, q ^ k * g₀ :=
          Finset.sum_le_sum fun k _ => htgauge k
  have hGcauchy : CauchySeq G := by
    have hsummable : Summable fun k : ℕ => q ^ k * g₀ :=
      (summable_geometric_of_lt_one hq0 hq1).mul_right g₀
    exact hsummable.hasSum.tendsto_sum_nat.cauchySeq
  have hPcauchy : ∀ ε : ℝ, 0 < ε → ∃ N₀, ∀ m n, N₀ ≤ m → N₀ ≤ n →
      N.gauge (P m - P n) < ε := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.mp hGcauchy ε hε
    refine ⟨N₀, fun m n hm hn => ?_⟩
    rcases le_total n m with h | h
    · refine lt_of_le_of_lt (hgap h) ?_
      calc G m - G n ≤ |G m - G n| := le_abs_self _
        _ = dist (G m) (G n) := (Real.dist_eq _ _).symm
        _ < ε := hN₀ m hm n hn
    · have hswap : N.gauge (P m - P n) = N.gauge (P n - P m) := by
        rw [show P m - P n = -(P n - P m) from by abel,
          N.gauge_neg (N.sub_mem (hPmem n) (hPmem m))]
      rw [hswap]
      refine lt_of_le_of_lt (hgap h) ?_
      calc G n - G m ≤ |G n - G m| := le_abs_self _
        _ = dist (G n) (G m) := (Real.dist_eq _ _).symm
        _ < ε := hN₀ n hn m hm
  obtain ⟨L, hLmem, hLlim⟩ := N.gauge_complete P hPmem hPcauchy
  -- the partial sums converge to `L` in operator norm
  have hPL : Filter.Tendsto P Filter.atTop (nhds L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => N.opNorm_le_gauge (N.sub_mem (hPmem n) hLmem)) ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hLlim ε hε
    refine ⟨N₀, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (N.gauge_nonneg (N.sub_mem (hPmem n) hLmem))]
    exact hN₀ n hn
  -- the partial sums converge to `X` in operator norm
  have hfix' : X = t 0 + T X := by
    conv_lhs => rw [hfix]
    rw [ht0, ContinuousLinearMap.comp_add]
  have hchain : ∀ n, T^[n] X = t n + T^[n + 1] X := by
    intro n
    induction n with
    | zero => simpa using hfix'
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hTadd, ← htsucc,
          ← Function.iterate_succ_apply' T (n + 1) X]
  have hXP : ∀ n, X = P n + T^[n] X := by
    intro n
    induction n with
    | zero => simp [hPdef]
    | succ n ih =>
        have hPsucc : P (n + 1) = P n + t n := Finset.sum_range_succ _ _
        rw [hPsucc]
        calc X = P n + T^[n] X := ih
          _ = P n + (t n + T^[n + 1] X) := by rw [hchain n]
          _ = P n + t n + T^[n + 1] X := by abel
  have htail : ∀ n, ‖T^[n] X‖ ≤ q ^ n * ‖X‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ]
        calc ‖T (T^[n] X)‖ ≤ q * ‖T^[n] X‖ := hTnorm _
          _ ≤ q * (q ^ n * ‖X‖) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ n * q * ‖X‖ := by ring
  have hPX : Filter.Tendsto P Filter.atTop (nhds X) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n, ‖P n - X‖ ≤ q ^ n * ‖X‖ := by
      intro n
      have hPnX : P n - X = -(T^[n] X) := by
        conv_lhs => rw [hXP n]
        abel
      rw [hPnX, norm_neg]
      exact htail n
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖X‖
  have hXL : X = L := tendsto_nhds_unique hPX hPL
  have hXmem : N.Mem X := by rw [hXL]; exact hLmem
  -- the gauge estimate by absorption through the fixed point
  have hXBmem : N.Mem (X ∘L B) := N.comp_right_mem B hXmem
  have hgauge : N.gauge X ≤ (ρ + δ)⁻¹ * (N.gauge C + N.gauge X * ρ) := by
    conv_lhs => rw [hfix]
    calc N.gauge (J ∘L (C + X ∘L B))
        ≤ ‖J‖ * N.gauge (C + X ∘L B) :=
          N.gauge_comp_left_le_mul J (N.add_mem hC hXBmem)
      _ ≤ (ρ + δ)⁻¹ * N.gauge (C + X ∘L B) :=
          mul_le_mul_of_nonneg_right hInvNorm
            (N.gauge_nonneg (N.add_mem hC hXBmem))
      _ ≤ (ρ + δ)⁻¹ * (N.gauge C + N.gauge X * ρ) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hρδ.le)
          refine (N.gauge_add_le hC hXBmem).trans (add_le_add le_rfl ?_)
          exact (N.gauge_comp_right_le_mul B hXmem).trans
            (mul_le_mul_of_nonneg_left hB (N.gauge_nonneg hXmem))
  refine ⟨hXmem, ?_⟩
  have hkey := mul_le_mul_of_nonneg_left hgauge hρδ.le
  rw [← mul_assoc, mul_inv_cancel₀ hρδ.ne', one_mul] at hkey
  linarith



/-- Transfer a closed Sylvester equation to a bounded realization of its
right block.  Agreement on the dense domain extends to the whole space through
the closed graph of the left block. -/
theorem closedSylvesterEquation_boundedRealization
    {A : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := E)}
    {B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F)}
    {X C : F →L[𝕜] E} {T : F →L[𝕜] F}
    (hEq : HasClosedSylvesterEquation A B X C)
    (hT : ∀ y : B.domain, T (y : F) = B.toLinearMap y) :
    HasUnboundedBoundedSylvesterEquation A T X C := by
  have key : ∀ x : F, ∃ hx : X x ∈ A.domain,
      A.toLinearMap ⟨X x, hx⟩ = C x + X (T x) := by
    intro x
    have hx_closure : x ∈ closure (B.domain : Set F) := by
      rw [B.dense_domain.closure_eq]
      trivial
    obtain ⟨u, hu_mem, hu_tendsto⟩ := mem_closure_iff_seq_limit.mp hx_closure
    have hgraph_mem : ∀ n, (X (u n), C (u n) + X (T (u n))) ∈
        Set.range (fun z : A.domain => ((z : E), A.toLinearMap z)) := by
      intro n
      refine ⟨⟨X (u n), hEq.mapsTo_domain ⟨u n, hu_mem n⟩⟩, Prod.ext rfl ?_⟩
      show A.toLinearMap ⟨X (u n), hEq.mapsTo_domain ⟨u n, hu_mem n⟩⟩ =
        C (u n) + X (T (u n))
      have heq := hEq.equation ⟨u n, hu_mem n⟩
      have hval : A.toLinearMap
          ⟨X (u n), hEq.mapsTo_domain ⟨u n, hu_mem n⟩⟩ =
          C (u n) + X (B.toLinearMap ⟨u n, hu_mem n⟩) := by
        rw [← heq]; abel
      rw [hval, hT ⟨u n, hu_mem n⟩]
    have hconv : Filter.Tendsto (fun n => (X (u n), C (u n) + X (T (u n))))
        Filter.atTop (nhds (X x, C x + X (T x))) := by
      refine Filter.Tendsto.prodMk_nhds ?_ ?_
      · exact (X.continuous.tendsto x).comp hu_tendsto
      · refine Filter.Tendsto.add ?_ ?_
        · exact (C.continuous.tendsto x).comp hu_tendsto
        · exact ((X.comp T).continuous.tendsto x).comp hu_tendsto
    obtain ⟨z, hz⟩ := A.closed_graph.isSeqClosed hgraph_mem hconv
    have hz1 : (z : E) = X x := congrArg Prod.fst hz
    have hz2 : A.toLinearMap z = C x + X (T x) := congrArg Prod.snd hz
    refine ⟨hz1 ▸ z.2, ?_⟩
    have hzz : z = ⟨X x, hz1 ▸ z.2⟩ := Subtype.ext hz1
    rw [← hzz]
    exact hz2
  refine ⟨fun x => (key (x : F)).choose, fun x => ?_⟩
  have h := (key (x : F)).choose_spec
  change A.toLinearMap ⟨X (x : F), (key (x : F)).choose⟩ - X (T (x : F)) =
    C (x : F)
  rw [h]
  abel


/-- **Ideal-gauge constant-one Sylvester estimate with the unbounded block on
    the right.**  This is the right-handed companion of
    `sylvester_mem_and_gauge_le_of_unbounded_bound_inverse`.  A bounded left
    block and a bounded shifted right inverse yield a Neumann contraction
    `Y ↦ S Y J`, preserving membership and the sharp constant-one gauge bound. -/
theorem mem_and_gauge_le_of_boundedLeft_exteriorRight
    (N : RectangularSymmetricIdealFamily (𝕜 := 𝕜))
    {G : Type v}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    {S : F →L[𝕜] F}
    {Λ : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := G)}
    {Y C : G →L[𝕜] F} {c ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hSnorm : ‖S‖ ≤ ρ)
    {J : G →L[𝕜] G} (hdom : ∀ z : G, J z ∈ Λ.domain)
    (hres : ∀ z : G,
      Λ.toLinearMap ⟨J z, hdom z⟩ - ((c : ℝ) : 𝕜) • J z = z)
    (hJnorm : ‖J‖ ≤ (ρ + δ)⁻¹)
    (hEq : ∀ y : Λ.domain,
      S (Y (y : G)) -
        (Y (Λ.toLinearMap y) - ((c : ℝ) : 𝕜) • Y (y : G)) = C (y : G))
    (hC : N.Mem C) :
    N.Mem Y ∧ δ * N.gauge Y ≤ N.gauge C := by
  have hρδ : (0 : ℝ) < ρ + δ := by linarith
  set q : ℝ := ρ * (ρ + δ)⁻¹ with hqdef
  have hq0 : 0 ≤ q := mul_nonneg hρ (inv_nonneg.mpr hρδ.le)
  have hq1 : q < 1 := by
    rw [hqdef, ← div_eq_mul_inv]
    exact (div_lt_one hρδ).mpr (by linarith)
  -- the bounded fixed-point identity `Y = S Y J - C J`
  have hfix : Y = S ∘L Y ∘L J + -(C ∘L J) := by
    ext z
    have hres' : Λ.toLinearMap ⟨J z, hdom z⟩ =
        z + ((c : ℝ) : 𝕜) • J z := sub_eq_iff_eq_add.mp (hres z)
    have h1 := hEq ⟨J z, hdom z⟩
    rw [hres', map_add, map_smul] at h1
    have h2 : S (Y (J z)) - Y z = C (J z) := by
      calc S (Y (J z)) - Y z
          = S (Y (J z)) -
              (Y z + ((c : ℝ) : 𝕜) • Y (J z) -
                ((c : ℝ) : 𝕜) • Y (J z)) := by abel
        _ = C (J z) := h1
    have h3 : S (Y (J z)) = C (J z) + Y z := sub_eq_iff_eq_add.mp h2
    show Y z = (S ∘L Y ∘L J) z + (-(C ∘L J)) z
    simp only [ContinuousLinearMap.comp_apply, neg_apply]
    rw [h3]
    abel
  -- the Neumann contraction `W ↦ S W J`
  set T : (G →L[𝕜] F) → (G →L[𝕜] F) := fun W => S ∘L W ∘L J with hTdef
  have hTadd : ∀ W Z : G →L[𝕜] F, T (W + Z) = T W + T Z := by
    intro W Z
    simp only [hTdef]
    simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  have hTnorm : ∀ W : G →L[𝕜] F, ‖T W‖ ≤ q * ‖W‖ := by
    intro W
    calc ‖T W‖ ≤ ‖S‖ * ‖W‖ * ‖J‖ :=
          RectangularSymmetricIdealFamily.opNorm_comp_comp_le S W J
      _ ≤ ρ * ‖W‖ * (ρ + δ)⁻¹ :=
          mul_le_mul (mul_le_mul_of_nonneg_right hSnorm (norm_nonneg W))
            hJnorm (norm_nonneg J) (mul_nonneg hρ (norm_nonneg W))
      _ = q * ‖W‖ := by rw [hqdef]; ring
  have hTmem : ∀ W : G →L[𝕜] F, N.Mem W → N.Mem (T W) := fun W hW =>
    N.comp_mem S J hW
  have hTgauge : ∀ W : G →L[𝕜] F, N.Mem W →
      N.gauge (T W) ≤ q * N.gauge W := by
    intro W hW
    calc N.gauge (T W) ≤ ‖S‖ * N.gauge W * ‖J‖ := N.gauge_comp_le S J hW
      _ ≤ ρ * N.gauge W * (ρ + δ)⁻¹ :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right hSnorm (N.gauge_nonneg hW))
            hJnorm (norm_nonneg J)
            (mul_nonneg hρ (N.gauge_nonneg hW))
      _ = q * N.gauge W := by rw [hqdef]; ring
  -- the Neumann iterates and their partial sums
  have hbasemem : N.Mem (-(C ∘L J)) := N.neg_mem (N.comp_right_mem J hC)
  set t : ℕ → G →L[𝕜] F := fun n => T^[n] (-(C ∘L J)) with htdef
  have ht0 : t 0 = -(C ∘L J) := rfl
  have htsucc : ∀ n, t (n + 1) = T (t n) := by
    intro n
    simp only [htdef, Function.iterate_succ_apply']
  have htmem : ∀ n, N.Mem (t n) := by
    intro n
    induction n with
    | zero => exact hbasemem
    | succ n ih => rw [htsucc]; exact hTmem _ ih
  set g₀ : ℝ := N.gauge (-(C ∘L J)) with hg₀def
  have htgauge : ∀ n, N.gauge (t n) ≤ q ^ n * g₀ := by
    intro n
    induction n with
    | zero => simp [htdef, hg₀def]
    | succ n ih =>
        rw [htsucc, pow_succ]
        calc N.gauge (T (t n)) ≤ q * N.gauge (t n) := hTgauge _ (htmem n)
          _ ≤ q * (q ^ n * g₀) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ n * q * g₀ := by ring
  set P : ℕ → G →L[𝕜] F := fun n => ∑ k ∈ Finset.range n, t k with hPdef
  have hPmem : ∀ n, N.Mem (P n) := by
    intro n
    simp only [hPdef]
    exact N.finset_sum_mem (Finset.range n) t fun k _ => htmem k
  set Gs : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, q ^ k * g₀ with hGdef
  have hgap : ∀ {m n : ℕ}, n ≤ m → N.gauge (P m - P n) ≤ Gs m - Gs n := by
    intro m n hnm
    have hsum : P m - P n = ∑ k ∈ Finset.Ico n m, t k :=
      (Finset.sum_Ico_eq_sub _ hnm).symm
    have hG : ∑ k ∈ Finset.Ico n m, q ^ k * g₀ = Gs m - Gs n :=
      Finset.sum_Ico_eq_sub _ hnm
    rw [hsum, ← hG]
    calc N.gauge (∑ k ∈ Finset.Ico n m, t k)
        ≤ ∑ k ∈ Finset.Ico n m, N.gauge (t k) :=
          N.gauge_finset_sum_le (Finset.Ico n m) t fun k _ => htmem k
      _ ≤ ∑ k ∈ Finset.Ico n m, q ^ k * g₀ :=
          Finset.sum_le_sum fun k _ => htgauge k
  have hGcauchy : CauchySeq Gs := by
    have hsummable : Summable fun k : ℕ => q ^ k * g₀ :=
      (summable_geometric_of_lt_one hq0 hq1).mul_right g₀
    exact hsummable.hasSum.tendsto_sum_nat.cauchySeq
  have hPcauchy : ∀ ε : ℝ, 0 < ε → ∃ N₀, ∀ m n, N₀ ≤ m → N₀ ≤ n →
      N.gauge (P m - P n) < ε := by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := Metric.cauchySeq_iff.mp hGcauchy ε hε
    refine ⟨N₀, fun m n hm hn => ?_⟩
    rcases le_total n m with h | h
    · refine lt_of_le_of_lt (hgap h) ?_
      calc Gs m - Gs n ≤ |Gs m - Gs n| := le_abs_self _
        _ = dist (Gs m) (Gs n) := (Real.dist_eq _ _).symm
        _ < ε := hN₀ m hm n hn
    · have hswap : N.gauge (P m - P n) = N.gauge (P n - P m) := by
        rw [show P m - P n = -(P n - P m) from by abel,
          N.gauge_neg (N.sub_mem (hPmem n) (hPmem m))]
      rw [hswap]
      refine lt_of_le_of_lt (hgap h) ?_
      calc Gs n - Gs m ≤ |Gs n - Gs m| := le_abs_self _
        _ = dist (Gs n) (Gs m) := (Real.dist_eq _ _).symm
        _ < ε := hN₀ n hn m hm
  obtain ⟨L, hLmem, hLlim⟩ := N.gauge_complete P hPmem hPcauchy
  -- the partial sums converge to `L` in operator norm
  have hPL : Filter.Tendsto P Filter.atTop (nhds L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => N.opNorm_le_gauge (N.sub_mem (hPmem n) hLmem)) ?_
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := hLlim ε hε
    refine ⟨N₀, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (N.gauge_nonneg (N.sub_mem (hPmem n) hLmem))]
    exact hN₀ n hn
  -- the partial sums converge to `Y` in operator norm
  have hfix' : Y = t 0 + T Y := by
    conv_lhs => rw [hfix]
    rw [ht0]
    abel
  have hchain : ∀ n, T^[n] Y = t n + T^[n + 1] Y := by
    intro n
    induction n with
    | zero => simpa using hfix'
    | succ n ih =>
        rw [Function.iterate_succ_apply', ih, hTadd, ← htsucc,
          ← Function.iterate_succ_apply' T (n + 1) Y]
  have hYP : ∀ n, Y = P n + T^[n] Y := by
    intro n
    induction n with
    | zero => simp [hPdef]
    | succ n ih =>
        have hPsucc : P (n + 1) = P n + t n := Finset.sum_range_succ _ _
        rw [hPsucc]
        calc Y = P n + T^[n] Y := ih
          _ = P n + (t n + T^[n + 1] Y) := by rw [hchain n]
          _ = P n + t n + T^[n + 1] Y := by abel
  have htail : ∀ n, ‖T^[n] Y‖ ≤ q ^ n * ‖Y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Function.iterate_succ_apply', pow_succ]
        calc ‖T (T^[n] Y)‖ ≤ q * ‖T^[n] Y‖ := hTnorm _
          _ ≤ q * (q ^ n * ‖Y‖) := mul_le_mul_of_nonneg_left ih hq0
          _ = q ^ n * q * ‖Y‖ := by ring
  have hPY : Filter.Tendsto P Filter.atTop (nhds Y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ n, ‖P n - Y‖ ≤ q ^ n * ‖Y‖ := by
      intro n
      have hPnY : P n - Y = -(T^[n] Y) := by
        conv_lhs => rw [hYP n]
        abel
      rw [hPnY, norm_neg]
      exact htail n
    refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖Y‖
  have hYL : Y = L := tendsto_nhds_unique hPY hPL
  have hYmem : N.Mem Y := by rw [hYL]; exact hLmem
  -- the gauge estimate by absorption through the fixed point
  have hgauge : N.gauge Y ≤ (ρ + δ)⁻¹ * (ρ * N.gauge Y + N.gauge C) := by
    conv_lhs => rw [hfix]
    calc N.gauge (S ∘L Y ∘L J + -(C ∘L J))
        ≤ N.gauge (S ∘L Y ∘L J) + N.gauge (-(C ∘L J)) :=
          N.gauge_add_le (N.comp_mem S J hYmem) hbasemem
      _ ≤ ‖S‖ * N.gauge Y * ‖J‖ + N.gauge (C ∘L J) :=
          add_le_add (N.gauge_comp_le S J hYmem)
            (le_of_eq (N.gauge_neg (N.comp_right_mem J hC)))
      _ ≤ ρ * N.gauge Y * (ρ + δ)⁻¹ + N.gauge C * (ρ + δ)⁻¹ := by
          refine add_le_add
            (mul_le_mul
              (mul_le_mul_of_nonneg_right hSnorm (N.gauge_nonneg hYmem))
              hJnorm (norm_nonneg J)
              (mul_nonneg hρ (N.gauge_nonneg hYmem))) ?_
          exact (N.gauge_comp_right_le_mul J hC).trans
            (mul_le_mul_of_nonneg_left hJnorm (N.gauge_nonneg hC))
      _ = (ρ + δ)⁻¹ * (ρ * N.gauge Y + N.gauge C) := by ring
  refine ⟨hYmem, ?_⟩
  have hkey := mul_le_mul_of_nonneg_left hgauge hρδ.le
  rw [← mul_assoc, mul_inv_cancel₀ hρδ.ne', one_mul] at hkey
  linarith
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
