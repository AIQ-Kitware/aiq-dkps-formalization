/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Sylvester.ClosedSylvesterEquation
import DavisKahan.SpectralTheory.ClosedOperator.Complex
import DavisKahan.SpectralTheory.ClosedOperator.BoundedRealization
import DavisKahan.Sylvester.Gap
import DavisKahan.Sylvester.Unbounded.Neumann
import DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Open obligations of the unbounded spectral theory

The proved front now lives in `DavisKahan.Sylvester.ClosedSylvesterEquation`,
`DavisKahan.SpectralTheory.ClosedOperator.BoundedRealization`,
`DavisKahan.Sylvester.Gap` and `DavisKahan.Sylvester.Unbounded.Neumann`.

The provisional adjoint properties, the spectral projections and the bounded
spectral truncation remain unresolved and stay here.  They are a useful API test
bed, but they are *not* the production implementation: the production route to
the interval/exterior estimate goes through the vendored Spectra calculus, which
proves the same statements outright.
-/

namespace TauCeti
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
  rw [A.graph_adjoint_eq_flip_orthogonal_graph]
  exact A.closed_graph.orthogonal.preimage continuous_swap

/-- Double adjoint recovers a densely defined closed operator. -/
theorem closedOperator_adjoint_adjoint
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) :
    A.adjoint.adjoint = A := by
  apply TauCeti.DavisKahanExt.ClosedOperator.ext
  · exact A.domain_adjoint_adjoint
  · intro x
    exact A.adjoint_adjoint_apply x

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
  classical
  let T := A.subScalar z
  have hbelow : ∀ x : A.domain,
      |RCLike.im z| * ‖(x : E)‖ ≤ ‖T.toLinearMap x‖ := by
    intro x
    have him : RCLike.im ⟪T.toLinearMap x, (x : E)⟫_𝕜 =
        -RCLike.im z * ‖(x : E)‖^2 := by
      simp [T, TauCeti.DavisKahanExt.ClosedOperator.subScalar,
        hA.inner_real]
    exact lowerBound_of_inner_imaginary_part him
  have hkerAdj : T.adjoint.domain ⊓ LinearMap.ker T.adjoint.toLinearMap = ⊥ := by
    apply Submodule.eq_bot_iff.mpr
    intro x hx
    have hbelowAdj := hbelow_for_adjoint_shift hA z hz x
    simpa [hx.2] using hbelowAdj
  have hdense : DenseRange T.toLinearMap := by
    rw [T.denseRange_iff_adjoint_ker_bot]
    exact hkerAdj
  have hclosedRange : IsClosed (LinearMap.range T.toLinearMap) :=
    T.closedRange_of_boundedBelow hbelow
  have hsurj : Function.Surjective T.toLinearMap :=
    denseRange_and_closedRange_implies_surjective hdense hclosedRange
  let e : A.domain ≃L[𝕜] E :=
    ContinuousLinearEquiv.ofClosedBijective T.graphNormMap hbelow hsurj
  exact
    { resolvent := e.symm.toContinuousLinearMap
      mapsTo_domain := fun y => (e.symm y).property
      right_inverse := fun y => e.apply_symm_apply y
      left_inverse := fun x => e.symm_apply_apply x }

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
  let D := selfAdjoint_resolventData_of_im_ne_zero A hA z hz
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 (abs_nonneg _)) ?_
  intro y
  let x : A.domain := ⟨D.resolvent y, D.mapsTo_domain y⟩
  have hbelow := selfAdjoint_shift_lowerBound hA z hz x
  rw [D.right_inverse] at hbelow
  exact (le_div_iff₀ (abs_pos.2 hz)).mp hbelow

section ComplexCayley

variable {H : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Cayley transform of a complex self-adjoint closed operator. -/
noncomputable def closedOperatorCayleyTransform
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) : H →L[ℂ] H :=
  1 - (2 * Complex.I) •
    closedOperatorResolvent A hA Complex.I (by norm_num)

/-- The complex Cayley transform is unitary. -/
theorem closedOperatorCayleyTransform_unitary
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) :
    IsometricEmbedding (closedOperatorCayleyTransform A hA) ∧
      Function.Surjective (closedOperatorCayleyTransform A hA) := by
  let Rplus := closedOperatorResolvent A hA Complex.I (by norm_num)
  let Rminus := closedOperatorResolvent A hA (-Complex.I) (by norm_num)
  have hstar : star Rplus = Rminus :=
    selfAdjoint_resolvent_star hA Complex.I
  have hresolvent := closed_first_resolvent_identity
    A hA Complex.I (-Complex.I)
  have hUU : star (closedOperatorCayleyTransform A hA) ∘L
      closedOperatorCayleyTransform A hA = 1 := by
    simp [closedOperatorCayleyTransform, hstar]
    linear_combination hresolvent
  have hUUs : closedOperatorCayleyTransform A hA ∘L
      star (closedOperatorCayleyTransform A hA) = 1 := by
    simp [closedOperatorCayleyTransform, hstar]
    linear_combination hresolvent
  exact isUnitaryOperator_of_star_mul_self_and_mul_star_self hUU hUUs

end ComplexCayley

/-- Measurable spectral projection of a self-adjoint closed operator.

The generic `RCLike` signature includes the real case; its implementation is
expected to use complexification and descent.  Laws are only asserted for
measurable sets. -/
noncomputable def selfAdjointSpectralProjection
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) : E →L[𝕜] E :=
  RCLikeUnboundedSpectralTheorem.projection A hA s

/-- A measurable spectral projection is idempotent. -/
theorem selfAdjointSpectralProjection_idempotent
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) (hs : MeasurableSet s) :
    selfAdjointSpectralProjection A hA s ∘L
      selfAdjointSpectralProjection A hA s =
        selfAdjointSpectralProjection A hA s :=
  RCLikeUnboundedSpectralTheorem.projection_idempotent A hA s hs

/-- A measurable spectral projection is symmetric. -/
theorem selfAdjointSpectralProjection_symmetric
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) (hs : MeasurableSet s) :
    (selfAdjointSpectralProjection A hA s).IsSymmetric :=
  RCLikeUnboundedSpectralTheorem.projection_symmetric A hA s hs

/-- Spectral projection of the empty set. -/
theorem selfAdjointSpectralProjection_empty
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    selfAdjointSpectralProjection A hA ∅ = 0 :=
  RCLikeUnboundedSpectralTheorem.projection_empty A hA

/-- Spectral projection of the whole real line. -/
theorem selfAdjointSpectralProjection_univ
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    selfAdjointSpectralProjection A hA Set.univ =
      ContinuousLinearMap.id 𝕜 E :=
  RCLikeUnboundedSpectralTheorem.projection_univ A hA

/-- Multiplication of measurable spectral projections corresponds to
intersection. -/
theorem selfAdjointSpectralProjection_inter
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    selfAdjointSpectralProjection A hA s ∘L
      selfAdjointSpectralProjection A hA t =
        selfAdjointSpectralProjection A hA (s ∩ t) :=
  RCLikeUnboundedSpectralTheorem.projection_inter A hA s t hs ht

/-- Finite additivity on disjoint measurable sets. -/
theorem selfAdjointSpectralProjection_disjoint_additive
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hst : Disjoint s t) :
    selfAdjointSpectralProjection A hA (s ∪ t) =
      selfAdjointSpectralProjection A hA s +
        selfAdjointSpectralProjection A hA t :=
  RCLikeUnboundedSpectralTheorem.projection_disjoint_union
    A hA s t hs ht hst

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
      (𝓝 (selfAdjointSpectralProjection A hA (⋃ k, s k) x)) :=
  RCLikeUnboundedSpectralTheorem.projection_iUnion_strong
    A hA s hs hdisj x

/-- A measurable set disjoint from the real spectrum has zero projection. -/
theorem selfAdjointSpectralProjection_eq_zero_of_disjoint_spectrum
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ)
    (hs : MeasurableSet s)
    (hdisj : Disjoint s A.realSpectrum) :
    selfAdjointSpectralProjection A hA s = 0 := by
  rw [← selfAdjointSpectralProjection_inter A hA s A.realSpectrum
    hs hA.measurableSet_realSpectrum]
  rw [hdisj.inter_eq, selfAdjointSpectralProjection_empty]
  exact RCLikeUnboundedSpectralTheorem.projection_spectrum A hA

/-- Vectors in a bounded spectral interval belong to the operator domain. -/
theorem selfAdjointSpectralProjection_Icc_range_le_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (a b : ℝ) :
    LinearMap.range
      (selfAdjointSpectralProjection A hA (Set.Icc a b)).toLinearMap ≤
        A.domain := by
  rintro x ⟨y, rfl⟩
  apply hA.mem_domain_iff_secondMoment_finite.mpr
  have hbound : ∫ λ in hA.scalarSpectralMeasure y,
      λ^2 * Set.indicator (Set.Icc a b) 1 λ ≤
      max |a| |b| ^ 2 * ‖y‖^2 :=
    spectralSecondMoment_Icc_bound hA a b y
  exact lt_of_le_of_lt hbound (by positivity)

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
      (spectralCutoff A hA τ).IsSymmetric :=
  ⟨selfAdjointSpectralProjection_idempotent A hA _ measurableSet_Icc,
    selfAdjointSpectralProjection_symmetric A hA _ measurableSet_Icc⟩

/-- Cutoff vectors belong to the operator domain. -/
theorem spectralCutoff_range_le_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    LinearMap.range (spectralCutoff A hA τ).toLinearMap ≤ A.domain :=
  selfAdjointSpectralProjection_Icc_range_le_domain A hA (-τ) τ

/-- Spectral cutoffs preserve the operator domain and commute with the
operator there. -/
theorem spectralCutoff_commutes_on_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) (x : A.domain) :
    ∃ hx : spectralCutoff A hA τ (x : E) ∈ A.domain,
      A.toLinearMap ⟨spectralCutoff A hA τ (x : E), hx⟩ =
        spectralCutoff A hA τ (A.toLinearMap x) := by
  let hx := spectralCutoff_range_le_domain A hA τ
    (LinearMap.mem_range_self _ (x : E))
  exact ⟨hx, hA.spectralProjection_commutes_apply measurableSet_Icc x⟩

/-- Spectral cutoffs converge strongly to the identity. -/
theorem spectralCutoff_tendsto_identity
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    ∀ x, Tendsto (fun τ : ℝ => spectralCutoff A hA τ x) atTop (𝓝 x) := by
  intro x
  exact hA.projection_Icc_tendsto_identity x

/-- Bounded truncation of a self-adjoint closed operator. -/
noncomputable def boundedSpectralTruncation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) : E →L[𝕜] E :=
  RCLikeUnboundedSpectralTheorem.boundedFunctionalCalculus A hA
    (fun λ => max (-τ) (min τ λ))

/-- Bounded truncation is self-adjoint. -/
theorem boundedSpectralTruncation_isSymmetric
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    (boundedSpectralTruncation A hA τ).IsSymmetric :=
  RCLikeUnboundedSpectralTheorem.boundedFunctionalCalculus_symmetric
    A hA _ (by fun_prop)

/-- Bounded truncation agrees with the original operator on the cutoff range. -/
theorem boundedSpectralTruncation_eq_on_cutoff
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) (x : E) :
    ∃ hx : spectralCutoff A hA τ x ∈ A.domain,
      boundedSpectralTruncation A hA τ x =
        A.toLinearMap ⟨spectralCutoff A hA τ x, hx⟩ := by
  let hx := spectralCutoff_range_le_domain A hA τ
    (LinearMap.mem_range_self _ x)
  refine ⟨hx, ?_⟩
  exact hA.spectralIntegral_truncate_eq_on_Icc τ x

/-- Spectral truncations reconstruct the closed operator on its domain. -/
theorem boundedSpectralTruncation_tendsto_on_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (x : A.domain) :
    Tendsto
      (fun τ : ℝ => boundedSpectralTruncation A hA τ (x : E))
      atTop (𝓝 (A.toLinearMap x)) :=
  hA.truncatedSpectralIntegral_tendsto x

/-- Domain characterization by uniform boundedness of the spectral
truncations.  This is the concrete replacement for an opaque domain field in a
spectral-resolution record. -/
theorem mem_domain_iff_boundedSpectralTruncation_norm_bounded
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (x : E) :
    x ∈ A.domain ↔
      ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖boundedSpectralTruncation A hA τ x‖ ≤ C := by
  rw [hA.mem_domain_iff_secondMoment_finite]
  exact hA.secondMoment_finite_iff_truncations_uniformly_bounded x

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
  intro x
  have hspectrum : A.realSpectrum ⊆ Set.Ici c :=
    hA.spectrum_subset_Ici_of_semiboundedBelow hLower
  rw [hA.inner_boundedFunctionalCalculus_projection]
  exact integral_mono_ae (by positivity) (by
    filter_upwards with λ hλ
    exact mul_le_mul_of_nonneg_right (hspectrum hλ) (by positivity))

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
  intro x
  have hspectrum : A.realSpectrum ⊆ Set.Iic c :=
    hA.spectrum_subset_Iic_of_semiboundedAbove hUpper
  rw [hA.inner_boundedFunctionalCalculus_projection]
  exact integral_mono_ae (by positivity) (by
    filter_upwards with λ hλ
    exact mul_le_mul_of_nonneg_right (hspectrum hλ) (by positivity))

/-- Bounded spectral truncation commutes with its cutoff projection. -/
theorem boundedSpectralTruncation_commutes_cutoff
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    boundedSpectralTruncation A hA τ ∘L spectralCutoff A hA τ =
      boundedSpectralTruncation A hA τ ∧
    spectralCutoff A hA τ ∘L boundedSpectralTruncation A hA τ =
      boundedSpectralTruncation A hA τ := by
  constructor
  · exact hA.functionalCalculus_mul_projection_of_support_Icc τ
  · exact hA.projection_mul_functionalCalculus_of_support_Icc τ

/-- Bounded spectrum forces the domain of a self-adjoint closed operator to be
all of the ambient Hilbert space. -/
theorem domain_eq_top_of_spectrumIn_Icc
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) {β α : ℝ} (hβα : β ≤ α)
    (hσ : A.realSpectrum ⊆ Set.Icc β α) :
    A.domain = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  apply hA.mem_domain_iff_secondMoment_finite.mpr
  exact hA.secondMoment_le_of_spectrum_subset_Icc hσ x

/-- Spectral inclusion in a bounded interval produces a bounded realization. -/
theorem boundedRealization_of_spectrumIn_Icc
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) {β α : ℝ} (hβα : β ≤ α)
    (hσ : A.realSpectrum ⊆ Set.Icc β α) :
    ∃ hB : BoundedRealization A,
      ‖hB.operator - (((β + α) / 2 : ℝ) : 𝕜) •
        ContinuousLinearMap.id 𝕜 E‖ ≤ (α - β) / 2 := by
  let hdom := domain_eq_top_of_spectrumIn_Icc A hA hβα hσ
  let B := A.toContinuousLinearMapOfDomainTop hdom
  refine ⟨⟨B, hdom, A.toContinuousLinearMapOfDomainTop_agrees hdom⟩, ?_⟩
  rw [B.norm_sub_scalar_eq_spectralRadius hA]
  exact sup_norm_sub_midpoint_le_of_subset_Icc hβα hσ

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
  let m := (β+α)/2
  let r := (α-β)/2 + δ
  have hr : 0 < r := by linarith
  let f : ℝ → ℝ := fun λ => (λ-m)⁻¹
  let B := RCLikeUnboundedSpectralTheorem.boundedFunctionalCalculus A hA f
  have hdist : ∀ λ ∈ A.realSpectrum, r ≤ |λ-m| := by
    intro λ hλ
    rcases hσ hλ with hλ | hλ <;> simp [m, r] <;> linarith
  have hnorm : ‖B‖ ≤ r⁻¹ := by
    apply RCLikeUnboundedSpectralTheorem.norm_le
    intro λ hλ
    simpa [f, abs_inv] using inv_le_inv₀ hr (hdist λ hλ)
  refine ⟨{
    inv := B
    inv_mapsTo_domain := fun y =>
      hA.boundedFunctionalCalculus_inverse_mapsTo_domain hdist y
    apply_inv := fun y => by
      apply hA.spectralIntegral_ext
      intro λ hλ
      simp [f, ne_of_gt (lt_of_lt_of_le hr (hdist λ hλ))]
    inv_apply := fun x => by
      apply hA.spectralIntegral_ext_on_domain x
      intro λ hλ
      simp [f, ne_of_gt (lt_of_lt_of_le hr (hdist λ hλ))] }, hnorm⟩

end ExactSinTheta
end Experimental
end DavisKahan
end TauCeti