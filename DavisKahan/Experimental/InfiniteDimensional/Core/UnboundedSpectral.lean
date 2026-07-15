/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import DavisKahan.Experimental.InfiniteDimensional.Ideals.Rectangular
import DavisKahan.Experimental.InfiniteDimensional.Core.Unbounded
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Unbounded self-adjoint spectral substrate

The construction follows the standard route: define adjoints by orthogonality
to the graph, prove the nonreal resolvent estimate, obtain the complex spectral
measure from the Cayley transform, descend through complexification for real
Hilbert spaces, and define bounded truncations by measurable functional
calculus.  The final theorem is the one-unbounded Neumann-series Sylvester
estimate used in the interval/exterior branch of Davis--Kahan.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta

open scoped InnerProductSpace Topology
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

def SemiboundedBelow
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    c * ‖(x : E)‖ ^ 2 ≤
      RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜

def SemiboundedAbove
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (c : ℝ) : Prop :=
  ∀ x : A.domain,
    RCLike.re ⟪A.toLinearMap x, (x : E)⟫_𝕜 ≤
      c * ‖(x : E)‖ ^ 2

def HasClosedSylvesterEquation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : ClosedOperatorF (𝕜 := 𝕜) (F := F))
    (X C : F →L[𝕜] E) : Prop :=
  ∀ x : B.domain,
    ∃ hx : X (x : F) ∈ A.domain,
      A.toLinearMap ⟨X (x : F), hx⟩ -
        X (B.toLinearMap x) = C (x : F)

structure HasBoundedEverywhereInverse
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) where
  inv : E →L[𝕜] E
  inv_mapsTo_domain : ∀ y, inv y ∈ A.domain
  apply_inv : ∀ y,
    A.toLinearMap ⟨inv y, inv_mapsTo_domain y⟩ = y
  inv_apply : ∀ x : A.domain, inv (A.toLinearMap x) = (x : E)

/-- The adjoint graph is the inverse coordinate flip of the orthogonal
complement of the original graph, hence is closed. -/
theorem closedOperator_adjoint_closed
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) :
    IsClosed (Set.range fun x : A.adjoint.domain =>
      ((x : E), A.adjoint.toLinearMap x)) := by
  rw [A.graph_adjoint_eq_flip_orthogonal_graph]
  exact A.closed_graph.orthogonal.preimage continuous_swap

/-- Closed densely defined operators equal their double adjoints. -/
theorem closedOperator_adjoint_adjoint
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) :
    A.adjoint.adjoint = A := by
  apply ForMathlib.DavisKahanExt.ClosedOperator.ext
  · exact A.domain_adjoint_adjoint
  · intro x
    exact A.adjoint_adjoint_apply x

structure ClosedResolventData
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) (z : 𝕜) where
  resolvent : E →L[𝕜] E
  mapsTo_domain : ∀ y, resolvent y ∈ A.domain
  right_inverse : ∀ y,
    A.toLinearMap ⟨resolvent y, mapsTo_domain y⟩ - z • resolvent y = y
  left_inverse : ∀ x : A.domain,
    resolvent (A.toLinearMap x - z • (x : E)) = (x : E)

/-- Nonreal shifts of a self-adjoint closed operator have a bounded everywhere
inverse. -/
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
      simp [T, ForMathlib.DavisKahanExt.ClosedOperator.subScalar,
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

noncomputable def closedOperatorResolvent
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (z : 𝕜)
    (hz : RCLike.im z ≠ 0) : E →L[𝕜] E :=
  (selfAdjoint_resolventData_of_im_ne_zero A hA z hz).resolvent

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

abbrev ComplexClosedOperatorH :=
  ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := ℂ) (E := H)

noncomputable def closedOperatorCayleyTransform
    (A : ComplexClosedOperatorH (H := H))
    (hA : A.IsSelfAdjoint) : H →L[ℂ] H :=
  1 - (2 * Complex.I) •
    closedOperatorResolvent A hA Complex.I (by norm_num)

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

/-- Measurable spectral projection of a self-adjoint closed operator.  In the
complex case it is the pullback of the unitary spectral measure of the Cayley
transform.  In the real case the same construction is made on the
complexification and descended through conjugation invariance. -/
noncomputable def selfAdjointSpectralProjection
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) : E →L[𝕜] E :=
  RCLikeUnboundedSpectralTheorem.projection A hA s

theorem selfAdjointSpectralProjection_idempotent
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) (hs : MeasurableSet s) :
    selfAdjointSpectralProjection A hA s ∘L
      selfAdjointSpectralProjection A hA s =
        selfAdjointSpectralProjection A hA s :=
  RCLikeUnboundedSpectralTheorem.projection_idempotent A hA s hs

theorem selfAdjointSpectralProjection_symmetric
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s : Set ℝ) (hs : MeasurableSet s) :
    (selfAdjointSpectralProjection A hA s).IsSymmetric :=
  RCLikeUnboundedSpectralTheorem.projection_symmetric A hA s hs

theorem selfAdjointSpectralProjection_empty
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    selfAdjointSpectralProjection A hA ∅ = 0 :=
  RCLikeUnboundedSpectralTheorem.projection_empty A hA

theorem selfAdjointSpectralProjection_univ
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    selfAdjointSpectralProjection A hA Set.univ =
      ContinuousLinearMap.id 𝕜 E :=
  RCLikeUnboundedSpectralTheorem.projection_univ A hA

theorem selfAdjointSpectralProjection_inter
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (s t : Set ℝ)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    selfAdjointSpectralProjection A hA s ∘L
      selfAdjointSpectralProjection A hA t =
        selfAdjointSpectralProjection A hA (s ∩ t) :=
  RCLikeUnboundedSpectralTheorem.projection_inter A hA s t hs ht

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

/-- A bounded spectral interval is contained in the operator domain because
its second spectral moment is finite. -/
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

noncomputable def spectralCutoff
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) : E →L[𝕜] E :=
  selfAdjointSpectralProjection A hA (Set.Icc (-τ) τ)

theorem spectralCutoff_isOrthogonalProjection
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    spectralCutoff A hA τ ∘L spectralCutoff A hA τ =
        spectralCutoff A hA τ ∧
      (spectralCutoff A hA τ).IsSymmetric :=
  ⟨selfAdjointSpectralProjection_idempotent A hA _ measurableSet_Icc,
    selfAdjointSpectralProjection_symmetric A hA _ measurableSet_Icc⟩

theorem spectralCutoff_range_le_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    LinearMap.range (spectralCutoff A hA τ).toLinearMap ≤ A.domain :=
  selfAdjointSpectralProjection_Icc_range_le_domain A hA (-τ) τ

theorem spectralCutoff_commutes_on_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) (x : A.domain) :
    ∃ hx : spectralCutoff A hA τ (x : E) ∈ A.domain,
      A.toLinearMap ⟨spectralCutoff A hA τ (x : E), hx⟩ =
        spectralCutoff A hA τ (A.toLinearMap x) := by
  let hx := spectralCutoff_range_le_domain A hA τ
    (LinearMap.mem_range_self _ (x : E))
  exact ⟨hx, hA.spectralProjection_commutes_apply measurableSet_Icc x⟩

theorem spectralCutoff_tendsto_identity
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) :
    ∀ x, Tendsto (fun τ : ℝ => spectralCutoff A hA τ x) atTop (𝓝 x) := by
  intro x
  exact hA.projection_Icc_tendsto_identity x

/-- Bounded truncation `λ ↦ max (-τ) (min τ λ)`. -/
noncomputable def boundedSpectralTruncation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) : E →L[𝕜] E :=
  RCLikeUnboundedSpectralTheorem.boundedFunctionalCalculus A hA
    (fun λ => max (-τ) (min τ λ))

theorem boundedSpectralTruncation_isSymmetric
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (τ : ℝ) :
    (boundedSpectralTruncation A hA τ).IsSymmetric :=
  RCLikeUnboundedSpectralTheorem.boundedFunctionalCalculus_symmetric
    A hA _ (by fun_prop)

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

theorem boundedSpectralTruncation_tendsto_on_domain
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (x : A.domain) :
    Tendsto
      (fun τ : ℝ => boundedSpectralTruncation A hA τ (x : E))
      atTop (𝓝 (A.toLinearMap x)) :=
  hA.truncatedSpectralIntegral_tendsto x

theorem mem_domain_iff_boundedSpectralTruncation_norm_bounded
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) (x : E) :
    x ∈ A.domain ↔
      ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
        ‖boundedSpectralTruncation A hA τ x‖ ≤ C := by
  rw [hA.mem_domain_iff_secondMoment_finite]
  exact hA.secondMoment_finite_iff_truncations_uniformly_bounded x

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

theorem domain_eq_top_of_spectrumIn_Icc
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (hA : A.IsSelfAdjoint) {β α : ℝ} (hβα : β ≤ α)
    (hσ : A.realSpectrum ⊆ Set.Icc β α) :
    A.domain = ⊤ := by
  apply le_antisymm le_top
  intro x hx
  apply hA.mem_domain_iff_secondMoment_finite.mpr
  exact hA.secondMoment_le_of_spectrum_subset_Icc hσ x

structure BoundedRealization
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E)) where
  operator : E →L[𝕜] E
  domain_eq_top : A.domain = ⊤
  agrees : ∀ x : A.domain, operator (x : E) = A.toLinearMap x

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

def UnboundedIntervalExteriorGap
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : ForMathlib.DavisKahanExt.ClosedOperator (𝕜 := 𝕜) (E := F))
    (β α δ : ℝ) : Prop :=
  (A.realSpectrum ⊆ Set.Icc β α ∧
    B.realSpectrum ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x}) ∨
  (B.realSpectrum ⊆ Set.Icc β α ∧
    A.realSpectrum ⊆ {x | x ≤ β - δ ∨ α + δ ≤ x})

def HasUnboundedBoundedSylvesterEquation
    (A : ClosedOperatorE (𝕜 := 𝕜) (E := E))
    (B : F →L[𝕜] F) (X C : F →L[𝕜] E) : Prop :=
  ∀ x, ∃ hx : X x ∈ A.domain,
    A.toLinearMap ⟨X x, hx⟩ - X (B x) = C x

/-- One-unbounded bound/inverse Sylvester estimate.  Multiplying the equation
by `A⁻¹` gives `X = A⁻¹C + A⁻¹XB`; the second term is a strict contraction
because `‖A⁻¹‖ ‖B‖ ≤ ρ/(ρ+δ)`. -/
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
  have hfixed : X = hAinv.inv ∘L C + hAinv.inv ∘L X ∘L B := by
    ext x
    obtain ⟨hx, heq⟩ := hEq x
    have := congrArg hAinv.inv heq
    simpa [hAinv.inv_apply ⟨X x, hx⟩,
      map_sub, ContinuousLinearMap.comp_apply] using this
  have hq : ‖hAinv.inv‖ * ‖B‖ < 1 := by
    calc
      ‖hAinv.inv‖ * ‖B‖ ≤ (ρ+δ)⁻¹ * ρ :=
        mul_le_mul hInvNorm hB (norm_nonneg _) (by positivity)
      _ < 1 := by
        rw [inv_mul_lt_one₀ (by linarith)]
        linarith
  have hmem : N.Mem X := by
    rw [hfixed]
    exact N.add_mem
      (N.left_mem hAinv.inv hC)
      (N.right_mem B (N.left_mem hAinv.inv
        (N.fixedPoint_mem_of_contraction hq hC)))
  refine ⟨hmem, ?_⟩
  have hgauge := N.gauge_add_le
    (hAinv.inv ∘L C) (hAinv.inv ∘L X ∘L B)
  rw [← hfixed] at hgauge
  have hleft := N.gauge_left_le hAinv.inv C
  have hright := N.gauge_two_sided_le hAinv.inv X B
  have hsumpos : 0 < ρ+δ := by linarith
  calc
    δ * N.gauge X
        ≤ (ρ+δ) * N.gauge X - ρ * N.gauge X := by ring_nf
    _ ≤ N.gauge C := by
      nlinarith [hgauge, hleft, hright, hInvNorm, hB,
        N.gauge_nonneg X, N.gauge_nonneg C]

end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
