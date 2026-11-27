/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.BorelCalculus.Operator

/-!
# Laws for Borel symbols given by predicates

The calculus is Tau Ceti's bundled star algebra homomorphism.
The identities here express its laws in the unbundled symbol syntax used by
the existing spectral-calculus consumers.
-/

public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

namespace IsBddMeasurable

variable {f g : spectrum ℂ a → ℂ}

/-- Continuous symbols are admissible. -/
theorem of_continuous (g : C(spectrum ℂ a, ℂ)) : IsBddMeasurable (fun x => g x) :=
  ⟨g.continuous.measurable, ‖g‖, norm_nonneg _, fun x => g.norm_coe_le_norm x⟩

omit [CompleteSpace H] in
/-- Products of admissible symbols are admissible. -/
theorem mul (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    IsBddMeasurable (fun x => f x * g x) := by
  refine ⟨hf.measurable.mul hg.measurable, hf.chooseBound * hg.chooseBound, ?_, fun x => ?_⟩
  · have := hf.chooseBound_nonneg; have := hg.chooseBound_nonneg; positivity
  · rw [norm_mul]
    exact mul_le_mul (hf.norm_le_chooseBound x) (hg.norm_le_chooseBound x) (norm_nonneg _)
      hf.chooseBound_nonneg

omit [CompleteSpace H] in
/-- Admissible symbols are integrable against every finite measure on the
spectrum. -/
theorem integrable (hf : IsBddMeasurable f) (ν : Measure (spectrum ℂ a))
    [IsFiniteMeasure ν] : Integrable f ν :=
  (integrable_const hf.chooseBound).mono' hf.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall hf.norm_le_chooseBound)

omit [CompleteSpace H] in
/-- Conjugates of admissible symbols are admissible. -/
theorem conj (hf : IsBddMeasurable f) :
    IsBddMeasurable (fun x => (starRingEnd ℂ) (f x)) :=
  ⟨Complex.continuous_conj.measurable.comp hf.measurable, hf.chooseBound, hf.chooseBound_nonneg,
    fun x => by rw [RCLike.norm_conj]; exact hf.norm_le_chooseBound x⟩

omit [CompleteSpace H] in
/-- Sums of admissible symbols are admissible. -/
theorem add (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    IsBddMeasurable (fun x => f x + g x) := by
  refine ⟨hf.measurable.add hg.measurable, hf.chooseBound + hg.chooseBound, ?_, fun x => ?_⟩
  · have := hf.chooseBound_nonneg; have := hg.chooseBound_nonneg; positivity
  · exact le_trans (norm_add_le _ _)
      (add_le_add (hf.norm_le_chooseBound x) (hg.norm_le_chooseBound x))

omit [CompleteSpace H] in
/-- Scalar multiples of admissible symbols are admissible. -/
theorem const_smul (c : ℂ) (hf : IsBddMeasurable f) :
    IsBddMeasurable (fun x => c * f x) := by
  refine ⟨measurable_const.mul hf.measurable, ‖c‖ * hf.chooseBound, ?_, fun x => ?_⟩
  · have := hf.chooseBound_nonneg; positivity
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf.norm_le_chooseBound x) (norm_nonneg c)

end IsBddMeasurable

variable (ha : IsStarNormal a) {f g : spectrum ℂ a → ℂ}

/-- The Borel calculus extends the continuous functional calculus. -/
theorem borelCalculus_of_continuous (g : C(spectrum ℂ a, ℂ))
    (hg : IsBddMeasurable (fun x => g x)) :
    borelCalculus ha hg = cfcHom ha g := by
  have := ha
  rw [borelCalculus_eq_native,
    show hg.toBoundedBorelFunction = BoundedBorelFunction.ofContinuousMap g from
      BoundedBorelFunction.ext fun x => by simp,
    a.borelCalculus_ofContinuousMap]

/-- The Borel calculus is unital. -/
theorem borelCalculus_one (h1 : IsBddMeasurable (fun _ : spectrum ℂ a => (1 : ℂ))) :
    borelCalculus ha h1 = 1 := by
  have := ha
  rw [borelCalculus_eq_native,
    show h1.toBoundedBorelFunction = 1 from BoundedBorelFunction.ext fun x => by simp,
    map_one]

/-- The Borel calculus kills the zero symbol. -/
theorem borelCalculus_zero (h0 : IsBddMeasurable (fun _ : spectrum ℂ a => (0 : ℂ))) :
    borelCalculus ha h0 = 0 := by
  have := ha
  rw [borelCalculus_eq_native,
    show h0.toBoundedBorelFunction = 0 from BoundedBorelFunction.ext fun x => by simp,
    map_zero]

/-- The Borel calculus is multiplicative. -/
theorem borelCalculus_mul (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    borelCalculus ha (hf.mul hg) = borelCalculus ha hf * borelCalculus ha hg := by
  have := ha
  rw [borelCalculus_eq_native,
    show (hf.mul hg).toBoundedBorelFunction = hf.toBoundedBorelFunction *
        hg.toBoundedBorelFunction from BoundedBorelFunction.ext fun x => by simp,
    map_mul, ← borelCalculus_eq_native, ← borelCalculus_eq_native]

/-- The Borel calculus is additive in the symbol. -/
theorem borelCalculus_add (hf : IsBddMeasurable f) (hg : IsBddMeasurable g) :
    borelCalculus ha (hf.add hg) = borelCalculus ha hf + borelCalculus ha hg := by
  have := ha
  rw [borelCalculus_eq_native,
    show (hf.add hg).toBoundedBorelFunction = hf.toBoundedBorelFunction +
        hg.toBoundedBorelFunction from BoundedBorelFunction.ext fun x => by simp,
    map_add, ← borelCalculus_eq_native, ← borelCalculus_eq_native]

/-- The Borel calculus is homogeneous in the symbol. -/
theorem borelCalculus_const_smul (c : ℂ) (hf : IsBddMeasurable f) :
    borelCalculus ha (hf.const_smul c) = c • borelCalculus ha hf := by
  have := ha
  rw [borelCalculus_eq_native,
    show (hf.const_smul c).toBoundedBorelFunction = c • hf.toBoundedBorelFunction from
      BoundedBorelFunction.ext fun x => by simp [smul_eq_mul],
    map_smul, ← borelCalculus_eq_native]

/-- The Borel calculus respects equality almost everywhere for all diagonal measures. -/
theorem borelCalculus_congr_ae (hf : IsBddMeasurable f) (hg : IsBddMeasurable g)
    (h : ∀ η : H, f =ᵐ[(cfcHom ha).representationDiagMeasure η] g) :
    borelCalculus ha hf = borelCalculus ha hg := by
  have := ha
  rw [borelCalculus_eq_native, borelCalculus_eq_native]
  apply a.borelCalculus_congr_ae
  intro ξ
  rw [← a.spectralPVM_diag, spectralPVM_diag_eq_representation ha]
  simpa only [Filter.EventuallyEq, IsBddMeasurable.toBoundedBorelFunction_apply] using h ξ

/-- The Borel calculus preserves adjoints. -/
theorem borelCalculus_conj (hf : IsBddMeasurable f) :
    borelCalculus ha hf.conj = ContinuousLinearMap.adjoint (borelCalculus ha hf) := by
  have := ha
  rw [borelCalculus_eq_native,
    show hf.conj.toBoundedBorelFunction = star hf.toBoundedBorelFunction from
      BoundedBorelFunction.ext fun x => by simp,
    map_star, ContinuousLinearMap.star_eq_adjoint, ← borelCalculus_eq_native]

/-- A pointwise symbol bound gives the corresponding operator bound on every vector. -/
theorem norm_borelCalculus_apply_le (hf : IsBddMeasurable f) {M : ℝ} (hM : 0 ≤ M)
    (hfb : ∀ x, ‖f x‖ ≤ M) (ξ : H) :
    ‖borelCalculus ha hf ξ‖ ≤ M * ‖ξ‖ := by
  have := ha
  rw [borelCalculus_eq_native]
  exact a.norm_borelCalculus_apply_le hM
    (fun x => by simpa only [IsBddMeasurable.toBoundedBorelFunction_apply] using hfb x) ξ

end BorelCalculus
end TauCeti
