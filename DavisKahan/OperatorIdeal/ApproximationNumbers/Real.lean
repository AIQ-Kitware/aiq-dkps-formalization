/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
import DavisKahan.OperatorIdeal.ApproximationNumbers.Core
import DavisKahan.SpectralTheory.Complexification.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-!
# Real Hilbert-space localization of approximation numbers

This module proves the real counterpart of the accepted complex
infinite-dimensional Courant--Fischer localization theorem.

The pinned continuous-functional-calculus API is available for bounded
operators on complex Hilbert spaces, but not directly for bounded operators on
real Hilbert spaces.  We therefore complexify the positive Gram operator
`T†T`, apply a continuous high-energy cutoff, prove that the cutoff is fixed by
canonical conjugation, and descend it to a bounded real operator.  The descended
operator supplies both the finite-rank contradiction and the real
`(n+1)`-dimensional lower-modulus witness.

The public results are:

* `exists_linearIndependent_lowerBound_of_lt_approximationNumber_real`;
* `exists_finiteRestrictionApproximationNumber_gt_of_lt_real`;
* `approximationNumber_isLUB_finiteRestrictions_real`;
* `lt_approximationNumber_iff_exists_finiteDimensional_lowerBound_real`;
* `approximationSingularValue_comp_strongProjection_tendsto_real`;
* `kyFanApproximationGauge_comp_strongProjection_tendsto_real`;
* `kyFanApproximationGauge_add_le_real`.
-/

open scoped InnerProductSpace ComplexConjugate Topology

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta
namespace ApproximationNumbersReal

open Module (finrank)
open Filter
open Foundation
open Foundation.RealComplexification

noncomputable section

universe v vF vG vH w

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

noncomputable local instance complexOperatorRealAlgebra :
    Algebra ℝ (RealComplexification E →L[ℂ] RealComplexification E) :=
  Algebra.complexToReal

noncomputable local instance realContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ
      (RealComplexification E →L[ℂ] RealComplexification E) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

omit [CompleteSpace E] in
private theorem restrictedReal_smul_operator_eq
    (r : ℝ) (A : RealComplexification E →L[ℂ] RealComplexification E) :
    @SMul.smul ℝ (RealComplexification E →L[ℂ] RealComplexification E)
        complexOperatorRealAlgebra.toSMul r A = r • A := by
  apply ContinuousLinearMap.ext
  intro z
  change (r : ℂ) • A z = r • A z
  apply RealComplexification.ext
  · rw [RealComplexification.re_complex_smul,
      RealComplexification.re_real_smul]
    simp
  · rw [RealComplexification.im_complex_smul,
      RealComplexification.im_real_smul]
    simp

/-! ## Canonical conjugation on the complexification -/

/-- Canonical conjugation, bundled as an antiunitary involution. -/
private noncomputable def canonicalConjugation :
    RealComplexification E ≃ₗᵢ⋆[ℂ] RealComplexification E where
  toFun := conjugation
  invFun := conjugation
  left_inv := conjugation_involutive
  right_inv := conjugation_involutive
  map_add' z w := by
    apply RealComplexification.ext <;> simp
  map_smul' := conjugation_complex_smul
  norm_map' := conjugation.norm_map

omit [CompleteSpace E] in
@[simp]
private theorem canonicalConjugation_apply (z : RealComplexification E) :
    (canonicalConjugation (E := E)) z = conjugation z := rfl

omit [CompleteSpace E] in
@[simp]
private theorem canonicalConjugation_symm_apply (z : RealComplexification E) :
    (canonicalConjugation (E := E)).symm z = conjugation z := by
  apply (canonicalConjugation (E := E)).injective
  simp [canonicalConjugation]

omit [CompleteSpace E] in
/-- Conjugation reverses the two slots of the complex inner product. -/
private theorem inner_conjugation (z w : RealComplexification E) :
    ⟪conjugation z, conjugation w⟫_ℂ = ⟪w, z⟫_ℂ := by
  apply Complex.ext
  · simp [inner_apply, real_inner_comm]
  · simp [inner_apply, real_inner_comm]
    ring

omit [CompleteSpace E] in
private theorem inner_conjugation_left (z w : RealComplexification E) :
    ⟪conjugation z, w⟫_ℂ = ⟪conjugation w, z⟫_ℂ := by
  calc
    ⟪conjugation z, w⟫_ℂ =
        ⟪conjugation z, conjugation (conjugation w)⟫_ℂ := by simp
    _ = ⟪conjugation w, z⟫_ℂ := inner_conjugation z (conjugation w)

omit [CompleteSpace E] in
private theorem inner_conjugation_right (z w : RealComplexification E) :
    ⟪z, conjugation w⟫_ℂ = ⟪w, conjugation z⟫_ℂ := by
  calc
    ⟪z, conjugation w⟫_ℂ =
        ⟪conjugation (conjugation z), conjugation w⟫_ℂ := by simp
    _ = ⟪w, conjugation z⟫_ℂ := inner_conjugation (conjugation z) w

/-- Conjugation of a complexified bounded operator by canonical conjugation. -/
private noncomputable def conjugateOperator
    (A : RealComplexification E →L[ℂ] RealComplexification E) :
    RealComplexification E →L[ℂ] RealComplexification E :=
  (canonicalConjugation (E := E)).toLinearIsometry.toContinuousLinearMap.comp
    (A.comp (canonicalConjugation (E := E)).symm.toLinearIsometry.toContinuousLinearMap)

omit [CompleteSpace E] in
@[simp]
private theorem conjugateOperator_apply
    (A : RealComplexification E →L[ℂ] RealComplexification E)
    (z : RealComplexification E) :
    conjugateOperator A z = conjugation (A (conjugation z)) := by
  simp [conjugateOperator]

@[simp]
private theorem conjugateOperator_zero :
    conjugateOperator (0 : RealComplexification E →L[ℂ] RealComplexification E) = 0 := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

@[simp]
private theorem conjugateOperator_add (A B : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (A + B) = conjugateOperator A + conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

@[simp]
private theorem conjugateOperator_neg (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (-A) = -conjugateOperator A := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

@[simp]
private theorem conjugateOperator_sub (A B : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (A - B) = conjugateOperator A - conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

@[simp]
private theorem conjugateOperator_one :
    conjugateOperator (1 : RealComplexification E →L[ℂ] RealComplexification E) = 1 := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

@[simp]
private theorem conjugateOperator_mul (A B : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (A * B) = conjugateOperator A * conjugateOperator B := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;>
    simp [conjugateOperator_apply, mul_apply_eq_comp]

@[simp]
private theorem conjugateOperator_real_smul (r : ℝ) (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (r • A) = r • conjugateOperator A := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

@[simp]
private theorem conjugateOperator_involutive (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator (conjugateOperator A) = A := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

/-- Canonical conjugation commutes with taking adjoints. -/
private theorem conjugateOperator_adjoint (A : RealComplexification E →L[ℂ] RealComplexification E) :
    conjugateOperator A.adjoint = (conjugateOperator A).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff
    (conjugateOperator A.adjoint) (conjugateOperator A)).2
  intro x y
  calc
    ⟪conjugateOperator A.adjoint x, y⟫_ℂ =
        ⟪conjugation y, A.adjoint (conjugation x)⟫_ℂ := by
          rw [conjugateOperator_apply, inner_conjugation_left]
    _ = ⟪A (conjugation y), conjugation x⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_right A (conjugation y) (conjugation x)
    _ = ⟪x, conjugation (A (conjugation y))⟫_ℂ := by
      rw [inner_conjugation_right]
    _ = ⟪x, conjugateOperator A y⟫_ℂ := by rw [conjugateOperator_apply]

private theorem norm_conjugateOperator_le (A : RealComplexification E →L[ℂ] RealComplexification E) :
    ‖conjugateOperator A‖ ≤ ‖A‖ := by
  refine (conjugateOperator A).opNorm_le_bound (norm_nonneg A) ?_
  intro z
  calc
    ‖conjugateOperator A z‖ = ‖A (conjugation z)‖ := by simp
    _ ≤ ‖A‖ * ‖conjugation z‖ := A.le_opNorm _
    _ = ‖A‖ * ‖z‖ := by rw [conjugation.norm_map]

private theorem norm_conjugateOperator (A : RealComplexification E →L[ℂ] RealComplexification E) :
    ‖conjugateOperator A‖ = ‖A‖ := by
  apply le_antisymm (norm_conjugateOperator_le A)
  calc
    ‖A‖ = ‖conjugateOperator (conjugateOperator A)‖ := by simp
    _ ≤ ‖conjugateOperator A‖ := norm_conjugateOperator_le _

private theorem isometry_conjugateOperator :
    Isometry (conjugateOperator :
      (RealComplexification E →L[ℂ] RealComplexification E) →
        (RealComplexification E →L[ℂ] RealComplexification E)) := by
  apply Isometry.of_dist_eq
  intro A B
  rw [dist_eq_norm, dist_eq_norm, ← conjugateOperator_sub,
    norm_conjugateOperator]

/-- Canonical conjugation is a continuous real star-algebra automorphism of
bounded operators on the complexification. -/
private noncomputable def conjugateOperatorHom :
    (RealComplexification E →L[ℂ] RealComplexification E) →⋆ₐ[ℝ]
      (RealComplexification E →L[ℂ] RealComplexification E) where
  toFun := conjugateOperator
  map_one' := conjugateOperator_one
  map_zero' := conjugateOperator_zero
  map_mul' := conjugateOperator_mul
  map_add' := conjugateOperator_add
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    change conjugateOperator
        (@SMul.smul ℝ (RealComplexification E →L[ℂ] RealComplexification E)
          complexOperatorRealAlgebra.toSMul r 1) =
      @SMul.smul ℝ (RealComplexification E →L[ℂ] RealComplexification E)
        complexOperatorRealAlgebra.toSMul r 1
    rw [restrictedReal_smul_operator_eq,
      conjugateOperator_real_smul, conjugateOperator_one]
  map_star' A := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      conjugateOperator_adjoint A

private theorem continuous_conjugateOperatorHom :
    Continuous (conjugateOperatorHom :
      (RealComplexification E →L[ℂ] RealComplexification E) → (RealComplexification E →L[ℂ] RealComplexification E)) :=
  isometry_conjugateOperator.continuous

omit [CompleteSpace E] in
/-- Every complexified real operator is fixed by canonical conjugation. -/
private theorem conjugateOperator_complexify (A : E →L[ℝ] E) :
    conjugateOperator (complexify A) = complexify A := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext <;> simp [conjugateOperator_apply]

/-- Continuous real functional calculus of a conjugation-fixed self-adjoint
operator remains conjugation-fixed. -/
private theorem conjugateOperator_cfc_eq
    (C : RealComplexification E →L[ℂ] RealComplexification E) (hC : IsSelfAdjoint C)
    (hfix : conjugateOperator C = C) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ C)) :
    conjugateOperator (cfc f C) = cfc f C := by
  let φ : C(spectrum ℝ C, ℝ) →⋆ₐ[ℝ] (RealComplexification E →L[ℂ] RealComplexification E) :=
    conjugateOperatorHom.comp (cfcHom hC)
  have hφcont : Continuous φ := by
    exact continuous_conjugateOperatorHom.comp (cfcHom_continuous hC)
  have hφid : φ ((ContinuousMap.id ℝ).restrict (spectrum ℝ C)) = C := by
    change conjugateOperator
      (cfcHom hC ((ContinuousMap.id ℝ).restrict (spectrum ℝ C))) = C
    rw [cfcHom_id hC]
    exact hfix
  have heq : cfcHom hC = φ :=
    cfcHom_eq_of_continuous_of_map_id hC φ hφcont hφid
  rw [cfc_apply f C hC hf]
  let g : C(spectrum ℝ C, ℝ) := ⟨fun x => f x.1, hf.restrict⟩
  change conjugateOperator (cfcHom hC g) = cfcHom hC g
  have happ := DFunLike.congr_fun heq g
  change cfcHom hC g = conjugateOperator (cfcHom hC g) at happ
  exact happ.symm

/-! ## Descent of conjugation-fixed operators -/

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem norm_re_le (z : RealComplexification E) : ‖re z‖ ≤ ‖z‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq]
  nlinarith [sq_nonneg ‖im z‖]

/-- Restrict a complex operator to the real copy and take its real coordinate. -/
private noncomputable def realPartOperator
    (A : RealComplexification E →L[ℂ] RealComplexification E) :
    E →L[ℝ] E := by
  let L : E →ₗ[ℝ] E :=
    { toFun := fun x => re (A (ofReal x))
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  exact L.mkContinuous ‖A‖ fun x => by
    calc
      ‖re (A (ofReal x))‖ ≤ ‖A (ofReal x)‖ := norm_re_le _
      _ ≤ ‖A‖ * ‖ofReal x‖ := A.le_opNorm _
      _ = ‖A‖ * ‖x‖ := by rw [ofReal.norm_map]

omit [CompleteSpace E] in
@[simp]
private theorem realPartOperator_apply (A : RealComplexification E →L[ℂ] RealComplexification E) (x : E) :
    realPartOperator A x = re (A (ofReal x)) := rfl

omit [CompleteSpace E] in
private theorem fixed_operator_maps_real_to_real
    {A : RealComplexification E →L[ℂ] RealComplexification E} (hfix : conjugateOperator A = A) (x : E) :
    im (A (ofReal x)) = 0 := by
  have hpoint := congrArg (fun B : RealComplexification E →L[ℂ] RealComplexification E => B (ofReal x)) hfix
  have hcoord := congrArg im hpoint
  have hneg : -im (A (ofReal x)) = im (A (ofReal x)) := by
    simpa only [conjugateOperator_apply, conjugation_ofReal, im_conj] using hcoord
  have htwo : (2 : ℝ) • im (A (ofReal x)) = 0 := by
    calc
      (2 : ℝ) • im (A (ofReal x)) =
          im (A (ofReal x)) + im (A (ofReal x)) := two_smul ℝ _
      _ = -im (A (ofReal x)) + im (A (ofReal x)) :=
        congrArg (fun y => y + im (A (ofReal x))) hneg.symm
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

private theorem fixed_operator_on_ofReal
    {A : RealComplexification E →L[ℂ] RealComplexification E} (hfix : conjugateOperator A = A) (x : E) :
    A (ofReal x) = ofReal (realPartOperator A x) := by
  apply RealComplexification.ext
  · simp
  · simp [fixed_operator_maps_real_to_real hfix x]

/-- A conjugation-fixed complex operator is exactly the complexification of its
restriction to the real copy. -/
private theorem complexify_realPartOperator
    {A : RealComplexification E →L[ℂ] RealComplexification E} (hfix : conjugateOperator A = A) :
    complexify (realPartOperator A) = A := by
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = ofReal (re z) + Complex.I • ofReal (im z) := by
    apply RealComplexification.ext <;> simp
  calc
    complexify (realPartOperator A) z =
        ofReal (realPartOperator A (re z)) +
          Complex.I • ofReal (realPartOperator A (im z)) := by
      apply RealComplexification.ext <;> simp
    _ = A (ofReal (re z)) + Complex.I • A (ofReal (im z)) := by
      rw [fixed_operator_on_ofReal hfix, fixed_operator_on_ofReal hfix]
    _ = A z := by
      rw [← map_smul, ← map_add, ← hz]

/-! ## Complexification and the Gram operator -/

/-- Complexification commutes with the Hilbert-space adjoint. -/
private theorem complexify_adjoint (T : E →L[ℝ] F) :
    complexify T.adjoint = (complexify T).adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff
    (complexify T.adjoint) (complexify T)).2
  intro z w
  simp only [inner_apply, re_complexify, im_complexify]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]

private theorem complexify_gram (T : E →L[ℝ] F) :
    complexify (T.adjoint ∘L T) =
      (complexify T).adjoint ∘L complexify T := by
  rw [complexify_comp, complexify_adjoint]

/-! ## Continuous high-energy cutoff -/

/-- A continuous cutoff which vanishes at energies at most `u²`, tends to one
at high energy, and gives a tail operator bounded by `u`. -/
private def spectralCutoff (u x : ℝ) : ℝ :=
  1 - u ^ 2 / max x (u ^ 2)

private theorem continuous_spectralCutoff (u : ℝ) (hu : 0 < u) :
    Continuous (spectralCutoff u) := by
  have hden : ∀ x : ℝ, max x (u ^ 2) ≠ 0 := by
    intro x hx
    have hle : u ^ 2 ≤ max x (u ^ 2) := le_max_right _ _
    have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu
    rw [hx] at hle
    linarith
  exact continuous_const.sub
    (continuous_const.div (continuous_id.max continuous_const) hden)

private theorem spectralCutoff_eq_zero_of_le
    {u x : ℝ} (hu : 0 < u) (hx : x ≤ u ^ 2) :
    spectralCutoff u x = 0 := by
  rw [spectralCutoff, max_eq_right hx]
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu.ne'
  rw [div_self hu2, sub_self]

private theorem spectralCutoff_tail_bound
    {u x : ℝ} (hu : 0 < u) (_hx0 : 0 ≤ x) :
    x * (1 - spectralCutoff u x) ^ 2 ≤ u ^ 2 := by
  by_cases hx : x ≤ u ^ 2
  · rw [spectralCutoff_eq_zero_of_le hu hx]
    simpa using hx
  · have hux : u ^ 2 < x := lt_of_not_ge hx
    have hxpos : 0 < x := (sq_pos_of_pos hu).trans hux
    rw [spectralCutoff, max_eq_left hux.le]
    have hid : 1 - (1 - u ^ 2 / x) = u ^ 2 / x := by ring
    rw [hid]
    have hmul : u ^ 4 ≤ u ^ 2 * x := by
      nlinarith [sq_nonneg (u ^ 2)]
    calc
      x * (u ^ 2 / x) ^ 2 = u ^ 4 / x := by
        field_simp [hxpos.ne']
      _ ≤ u ^ 2 := (div_le_iff₀ hxpos).2 hmul

private theorem spectralCutoff_lower_bound
    {u x : ℝ} (hu : 0 < u) :
    u ^ 2 * (spectralCutoff u x) ^ 2 ≤
      x * (spectralCutoff u x) ^ 2 := by
  by_cases hx : x ≤ u ^ 2
  · rw [spectralCutoff_eq_zero_of_le hu hx]
    simp
  · exact mul_le_mul_of_nonneg_right (le_of_not_ge hx)
      (sq_nonneg (spectralCutoff u x))

/-! ## The real threshold theorem -/

omit [CompleteSpace E] [CompleteSpace F] in
/-- Restriction to a real subspace cannot increase an approximation number. -/
theorem approximationNumber_comp_subtypeL_le_real
    (T : E →L[ℝ] F) (n : ℕ) (V : Submodule ℝ E) :
    (T ∘L V.subtypeL).approximationNumber n ≤ T.approximationNumber n := by
  have h := T.approximationNumber_comp_right_le V.subtypeL n
  have hsub : ‖V.subtypeL‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast V.norm_subtypeL_le
  calc
    (T ∘L V.subtypeL).approximationNumber n
        ≤ T.approximationNumber n * ‖V.subtypeL‖₊ := h
    _ ≤ T.approximationNumber n * 1 :=
      mul_le_mul_of_nonneg_left hsub bot_le
    _ = T.approximationNumber n := by rw [mul_one]

/-- Approximation numbers of restrictions to real spans of `n+1` vectors. -/
def finiteRestrictionApproximationNumbersReal
    (T : E →L[ℝ] F) (n : ℕ) : Set NNReal :=
  Set.range fun v : Fin (n + 1) → E =>
    (T ∘L (Submodule.span ℝ (Set.range v)).subtypeL).approximationNumber n

omit [CompleteSpace E] [CompleteSpace F] in
/-- The ambient real approximation number bounds all finite restrictions. -/
theorem finiteRestrictionApproximationNumbersReal_upperBound
    (T : E →L[ℝ] F) (n : ℕ) :
    T.approximationNumber n ∈
      upperBounds (finiteRestrictionApproximationNumbersReal T n) := by
  rintro _ ⟨v, rfl⟩
  exact approximationNumber_comp_subtypeL_le_real T n
    (Submodule.span ℝ (Set.range v))

/-- Real spectral-threshold form of infinite-dimensional Courant--Fischer.
Every strict nonnegative lower bound for `a_n(T)` is improved to a uniform
lower modulus on a real `(n+1)`-dimensional subspace. -/
theorem exists_linearIndependent_lowerBound_of_lt_approximationNumber_real
    (T : E →L[ℝ] F) (n : ℕ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < (T.approximationNumber n : ℝ)) :
    ∃ s : ℝ, r < s ∧
      ∃ v : Fin (n + 1) → E, LinearIndependent ℝ v ∧
        ∀ x ∈ Submodule.span ℝ (Set.range v),
          s * ‖x‖ ≤ ‖T x‖ := by
  classical
  let a : ℝ := (T.approximationNumber n : ℝ)
  let u : ℝ := (r + a) / 2
  have hru : r < u := by dsimp only [u, a]; linarith
  have hua : u < a := by dsimp only [u, a]; linarith
  have hu0 : 0 < u := by linarith

  let Tc : RealComplexification E →L[ℂ] RealComplexification F := complexify T
  let C0 : E →L[ℝ] E := T.adjoint ∘L T
  let C : RealComplexification E →L[ℂ] RealComplexification E := Tc.adjoint ∘L Tc
  have hCeq : C = complexify C0 := by
    dsimp only [C, C0, Tc]
    exact (complexify_gram T).symm
  have hCnonneg : (0 : RealComplexification E →L[ℂ] RealComplexification E) ≤ C := by
    dsimp only [C]
    exact (ContinuousLinearMap.nonneg_iff_isPositive _).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self Tc)
  have hC : IsSelfAdjoint C := IsSelfAdjoint.of_nonneg hCnonneg
  have hCfix : conjugateOperator C = C := by
    rw [hCeq, conjugateOperator_complexify]

  let p : ℝ → ℝ := spectralCutoff u
  let q : ℝ → ℝ := fun x => 1 - p x
  have hpcont : Continuous p := continuous_spectralCutoff u hu0
  have hqcont : Continuous q := continuous_const.sub hpcont
  let Pc : RealComplexification E →L[ℂ] RealComplexification E := cfc p C
  let Qc : RealComplexification E →L[ℂ] RealComplexification E := cfc q C
  have hPcfix : conjugateOperator Pc = Pc := by
    dsimp only [Pc]
    exact conjugateOperator_cfc_eq C hC hCfix p hpcont.continuousOn
  let P : E →L[ℝ] E := realPartOperator Pc
  let Q : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - P
  have hPcComplexify : complexify P = Pc := by
    dsimp only [P]
    exact complexify_realPartOperator hPcfix
  have hQcEq : Qc = ContinuousLinearMap.id ℂ (RealComplexification E) - Pc := by
    dsimp only [Qc, q, Pc]
    rw [cfc_sub (fun _ : ℝ => 1) p C,
      cfc_const_one ℝ C]
    rfl
  have hQcComplexify : complexify Q = Qc := by
    rw [hQcEq]
    dsimp only [Q]
    rw [complexify_sub, complexify_id, hPcComplexify]

  have hCspec_nonneg : ∀ x ∈ spectrum ℝ C, 0 ≤ x := by
    intro x hx
    exact spectrum_nonneg_of_nonneg hCnonneg hx

  have hQcSelfAdjoint : IsSelfAdjoint Qc := cfc_predicate q C
  have htailGram :
      (Tc ∘L Qc).adjoint ∘L (Tc ∘L Qc) =
        cfc (fun x => x * (q x) ^ 2) C := by
    rw [ContinuousLinearMap.adjoint_comp, hQcSelfAdjoint.adjoint_eq]
    calc
      (Qc ∘L Tc.adjoint) ∘L (Tc ∘L Qc) =
          (Qc ∘L C) ∘L Qc := by
        simp only [C, ContinuousLinearMap.comp_assoc]
      _ = cfc (fun x => x * (q x) ^ 2) C := by
        change cfc q C * C * cfc q C = _
        calc
          cfc q C * C * cfc q C =
              cfc q C * cfc (fun x : ℝ => x) C * cfc q C := by
            rw [cfc_id' ℝ C]
          _ = cfc (fun x : ℝ => q x * x) C * cfc q C := by
            rw [cfc_mul q (fun x : ℝ => x) C
              hqcont.continuousOn continuous_id.continuousOn]
          _ = cfc (fun x : ℝ => (q x * x) * q x) C := by
            rw [cfc_mul (fun x : ℝ => q x * x) q C
              (hqcont.mul continuous_id).continuousOn hqcont.continuousOn]
          _ = cfc (fun x => x * (q x) ^ 2) C := by
            apply cfc_congr
            intro x _
            ring

  have htailCfcNorm :
      ‖cfc (fun x => x * (q x) ^ 2) C‖ ≤ u ^ 2 := by
    refine norm_cfc_le (f := fun x : ℝ => x * (q x) ^ 2) (a := C)
      (sq_nonneg u) ?_
    intro x hx
    have hx0 := hCspec_nonneg x hx
    have hbound := spectralCutoff_tail_bound hu0 hx0
    change |x * (1 - spectralCutoff u x) ^ 2| ≤ u ^ 2
    rw [abs_of_nonneg (mul_nonneg hx0 (sq_nonneg _))]
    exact hbound
  have htailComplex : ‖Tc ∘L Qc‖ ≤ u := by
    have hsq : ‖Tc ∘L Qc‖ ^ 2 ≤ u ^ 2 := by
      calc
        ‖Tc ∘L Qc‖ ^ 2 =
            ‖(Tc ∘L Qc).adjoint ∘L (Tc ∘L Qc)‖ := by
              rw [sq, ContinuousLinearMap.norm_adjoint_comp_self]
        _ = ‖cfc (fun x => x * (q x) ^ 2) C‖ := by rw [htailGram]
        _ ≤ u ^ 2 := htailCfcNorm
    exact le_of_sq_le_sq hsq hu0.le
  have htailReal : ‖T ∘L Q‖ ≤ u := by
    rw [← norm_complexify]
    rw [complexify_comp, hQcComplexify]
    exact htailComplex

  have hlowerCfcNonneg :
      (0 : RealComplexification E →L[ℂ] RealComplexification E) ≤
        cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C := by
    apply cfc_nonneg
    intro x hx
    have hx0 := hCspec_nonneg x hx
    have hcut := spectralCutoff_lower_bound (x := x) hu0
    change 0 ≤ (x - u ^ 2) * (spectralCutoff u x) ^ 2
    nlinarith
  have hlowerIdentity :
      cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C =
        Pc * C * Pc - u ^ 2 • (Pc * Pc) := by
    have hpcmul : Pc * Pc = cfc (fun x => (p x) ^ 2) C := by
      dsimp only [Pc]
      calc
        cfc p C * cfc p C = cfc (fun x : ℝ => p x * p x) C :=
          (cfc_mul p p C hpcont.continuousOn hpcont.continuousOn).symm
        _ = cfc (fun x => (p x) ^ 2) C := by
          apply cfc_congr
          intro x _
          ring
    have hpcCpc : Pc * C * Pc = cfc (fun x => x * (p x) ^ 2) C := by
      dsimp only [Pc]
      calc
        cfc p C * C * cfc p C =
            cfc p C * cfc (fun x : ℝ => x) C * cfc p C := by
          rw [cfc_id' ℝ C]
        _ = cfc (fun x : ℝ => p x * x) C * cfc p C := by
          rw [cfc_mul p (fun x : ℝ => x) C
            hpcont.continuousOn continuous_id.continuousOn]
        _ = cfc (fun x : ℝ => (p x * x) * p x) C := by
          rw [cfc_mul (fun x : ℝ => p x * x) p C
            (hpcont.mul continuous_id).continuousOn hpcont.continuousOn]
        _ = cfc (fun x => x * (p x) ^ 2) C := by
          apply cfc_congr
          intro x _
          ring
    have hscale :
        u ^ 2 • (Pc * Pc) = cfc (fun x => u ^ 2 * (p x) ^ 2) C := by
      rw [hpcmul]
      calc
        u ^ 2 • cfc (fun x => (p x) ^ 2) C =
            @SMul.smul ℝ
              (RealComplexification E →L[ℂ] RealComplexification E)
              complexOperatorRealAlgebra.toSMul (u ^ 2)
              (cfc (fun x => (p x) ^ 2) C) := by
          exact (restrictedReal_smul_operator_eq
            (u ^ 2) (cfc (fun x => (p x) ^ 2) C)).symm
        _ = cfc (fun x => u ^ 2 * (p x) ^ 2) C :=
          (cfc_const_mul (u ^ 2) (fun x => (p x) ^ 2) C
            (hpcont.fun_pow 2).continuousOn).symm
    calc
      cfc (fun x => (x - u ^ 2) * (p x) ^ 2) C =
          cfc (fun x => x * (p x) ^ 2 - u ^ 2 * (p x) ^ 2) C := by
        apply cfc_congr
        intro x _
        ring
      _ = cfc (fun x => x * (p x) ^ 2) C -
          cfc (fun x => u ^ 2 * (p x) ^ 2) C := by
        exact cfc_sub (fun x => x * (p x) ^ 2)
          (fun x => u ^ 2 * (p x) ^ 2) C
          ((continuous_id.mul (hpcont.fun_pow 2)).continuousOn)
          ((continuous_const.mul (hpcont.fun_pow 2)).continuousOn)
      _ = Pc * C * Pc - u ^ 2 • (Pc * Pc) := by
        rw [← hpcCpc, ← hscale]
  have hPcLower : ∀ z : RealComplexification E, u * ‖Pc z‖ ≤ ‖Tc (Pc z)‖ := by
    intro z
    have hpositive :=
      (ContinuousLinearMap.nonneg_iff_isPositive _).mp hlowerCfcNonneg
    have hform := hpositive.re_inner_nonneg_left z
    rw [hlowerIdentity] at hform
    have henergy :
        u ^ 2 * ‖Pc z‖ ^ 2 ≤ ‖Tc (Pc z)‖ ^ 2 := by
      change 0 ≤
        RCLike.re ⟪(Pc * C * Pc - u ^ 2 • (Pc * Pc)) z, z⟫_ℂ at hform
      have hPcsa : IsSelfAdjoint Pc := cfc_predicate p C
      have h1 :
          RCLike.re ⟪(Pc * C * Pc) z, z⟫_ℂ = ‖Tc (Pc z)‖ ^ 2 := by
        simp only [mul_apply_eq_comp]
        have hadj : ⟪Pc (C (Pc z)), z⟫_ℂ = ⟪C (Pc z), Pc z⟫_ℂ := by
          simpa only [hPcsa.adjoint_eq] using
            (ContinuousLinearMap.adjoint_inner_left Pc z (C (Pc z)))
        rw [hadj]
        dsimp only [C]
        exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left Tc (Pc z)).symm
      have h2 :
          RCLike.re ⟪(u ^ 2 • (Pc * Pc)) z, z⟫_ℂ =
            u ^ 2 * ‖Pc z‖ ^ 2 := by
        have hadj : ⟪Pc (Pc z), z⟫_ℂ = ⟪Pc z, Pc z⟫_ℂ := by
          simpa only [hPcsa.adjoint_eq] using
            (ContinuousLinearMap.adjoint_inner_left Pc z (Pc z))
        simp only [smul_apply, mul_apply_eq_comp]
        rw [inner_smul_left_eq_smul, hadj, inner_self_eq_norm_sq_to_K,
          RCLike.smul_re, RCLike.re_ofReal_pow]
      have hform' :
          0 ≤ RCLike.re ⟪(Pc * C * Pc) z, z⟫_ℂ -
            RCLike.re ⟪(u ^ 2 • (Pc * Pc)) z, z⟫_ℂ := by
        simpa only [sub_apply, inner_sub_left, map_sub] using hform
      rw [h1, h2] at hform'
      linarith
    exact le_of_sq_le_sq (by simpa [mul_pow] using henergy) (norm_nonneg _)
  have hPLower : ∀ x : E, u * ‖P x‖ ≤ ‖T (P x)‖ := by
    intro x
    have h := hPcLower (ofReal x)
    have hPcReal : Pc (ofReal x) = ofReal (P x) := by
      rw [← hPcComplexify, complexify_ofReal]
    calc
      u * ‖P x‖ = u * ‖Pc (ofReal x)‖ := by
        rw [hPcReal, ofReal.norm_map]
      _ ≤ ‖Tc (Pc (ofReal x))‖ := h
      _ = ‖T (P x)‖ := by
        rw [hPcReal]
        dsimp only [Tc]
        rw [complexify_ofReal, ofReal.norm_map]

  have hPrank : ¬ P.rank ≤ (n : Cardinal) := by
    intro hP
    let R : E →L[ℝ] F := T ∘L P
    -- `R.rank` and `P.rank` live in different universes once the codomain is
    -- independent, so the comparison goes through the natural-number bound.
    have hRrank : R.rank ≤ (n : Cardinal) :=
      ContinuousLinearMap.rank_comp_left_le_of_rank_le T P hP
    have herr : T - R = T ∘L Q := by
      ext x
      change T x - T (P x) = T (Q x)
      dsimp only [Q]
      rw [sub_apply, ContinuousLinearMap.id_apply, map_sub]
    have happrox := T.approximationNumber_le hRrank
    have happroxReal : a ≤ ‖T - R‖ := by
      have hco := NNReal.coe_le_coe.mpr happrox
      change a ≤ ‖T - R‖ at hco
      exact hco
    have hau : a ≤ u := by
      calc
        a ≤ ‖T - R‖ := happroxReal
        _ = ‖T ∘L Q‖ := by rw [herr]
        _ ≤ u := htailReal
    exact (not_le_of_gt hua) hau

  let W : Submodule ℝ E := P.range
  have hnrank : ((n + 1 : ℕ) : Cardinal) ≤ Module.rank ℝ W := by
    change ((n + 1 : ℕ) : Cardinal) ≤ P.rank
    have hlt : (n : Cardinal) < P.rank := lt_of_not_ge hPrank
    rw [← Cardinal.natCast_add_one_le_iff, ← Nat.cast_add_one] at hlt
    exact hlt
  obtain ⟨f, hf⟩ := (Module.le_rank_iff).mp hnrank
  let v : Fin (n + 1) → E := W.subtype ∘ f
  have hv : LinearIndependent ℝ v := by
    change LinearIndependent ℝ (W.subtype ∘ f)
    exact hf.map' W.subtype
      (LinearMap.ker_eq_bot.mpr W.injective_subtype)
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  have hVle : V ≤ W := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (f i).2
  refine ⟨u, hru, v, hv, ?_⟩
  intro x hxV
  have hxW : x ∈ W := hVle hxV
  obtain ⟨y, hy⟩ := hxW
  rw [← hy]
  exact hPLower y

/-- Every strict real lower threshold for the ambient approximation number is
exceeded by an approximation number of an `(n+1)`-generated real restriction. -/
theorem exists_finiteRestrictionApproximationNumber_gt_of_lt_real
    (T : E →L[ℝ] F) (n : ℕ) {r : NNReal}
    (hr : r < T.approximationNumber n) :
    ∃ v : Fin (n + 1) → E,
      r < (T ∘L (Submodule.span ℝ (Set.range v)).subtypeL).approximationNumber n := by
  have hrReal : (r : ℝ) < (T.approximationNumber n : ℝ) := by
    exact_mod_cast hr
  obtain ⟨s, hrs, v, hv, hV⟩ :=
    exists_linearIndependent_lowerBound_of_lt_approximationNumber_real
      T n (NNReal.coe_nonneg r) hrReal
  have hs0 : 0 ≤ s := (NNReal.coe_nonneg r).trans hrs.le
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range v)
  let b : Module.Basis (Fin (n + 1)) ℝ V := Module.Basis.span hv
  let w : Fin (n + 1) → V := fun i => b i
  have hw : LinearIndependent ℝ w := by
    simpa only [w] using b.linearIndependent
  have hsNN : (⟨s, hs0⟩ : NNReal) ≤
      (T ∘L V.subtypeL).approximationNumber n := by
    apply ContinuousLinearMap.lowerBound_le_approximationNumber_of_linearIndependent
      (T ∘L V.subtypeL) n w hw
    intro x _ hxNorm
    have hxV : ((x : V) : E) ∈ V := x.property
    have hxNormE : ‖((x : V) : E)‖ = 1 := by
      simpa using hxNorm
    change s ≤ ‖T ((x : V) : E)‖
    calc
      s = s * ‖((x : V) : E)‖ := by rw [hxNormE, mul_one]
      _ ≤ ‖T ((x : V) : E)‖ := hV ((x : V) : E) hxV
  have hrsNN : r < (⟨s, hs0⟩ : NNReal) := by
    change (r : ℝ) < s
    exact hrs
  refine ⟨v, ?_⟩
  simpa only [V] using hrsNN.trans_le hsNN

/-- Exact real finite-dimensional localization: the ambient approximation
number is the least upper bound of the approximation numbers of restrictions
to spans of `n+1` real vectors. -/
theorem approximationNumber_isLUB_finiteRestrictions_real
    (T : E →L[ℝ] F) (n : ℕ) :
    IsLUB (finiteRestrictionApproximationNumbersReal T n)
      (T.approximationNumber n) := by
  refine ⟨finiteRestrictionApproximationNumbersReal_upperBound T n, ?_⟩
  intro b hb
  by_contra hnot
  have hlt : b < T.approximationNumber n := lt_of_not_ge hnot
  obtain ⟨v, hv⟩ :=
    exists_finiteRestrictionApproximationNumber_gt_of_lt_real T n hlt
  have hle := hb (show
    (T ∘L (Submodule.span ℝ (Set.range v)).subtypeL).approximationNumber n ∈
      finiteRestrictionApproximationNumbersReal T n from ⟨v, rfl⟩)
  exact (not_le_of_gt hv) hle

/-- Epsilon-form real generalized Courant--Fischer characterization. -/
theorem lt_approximationNumber_iff_exists_finiteDimensional_lowerBound_real
    (T : E →L[ℝ] F) (n : ℕ) {r : ℝ} (hr0 : 0 ≤ r) :
    r < (T.approximationNumber n : ℝ) ↔
      ∃ s : ℝ, r < s ∧
        ∃ v : Fin (n + 1) → E, LinearIndependent ℝ v ∧
          ∀ x ∈ Submodule.span ℝ (Set.range v),
            s * ‖x‖ ≤ ‖T x‖ := by
  constructor
  · exact exists_linearIndependent_lowerBound_of_lt_approximationNumber_real
      T n hr0
  · rintro ⟨s, hrs, v, hv, hV⟩
    have hs0 : 0 ≤ s := hr0.trans hrs.le
    have hsNN : (⟨s, hs0⟩ : NNReal) ≤ T.approximationNumber n := by
      apply ContinuousLinearMap.lowerBound_le_approximationNumber_of_linearIndependent
        T n v hv
      intro x hxV hxNorm
      change s ≤ ‖T x‖
      calc
        s = s * ‖x‖ := by rw [hxNorm, mul_one]
        _ ≤ ‖T x‖ := hV x hxV
    have hs : s ≤ (T.approximationNumber n : ℝ) := by
      exact NNReal.coe_le_coe.mpr hsNN
    exact hrs.trans_le hs


/-! ## Strong cutoffs and finite Ky Fan gauges over real Hilbert spaces -/

/-- Real-Hilbert-space cutoff convergence, obtained from finite-dimensional
localization and uniform convergence on each witness subspace. -/
theorem approximationSingularValue_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (n : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) := by
  have hUpper : ∀ i,
      approximationSingularValue n (K ∘L P i) ≤
        approximationSingularValue n K := by
    intro i
    have hnormNN : ‖P i‖₊ ≤ (1 : NNReal) := by
      exact_mod_cast (hPproj i).norm_le_one
    have hNN : (K ∘L P i).approximationNumber n ≤
        K.approximationNumber n := by
      calc
        (K ∘L P i).approximationNumber n
            ≤ K.approximationNumber n * ‖P i‖₊ :=
          K.approximationNumber_comp_right_le (P i) n
        _ ≤ K.approximationNumber n * 1 :=
          mul_le_mul_of_nonneg_left hnormNN bot_le
        _ = K.approximationNumber n := by rw [mul_one]
    exact_mod_cast hNN
  have hLower : ∀ r : ℝ,
      r < approximationSingularValue n K →
      ∀ᶠ i in l, r < approximationSingularValue n (K ∘L P i) := by
    intro r hr
    by_cases hr0 : 0 ≤ r
    · obtain ⟨s, hrs, v, hv, hV⟩ :=
        exists_linearIndependent_lowerBound_of_lt_approximationNumber_real
          K n hr0 hr
      let c : ℝ := (r + s) / 2
      have hrc : r < c := by dsimp only [c]; linarith
      have hcs : c < s := by dsimp only [c]; linarith
      have hc0 : 0 ≤ c := hr0.trans hrc.le
      let V : Submodule ℝ E := Submodule.span ℝ (Set.range v)
      let b : Module.Basis (Fin (n + 1)) ℝ V := Module.Basis.span hv
      letI : FiniteDimensional ℝ V := b.finiteDimensional_of_finite
      let D : ι → V →L[ℝ] F := fun i =>
        (K ∘L P i ∘L V.subtypeL) - (K ∘L V.subtypeL)
      have hDpoint : ∀ x : V, Tendsto (fun i => D i x) l (𝓝 0) := by
        intro x
        have hKP : Tendsto (fun i => K (P i (V.subtypeL x))) l
            (𝓝 (K (V.subtypeL x))) :=
          (K.continuous.tendsto (V.subtypeL x)).comp (hP (V.subtypeL x))
        have hconst : Tendsto (fun _ : ι => K (V.subtypeL x)) l
            (𝓝 (K (V.subtypeL x))) := tendsto_const_nhds
        change Tendsto
          (fun i => K (P i (V.subtypeL x)) - K (V.subtypeL x))
          l (𝓝 0)
        simpa only [sub_self] using hKP.sub hconst
      have hDnorm : Tendsto (fun i => ‖D i‖) l (𝓝 0) :=
        tendsto_opNorm_zero_of_finiteDimensional D hDpoint
      have hsmall : ∀ᶠ i in l, ‖D i‖ < s - c :=
        hDnorm.eventually (Iio_mem_nhds (sub_pos.mpr hcs))
      filter_upwards [hsmall] with i hi
      have hcNN : (⟨c, hc0⟩ : NNReal) ≤
          (K ∘L P i).approximationNumber n := by
        apply ContinuousLinearMap.lowerBound_le_approximationNumber_of_linearIndependent
          (K ∘L P i) n v hv
        intro x hxV hxNorm
        have hDx : ‖D i ⟨x, hxV⟩‖ ≤ ‖D i‖ := by
          have h := (D i).le_opNorm ⟨x, hxV⟩
          change ‖D i ⟨x, hxV⟩‖ ≤ ‖D i‖ * ‖x‖ at h
          rw [hxNorm, mul_one] at h
          exact h
        have hDapply : D i ⟨x, hxV⟩ = K (P i x) - K x := by
          rfl
        have htri : ‖K x‖ ≤ ‖K (P i x)‖ + ‖D i ⟨x, hxV⟩‖ := by
          rw [hDapply]
          have h := norm_sub_le (K (P i x)) (K (P i x) - K x)
          convert h using 1 <;> abel
        have hsx : s ≤ ‖K x‖ := by
          have := hV x hxV
          simpa only [hxNorm, mul_one] using this
        apply NNReal.coe_le_coe.mpr
        change c ≤ ‖K (P i x)‖
        linarith
      have hcReal : c ≤ approximationSingularValue n (K ∘L P i) := by
        exact_mod_cast hcNN
      exact hrc.trans_le hcReal
    · have hrneg : r < 0 := lt_of_not_ge hr0
      filter_upwards [] with i
      exact hrneg.trans_le
        (approximationSingularValue_nonneg n (K ∘L P i))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hlower := hLower
    (approximationSingularValue n K - ε) (by linarith)
  filter_upwards [hlower] with i hi
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith
  · have := hUpper i
    linarith

/-- Real finite Ky Fan approximation gauges converge under strong orthogonal
cutoffs. -/
theorem kyFanApproximationGauge_comp_strongProjection_tendsto_real
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (k : ℕ) (K : E →L[ℝ] F) :
    Tendsto
      (fun i => kyFanApproximationGauge k (K ∘L P i))
      l (𝓝 (kyFanApproximationGauge k K)) := by
  simp only [kyFanApproximationGauge]
  exact tendsto_finsetSum (Finset.range k)
    (fun n _ => approximationSingularValue_comp_strongProjection_tendsto_real
      hPproj hP n K)

omit [CompleteSpace E] [CompleteSpace F] in
/-- Restricting a real operator to a larger source subspace can only increase
its approximation singular values. -/
theorem approximationSingularValue_restrict_mono_real
    (T : E →L[ℝ] F) (n : ℕ) {U V : Submodule ℝ E}
    (hUV : U ≤ V) :
    approximationSingularValue n (T ∘L U.subtypeL) ≤
      approximationSingularValue n (T ∘L V.subtypeL) := by
  let J : U →L[ℝ] V :=
    (Submodule.inclusion hUV).mkContinuous 1 (fun x => by
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp)
  have hJnorm : ‖J‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast (J.opNorm_le_bound zero_le_one fun x => by
      change ‖((x : U) : E)‖ ≤ 1 * ‖x‖
      simp)
  have hcomp : T ∘L U.subtypeL = (T ∘L V.subtypeL) ∘L J := by
    ext x
    rfl
  have hNN : (T ∘L U.subtypeL).approximationNumber n ≤
      (T ∘L V.subtypeL).approximationNumber n := by
    rw [hcomp]
    calc
      ((T ∘L V.subtypeL) ∘L J).approximationNumber n
          ≤ (T ∘L V.subtypeL).approximationNumber n * ‖J‖₊ :=
        (T ∘L V.subtypeL).approximationNumber_comp_right_le J n
      _ ≤ (T ∘L V.subtypeL).approximationNumber n * 1 :=
        mul_le_mul_of_nonneg_left hJnorm bot_le
      _ = (T ∘L V.subtypeL).approximationNumber n := by rw [mul_one]
  change ((T ∘L U.subtypeL).approximationNumber n : ℝ) ≤
    ((T ∘L V.subtypeL).approximationNumber n : ℝ)
  exact_mod_cast hNN

/-- Projecting the codomain onto a real subspace containing the operator range
preserves every approximation singular value. -/
theorem approximationSingularValue_orthogonalProjectionOnto_comp_eq_real
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (W : Submodule ℝ G) [W.HasOrthogonalProjection]
    (A : V →L[ℝ] G) (hA : ∀ x, A x ∈ W) (n : ℕ) :
    approximationSingularValue n (W.orthogonalProjectionOnto ∘L A) =
      approximationSingularValue n A := by
  let AW : V →L[ℝ] W := W.orthogonalProjectionOnto ∘L A
  have hfactor : W.subtypeL ∘L AW = A := by
    ext x
    change W.starProjection (A x) = A x
    exact W.starProjection_eq_self_iff.mpr (hA x)
  have hproj : ‖W.orthogonalProjectionOnto‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast W.orthogonalProjectionOnto_norm_le
  have hsub : ‖W.subtypeL‖₊ ≤ (1 : NNReal) := by
    exact_mod_cast W.norm_subtypeL_le
  have hNN : AW.approximationNumber n = A.approximationNumber n := by
    apply le_antisymm
    · calc
        AW.approximationNumber n
            ≤ ‖W.orthogonalProjectionOnto‖₊ * A.approximationNumber n :=
          ContinuousLinearMap.approximationNumber_comp_left_le
            W.orthogonalProjectionOnto A n
        _ ≤ 1 * A.approximationNumber n :=
          mul_le_mul_of_nonneg_right hproj bot_le
        _ = A.approximationNumber n := by rw [one_mul]
    · rw [← hfactor]
      calc
        (W.subtypeL ∘L AW).approximationNumber n
            ≤ ‖W.subtypeL‖₊ * AW.approximationNumber n :=
          ContinuousLinearMap.approximationNumber_comp_left_le W.subtypeL AW n
        _ ≤ 1 * AW.approximationNumber n :=
          mul_le_mul_of_nonneg_right hsub bot_le
        _ = AW.approximationNumber n := by rw [one_mul]
  change (AW.approximationNumber n : ℝ) = (A.approximationNumber n : ℝ)
  exact congrArg (fun x : NNReal => (x : ℝ)) hNN

/-- Projecting the codomain onto a real subspace containing the range preserves
all finite Ky Fan approximation gauges. -/
theorem kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq_real
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (W : Submodule ℝ G) [W.HasOrthogonalProjection]
    (A : V →L[ℝ] G) (hA : ∀ x, A x ∈ W) (k : ℕ) :
    kyFanApproximationGauge k (W.orthogonalProjectionOnto ∘L A) =
      kyFanApproximationGauge k A := by
  unfold kyFanApproximationGauge
  exact Finset.sum_congr rfl fun n _ =>
    approximationSingularValue_orthogonalProjectionOnto_comp_eq_real W A hA n

/-- The Ky Fan approximation-gauge triangle inequality when the real source is
finite-dimensional and the codomain is arbitrary. -/
theorem kyFanApproximationGauge_add_le_finiteSource_real
    {V : Type vG} {G : Type vH}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (k : ℕ) (A B : V →L[ℝ] G) :
    kyFanApproximationGauge k (A + B) ≤
      kyFanApproximationGauge k A + kyFanApproximationGauge k B := by
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let C : V × V →L[ℝ] G :=
    A ∘L ContinuousLinearMap.fst ℝ V V +
      B ∘L ContinuousLinearMap.snd ℝ V V
  let W : Submodule ℝ G := C.range
  letI : FiniteDimensional ℝ W := by
    apply FiniteDimensional.of_surjective C.rangeRestrict.toLinearMap
    intro y
    rcases y.property with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  letI : CompleteSpace W := FiniteDimensional.complete ℝ W
  letI : W.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace W
  have hA : ∀ x, A x ∈ W := by
    intro x
    change A x ∈ C.range
    refine ⟨(x, 0), ?_⟩
    simp [C]
  have hB : ∀ x, B x ∈ W := by
    intro x
    change B x ∈ C.range
    refine ⟨(0, x), ?_⟩
    simp [C]
  have hAB : ∀ x, (A + B) x ∈ W := by
    intro x
    exact W.add_mem (hA x) (hB x)
  let AW : V →L[ℝ] W := W.orthogonalProjectionOnto ∘L A
  let BW : V →L[ℝ] W := W.orthogonalProjectionOnto ∘L B
  have hsum : W.orthogonalProjectionOnto ∘L (A + B) = AW + BW := by
    ext x
    simp [AW, BW]
  have hAWcont : AW.toLinearMap.toContinuousLinearMap = AW := by
    ext x
    rfl
  have hBWcont : BW.toLinearMap.toContinuousLinearMap = BW := by
    ext x
    rfl
  have hsumcont :
      (AW.toLinearMap + BW.toLinearMap).toContinuousLinearMap = AW + BW := by
    ext x
    rfl
  have htri := kyFanApproximationGauge_add_le_finiteDimensional
    (𝕜 := ℝ) k AW.toLinearMap BW.toLinearMap
  rw [hsumcont, hAWcont, hBWcont] at htri
  calc
    kyFanApproximationGauge k (A + B) =
        kyFanApproximationGauge k (W.orthogonalProjectionOnto ∘L (A + B)) :=
      (kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq_real
        W (A + B) hAB k).symm
    _ = kyFanApproximationGauge k (AW + BW) := by rw [hsum]
    _ ≤ kyFanApproximationGauge k AW + kyFanApproximationGauge k BW := htri
    _ = kyFanApproximationGauge k A + kyFanApproximationGauge k B := by
      rw [kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq_real W A hA k,
        kyFanApproximationGauge_orthogonalProjectionOnto_comp_eq_real W B hB k]

/-- Every positive tolerance admits a real finite-source restriction whose
approximation number is within that tolerance of the ambient value. -/
theorem exists_finiteRestrictionApproximationNumber_add_gt_real
    (T : E →L[ℝ] F) (n : ℕ) (ε : NNReal) (hε : 0 < ε) :
    ∃ v : Fin (n + 1) → E,
      T.approximationNumber n <
        (T ∘L (Submodule.span ℝ (Set.range v)).subtypeL).approximationNumber n + ε := by
  by_cases hsmall : T.approximationNumber n < ε
  · refine ⟨fun _ => 0, hsmall.trans_le ?_⟩
    exact le_add_of_nonneg_left bot_le
  · have hεle : ε ≤ T.approximationNumber n := le_of_not_gt hsmall
    have ha0 : 0 < T.approximationNumber n := hε.trans_le hεle
    have hsub : T.approximationNumber n - ε < T.approximationNumber n :=
      tsub_lt_self ha0 hε
    obtain ⟨v, hv⟩ :=
      exists_finiteRestrictionApproximationNumber_gt_of_lt_real T n hsub
    refine ⟨v, ?_⟩
    calc
      T.approximationNumber n =
          (T.approximationNumber n - ε) + ε :=
        (tsub_add_cancel_of_le hεle).symm
      _ < (T ∘L (Submodule.span ℝ (Set.range v)).subtypeL).approximationNumber n + ε :=
        add_lt_add_left hv ε

/-- Infinite-dimensional Ky Fan addition inequality over real Hilbert spaces,
obtained from simultaneous finite-dimensional localization. -/
theorem kyFanApproximationGauge_add_le_real
    (k : ℕ) (K L : E →L[ℝ] F) :
    kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k K + kyFanApproximationGauge k L := by
  classical
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  apply le_of_forall_pos_le_add
  intro ε hε
  let δr : ℝ := ε / (k : ℝ)
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hδr : 0 < δr := div_pos hε hkreal
  let δ : NNReal := ⟨δr, hδr.le⟩
  have hδ : 0 < δ := by
    change 0 < δr
    exact hδr
  choose v hv using fun n =>
    exists_finiteRestrictionApproximationNumber_add_gt_real (K + L) n δ hδ
  let β : Type := Σ n : Fin k, Fin (n.1 + 1)
  let w : β → E := fun p => v p.1.1 p.2
  let V : Submodule ℝ E := Submodule.span ℝ (Set.range w)
  letI : FiniteDimensional ℝ V :=
    Module.Finite.span_of_finite ℝ (Set.finite_range w)
  letI : CompleteSpace V := FiniteDimensional.complete ℝ V
  let KV : V →L[ℝ] F := K ∘L V.subtypeL
  let LV : V →L[ℝ] F := L ∘L V.subtypeL
  have hsumRestrict : (K + L) ∘L V.subtypeL = KV + LV := by
    ext x
    rfl
  have hterm : ∀ n ∈ Finset.range k,
      approximationSingularValue n (K + L) ≤
        approximationSingularValue n (KV + LV) + (δ : ℝ) := by
    intro n hn
    let U : Submodule ℝ E := Submodule.span ℝ (Set.range (v n))
    have hUV : U ≤ V := by
      apply Submodule.span_le.mpr
      rintro x ⟨j, rfl⟩
      apply Submodule.subset_span
      exact ⟨(⟨⟨n, Finset.mem_range.mp hn⟩, j⟩ : β), rfl⟩
    have hmono := approximationSingularValue_restrict_mono_real
      (K + L) n hUV
    have hvNN : (K + L).approximationNumber n <
        ((K + L) ∘L U.subtypeL).approximationNumber n + δ := by
      simpa only [U] using hv n
    have hvReal : approximationSingularValue n (K + L) <
        approximationSingularValue n ((K + L) ∘L U.subtypeL) + (δ : ℝ) := by
      change ((K + L).approximationNumber n : ℝ) <
        (((K + L) ∘L U.subtypeL).approximationNumber n : ℝ) + (δ : ℝ)
      exact_mod_cast hvNN
    calc
      approximationSingularValue n (K + L)
          ≤ approximationSingularValue n ((K + L) ∘L U.subtypeL) + (δ : ℝ) :=
        le_of_lt hvReal
      _ ≤ approximationSingularValue n ((K + L) ∘L V.subtypeL) + (δ : ℝ) :=
        add_le_add_left hmono (δ : ℝ)
      _ = approximationSingularValue n (KV + LV) + (δ : ℝ) := by
        rw [hsumRestrict]
  have hlocal : kyFanApproximationGauge k (K + L) ≤
      kyFanApproximationGauge k (KV + LV) + ε := by
    unfold kyFanApproximationGauge
    calc
      ∑ n ∈ Finset.range k, approximationSingularValue n (K + L)
          ≤ ∑ n ∈ Finset.range k,
              (approximationSingularValue n (KV + LV) + (δ : ℝ)) :=
        Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.range k, approximationSingularValue n (KV + LV)) +
          (k : ℝ) * (δ : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [nsmul_eq_mul]
      _ = (∑ n ∈ Finset.range k, approximationSingularValue n (KV + LV)) + ε := by
        change _ + (k : ℝ) * δr = _ + ε
        rw [mul_div_cancel₀ ε hkreal.ne']
  have htri := kyFanApproximationGauge_add_le_finiteSource_real k KV LV
  have hKrestrict : kyFanApproximationGauge k KV ≤ kyFanApproximationGauge k K := by
    unfold kyFanApproximationGauge
    apply Finset.sum_le_sum
    intro n _
    change ((K ∘L V.subtypeL).approximationNumber n : ℝ) ≤
      (K.approximationNumber n : ℝ)
    exact_mod_cast approximationNumber_comp_subtypeL_le_real K n V
  have hLrestrict : kyFanApproximationGauge k LV ≤ kyFanApproximationGauge k L := by
    unfold kyFanApproximationGauge
    apply Finset.sum_le_sum
    intro n _
    change ((L ∘L V.subtypeL).approximationNumber n : ℝ) ≤
      (L.approximationNumber n : ℝ)
    exact_mod_cast approximationNumber_comp_subtypeL_le_real L n V
  calc
    kyFanApproximationGauge k (K + L)
        ≤ kyFanApproximationGauge k (KV + LV) + ε := hlocal
    _ ≤ (kyFanApproximationGauge k KV + kyFanApproximationGauge k LV) + ε :=
      add_le_add_left htri ε
    _ ≤ (kyFanApproximationGauge k K + kyFanApproximationGauge k L) + ε :=
      add_le_add_left (add_le_add hKrestrict hLrestrict) ε

end

end ApproximationNumbersReal
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
