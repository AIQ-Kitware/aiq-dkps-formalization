/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import DavisKahan.SinTheta.FrameFactorizationGeneric
public import ForTauCeti.Analysis.InnerProductSpace.Complexification.FunctionalCalculus
public import ForTauCeti.Analysis.InnerProductSpace.CoerciveUnit
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

public section

open TauCeti.DavisKahan.Sylvester

/-!
# Real infinite-dimensional lower-frame polar factorization

The real trial map uses the same native modulus and polar factor construction
as the complex one. The complexification lemmas below concern lower bounds and
functional-calculus descent independently of the polar package.

-/

namespace TauCeti

open TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace
open TauCeti.RealComplexification
open RealComplexification

noncomputable section

universe v

variable {E F G : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-! The real algebra structure and the real continuous functional calculus on the
complexified operator algebra are `scoped instance`s of
`RealComplexification`, opened below.  They used to be reinstalled
here as a second `local instance`, which made them a *different declaration* from the
one the imported lemmas are stated against; see lane `{lane:CPLX-DEDUP-3}`. -/
open scoped TauCeti.RealComplexification

omit [CompleteSpace E] [CompleteSpace F] in
/-- A positive real lower-frame estimate survives coordinatewise
complexification with the same constant. -/
theorem lowerFrameBound_complexify
    (X : F →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 ≤ ε) :
    LowerFrameBound (complexify X) ε := by
  intro z
  have hre := hX (re z)
  have him := hX (im z)
  have hre0 : 0 ≤ ε * ‖re z‖ := mul_nonneg hε (norm_nonneg _)
  have him0 : 0 ≤ ε * ‖im z‖ := mul_nonneg hε (norm_nonneg _)
  have hreSq : (ε * ‖re z‖) ^ 2 ≤ ‖X (re z)‖ ^ 2 :=
    (sq_le_sq₀ hre0 (norm_nonneg _)).2 hre
  have himSq : (ε * ‖im z‖) ^ 2 ≤ ‖X (im z)‖ ^ 2 :=
    (sq_le_sq₀ him0 (norm_nonneg _)).2 him
  have hsq : (ε * ‖z‖) ^ 2 ≤ ‖complexify X z‖ ^ 2 := by
    rw [mul_pow, norm_sq, norm_sq]
    simp only [re_complexify, im_complexify]
    nlinarith
  exact (sq_le_sq₀
    (mul_nonneg hε (norm_nonneg z)) (norm_nonneg (complexify X z))).1 hsq

/-- The complex Gram operator of a complexified real map is fixed by canonical
conjugation. -/
theorem conjugateOperator_complexify_gram
    (X : F →L[ℝ] E) :
    conjugateOperator ((complexify X).adjoint ∘L complexify X) =
      (complexify X).adjoint ∘L complexify X := by
  rw [← complexify_gram]
  exact conjugateOperator_complexify (X.adjoint ∘L X)

/-- Real continuous functional calculus descent for a positive real power of a
complexified positive operator. -/
theorem conjugateOperator_rpow_eq
    (C : RealComplexification F →L[ℂ] RealComplexification F)
    (hC : 0 ≤ C) (hunit : IsUnit C)
    (hfix : conjugateOperator C = C) (r : ℝ) :
    conjugateOperator (C ^ r) = C ^ r := by
  rw [CFC.rpow_eq_cfc_real hC]
  refine conjugateOperator_cfc_eq C hC.isSelfAdjoint hfix
    (fun x : ℝ => x ^ r) ?_
  refine continuousOn_id.rpow_const fun x hx => Or.inl ?_
  intro hx0
  rw [id_eq] at hx0
  subst hx0
  exact (spectrum.zero_notMem ℝ hunit) hx

/-- Existence of the real lower-frame polar package. -/
theorem lowerFramePolarData_real_nonempty
    (X : F →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    Nonempty (LowerFramePolarData X ε hX hε) :=
  ⟨lowerFramePolarData X hX hε⟩

/-- The real lower-frame polar package. -/
@[expose]
noncomputable def lowerFramePolarDataReal
    (X : F →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) :
    LowerFramePolarData X ε hX hε :=
  lowerFramePolarData X hX hε

/-- The selected real normalized frame isometry. -/
noncomputable def frameIsometryReal
    (X : F →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : F →L[ℝ] E :=
  frameIsometryOfPolarData (lowerFramePolarDataReal X hX hε)

/-- The selected real generalized complementary sine block. -/
@[expose]
noncomputable def sinThetaBlockReal
    (X : F →L[ℝ] E) (F₁ : G →L[ℝ] E) {ε : ℝ}
    (hX : LowerFrameBound X ε) (hε : 0 < ε) : G →L[ℝ] F :=
  sinThetaBlockOfPolarData (lowerFramePolarDataReal X hX hε) F₁

end

end ExactSinTheta
end DavisKahan
end TauCeti