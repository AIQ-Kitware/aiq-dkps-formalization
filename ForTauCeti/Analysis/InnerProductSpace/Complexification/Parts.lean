/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import ForTauCeti.Analysis.InnerProductSpace.Complexification.Basic

/-!
# Real and imaginary parts of complexified operators

The existing real-part operator and its imaginary counterpart decompose
every complex-linear operator on concrete real complexifications. The
coordinate formulas also give the real and imaginary components of an
operator product. No finite-dimensionality is used.
-/

public section

noncomputable section

namespace TauCeti.RealComplexification

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The imaginary component of a complex-linear operator, expressed
through the established real-part operator. -/
@[expose]
def imaginaryPartOperator (T : RealComplexification E →L[ℂ] RealComplexification F) :
    E →L[ℝ] F := realPartOperator (-Complex.I • T)

/-- Evaluate the imaginary operator on the real copy. -/
@[simp]
theorem imaginaryPartOperator_apply
    (T : RealComplexification E →L[ℂ] RealComplexification F) (x : E) :
    imaginaryPartOperator T x = im (T (ofReal x)) := by
  simp [imaginaryPartOperator, realPartOperator_apply]

/-- The real coordinate of an arbitrary operator value. -/
theorem re_apply_eq_parts (T : RealComplexification E →L[ℂ] RealComplexification F)
    (z : RealComplexification E) :
    re (T z) = realPartOperator T (re z) - imaginaryPartOperator T (im z) := by
  have h : T z = T (ofReal (re z)) + Complex.I • T (ofReal (im z)) := by
    conv_lhs => rw [eq_ofReal_add_I_smul_ofReal z]
    rw [map_add, map_smul]
  rw [h]
  simp [sub_eq_add_neg]

/-- The imaginary coordinate of an arbitrary operator value. -/
theorem im_apply_eq_parts (T : RealComplexification E →L[ℂ] RealComplexification F)
    (z : RealComplexification E) :
    im (T z) = imaginaryPartOperator T (re z) + realPartOperator T (im z) := by
  have h : T z = T (ofReal (re z)) + Complex.I • T (ofReal (im z)) := by
    conv_lhs => rw [eq_ofReal_add_I_smul_ofReal z]
    rw [map_add, map_smul]
  rw [h]
  simp

/-- Every complex-linear operator is the complexification of its real
component plus `i` times the complexification of its imaginary component. -/
theorem eq_complexify_real_add_I_imag
    (T : RealComplexification E →L[ℂ] RealComplexification F) :
    T = complexify (realPartOperator T) + Complex.I • complexify (imaginaryPartOperator T) := by
  apply ContinuousLinearMap.ext
  intro z
  apply RealComplexification.ext
  · simpa [sub_eq_add_neg] using re_apply_eq_parts T z
  · simpa [add_comm] using im_apply_eq_parts T z

/-- Real components of an operator product obey the usual complex product
identity, with operator composition in the stated order. -/
theorem realPartOperator_comp
    (T : RealComplexification E →L[ℂ] RealComplexification F)
    (S : RealComplexification F →L[ℂ] RealComplexification G) :
    realPartOperator (S ∘L T) =
      realPartOperator S ∘L realPartOperator T -
        imaginaryPartOperator S ∘L imaginaryPartOperator T := by
  ext x
  simpa only [realPartOperator_apply, imaginaryPartOperator_apply,
    ContinuousLinearMap.comp_apply, sub_apply] using
      re_apply_eq_parts S (T (ofReal x))

/-- Imaginary components of an operator product obey the usual complex
product identity, including noncommuting operator factors. -/
theorem imaginaryPartOperator_comp
    (T : RealComplexification E →L[ℂ] RealComplexification F)
    (S : RealComplexification F →L[ℂ] RealComplexification G) :
    imaginaryPartOperator (S ∘L T) =
      imaginaryPartOperator S ∘L realPartOperator T +
        realPartOperator S ∘L imaginaryPartOperator T := by
  ext x
  simpa only [realPartOperator_apply, imaginaryPartOperator_apply,
    ContinuousLinearMap.comp_apply, add_apply] using
      im_apply_eq_parts S (T (ofReal x))

end TauCeti.RealComplexification
