/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.Scratch.IdealBanach.Basic
import DavisKahan.Experimental.MathAhead.HiddenFoundations.HilbertSchmidtComplexFamily
import DavisKahan.Experimental.Scratch.RectangularHilbertSchmidt.RealDescent

/-!
# Bochner integration in the rectangular Hilbert--Schmidt norm

The generic ideal Banach-space construction immediately turns both completed
Hilbert--Schmidt families into Banach spaces.  Consequently, an integrable
Hilbert--Schmidt-valued field has a Hilbert--Schmidt integral, with the sharp
Minkowski bound on its square norm.

This is the integration layer needed to upgrade operator-norm Sylvester
integrals to Hilbert--Schmidt estimates once continuity or strong measurability
of the lifted orbit has been established.
-/

namespace ForMathlib
namespace DavisKahan
namespace Experimental
namespace ExactSinTheta
namespace Scratch
namespace RectangularHilbertSchmidt

open scoped InnerProductSpace
open MeasureTheory
open IdealBanach IdealBanach.IdealOperator
open HiddenFoundations

noncomputable section

universe v

/-- Complex rectangular Hilbert--Schmidt operators as a Banach space. -/
abbrev ComplexOperator
    (E F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] :=
  IdealOperator (E := E) (F := F) hilbertSchmidtComplex

/-- Real rectangular Hilbert--Schmidt operators as a Banach space. -/
abbrev RealOperator
    (E F : Type v)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :=
  IdealOperator (E := E) (F := F) hilbertSchmidtReal

section Complex

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

@[simp] theorem complex_norm_def (A : ComplexOperator E F) :
    ‖A‖ = paperHilbertSchmidtNorm A.toOp := rfl

@[simp] theorem hilbertSchmidtComplex_gauge_eq (A : E →L[ℂ] F) :
    hilbertSchmidtComplex.gauge A = paperHilbertSchmidtNorm A := rfl

/-- A complex Hilbert--Schmidt-valued Bochner integral remains
Hilbert--Schmidt. -/
theorem complex_integral_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ComplexOperator E F)
    (hf : Integrable f μ) :
    IsPaperHilbertSchmidt (∫ a, (f a).toOp ∂μ) := by
  exact mem_integral_toOp hilbertSchmidtComplex f hf

/-- Sharp square-norm estimate for a complex Hilbert--Schmidt-valued integral. -/
theorem complex_norm_integral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ComplexOperator E F)
    (hf : Integrable f μ) :
    paperHilbertSchmidtNorm (∫ a, (f a).toOp ∂μ) ≤
      ∫ a, paperHilbertSchmidtNorm (f a).toOp ∂μ := by
  have h := gauge_integral_toOp_le hilbertSchmidtComplex f hf
  simpa only [hilbertSchmidtComplex_gauge_eq, norm_def] using h

/-- Raw-field form of the complex integration theorem. -/
theorem complex_integral_mem_of_lift
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → E →L[ℂ] F)
    (hmem : ∀ a, IsPaperHilbertSchmidt (f a))
    (hlift : Integrable
      (fun a => ofMem hilbertSchmidtComplex (f a) (hmem a)) μ) :
    IsPaperHilbertSchmidt (∫ a, f a ∂μ) := by
  exact mem_integral_of_integrable_lift hilbertSchmidtComplex f hmem hlift

/-- Raw-field square-norm estimate in the complex case. -/
theorem complex_norm_integral_of_lift_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → E →L[ℂ] F)
    (hmem : ∀ a, IsPaperHilbertSchmidt (f a))
    (hlift : Integrable
      (fun a => ofMem hilbertSchmidtComplex (f a) (hmem a)) μ) :
    paperHilbertSchmidtNorm (∫ a, f a ∂μ) ≤
      ∫ a, paperHilbertSchmidtNorm (f a) ∂μ := by
  exact gauge_integral_of_integrable_lift_le
    hilbertSchmidtComplex f hmem hlift

end Complex

section Real

variable {E F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

@[simp] theorem real_norm_def (A : RealOperator E F) :
    ‖A‖ = paperHilbertSchmidtNorm A.toOp := rfl

@[simp] theorem hilbertSchmidtReal_gauge_eq (A : E →L[ℝ] F) :
    hilbertSchmidtReal.gauge A = paperHilbertSchmidtNorm A := rfl

/-- A real Hilbert--Schmidt-valued Bochner integral remains
Hilbert--Schmidt. -/
theorem real_integral_mem
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → RealOperator E F)
    (hf : Integrable f μ) :
    IsPaperHilbertSchmidt (∫ a, (f a).toOp ∂μ) := by
  exact mem_integral_toOp hilbertSchmidtReal f hf

/-- Sharp square-norm estimate for a real Hilbert--Schmidt-valued integral. -/
theorem real_norm_integral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → RealOperator E F)
    (hf : Integrable f μ) :
    paperHilbertSchmidtNorm (∫ a, (f a).toOp ∂μ) ≤
      ∫ a, paperHilbertSchmidtNorm (f a).toOp ∂μ := by
  have h := gauge_integral_toOp_le hilbertSchmidtReal f hf
  simpa only [hilbertSchmidtReal_gauge_eq, norm_def] using h

/-- Raw-field form of the real integration theorem. -/
theorem real_integral_mem_of_lift
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → E →L[ℝ] F)
    (hmem : ∀ a, IsPaperHilbertSchmidt (f a))
    (hlift : Integrable
      (fun a => ofMem hilbertSchmidtReal (f a) (hmem a)) μ) :
    IsPaperHilbertSchmidt (∫ a, f a ∂μ) := by
  exact mem_integral_of_integrable_lift hilbertSchmidtReal f hmem hlift

/-- Raw-field square-norm estimate in the real case. -/
theorem real_norm_integral_of_lift_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → E →L[ℝ] F)
    (hmem : ∀ a, IsPaperHilbertSchmidt (f a))
    (hlift : Integrable
      (fun a => ofMem hilbertSchmidtReal (f a) (hmem a)) μ) :
    paperHilbertSchmidtNorm (∫ a, f a ∂μ) ≤
      ∫ a, paperHilbertSchmidtNorm (f a) ∂μ := by
  exact gauge_integral_of_integrable_lift_le
    hilbertSchmidtReal f hmem hlift

end Real

end

end RectangularHilbertSchmidt
end Scratch
end ExactSinTheta
end Experimental
end DavisKahan
end ForMathlib
