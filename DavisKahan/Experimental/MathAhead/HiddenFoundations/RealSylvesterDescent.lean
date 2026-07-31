/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Basic
import DavisKahan.Experimental.MathAhead.HiddenFoundations.KyFanBochner
import DavisKahan.Experimental.InfiniteDimensional.Sylvester.OrderedSemigroup
import DavisKahan.OperatorIdeal.ComplexificationApproximation
import DavisKahan.SpectralTheory.Complexification.FunctionalCalculus

/-!
# Real descent for the separated bounded Sylvester theorem

The Fourier representation itself is intrinsically complex.  The real theorem
is obtained by complexifying the real Sylvester equation, applying the complex
finite-Ky-Fan estimates, and descending through exact preservation of every
approximation number.

The only genuinely spectral bridge is proved separately below: a real scalar
belongs to the spectrum of a bounded real operator exactly when its complex
image belongs to the spectrum of the coordinatewise complexification.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open DavisKahanExt
open ExactSinTheta
open ExactSinTheta.ComplexificationApproximation
open ExactSinTheta.RealComplexificationFunctionalCalculus
open RealComplexification

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F]

/-- Complexification commutes with the bounded Sylvester operator. -/
theorem complexify_sylvesterOperator
    (A : F →L[ℝ] F) (B : E →L[ℝ] E) (X : E →L[ℝ] F) :
    complexify (sylvesterOperator A B X) =
      sylvesterOperator (complexify A) (complexify B) (complexify X) := by
  simp [sylvesterOperator, complexify_comp, complexify_sub]

/-- A bounded real Sylvester equation complexifies exactly. -/
theorem complexify_sylvesterEquation
    {A : F →L[ℝ] F} {B : E →L[ℝ] E} {X C : E →L[ℝ] F}
    (hEq : sylvesterOperator A B X = C) :
    sylvesterOperator (complexify A) (complexify B) (complexify X) =
      complexify C := by
  rw [← complexify_sylvesterOperator, hEq]

/-- A bounded real self-adjoint operator remains self-adjoint after
complexification. -/
theorem isSelfAdjointOperator_complexify
    {A : E →L[ℝ] E} (hA : IsSelfAdjointOperator A) :
    IsSelfAdjointOperator (complexify A) := by
  exact (complexify_isSymmetric_iff A).2 hA

/-- A real inverse complexifies to an inverse of the complexified operator. -/
theorem isUnit_complexify_of_isUnit
    (T : E →L[ℝ] E) (hT : IsUnit T) : IsUnit (complexify T) := by
  rcases hT with ⟨u, rfl⟩
  let uc : (RealComplexification E →L[ℂ] RealComplexification E)ˣ :=
    { val := complexify (u : E →L[ℝ] E)
      inv := complexify (↑(u⁻¹) : E →L[ℝ] E)
      val_inv := by
        rw [← complexify_comp]
        simpa [ContinuousLinearMap.mul_def] using congrArg complexify u.val_inv
      inv_val := by
        rw [← complexify_comp]
        simpa [ContinuousLinearMap.mul_def] using congrArg complexify u.inv_val }
  exact ⟨uc, rfl⟩

/-- An inverse of a complexified real operator descends by restricting it to
the fixed real copy and taking real coordinates. -/
theorem isUnit_of_isUnit_complexify
    (T : E →L[ℝ] E) (hT : IsUnit (complexify T)) : IsUnit T := by
  rcases hT with ⟨u, hu⟩
  let R : RealComplexification E →L[ℂ] RealComplexification E :=
    (↑(u⁻¹) : RealComplexification E →L[ℂ] RealComplexification E)
  let RrLinear : E →ₗ[ℝ] E :=
    { toFun := fun x => re (R (ofReal x))
      map_add' := fun x y => by simp
      map_smul' := fun r x => by simp }
  let Rr : E →L[ℝ] E :=
    RrLinear.mkContinuous ‖R‖ (fun x => by
      calc
        ‖RrLinear x‖ ≤ ‖R (ofReal x)‖ :=
          TauCeti.DavisKahan.Experimental.Foundation.RealComplexification.norm_re_le _
        _ ≤ ‖R‖ * ‖ofReal x‖ := R.le_opNorm _
        _ = ‖R‖ * ‖x‖ := by rw [ofReal.norm_map])
  have hleftC : complexify T ∘L R = 1 := by
    have hv := u.val_inv
    rw [← hu] at hv
    simpa [R, ContinuousLinearMap.mul_def] using hv
  have hrightC : R ∘L complexify T = 1 := by
    have hv := u.inv_val
    rw [← hu] at hv
    simpa [R, ContinuousLinearMap.mul_def] using hv
  have hleft : T ∘L Rr = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := DFunLike.congr_fun hleftC (ofReal x)
    apply ofReal_injective
    simpa [Rr, RrLinear, complexify_comp] using congrArg re hx
  have hright : Rr ∘L T = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    have hx := DFunLike.congr_fun hrightC (ofReal x)
    apply ofReal_injective
    simpa [Rr, RrLinear, complexify_comp] using congrArg re hx
  exact ⟨
    { val := T
      inv := Rr
      val_inv := by simpa [ContinuousLinearMap.mul_def] using hleft
      inv_val := by simpa [ContinuousLinearMap.mul_def] using hright }, rfl⟩

/-- Invertibility of bounded real operators is exactly preserved by coordinate
complexification. -/
theorem isUnit_complexify_iff (T : E →L[ℝ] E) :
    IsUnit (complexify T) ↔ IsUnit T :=
  ⟨isUnit_of_isUnit_complexify T, isUnit_complexify_of_isUnit T⟩

/-- The real Banach-algebra spectrum of a bounded self-adjoint real operator is
exactly the real trace of the complex spectrum of its complexification. -/
theorem realSpectrum_complexify_bounded (A : E →L[ℝ] E) :
    realSpectrum (complexify A) = realSpectrum A := by
  ext lam
  change (lam : ℂ) ∈ spectrum ℂ (complexify A) ↔
    lam ∈ spectrum ℝ A
  rw [spectrum.mem_iff, spectrum.mem_iff]
  have hshift :
      (algebraMap ℂ (RealComplexification E →L[ℂ] RealComplexification E)
          (lam : ℂ) - complexify A) =
        complexify
          (algebraMap ℝ (E →L[ℝ] E) lam - A) := by
    apply ContinuousLinearMap.ext
    intro z
    apply RealComplexification.ext <;> simp
  rw [hshift, isUnit_complexify_iff]

/-- Full-space separated spectra are preserved by bounded real
complexification. -/
theorem spectraSeparated_top_complexify
    {A : F →L[ℝ] F} {B : E →L[ℝ] E} {d : ℝ}
    (hsep : SpectraSeparated A ⊤ B ⊤ d) :
    SpectraSeparated (complexify A) ⊤ (complexify B) ⊤ d := by
  refine ⟨by intro x hx; trivial, by intro x hx; trivial, ?_⟩
  intro a ha b hb
  have haR : a ∈ realSpectrum A := by
    rw [restrictedSpectrum_top_eq_realSpectrum] at ha
    rw [realSpectrum_complexify_bounded] at ha
    exact ha
  have hbR : b ∈ realSpectrum B := by
    rw [restrictedSpectrum_top_eq_realSpectrum] at hb
    rw [realSpectrum_complexify_bounded] at hb
    exact hb
  apply hsep.2.2 a
  · rw [restrictedSpectrum_top_eq_realSpectrum]
    exact haR
  · rw [restrictedSpectrum_top_eq_realSpectrum]
    exact hbR

/-- Every finite Ky Fan approximation gauge satisfies the real `pi/2`
Sylvester estimate. -/
theorem real_bounded_separated_sylvester_kyFan
    {A : F →L[ℝ] F} {B : E →L[ℝ] E} {X C : E →L[ℝ] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) (k : ℕ) :
    d * kyFanApproximationGauge k X ≤
      (Real.pi / 2) * kyFanApproximationGauge k C := by
  by_cases hk : k = 0
  · subst k
    simp [kyFanApproximationGauge, ContinuousLinearMap.kyFanGauge]
  · let N := KyFanDominantIdealFamily.kyFan (𝕜 := ℂ) k
      (Nat.pos_of_ne_zero hk)
    have hfan := complex_separated_sylvester_kyFan
      (isSelfAdjointOperator_complexify hA)
      (isSelfAdjointOperator_complexify hB) hd
      (spectraSeparated_top_complexify hsep)
      (complexify_sylvesterEquation hEq) k
    change d * kyFanApproximationGauge k (complexify X) ≤
      (Real.pi / 2) * kyFanApproximationGauge k (complexify C) at hfan
    simpa only [kyFanApproximationGauge_complexify] using hfan

/-- Real arbitrary-ideal `pi/2` estimate, reconstructed from all finite Ky Fan
bounds. -/
theorem real_bounded_separated_sylvester
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    {A : F →L[ℝ] F} {B : E →L[ℝ] E} {X C : E →L[ℝ] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C)
    (hC : N.Mem C) :
    N.Mem X ∧
      d * N.gauge X ≤
        (Real.pi / 2) * N.gauge C := by
  let c : ℝ := Real.pi / 2
  have hc : 0 < c := by
    dsimp [c]
    positivity
  let Cscaled : E →L[ℝ] F := c • C
  have hCscaled : N.Mem Cscaled :=
    N.toRectangularSymmetricIdealFamily.smul_mem c hC
  have hfan : ∀ k, d * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k Cscaled := by
    intro k
    rw [kyFanApproximationGauge_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact real_bounded_separated_sylvester_kyFan hA hB hd hsep hEq k
  obtain ⟨hX, hg⟩ :=
    mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N hd hCscaled hfan
  refine ⟨hX, ?_⟩
  have hhom := N.gauge_smul c hC
  rw [Real.norm_eq_abs, abs_of_pos hc] at hhom
  simpa [Cscaled, c, hhom] using hg

end

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti