/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import DavisKahan.Experimental.InfiniteDimensional.Sylvester.Basic
import DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bochner integration for finite Ky Fan approximation gauges

A positive finite Ky Fan gauge is a genuine norm on the rectangular operator
space.  This file packages the gauge as a continuous seminorm and records its
Bochner integral inequality.  Applying that inequality to the Fourier
Sylvester reconstruction upgrades the operator-norm estimate to simultaneous
finite-Ky-Fan majorization.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace Experimental
namespace MathAhead
namespace HiddenFoundations

open DavisKahanExt
open ExactSinTheta
open MeasureTheory

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
-- Source and target share a universe: `kyFanApproximationGauge_add_le` needs
-- `ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`, whose instance for `ℂ` quantifies over
-- one space universe.  With `E : Type u` and `F : Type v` the instance never applies and the
-- search for it is what times out below rather than failing outright.
variable {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F]

/-- The finite Ky Fan approximation gauge as a continuous seminorm. -/
noncomputable def kyFanApproximationSeminorm (k : ℕ) :
    Seminorm ℂ (E →L[ℂ] F) where
  toFun := kyFanApproximationGauge k
  map_zero' := kyFanApproximationGauge_zero_map k
  add_le' := fun S T => kyFanApproximationGauge_add_le k S T
  neg' := fun T => kyFanApproximationGauge_neg k T
  smul' := fun c T => kyFanApproximationGauge_smul k c T

@[simp]
theorem kyFanApproximationSeminorm_apply (k : ℕ) (T : E →L[ℂ] F) :
    kyFanApproximationSeminorm k T = kyFanApproximationGauge k T := rfl

/-- A finite Ky Fan gauge is operator-norm continuous. -/
theorem continuous_kyFanApproximationGauge (k : ℕ) :
    Continuous (kyFanApproximationGauge k : (E →L[ℂ] F) → ℝ) := by
  exact (kyFanApproximationSeminorm (E := E) (F := F) k).continuous

/-- Minkowski's inequality for a finite Ky Fan gauge and a Bochner integral. -/
theorem kyFanApproximationGauge_integral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (k : ℕ) {f : α → E →L[ℂ] F} (hf : Integrable f μ) :
    kyFanApproximationGauge k (∫ a, f a ∂μ) ≤
      ∫ a, kyFanApproximationGauge k (f a) ∂μ := by
  simpa [kyFanApproximationSeminorm] using
    (kyFanApproximationSeminorm (E := E) (F := F) k).integral_le hf

/-- Left and right multiplication by unitary operators preserves every finite
Ky Fan approximation gauge. -/
theorem kyFanApproximationGauge_unitary_left_right
    (k : ℕ) (L : F →L[ℂ] F) (R : E →L[ℂ] E)
    (hL : L† ∘L L = 1) (hLL : L ∘L L† = 1)
    (hR : R† ∘L R = 1) (hRR : R ∘L R† = 1)
    (T : E →L[ℂ] F) :
    kyFanApproximationGauge k (L ∘L T ∘L R) =
      kyFanApproximationGauge k T := by
  apply le_antisymm
  · calc
      kyFanApproximationGauge k (L ∘L T ∘L R)
          ≤ ‖L‖ * kyFanApproximationGauge k T * ‖R‖ :=
        kyFanApproximationGauge_comp_le k L T R
      _ = kyFanApproximationGauge k T := by
        have hLn : ‖L‖ = 1 := norm_eq_one_of_isometry_and_surjective hL hLL
        have hRn : ‖R‖ = 1 := norm_eq_one_of_isometry_and_surjective hR hRR
        rw [hLn, hRn, one_mul, mul_one]
  · have hrecover : T = L† ∘L (L ∘L T ∘L R) ∘L R† := by
      ext x
      simp only [ContinuousLinearMap.comp_apply]
      have h1 := DFunLike.congr_fun hRR x
      have h2 := DFunLike.congr_fun hL (T x)
      simp only [ContinuousLinearMap.comp_apply, one_apply_eq_self] at h1 h2
      rw [h1, h2]
    rw [hrecover]
    calc
      kyFanApproximationGauge k
          (L† ∘L (L ∘L T ∘L R) ∘L R†)
          ≤ ‖L†‖ * kyFanApproximationGauge k (L ∘L T ∘L R) * ‖R†‖ :=
        kyFanApproximationGauge_comp_le k L† (L ∘L T ∘L R) R†
      _ = kyFanApproximationGauge k (L ∘L T ∘L R) := by
        have hLn : ‖L†‖ = 1 := by
          rw [ContinuousLinearMap.norm_adjoint]
          exact norm_eq_one_of_isometry_and_surjective hL hLL
        have hRn : ‖R†‖ = 1 := by
          rw [ContinuousLinearMap.norm_adjoint]
          exact norm_eq_one_of_isometry_and_surjective hR hRR
        rw [hLn, hRn, one_mul, mul_one]

/-- The unitary orbit in the Fourier inverse preserves each finite Ky Fan
gauge. -/
theorem kyFanApproximationGauge_unitaryGroup_orbit
    (k : ℕ) (A : F →L[ℂ] F) (B : E →L[ℂ] E)
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    (t : ℝ) (C : E →L[ℂ] F) :
    kyFanApproximationGauge k
        (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)) =
      kyFanApproximationGauge k C := by
  apply kyFanApproximationGauge_unitary_left_right
  · simpa [unitaryGroup_adjoint hA] using unitaryGroup_mul_neg A t
  · simpa [unitaryGroup_adjoint hA] using unitaryGroup_neg_mul A t
  · simpa [unitaryGroup_adjoint hB] using unitaryGroup_mul_neg B (-t)
  · simpa [unitaryGroup_adjoint hB] using unitaryGroup_neg_mul B (-t)

/-- The complex separated Sylvester theorem in every finite Ky Fan gauge. -/
theorem complex_separated_sylvester_kyFan
    {A : F →L[ℂ] F} {B : E →L[ℂ] E} {X C : E →L[ℂ] F}
    (hA : IsSelfAdjointOperator A) (hB : IsSelfAdjointOperator B)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : sylvesterOperator A B X = C) (k : ℕ) :
    d * kyFanApproximationGauge k X ≤
      (Real.pi / 2) * kyFanApproximationGauge k C := by
  rw [separatedSylvester_reconstruction hA hB hd hsep X C hEq]
  unfold separatedSylvesterSolution
  have hint := separatedSylvester_integrable hA hB hd C
  calc
    d * kyFanApproximationGauge k
        (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
          (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)))
        ≤ d * ∫ t : ℝ,
          kyFanApproximationGauge k
            (separatedSylvesterMultiplier d hd t •
              (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))) := by
      gcongr
      exact kyFanApproximationGauge_integral_le k hint
    _ = d * ∫ t : ℝ,
          ‖separatedSylvesterMultiplier d hd t‖ *
            kyFanApproximationGauge k C := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [kyFanApproximationGauge_smul,
        kyFanApproximationGauge_unitaryGroup_orbit k A B hA hB]
    _ = d * ((∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖) *
          kyFanApproximationGauge k C) := by
      rw [integral_mul_const]
    _ = (Real.pi / 2) * kyFanApproximationGauge k C := by
      rw [l1_norm_separatedSylvesterMultiplier d hd]
      field_simp [ne_of_gt hd]

end

end HiddenFoundations
end MathAhead
end Experimental
end DavisKahan
end TauCeti