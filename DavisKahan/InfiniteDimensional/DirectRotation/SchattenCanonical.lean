/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.Geometry.Polar.DisplacementSquareExtremal
public import ForTauCeti.Analysis.OperatorIdeal.Family.SchattenGram
public import ForTauCeti.Analysis.InnerProductSpace.Projection.UnitaryTransport

/-!
# Canonical Schatten transport optimality for finite exponents at least two

The squared-displacement Ky Fan theorem and the accepted Schatten Gram
identity prove that every completed direct rotation minimizes the actual
Schatten gauge against every complex ambient unitary transporter.
No compactness, dimension, separability or finite-cost hypothesis is
needed. This is the classical Q-norm regime, not a new priority claim.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Canonical optimality for `p>=2` in arbitrary complex Hilbert
dimension.** Every completed direct rotation minimizes displacement in
the accepted Schatten family. Infinite values and right-angle defects
are included, and no block hypothesis is placed on the competitor. -/
theorem schatten_nonacuteDirectRotation_le_transport
    (p : ℝ) (hp : 2 ≤ p)
    (K L : Submodule ℂ H) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (J : halmosSourceDefect K L ≃ₗᵢ[ℂ] halmosTargetDefect K L)
    (U : H ≃ₗᵢ[ℂ] H) (hmap : K.map U.toLinearMap = L) :
    (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge (1 - nonacuteDirectRotation K L J) ≤
      (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge (1 - (U : H →L[ℂ] H)) := by
  let R := nonacuteDirectRotation K L J
  have hinter : (U : H →L[ℂ] H) * K.starProjection = L.starProjection * (U : H →L[ℂ] H) := by
    ext x
    change U (K.starProjection x) = L.starProjection (U x)
    have h := Submodule.starProjection_map_apply U K (U x)
    simpa only [hmap, U.symm_apply_apply] using h.symm
  have hgram (T : H →L[ℂ] H) :
      (1 - T).adjoint ∘L (1 - T) = (1 - star T) * (1 - T) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, star_sub, star_one]
    rfl
  have hky (k : ℕ) : ((1 - R).adjoint ∘L (1 - R)).kyFanGauge k ≤
      ((1 - (U : H →L[ℂ] H)).adjoint ∘L (1 - (U : H →L[ℂ] H))).kyFanGauge k := by
    have h := Section4.proposition4_3_nonacute_squaredDisplacement_kyFan K L J
      (U : H →L[ℂ] H) (Unitary.linearIsometryEquiv.symm U).property hinter k
    rw [hgram, hgram]
    apply NNReal.coe_le_coe.mp
    exact h
  have hdom :
      (OperatorIdealFamily.schatten ℂ (p / 2) (by linarith)).gauge
          ((1 - R).adjoint ∘L (1 - R)) ≤
        (OperatorIdealFamily.schatten ℂ (p / 2) (by linarith)).gauge
          ((1 - (U : H →L[ℂ] H)).adjoint ∘L (1 - (U : H →L[ℂ] H))) := by
    simpa only [OperatorIdealFamily.schatten_def, SymmetricGauge.operatorIdealFamily_gauge] using
      (SymmetricGauge.lpGauge (p / 2) (by linarith)).opGauge_le_of_forall_kyFanGauge_le hky
  rw [OperatorIdealFamily.gauge_schatten_gram_eq_sq p hp,
    OperatorIdealFamily.gauge_schatten_gram_eq_sq p hp] at hdom
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp hdom

end TauCeti.DavisKahan.InfiniteDimensional
