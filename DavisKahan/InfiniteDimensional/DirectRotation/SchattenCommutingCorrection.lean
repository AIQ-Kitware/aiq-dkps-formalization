/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6 (Codex; configuration unspecified)
-/
module

public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenCanonical
public import DavisKahan.InfiniteDimensional.DirectRotation.SchattenFeasibility
public import DavisKahan.Geometry.Polar.CommutingCorrection

/-!
# Exact ideal correction to a projection-commuting unitary

A unitary admits a Schatten-small correction commuting with a prescribed
projection exactly when its commutator is Schatten and the image/source
crossed defects are balanced. For complex Hilbert spaces and `p >= 2`,
the nearest commuting unitary is attained. The minimum compares with
all ambient commuting unitaries, not a prescribed block family.

The ideal and index hypotheses are both needed: an arbitrary unitary
image can have compact projection difference with nonzero pair index.
-/

public section

noncomputable section

namespace TauCeti.DavisKahan.InfiniteDimensional

open scoped ENNReal

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **Exact feasibility for Schatten commuting correction.** Finite
commutator cost must be supplemented by the finite pair-index balance.
This holds over both fields for every finite real exponent `p >= 1`. -/
theorem schatten_commuting_correction_iff_commutator_and_defect_balance
    (p : ℝ) (hp : 1 ≤ p) (K : Submodule 𝕜 H) [K.HasOrthogonalProjection]
    (A : H ≃ₗᵢ[𝕜] H) :
    (∃ C : H ≃ₗᵢ[𝕜] H, Commute (C : H →L[𝕜] H) K.starProjection ∧
      (OperatorIdealFamily.schatten 𝕜 p hp).gauge
        ((A : H →L[𝕜] H) - (C : H →L[𝕜] H)) ≠ ∞) ↔
    (OperatorIdealFamily.schatten 𝕜 p hp).gauge
      ((A : H →L[𝕜] H) * K.starProjection - K.starProjection * (A : H →L[𝕜] H)) ≠ ∞ ∧
      Module.finrank 𝕜 (halmosSourceDefect (K.map A.toLinearMap) K) =
        Module.finrank 𝕜 (halmosTargetDefect (K.map A.toLinearMap) K) := by
  let Φ := OperatorIdealFamily.schatten 𝕜 p hp
  rw [← Φ.gauge_projection_image_sub_eq_commutator K A,
    ← schatten_transport_iff_projection_sub_ne_top_and_defect_balance p hp
      (K.map A.toLinearMap) K]
  constructor
  · rintro ⟨C, hcomm, hcost⟩
    refine ⟨A.symm.trans C, ?_, ?_⟩
    · rw [K.map_correction_transport]
      exact (K.map_eq_self_iff_commute_starProjection C).mpr hcomm
    · rwa [Φ.gauge_unitary_sub_eq_displacement A C] at hcost
  · rintro ⟨T, hmap, hcost⟩
    let C := A.trans T
    have hrel : A.symm.trans C = T := by ext x; simp [C]
    refine ⟨C, ?_, ?_⟩
    · apply (K.map_eq_self_iff_commute_starProjection C).mp
      rw [← K.map_correction_transport A C, hrel]
      exact hmap
    · rw [Φ.gauge_unitary_sub_eq_displacement A C, hrel]
      exact hcost

end TauCeti.DavisKahan.InfiniteDimensional

namespace TauCeti.DavisKahan.InfiniteDimensional

open scoped ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Nearest unitary commuting with a prescribed projection.** For
`p >= 2`, a Schatten commutator and balanced finite crossed defects
give an actual finite-cost global nearest commuting unitary, in
arbitrary complex Hilbert dimension. No competitor block restriction
or finite-rank projection-difference assumption is imposed. -/
theorem exists_nearest_schatten_commuting_unitary
    (p : ℝ) (hp : 2 ≤ p) (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (A : H ≃ₗᵢ[ℂ] H)
    (hcomm : (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge
      ((A : H →L[ℂ] H) * K.starProjection - K.starProjection * (A : H →L[ℂ] H)) ≠ ∞)
    (hbalance : Module.finrank ℂ (halmosSourceDefect (K.map A.toLinearMap) K) =
      Module.finrank ℂ (halmosTargetDefect (K.map A.toLinearMap) K)) :
    ∃ C : H ≃ₗᵢ[ℂ] H, Commute (C : H →L[ℂ] H) K.starProjection ∧
      (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge
        ((A : H →L[ℂ] H) - (C : H →L[ℂ] H)) ≠ ∞ ∧
      ∀ V : H ≃ₗᵢ[ℂ] H, Commute (V : H →L[ℂ] H) K.starProjection →
        (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge
            ((A : H →L[ℂ] H) - (C : H →L[ℂ] H)) ≤
          (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge
            ((A : H →L[ℂ] H) - (V : H →L[ℂ] H)) := by
  let Φ := OperatorIdealFamily.schatten ℂ p (by linarith)
  have hD : Φ.gauge ((K.map A.toLinearMap).starProjection - K.starProjection) ≠ ∞ := by
    rwa [Φ.gauge_projection_image_sub_eq_commutator K A]
  obtain ⟨R, hRmap, hRcost, hmin⟩ :=
    exists_unitary_minimizing_schatten_transport_of_projection_sub_ne_top p hp
      (K.map A.toLinearMap) K hD hbalance
  let C := A.trans R
  have hrel : A.symm.trans C = R := by ext x; simp [C]
  refine ⟨C, ?_, ?_, ?_⟩
  · apply (K.map_eq_self_iff_commute_starProjection C).mp
    rw [← K.map_correction_transport A C, hrel]
    exact hRmap
  · rw [Φ.gauge_unitary_sub_eq_displacement A C, hrel]
    exact hRcost
  · intro V hV
    rw [Φ.gauge_unitary_sub_eq_displacement A C,
      Φ.gauge_unitary_sub_eq_displacement A V, hrel]
    apply hmin
    rw [K.map_correction_transport]
    exact (K.map_eq_self_iff_commute_starProjection V).mpr hV

/-- A commutator of operator norm strictly below one removes the
index obstruction. In the canonical Schatten regime this gives a
nearest commuting unitary from commutator hypotheses alone. -/
theorem exists_nearest_schatten_commuting_unitary_of_commutator_norm_lt_one
    (p : ℝ) (hp : 2 ≤ p) (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    (A : H ≃ₗᵢ[ℂ] H)
    (hnorm : ‖(A : H →L[ℂ] H) * K.starProjection -
      K.starProjection * (A : H →L[ℂ] H)‖ < 1)
    (hcomm : (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge
      ((A : H →L[ℂ] H) * K.starProjection - K.starProjection * (A : H →L[ℂ] H)) ≠ ∞) :
    ∃ C : H ≃ₗᵢ[ℂ] H, Commute (C : H →L[ℂ] H) K.starProjection ∧
      (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge
        ((A : H →L[ℂ] H) - (C : H →L[ℂ] H)) ≠ ∞ ∧
      ∀ V : H ≃ₗᵢ[ℂ] H, Commute (V : H →L[ℂ] H) K.starProjection →
        (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge
            ((A : H →L[ℂ] H) - (C : H →L[ℂ] H)) ≤
          (OperatorIdealFamily.schatten ℂ p (by linarith)).gauge
            ((A : H →L[ℂ] H) - (V : H →L[ℂ] H)) := by
  apply exists_nearest_schatten_commuting_unitary p hp K A hcomm
  have hacute : IsUniformlyAcute (K.map A.toLinearMap) K := by
    simpa only [IsUniformlyAcute, Submodule.projectionGap_def,
      K.norm_projection_image_sub_eq_commutator A] using hnorm
  rw [halmosSourceDefect_eq_bot_of_isUniformlyAcute _ _ hacute,
    halmosTargetDefect_eq_bot_of_isUniformlyAcute _ _ hacute]


end TauCeti.DavisKahan.InfiniteDimensional
